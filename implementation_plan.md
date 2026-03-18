# LLMによる理論自動構築（equational theory 限定）最小 prototype 実装計画

## 0. 目的

本計画の目的は、equational theory に対して以下のループを **最小構成で安定に回す prototype** を作ることである。

1. open problem を 1 つ選ぶ
2. LLM に証明または反例探索をさせる
3. Lean で verify する
4. 試行後に得られた新規問題を回収する
5. verify 成否に応じて状態を更新する
6. verify 済みの定理を後続の証明で再利用できるようにする

この段階では、理論の明示的 graph 管理、詳細ログ、artifacts 保存、高度な scoring は導入しない。

重点は以下に置く。

1. `open / solved / counterexample` の状態遷移が壊れずに回ること
2. prover が元問題を一通り試した後に、新規問題を適切に提案できること
3. 既存の skills / AGENTS.md を流用して自然言語または semi-formal な内容を Lean に落とせること
4. verify 済みの定理を `Derived.lean` に集約し、後続の試行で再利用できること

---

## 1. 基本方針

### 1.1 LLM に任せる部分

この prototype では新規 skill を 3 つに絞る。

#### (A) picker

役割:

* open problems から次に試す問題を 1 つ選ぶ

出力:

```json
{"selected_problem_id": "op_000031"}
```

score や reason は要求しない。

#### (B) prover

役割:

* 対象問題について proof / counterexample / stuck を返す
* 元問題への試行が終わった後に、その試行から得られた新規問題を 0〜2 個返す

重要:

* 新規問題生成は本題の代替ではなく、試行後の抽出である
* 新規問題は、今回の試行中に見えた補題・一般化・派生法則・放置したが気になるテーマから作る
* 新規問題は stuck 時だけでなく、proof 成功時や counterexample 試行時にも返してよい
* 新規問題は theory language 内に限らなくてよい
* ただし、明らかな変数名変更・左右反転・自明な対称変形は避ける

#### (C) Lean formalization

役割:

* prover の出力を既存の skills / AGENTS.md を使って Lean の statement / proof skeleton / counterexample 記述に落とす
* `Theory.lean` と `Derived.lean` を参照したうえで `Scratch.lean` を生成できる形にする

### 1.2 外部スクリプトで機械的に制御する部分

* JSONL の読み書き
* id 発番
* Lean の実行
* verify 成否に応じた状態更新
* `Derived.lean` への追記
* 新規問題の open への追加

状態更新は transaction なので LLM に任せない。

---

## 2. 最小ループ

システムは以下のループを回す。

1. `open_problems.jsonl` を読む
2. picker が次に試す問題を 1 つ選ぶ
3. prover が対象問題について `proof / counterexample / stuck` のいずれかを返す
4. prover が、元問題への試行後に得られた新規問題を 0〜2 個返す
5. 新規問題があれば、それらをそのまま `open_problems.jsonl` に追加する
6. `proof` または `counterexample` の場合は Lean formalization を呼ぶ
7. `Scratch.lean` を生成して Lean verify を実行する
8. verify 成功なら `solved_problems.jsonl` または `counterexamples.jsonl` に移す
9. proof verify 成功なら theorem を `Derived.lean` に追記する
10. verify 失敗または `stuck` の場合は open に残し、試行回数 `n` を増やす

重要なのは、新規問題生成が **元問題への試行の後段で行われる** ことである。

* 先に元問題に集中する
* その試行結果を踏まえて次世代の問題を抽出する
* proof 成功時にも理論拡張の種を回収する

---

## 3. ディレクトリ構成

```text
project/
  data/
    open_problems.jsonl
    solved_problems.jsonl
    counterexamples.jsonl
  theory/
    Theory.lean
    Derived.lean
    Scratch.lean
  prompts/
    picker.md
    prover_simple.md
  scripts/
    run_loop.py
    state_update.py
    lean_verify.py
    append_derived.py
  theories/
    semigroup_like_01/
      seeds.jsonl
```

この段階では以下は持たない。

* artifacts ディレクトリ
* 詳細 JSONL ログ
* graph 構造
* candidate queue
* canonicalization スクリプト

必要ならデバッグ用に `last_error.txt` 程度は置いてよいが、本仕様の中心には含めない。

---

## 4. 状態ファイルの設計

JSONL はできる限り簡潔にする。
`stmt` は Lean の命題文字列または今後形式化したい semi-formal / natural language を含んでもよい。

### 4.1 open_problems.jsonl

```json
{
  "id": "op_000031",
  "stmt": "∀ x y z, op (op x y) z = op x (op y z)",
  "src": "seed",
  "n": 0
}
```

または生成問題の例:

```json
{
  "id": "op_000105",
  "stmt": "Investigate whether a left-cancellation law is enough to derive the target associativity pattern.",
  "src": "generated",
  "n": 0
}
```

最小意味:

* `id`: 問題 id
* `stmt`: 問題記述
* `src`: `seed | generated`
* `n`: 試行回数

### 4.2 solved_problems.jsonl

```json
{
  "id": "op_000031",
  "stmt": "∀ x y z, op (op x y) z = op x (op y z)",
  "thm": "thm_op_000031"
}
```

* `thm`: `Derived.lean` に追加された theorem 名

### 4.3 counterexamples.jsonl

```json
{
  "id": "op_000078",
  "stmt": "∀ x y, op x y = op y x"
}
```

この段階では以下は持たない。

* candidate 専用ファイル
* `parent`
* `reasoning_events`
* 複雑な provenance
* score
* canonical form

---

## 5. 新規問題の意味

この prototype では `subgoal` / `byproduct` / `candidate` を厳密に分けず、**試行後に抽出された新規問題**をそのまま open に追加する。

### 5.1 新規問題の位置づけ

新規問題は独立に思いつかれたものではなく、**1 回の試行の post-processing として得られた次世代問題**である。

典型例:

* 今回の証明を直接進める補題
* 証明中に見えた一般化
* 途中で何度も現れた派生法則
* 今回は追わなかったが独立に面白いテーマ

### 5.2 保存条件

保存対象は以下のようなものを含んでよい。

* Lean の statement としてすぐ書ける命題
* 現段階では theory language 外の語彙を含む問題記述
* 今後形式化すべき一般化や補題のメモに近い問題文

ただし、以下は避ける。

* 明らかな変数名変更
* 左右反転だけの重複
* 自明な対称変形
* 内容の薄い trivial problem

### 5.3 生成タイミング

新規問題生成は stuck 時の代替出力ではない。
**各試行の最後に、必要なら 0〜2 個返す**。

* `proof` のとき: 一般化や派生法則が出やすい
* `stuck` のとき: 直接補題や未解決テーマが出やすい
* `counterexample` のとき: 境界条件や別方向の問題が出やすい

### 5.4 なぜ candidate queue を持たないか

prototype 段階では、candidate queue を挟むよりも

* 問題を解く
* その試行から新しい問題を得る
* それをそのまま次の open problem として扱う

という自己増殖型のループにした方が単純である。

---

## 6. 重複回避の方針

この prototype では canonicalization を導入しない。

代わりに、重複回避は主に以下に依存する。

1. prover が `Derived.lean` と既存 open problems を見たうえで、既知のものをなるべく再提案しないこと
2. prover が変数名変更・左右反転・自明な対称変形を避けること
3. 新規問題数を 0〜2 個に制限して増殖を抑えること

完全な重複除去は目指さない。
この段階では多少の重複は許容し、その挙動を観察する。

---

## 7. picker の仕様

### 7.1 役割

* open problems の中から次に試す問題を 1 つ選ぶ

### 7.2 入力

* theory axioms
* `Derived.lean` で利用可能な既知定理の要約
* open problems の列

### 7.3 出力

```json
{
  "selected_problem_id": "op_000031"
}
```

### 7.4 方針

* score を要求しない
* reason を要求しない
* 数式表現や問題記述を見て 1 問選ぶだけにする

---

## 8. prover の仕様

### 8.1 役割

1 問に対して

* まず証明または反例探索を試みる
* `proof | counterexample | stuck` のいずれかを返す
* その後、その試行から得られた新規問題を 0〜2 個返す

### 8.2 出力形式

```json
{
  "problem_id": "op_000031",
  "result": "stuck",
  "proof_text": "",
  "counterexample_text": "",
  "new_problems": [
    "A left-cancellation law may be enough to justify the blocked step.",
    "Investigate whether the repeatedly appearing idempotence-like pattern can be derived independently."
  ]
}
```

### 8.3 制約

prover には以下を明記する。

* まず対象問題を一通り試すこと
* 新規問題生成はその後に行うこと
* 新規問題は今回の試行内容に依存したものに限ること
* 新規問題は最大 2 個まで
* `Derived.lean` と既存 open problems を見て、既知のものや明らかな重複を避けること
* trivial problem は出さないこと

重要文言:

> First attempt the given problem. Only after that, propose at most two new problems that arose from the attempt itself.

---

## 9. Lean formalization の仕様

### 9.1 役割

既存の skills / AGENTS.md を流用して以下を行う。

* target statement を Lean theorem に落とす
* `proof_text` から Lean proof skeleton を生成する
* `counterexample_text` があれば Lean で検証可能な形にする
* `Theory.lean` と `Derived.lean` を参照した `Scratch.lean` を生成する

### 9.2 入力の想定

主に prover 出力の以下を使う。

* `problem_id`
* 対象問題の `stmt`
* `result`
* `proof_text` または `counterexample_text`

### 9.3 出力形式のイメージ

```json
{
  "problem_id": "op_000031",
  "theorem_name": "thm_op_000031",
  "mode": "proof",
  "lean_code": "import Theory
import Derived

theorem thm_op_000031 : ... := by
  ..."
}
```

または

```json
{
  "problem_id": "op_000078",
  "mode": "counterexample",
  "lean_code": "import Theory
import Derived

..."
}
```

### 9.4 実装方針

* 新規に重い formalizer を設計しない
* すでに持っている Lean 形式化 skill を薄いラッパーで呼ぶ
* 初期段階では repair loop は 0〜1 回に抑える

---

## 10. Lean verify の仕様

### 10.1 役割

* `Scratch.lean` を実行する
* `Theory.lean` と `Derived.lean` を import した状態で検証する
* 成功 / 失敗を返す

### 10.2 出力例

```json
{
  "problem_id": "op_000031",
  "success": true,
  "mode": "proof",
  "stderr": "",
  "stdout": ""
}
```

```json
{
  "problem_id": "op_000031",
  "success": false,
  "mode": "proof",
  "stderr": "type mismatch ...",
  "stdout": ""
}
```

### 10.3 成功時の状態遷移

* proof verify 成功: `open -> solved`
* counterexample verify 成功: `open -> counterexample`
* proof verify 成功時は theorem 本文を `Derived.lean` に追記する

### 10.4 失敗時の扱い

* open に残す
* `n` を増やす
* 必要なら 1 回だけ repair を試す
* `n` は上限 `MAX_ATTEMPTS` で打ち止めにする（固定値だが外部設定で変更可能にする）
* `stmt` が Lean 化不能（natural language のみで形式化不可）な場合は reject として扱い、open 維持 + `n` 増分に統一する

---

## 11. `Derived.lean` の役割

verify に成功した定理は `Derived.lean` に集約する。

```lean
import Theory

 theorem thm_op_000031 : ∀ x y z, op (op x y) z = op x (op y z) := by
   ...

 theorem thm_op_000044 : ... := by
   ...
```

以後の `Scratch.lean` では

```lean
import Theory
import Derived
```

として、既知結果を直接再利用できるようにする。

また、`Derived.lean` は既知定理の蓄積先であるだけでなく、prover が重複提案を避けるための主要な参照先でもある。

---

## 12. state update の仕様

state update は外部スクリプトが deterministic に行う。

### 12.1 やること

* `open_problems.jsonl` から対象問題を削除または更新する
* `solved_problems.jsonl` / `counterexamples.jsonl` に append する
* `n` を更新する
* 新規問題を `open_problems.jsonl` に append する
* verify 成功した theorem を `Derived.lean` に追記する

### 12.2 LLM に任せない理由

* transaction だから
* format 破壊を避けたいから
* status の誤更新を避けたいから

---

## 13. 「解けない問題」の意味

この prototype における「解けない」は数学的 impossibility ではなく、**現在の計算資源・時間・試行予算の下で未解決**という意味である。

つまり `stuck` は本質的に

* unresolved under current budget

を表す。

典型例:

* 制限ステップ数で証明が出なかった
* 制限ターン数で repair できなかった
* 制限時間内に proof / counterexample のどちらも得られなかった

したがって `open` に残すことは failure というより deferred processing である。

---

## 14. 初期 theory の選び方

最初の theory は狭くする。

候補:

* semigroup / monoid 風理論
* lattice-like axioms

最初に扱いやすい法則:

* associativity
* identity
* idempotence
* absorption
* commutativity

理由:

* 項構造が単純
* Lean 化しやすい
* rewrite 的発想が出やすい
* 試行後に有用な新規問題が出やすい

---

## 15. 実装ステップ

### Step 1. データ層を作る

* JSONL schema を確定する
* `open / solved / counterexample` を作る
* id 発番規則を実装する

### Step 2. picker を作る

* open problems を読み込む
* theory / solved / open を picker skill に渡す
* `selected_problem_id` だけ返す

### Step 3. prover を作る

* 1 問題について `proof / counterexample / stuck` を返す
* 試行後の新規問題を 0〜2 個返す
* 重複や trivial variation をなるべく避ける

### Step 4. Lean formalization を接続する

* 既存の skills / AGENTS.md を呼ぶ
* `proof_text` / `counterexample_text` から Lean code を生成する
* `Scratch.lean` を出力する

### Step 5. Lean verify を作る

* Lean ファイルを書き出す
* 実行する
* 成否とエラーを JSON 化する

### Step 6. state updater を作る

* verify 結果に応じて JSONL を更新する
* 新規問題を open に追加する
* `Derived.lean` に theorem を追記する

### Step 7. ループを統合する

* 1 問だけ処理する `run_loop.py` を作る
* 1 周回る縦切りを完成させる
* その後で複数周回にする

---

## 16. 最初に作るべきスクリプト

優先順位は以下。

1. `state_update.py`
2. `lean_verify.py`
3. `append_derived.py`
4. `run_loop.py`（まずは 1 問だけ回す版）
5. picker / prover / Lean formalization を呼ぶラッパー

---

## 17. 最初のマイルストーン

### Milestone 1

* human seed を `open_problems.jsonl` に入れる
* picker が 1 問選ぶ
* prover が `result` と `new_problems` を返す
* 新規問題があれば open に追加する
* Lean formalization を呼ぶ
* Lean verify を実行する
* proof 成功なら `Derived.lean` に追記し `solved` に移す
* failure / stuck なら open に残す

### Milestone 2

* 2 周以上ループが回る
* proof 成功時にも新規問題が生まれることを確認する
* open の増殖が極端でないかを観察する

### Milestone 3

* Lean error に対して 1 回だけ repair を試す
* 重複が実用上どの程度問題になるかを観察する

---

## 18. 今回は未実装とするもの

* artifacts 保存
* 詳細ログ基盤
* reasoning events
* `parent` や複雑な provenance
* graph 管理
* scoring
* critic
* finite model search
* heavy repair loop
* canonicalization
* candidate queue
* semantic duplicate checker

これらは prototype が安定に回った後で拡張する。

---

## 19. 現時点での最終仕様まとめ

この prototype は次の思想で実装する。

* 新規 skill は `picker`, `prover`, `Lean formalization` の 3 つに絞る
* JSONL はできる限り簡潔にする
* `stmt` は Lean の命題文字列でも semi-formal / natural language でもよい
* `parent` は持たない
* reasoning events は持たない
* canonicalization は行わない
* candidate queue は持たない
* prover はまず元問題を試し、その後に新規問題を最大 2 個まで返す
* 新規問題はそのまま open に追加する
* 重複回避は主に `Derived.lean` と既存 open problems を見た prover の判断に委ねる
* state update は外部スクリプトが機械的に行う
* `n` は上限付きで運用し、上限値は外部設定で変更可能にする
* Lean 化不能な natural language `stmt` は reject して open 維持にする
* verify 済み theorem は `Derived.lean` に集約し、後続の証明で再利用する
* Lean verification を最終判定にする
* まずは 1 問の縦切りを安定に通すことを優先する

---

## 20. 直近の実装タスク

直近で着手する順番は以下。

1. JSONL schema を確定する
2. `open_problems.jsonl` に初期 seed を流し込む
3. picker の最小プロンプトを書く
4. prover の最小プロンプトを書く
5. 既存 Lean formalization skill を呼ぶラッパーを書く
6. Lean verify ラッパーを書く
7. 新規問題の open 追加を含む state update を実装する
8. 1 問だけ回す `run_loop.py` を作る

この順で進めれば、prototype の最初の縦切りが作れる。
