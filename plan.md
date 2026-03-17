# LLMによる理論自動構築（equational theory 限定）

## 1. 目的

本リポジトリの短期目標は、equational theory に対して次の最小ループを壊さず回すことである。

1. open problem を 1 つ選ぶ
2. prover が `proof | counterexample | stuck` を返す
3. Lean formalization / verify を行う
4. verify 成否に応じて状態を更新する
5. 試行後に得た新規問題（0〜2件）を open に追加する

重点は `open / solved / counterexample` の状態遷移と、`Derived.lean` を通じた再利用に置く。

---

## 2. 基本設定

対象は equational theory に限定する。

- `open_problems.jsonl`: 未解決問題
- `solved_problems.jsonl`: verify 済み定理
- `counterexamples.jsonl`: verify 済み反例

初期 seed は人間が与える。

---

## 3. 最小ループ

1. `open_problems.jsonl` から picker が 1 問選ぶ
2. prover が対象問題を試行し、`proof | counterexample | stuck` を返す
3. prover は試行後に新規問題を 0〜2 件返してよい
4. `proof` または `counterexample` のとき Lean formalization を行う
5. `Scratch.lean` を `lake env lean` で verify する
6. 成功時は `open -> solved` または `open -> counterexample`
7. 失敗時・`stuck` 時は open 維持で `n` を増やす

新規問題生成は、元問題の試行後に行う。

---

## 4. 役割分担

### 4.1 LLM 側

- picker: `selected_problem_id` を 1 つ返す
- prover: `result` と補助テキスト、`new_problems`（最大2件）を返す
- Lean formalization: 既存 `.codex` 運用（lean-rule / mathlib-usage）を再利用する

### 4.2 外部スクリプト側（deterministic）

- JSONL 読み書き
- id 発番
- 重複フィルタ（軽量 dedup）
- 状態遷移
- `Derived.lean` への追記

transaction を伴う更新は LLM に任せない。

---

## 5. 新規問題の扱い

この段階では `subgoal / byproduct / candidate` を厳密に分けない。
「試行後に得られた新規問題」をそのまま open に追加する。

- 返却数は 0〜2 件
- 明らかな trivial variation は避ける
- 重複除去は完全一致正規化レベルの軽量 dedup を scripts 側で担保する

---

## 6. 重複回避方針

prototype では canonicalization を導入しない。

- prover に重複回避の努力義務を持たせる
- scripts で軽量 dedup を行う
- 完全な同値判定はスコープ外

---

## 7. verify と失敗時ポリシー

- proof verify 成功: solved へ移動し、theorem を `Derived.lean` に追記
- counterexample verify 成功: counterexamples へ移動
- verify 失敗 / stuck: open 維持で `n` 増分

`n` は上限付き運用で、外部設定で変更可能。

また、自然言語 `stmt` が Lean 化不能な場合は reject として扱い、open 維持 + `n` 増分で統一する。

---

## 8. 現時点で未実装のもの

次はまだ導入しない。

- graph 管理
- artifacts 保存
- 詳細ログ基盤
- scoring / critic
- finite model search
- heavy repair loop
- canonicalization
- candidate queue

---

## 9. まとめ

この計画は、

- picker / prover / Lean formalization の3役
- deterministic な state update
- Lean verification を最終判定

を軸に、まず 1 問の縦切りを安定に通すことを目的とする。
