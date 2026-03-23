---
title: GitHub Pages を整備した
date: 2026-03-23 12:00:00 +0900
categories: [meta]
excerpt: Lean プロジェクトのリポジトリに、そのまま研究ログを書ける GitHub Pages を追加した。
---

このリポジトリに GitHub Pages を追加して、研究の進捗や実験メモを Markdown で残せるようにした。

## 今回入れたもの

- `_posts/` に記事を置くブログ構成
- `GitHub Actions` 経由の Pages 配備
- project site でも壊れない `baseurl` 対応

## 次にやること

記事を追加するときは、たとえば次のようなファイルを作ればよい。

```md
---
title: 新しい記事
date: 2026-03-24 09:00:00 +0900
---

ここに本文を書く。
```
