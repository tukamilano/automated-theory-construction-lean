---
title: Write
permalink: /write/
---

<section class="content-card">
  <p class="eyebrow">Write</p>
  <h1 class="section-title">記事を書くためのページ</h1>
  <p>
    このサイトでは、記事は <code>_posts/</code> に Markdown ファイルを追加して書きます。GitHub Pages 側では Jekyll が記事として解釈します。
  </p>
</section>

<section class="grid">
  <article class="content-card">
    <p class="eyebrow">Step 1</p>
    <h2 class="section-title">ファイルを作る</h2>
    <p>
      ファイル名は <code>YYYY-MM-DD-title.md</code> にしてください。たとえば
      <code>_posts/2026-03-24-first-note.md</code> のような形です。
    </p>
  </article>

  <article class="content-card">
    <p class="eyebrow">Step 2</p>
    <h2 class="section-title">最小テンプレートを使う</h2>
    <p>
      下の front matter をそのまま使えば公開できます。<code>excerpt</code> は一覧ページの短い説明です。
    </p>
  </article>
</section>

<section class="content-card">
  <p class="eyebrow">Template</p>
  <h2 class="section-title">コピペ用テンプレート</h2>
  <pre><code>---
title: 記事タイトル
date: 2026-03-24 09:00:00 +0900
categories: [log]
excerpt: 記事の短い説明をここに書く。
---

導入を書く。

## 見出し

本文を書く。
</code></pre>
</section>

<section class="grid">
  <article class="content-card">
    <p class="eyebrow">Step 3</p>
    <h2 class="section-title">本文を書く</h2>
    <p>
      Markdown がそのまま使えます。コードブロック、見出し、箇条書きは通常どおり書いて大丈夫です。
    </p>
  </article>

  <article class="content-card">
    <p class="eyebrow">Step 4</p>
    <h2 class="section-title">push して公開する</h2>
    <p>
      対象ブランチへ push すると、<code>.github/workflows/pages.yml</code> により GitHub Pages が更新されます。
    </p>
  </article>
</section>

<section class="content-card">
  <p class="eyebrow">Tips</p>
  <h2 class="section-title">よく触る場所</h2>
  <p><code>_posts/</code>: 記事本体を置くディレクトリ</p>
  <p><code>blog/</code>: 記事一覧ページ</p>
  <p><code>assets/css/style.css</code>: 見た目の調整</p>
</section>
