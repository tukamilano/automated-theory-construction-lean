---
title: Home
---

<section class="hero">
  <p class="eyebrow">GitHub Pages</p>
  <h1>研究ログと実験メモを、このリポジトリのまま公開する。</h1>
  <p class="hero-lead">
    Lean / Mathlib ベースの Automated Theory Construction の進捗を、GitHub Pages 上でそのままブログとして更新できるようにしました。
  </p>
  <div class="hero-actions">
    <a class="button" href="{{ '/write/' | relative_url }}">記事を書く</a>
    <a class="button-secondary" href="{{ '/blog/' | relative_url }}">記事一覧を見る</a>
  </div>
  <div class="hero-actions">
    <a class="button-secondary" href="{{ '/about/' | relative_url }}">このサイトについて</a>
  </div>
</section>

<section class="grid">
  <article class="content-card">
    <p class="eyebrow">Write</p>
    <h2 class="section-title">執筆ページを用意した</h2>
    <p>
      <a class="text-link" href="{{ '/write/' | relative_url }}">Write ページ</a> に、ファイル名の形式、front matter のテンプレート、公開までの手順をまとめました。
    </p>
  </article>

  <article class="content-card">
    <p class="eyebrow">Deploy</p>
    <h2 class="section-title">Push で Pages 配備</h2>
    <p>
      <code>.github/workflows/pages.yml</code> を追加してあるので、対象ブランチへ push すると GitHub Actions で Pages を更新します。
    </p>
  </article>
</section>
