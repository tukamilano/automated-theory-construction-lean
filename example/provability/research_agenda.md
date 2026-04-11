# Research Agenda (Provability)

## Themes

- Develop an abstract existence theory for fixed points of operators built from provability and refutability, not only consequences of already-given Gödelian fixed points.
- Clarify which structural assumptions force or obstruct the existence of fixed points, prefixpoints, periodic points, and uniqueness phenomena.
- Treat implication, contraction, and weakening as structural resources whose presence or absence changes what kinds of fixed points can actually be constructed.
- Build toward a reusable account of positive constructions and non-classical counterexamples for operator-level fixed-point principles.

## Valued Problem Types

- Weakest-assumption theorems for existence of fixed points of operators or operator words built from `□` and `⊠`.
- Classification results separating existence, uniqueness up to equivalence, multiplicity, periodicity, and stabilization behavior of such fixed points.
- Systematic test cases for concrete operator words under varied assumptions, such as asking how the fixed-point behavior changes for `(□⊠)^n` as `n` varies, and comparing existence, uniqueness, periodicity, and stabilization across structural settings.
- Sharp boundary theorems identifying which structural assumptions are really responsible for constructing the desired fixed points.
- Counterexamples showing that fixed-point existence for one operator does not automatically transfer to nearby operators or presentations.
- Formal developments that reorganize the story into reusable abstractions for constructing fixed points, not only deriving consequences from them.

## Anti-Goals

- Isolated reproving of paper lemmas when they do not clarify why a desired fixed point exists, fails to exist, or ceases to be unique.
- Example-specific calculations in a single sequent system unless they witness a genuine separation result or expose a reusable construction pattern.
- Overcommitting early to arithmetic codings, syntactic Gödel-number machinery, or implementation-heavy encodings before the abstract existence theory is stable.
- Cosmetic variants of fixed-point theorems that do not change the map of which assumptions are essential for construction.

## Canonical Targets

- A reusable abstraction for operator-level fixed points that subsumes Gödel and Henkin fixed points as special cases.
- A characterization theorem, or sharp boundary theorem, for when a desired operator admits a fixed point under abstract provability structure assumptions.
- Boundary results isolating which forms of contraction, weakening, or implication are the real drivers of fixed-point existence and uniqueness.
- A formalized non-classical example showing existence for some fixed-point principles together with failure of transfer, uniqueness, or formalized G2.
- A theory-level summary theorem explaining which fixed-point phenomena belong to the abstract operator theory and which require stronger presentation-specific structure.

## Soft Constraints

- Prefer operator-level existence and boundary statements over consequence-only corollaries.
- When extending the library, introduce assumptions in the weakest reusable form available, so separation results remain visible.
- Favor a small number of definitions that support both positive existence theorems and negative counterexamples.
