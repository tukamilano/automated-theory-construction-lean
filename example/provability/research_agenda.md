# Research Agenda (Provability)

## Themes

- Develop the abstract theory of Gödel's second incompleteness theorem at the level of consequence relations and provability/refutability operators, not only for specific arithmetical encodings.
- Clarify the boundary between what follows from minimal abstract provability structure axioms and what genuinely requires implication, contraction, or weakening.
- Treat contraction and weakening as structural resources whose presence or absence changes the behavior of fixed points, formalized G2, and Löb-style principles.
- Build toward a reusable account of non-classical counterexamples, especially systems with fixed points where Löb conditions hold but formalized G2 or uniqueness fails.

## Valued Problem Types

- Equivalence and transfer results showing how APS-style axioms, implication-based formulations, and sequent-calculus presentations correspond to one another.
- Sharp boundary theorems identifying the weakest structural assumptions under which irrefutability of inconsistency, uniqueness of Gödelian fixed points, or Löb-style consequences still go through.
- Classification results for fixed points: existence, uniqueness up to equivalence, multiplicity, and their relation to inconsistency assertions such as `⊠⊤` or `□⊥`.
- Counterexamples that separate nearby principles, for example: Löb conditions from formalized G2, weakening from uniqueness, or fixed-point existence from diagonalizable-algebra behavior.
- Formal developments that reorganize the story of the paper into a small number of reusable abstractions rather than many theorem-specific encodings.

## Anti-Goals

- Isolated reproving of paper lemmas when they do not clarify the structural role of contraction, weakening, or the provability/refutability interface.
- Example-specific calculations in a single sequent system unless they witness a genuine separation result or expose a new structural phenomenon.
- Overcommitting early to arithmetic codings, syntactic Gödel-number machinery, or implementation-heavy encodings before the abstract layer is stable.
- Cosmetic variants of fixed-point theorems that do not change the map of which assumptions are essential.

## Canonical Targets

- A modular formal package for abstract provability structures that cleanly derives irrefutability of `⊠⊤` from Gödelian fixed points.
- A precise account of which additional assumptions recover the implication-based/Löb presentation from the abstract APS presentation.
- Boundary results isolating `□`-contraction and `□`-weakening as the real drivers of formalized G2 and fixed-point uniqueness.
- A formalized non-classical example showing that fixed points and Löb-style principles can coexist with failure of formalized G2 or failure of uniqueness.
- A theory-level summary theorem explaining when one can and cannot pass from fixed-point-rich provability structures to something like diagonalizable algebras.

## Soft Constraints

- Prefer statements that improve the global picture of the theory over local proof artifacts.
- Stay close to the vocabulary already present in [Theory.lean](/Users/milano/ATC_private/example/provability/Theory.lean): abstract consequence relations, APS, Gödelian fixed points, consistency, and `⊠⊤`.
- When extending the library, introduce assumptions in the weakest reusable form available, so separation results remain visible.
- Favor a small number of definitions that support both positive transfer theorems and negative counterexamples.
