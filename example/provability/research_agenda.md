# Research Agenda for the APS Provability Toy

This document sets out the current research agenda for APS, the very simple model proposed by Beklemishev and Shamkanov for understanding provability. The aim is to organize work around structural questions about fixed points of composites of the operators `□` and `⊠`, rather than around isolated example calculations alone.

## 1. Themes

Let `△` denote any operator obtained by composing `□` and `⊠` finitely many times, for example `□⊠□`.

* **Existence and uniqueness of fixed points for composites `△`**
  Clarify when a given composite `△` has a fixed point, and when such a fixed point must be unique.
* **Structural conditions for generalized composites**
  When `△` is generalized, identify conditions that genuinely characterize the existence or uniqueness of fixed points, rather than conditions tailored to a single construction.
* **Counterexample models for nonexistence of fixed points**
  If `△` has no fixed point, determine what kinds of APS models can witness this failure.
* **Minimal causes of counterexample formation**
  Isolate which structural assumptions are truly necessary for constructing a model in which a given `△` has no fixed point.

## 2. Valued Problem Types

Within this agenda, the following kinds of results are especially valuable:

* **Order-theoretic proofs with reuse value**
  Prefer proofs that connect APS fixed-point questions to existing order-theoretic ideas, since such methods may apply more broadly. In particular, meaningful connections with major fixed-point principles such as the Knaster-Tarski theorem would be highly valuable.
* **Sharp separation between finite and infinite underlying sets**
  Establish results that distinguish the role of finiteness from that of infiniteness in APS. For example, it would be valuable to show that certain counterexample models exist on infinite underlying sets but cannot occur on finite ones.
* **Results stated for genuinely general classes of `△`**
  Favor statements that continue to make sense beyond one narrowly specified syntactic form of composite operator.
* **Logically meaningful phenomena even in restricted settings**
  Even when a result is not maximally general, it is valuable if it reveals phenomena relevant to mathematical logic or to themes surrounding the incompleteness theorems.

## 3. Anti-Goals

The following kinds of outputs are not mathematically interesting for this project and should be avoided:

* **Superficial reformulations**
  Avoid proposals that merely rewrite existing statements or proofs in different notation without producing new mathematical insight.
* **Complexity without conceptual gain**
  Avoid making `△` or its surrounding assumptions more complicated when the only effect is to make calculations harder without creating new structure or explanation.
* **Overly specialized conditions**
  Avoid generating conditions that are optimized for a very specific situation but do not plausibly capture broader fixed-point behavior.

## 4. Canonical Targets

1. **A characterization of fixed-point existence and uniqueness**
   Develop conditions on composites `△` that explain when fixed points exist and when they are uniquely determined.
2. **A theory of counterexample construction**
   Determine what kinds of APS models witness the nonexistence of fixed points, and identify which structural ingredients are genuinely necessary in such constructions.
3. **A finite-versus-infinite dichotomy**
   Clarify whether the existence of certain counterexamples depends essentially on the underlying set being infinite, or whether similar failures already occur in finite APS models.
4. **Odd-parity and even-parity generalizations**
   Define and study two generalizations of `△`: one in which `⊠` appears an odd number of times, and one in which `⊠` appears an even number of times.

## 5. Sample Problems

As a check on understanding, the following concrete questions should be kept in view:

1. Does there exist an APS with no Gödelian fixed point such that `⊠⊤` is refutable?
2. Does there exist an APS in which `⊤` is not maximal and which has a Gödelian fixed point not equivalent to `⊠⊤`?
3. Does there exist an APS in which `⊤` is not maximal but Gödelian fixed points do exist, and in which `⊠⊤` is not equivalent to `⊠⊠⊤`?
4. Does there exist an APS in which `⊤` is maximal but no Gödelian fixed point exists?
