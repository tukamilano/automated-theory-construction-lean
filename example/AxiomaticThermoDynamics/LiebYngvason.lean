import AxiomaticThermoDynamics.LiebYngvason.Defs
import AxiomaticThermoDynamics.LiebYngvason.CancellationLaw
import AxiomaticThermoDynamics.LiebYngvason.Entropy
import AxiomaticThermoDynamics.LiebYngvason.Concavity
import AxiomaticThermoDynamics.LiebYngvason.SimpleSystems
import AxiomaticThermoDynamics.LiebYngvason.ThermalEquilibrium
import AxiomaticThermoDynamics.LiebYngvason.Temperature
import AxiomaticThermoDynamics.LiebYngvason.Mixing

/-!
# The Physics and Mathematics of the Second Law of Thermodynamics

A formalization of the paper by Elliott H. Lieb and Jakob Yngvason,
*Physics Reports* **310** (1999), 1–96.

## Overview

This paper develops a rigorous axiomatic foundation for the second law of
thermodynamics, deriving the existence and properties of entropy from a
small set of physically motivated axioms about **adiabatic accessibility**.

### Structure of the formalization

The formalization follows the paper's structure:

1. **Defs**: Core definitions — compound states, the axiom system (A1–A6),
   the comparison hypothesis, the canonical entropy function.

2. **CancellationLaw**: Theorem 2.1 — the cancellation law, the first
   non-trivial consequence of axioms A1–A6.

3. **Entropy**: The entropy construction (Section II.D–E) — Lemmas 2.1–2.3,
   Theorem 2.2 (equivalence of entropy and axioms), Theorem 2.3 (uniqueness).

4. **Concavity**: Convexity of forward sectors and concavity of entropy
   (Section II.F–H) — Theorems 2.6–2.12.

5. **SimpleSystems**: Simple systems and their geometry (Section III) —
   axioms S1–S3, Theorems 3.1–3.7.

6. **ThermalEquilibrium**: Thermal contact and the zeroth law (Section IV) —
   axioms T1–T5, Theorems 4.1–4.8.

7. **Temperature**: Temperature as a consequence of entropy (Section V) —
   Theorems 5.1–5.6.

8. **Mixing**: Mixing, chemical reactions, and additive constants (Section VI) —
   Theorems 6.1–6.2.

### Summary of the axioms

**General axioms (A1–A6):**
- A1: Reflexivity (`X ≺ X`)
- A2: Transitivity (`X ≺ Y` and `Y ≺ Z` implies `X ≺ Z`)
- A3: Consistency (independent processes can be combined)
- A4: Scaling invariance (`X ≺ Y` implies `tX ≺ tY`)
- A5: Splitting and recombination (`X ~ (tX, (1-t)X)`)
- A6: Stability (infinitesimal perturbations don't enlarge accessible states)

**Convex combination axiom (A7):**
- `(tX, (1-t)Y) ≺ tX + (1-t)Y` for convex state spaces

**Simple system axioms (S1–S3):**
- S1: Irreversibility (existence of irreversible processes)
- S2: Lipschitz tangent planes (unique pressure function)
- S3: Connectedness of adiabatic surfaces

**Thermal axioms (T1–T5):**
- T1: Thermal contact (existence of thermal join)
- T2: Thermal splitting
- T3: Zeroth law (thermal equilibrium is transitive)
- T4: Transversality
- T5: Universal temperature range

### Main results

- **Theorem 2.1**: Cancellation law (from A1–A6)
- **Theorem 2.2**: Entropy principle ⟺ axioms A1–A6 + CH
- **Theorem 2.3**: Uniqueness of entropy (up to affine transformation)
- **Theorem 2.8**: Concavity of entropy
- **Theorem 3.7**: Comparison hypothesis for simple systems
- **Theorem 4.8**: Entropy principle for products of simple systems
- **Theorem 5.1**: Uniqueness of temperature
- **Theorem 5.3**: Differentiability of entropy
- **Theorem 5.4**: Energy flows from hot to cold
- **Theorem 6.2**: Weak entropy principle for mixing/reactions

## References

* E. H. Lieb, J. Yngvason, *The physics and mathematics of the second law
  of thermodynamics*, Physics Reports **310** (1999), 1–96.
-/
