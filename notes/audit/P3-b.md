# Audit P3-b: `Semialgebraic/Finiteness/Cells.lean` (C2, L3a)

**Verdict: ACCEPT.** Required fixes: none.

1. Build: `lake build Semialgebraic.Finiteness.Cells` succeeds. Only warnings: the expected "designed for use with the module system" import warnings (5 imports). No deprecation or linter warnings.
2. Forbidden tokens: grep for sorry/admit/axiom/native_decide/unsafe/implemented_by/extern/opaque/instance/set_option/class names: no hits (not even in comments). No `set_option`.
3. Axioms (scratch `/tmp/audit-p3b/A.lean`):
   - `Semialgebraic.exists_setOf_sign_eq_eq` depends on axioms: [propext, Classical.choice, Quot.sound]
   - `Semialgebraic.compl_iUnion_iInter_pos` depends on axioms: [propext, Classical.choice, Quot.sound]
4. Faithfulness: both statements are textually identical to the brief (binders, implicitness, types, hypotheses, conclusion). Decisive test: `example : <verbatim statement> := fun .. => Semialgebraic.<thm> ..` elaborates for both. Header declares no deviation; none exists.
5. No definitional cheating: no new def/abbrev/structure/class/notation. Sanity and edge cases for L3a:
   - I = 0: LHS = (empty union)ᶜ = univ. RHS: `Fin (J^0) = Fin 1`, one empty intersection = univ. Equal, non-vacuous.
   - I > 0, J = 0: `⋂ j : Fin 0` = univ, so each disjunct of the union is univ and LHS = ∅. RHS: `Fin (0^I) = Fin 0`, empty union = ∅. Equal.
   - I = J = 0: both univ (`0^0 = 1`).
   - Direction: `finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m^n)`, so `.symm k : Fin I → Fin J` is a choice function (type-checks with I as domain, J as codomain). The proof uses `finFunctionFinEquiv φ` and `symm_apply_apply`; the converse direction needs no inverse property. Statement is true for all I, J, as proved.
   - Generic instance: I = 2, J = 2 gives 4 choice functions, so the complement of (A1∩A2)∪(B1∩B2) is the union of 4 basic closed sets {¬A_a ∧ ¬B_b}. Correct.
   - C2 sanity: m = 0 gives the cell univ = {0 = 0}, with the empty g; m = 1, ε = 0 gives f = p², g = 1 (cell {p = 0}); ε = 1 gives f = 0, g = p; ε = -1 gives g = -p. The empty ι/m cases are non-vacuous (cells can be nonempty).
6. Interface theorem: not applicable.
7. Hygiene (non-blocking): proofs short, commented per step; `classical` used locally only; `simp` non-terminal uses are `simp only`; the terminal `simp [..]` calls are fine. Unused import risk: `Mathlib.Algebra.Order.BigOperators.Group.Finset` is used (`sum_eq_zero_iff_of_nonneg`). The report's file-vs-report claims all match the file.
