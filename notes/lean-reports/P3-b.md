# Report P3-b (writer): `Semialgebraic/Finiteness/Cells.lean` — ids C2, L3a

Status: builds (`lake build Semialgebraic.Finiteness.Cells`, "Build completed successfully"), no `sorry`/`admit`/
`axiom`/`native_decide`/`unsafe`. Only warnings: Lake's "imports … designed for use with the module system;
consider adding `module`" for each Mathlib import (expected: library files are ordinary, non-`module` files per the
standing brief). No linter or deprecation warnings.

## Final statements (copied from the file)

```lean
/-- C2. A sign cell of `m` polynomials is the zero set of one polynomial cut by `m` strict inequalities. -/
theorem exists_setOf_sign_eq_eq {ι : Type*} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ)
    (ε : Fin m → SignType) :
    ∃ (f : MvPolynomial ι ℝ) (g : Fin m → MvPolynomial ι ℝ),
      {x : ι → ℝ | ∀ i, SignType.sign (MvPolynomial.eval x (p i)) = ε i} =
        {x | MvPolynomial.eval x f = 0 ∧ ∀ j, 0 < MvPolynomial.eval x (g j)}

/-- L3a. The complement of a finite union of basic open sets is a finite union of basic closed sets. -/
theorem compl_iUnion_iInter_pos {ι : Type*} {I J : ℕ} (Q : Fin I → Fin J → MvPolynomial ι ℝ) :
    (⋃ i, ⋂ j, {x : ι → ℝ | 0 < MvPolynomial.eval x (Q i j)})ᶜ =
      ⋃ k : Fin (J ^ I), ⋂ i : Fin I,
        {x | 0 ≤ MvPolynomial.eval x (-Q i (finFunctionFinEquiv.symm k i))}
```

Both in namespace `Semialgebraic`, exactly as in the brief.

## Deviations

None. Proofs follow the brief (C2: `f := ∑ i, if ε i = 0 then p i ^ 2 else 0`, `g i := 1 / p i / -p i`;
L3a: pointwise with `choose` and `finFunctionFinEquiv`), adapted from the Appendix B prototype.

## Imports

`Mathlib.Algebra.BigOperators.Fin` (`finFunctionFinEquiv`), `Mathlib.Algebra.MvPolynomial.Eval`,
`Mathlib.Algebra.Order.BigOperators.Group.Finset` (`Finset.sum_eq_zero_iff_of_nonneg`),
`Mathlib.Basic.Real.Basic`, `Mathlib.Basic.Sign.Basic`. No TauCeti import, no import of
`Semialgebraic.Finiteness.Lojasiewicz`.

## Helper lemmas

None (no public helpers).

## Names not as expected

At this Mathlib pin, `Data.Real.Basic` / `Data.Sign.*` live under `Mathlib/Basic/` (`Mathlib.Basic.Real.Basic`,
`Mathlib.Basic.Sign.Defs`/`Basic`). `Set.mem_ofPred_eq` is the non-deprecated replacement of `Set.mem_setOf_eq`.

## `#print axioms`

```
'Semialgebraic.exists_setOf_sign_eq_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.compl_iUnion_iInter_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
```
