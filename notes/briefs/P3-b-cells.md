# Unit P3-b (writer): `Semialgebraic/Finiteness/Cells.lean` — ids C2, L3a

Read `notes/briefs/standing.md`, `PLAN.md` §4.4, then `notes/research/route1-lojasiewicz.md` §3.2 (C2), §3.3 (L3),
§4 (statements, dependency table, risks) and its audit `notes/audit/R1-lojasiewicz.md` (corrections there override
the report). Appendix B of the report contains an unaudited scratch prototype that elaborated at the pins; you may
start from it, but your file must follow the standing brief (specific imports, header, namespace `Semialgebraic`,
comments), and you are responsible for every line.

You write exactly one Lean file, `Semialgebraic/Finiteness/Cells.lean`, and the report
`notes/lean-reports/P3-b.md`. This file is purely combinatorial: it needs no projection theorem and should import
only the Mathlib modules it uses (and, if convenient, `TauCeti.Geometry.RealAlgebraic.Semialgebraic.Basic`). It must
not import `Semialgebraic.Finiteness.Lojasiewicz`, which another writer is writing at the same time.

## Required public statements (namespace `Semialgebraic`; do not change them)

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

Proofs: C2 with `f := ∑ i, if ε i = 0 then p i ^ 2 else 0` and `g i := 1`, `p i`, `-p i` according to
`ε i = 0, 1, -1` (a sum of squares vanishes iff each term does; then compare the three cases of `ε i` using
`sign_eq_zero_iff`, `sign_eq_one_iff`, `sign_eq_neg_one_iff`). L3a pointwise:
`x ∉ ⋃ i, ⋂ j, {0 < Q i j} ↔ ∀ i, ∃ j, Q i j x ≤ 0 ↔ ∃ φ : Fin I → Fin J, ∀ i, 0 ≤ -(Q i (φ i)) x`, then transport
`φ` through `finFunctionFinEquiv : (Fin I → Fin J) ≃ Fin (J ^ I)`.

Build: `lake build Semialgebraic.Finiteness.Cells`. Acceptance: builds; no forbidden token; axioms of every public
theorem are `[propext, Classical.choice, Quot.sound]`.
