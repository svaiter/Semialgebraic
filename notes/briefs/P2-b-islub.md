# Unit P2-b (writer): `Semialgebraic/Growth/IsLUB.lean` — plan id G3

Read `notes/briefs/standing.md` and `PLAN.md` §4.2 first. You write exactly one file,
`Semialgebraic/Growth/IsLUB.lean`, and the report `notes/lean-reports/P2-b.md`.

## Required public statements (namespace `Semialgebraic`; do not change them)

```lean
/-- G3. The graph of the fibrewise least upper bound of a semialgebraic family of subsets of `ℝ` is
semialgebraic. `Sum.inl` coordinates are the parameters, `Sum.inr ()` is the value. No finiteness of `σ`. -/
theorem isSemialgebraic_setOf_isLUB {σ : Type*} {E : Set (σ ⊕ Unit → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    TauCeti.IsSemialgebraic
      {z : σ ⊕ Unit → ℝ | IsLUB {u : ℝ | Sum.elim (z ∘ Sum.inl) (fun _ => u) ∈ E} (z (Sum.inr ()))}

/-- G3 in the plane: coordinate `0` is the value, coordinate `1` is the parameter. -/
theorem isSemialgebraic_setOf_isLUB_fin_two {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    TauCeti.IsSemialgebraic {z : Fin 2 → ℝ | IsLUB {u : ℝ | ![u, z 1] ∈ E} (z 0)}
```

## Proof route

`IsLUB A s ↔ (∀ u ∈ A, u ≤ s) ∧ (∀ s', s' < s → ∃ u ∈ A, s' < u)` (prove this for subsets of `ℝ`, e.g. from
`isLUB_iff_le_iff`, `lt_isLUB_iff`, or directly from `IsLUB`, `upperBounds`, `lowerBounds`).

Each half is a semialgebraic condition on `z`, obtained with TauCeti's projection lemmas over `ℝ`
(`TauCeti/Geometry/RealAlgebraic/Semialgebraic/Image.lean`, instance from
`TauCeti/Geometry/RealAlgebraic/CAD/Existence.lean` — import both):

```lean
theorem TauCeti.IsSemialgebraic.setOf_exists_sumElim [Finite τ] {s : Set (σ ⊕ τ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic {x : σ → R | ∃ y : τ → R, Sum.elim x y ∈ s}
theorem TauCeti.IsSemialgebraic.setOf_forall_sumElim [Finite τ] {s : Set (σ ⊕ τ → R)} (hs : IsSemialgebraic s) :
    IsSemialgebraic {x : σ → R | ∀ y : τ → R, Sum.elim x y ∈ s}
```

together with pullbacks along coordinate maps (`TauCeti.IsSemialgebraic.preimage_comp`,
`TauCeti.IsSemialgebraic.preimage_eval`), Boolean operations, and polynomial sign conditions
(`TauCeti.isSemialgebraic_eval_le`, `isSemialgebraic_eval_lt`, with `MvPolynomial.X`), all in
`TauCeti/Geometry/RealAlgebraic/Semialgebraic/Basic.lean` (signatures in `notes/api/tauceti-semialgebraic-1.txt`).

* Upper bound: `{z | ∀ u, (z∘inl, u) ∈ E → u ≤ z (inr ())}`. Work in `(σ ⊕ Unit) ⊕ Unit → ℝ` with points
  `w = Sum.elim z (fun _ => u)`: the set `{w | (w (inl (inl ·)), w (inr ())) ∉ E ∨ w (inr ()) ≤ w (inl (inr ()))}`
  is semialgebraic (pullback of `E` along a coordinate map, union with a polynomial inequality), then
  `setOf_forall_sumElim` with `τ := Unit`. A quantifier over `u : ℝ` and one over `y : Unit → ℝ` are interchanged by
  `y ↦ y ()` / `u ↦ fun _ => u`.
* Least: `{z | ∀ s', s' < z (inr ()) → ∃ u, (z∘inl, u) ∈ E ∧ s' < u}`: one `∃` over `u` inside one `∀` over `s'`,
  so the ambient space is `((σ ⊕ Unit) ⊕ Unit) ⊕ Unit → ℝ`; proceed from the inside out.
* The `Fin 2` form follows from the general form with `σ := Unit` by pulling back along a coordinate bijection
  `Fin 2 ≃ Unit ⊕ Unit` (`TauCeti.isSemialgebraic_preimage_comp_equiv` or `preimage_comp` both ways); be careful
  that coordinate `0` is the value and `1` the parameter.

TauCeti also has first-order-formula tools (`Semialgebraic/QuantifierElimination.lean`,
`FirstOrder.Language.Formula.isSemialgebraic_setOf_realize`); use whichever is shorter.

It is useful (and encouraged) to factor out small general helpers that later units will reuse, as public lemmas in
this file, for example: "a real quantifier form of `setOf_exists_sumElim`/`setOf_forall_sumElim` with `τ := Unit`":

```lean
theorem isSemialgebraic_setOf_exists_real {σ : Type*} {S : Set (σ ⊕ Unit → ℝ)} (hS : TauCeti.IsSemialgebraic S) :
    TauCeti.IsSemialgebraic {x : σ → ℝ | ∃ u : ℝ, Sum.elim x (fun _ => u) ∈ S}
theorem isSemialgebraic_setOf_forall_real {σ : Type*} {S : Set (σ ⊕ Unit → ℝ)} (hS : TauCeti.IsSemialgebraic S) :
    TauCeti.IsSemialgebraic {x : σ → ℝ | ∀ u : ℝ, Sum.elim x (fun _ => u) ∈ S}
```

Acceptance: the file builds with `lake build Semialgebraic.Growth.IsLUB`; no forbidden token; axioms of the public
theorems are `[propext, Classical.choice, Quot.sound]`.
