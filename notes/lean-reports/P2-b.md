# P2-b report: `Semialgebraic/Growth/IsLUB.lean` (plan id G3)

Build: `lake build Semialgebraic.Growth.IsLUB` succeeds with no errors and no warnings.
No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`. Imports: `TauCeti.Geometry.RealAlgebraic.CAD.Existence`,
`TauCeti.Geometry.RealAlgebraic.Semialgebraic.Image` (only these two).

## Final statements (verbatim from the file, namespace `Semialgebraic`)

```lean
theorem isSemialgebraic_setOf_isLUB {σ : Type*} {E : Set (σ ⊕ Unit → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    TauCeti.IsSemialgebraic
      {z : σ ⊕ Unit → ℝ | IsLUB {u : ℝ | Sum.elim (z ∘ Sum.inl) (fun _ => u) ∈ E} (z (Sum.inr ()))}

theorem isSemialgebraic_setOf_isLUB_fin_two {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    TauCeti.IsSemialgebraic {z : Fin 2 → ℝ | IsLUB {u : ℝ | ![u, z 1] ∈ E} (z 0)}
```

## Deviations

None. Statements are exactly as in the brief.

## Reusable helper lemmas (public, namespace `Semialgebraic`)

```lean
theorem isSemialgebraic_setOf_exists_real {σ : Type*} {S : Set (σ ⊕ Unit → ℝ)}
    (hS : TauCeti.IsSemialgebraic S) :
    TauCeti.IsSemialgebraic {x : σ → ℝ | ∃ u : ℝ, Sum.elim x (fun _ => u) ∈ S}
theorem isSemialgebraic_setOf_forall_real {σ : Type*} {S : Set (σ ⊕ Unit → ℝ)}
    (hS : TauCeti.IsSemialgebraic S) :
    TauCeti.IsSemialgebraic {x : σ → ℝ | ∀ u : ℝ, Sum.elim x (fun _ => u) ∈ S}
theorem isSemialgebraic_setOf_le_coord {ι : Type*} (i j : ι) :
    TauCeti.IsSemialgebraic {x : ι → ℝ | x i ≤ x j}
theorem isSemialgebraic_setOf_lt_coord {ι : Type*} (i j : ι) :
    TauCeti.IsSemialgebraic {x : ι → ℝ | x i < x j}
theorem isLUB_iff_forall_lt_exists {A : Set ℝ} {s : ℝ} :
    IsLUB A s ↔ (∀ u ∈ A, u ≤ s) ∧ ∀ s' < s, ∃ u ∈ A, s' < u
```

## Names not as expected / traps

* `Set.mem_setOf` is deprecated at these pins; use `Set.mem_ofPred` (in `Mathlib/Data/Set/Operations.lean`).
* An explicit `import Mathlib.Order.Bounds.Basic` triggers a "designed for use with the module system" warning
  in a non-`module` file; dropped (it is imported transitively by TauCeti).
* Pulling `E` back along `Sum.elim …` coordinate maps: `simp [Sum.comp_elim]` does not close the goal; the working
  pattern is `exact Iff.of_eq (congrArg (· ∈ E) (funext fun i => by cases i <;> rfl))`.
* In `Fin 2` proofs, binder types of `fun _ => …` inside `Sum.elim` must be annotated (`fun _ : Unit => …`),
  otherwise elaboration fails.

## Proof route

As in the brief: `isLUB_iff_forall_lt_exists`; upper-bound half via `isSemialgebraic_setOf_forall_real` over
`(σ ⊕ Unit) ⊕ Unit`; least half via `isSemialgebraic_setOf_exists_real` over `((σ ⊕ Unit) ⊕ Unit) ⊕ Unit` and then
`isSemialgebraic_setOf_forall_real`; `Fin 2` form from `σ := Unit` with pullbacks along
`![Sum.inr (), Sum.inl ()] : Fin 2 → Unit ⊕ Unit` and `Sum.elim (fun _ => 1) (fun _ => 0) : Unit ⊕ Unit → Fin 2`
(`TauCeti.IsSemialgebraic.preimage_comp`).

## `#print axioms`

```
'Semialgebraic.isSemialgebraic_setOf_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isSemialgebraic_setOf_isLUB_fin_two' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isSemialgebraic_setOf_exists_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isSemialgebraic_setOf_forall_real' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isSemialgebraic_setOf_le_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isSemialgebraic_setOf_lt_coord' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isLUB_iff_forall_lt_exists' depends on axioms: [propext, Classical.choice, Quot.sound]
```
