# Report P2-c — `Growth/Main.lean`, `Interface/Growth.lean`, `SemialgebraicCheck/A3.lean` (G4, §4.3, A3)

Build: `lake build Semialgebraic.Growth.Main Semialgebraic.Interface.Growth SemialgebraicCheck.A3` succeeds.
No errors, no Lean warnings in the three new files (only Lake's "designed for use with the module system" notices
coming from imported files). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`; no `sSup` (the word appears only in
the header comment saying it is not used). Imports: `Main` imports only `Semialgebraic.Growth.OneVar` and
`Semialgebraic.Growth.IsLUB`; `Interface/Growth` imports only `Semialgebraic.Growth.Main`.

## Final statements (copied from the files)

```lean
-- Semialgebraic/Growth/Main.lean, namespace Semialgebraic
theorem exists_growth_isLUB {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → IsLUB {u : ℝ | ![u, t] ∈ E} s → |s| ≤ c * (1 + t) ^ M

theorem isSemialgebraic_setOf_exists_sq_sum_le_abs_eq {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : TauCeti.IsSemialgebraic {z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())}) :
    TauCeti.IsSemialgebraic {w : Fin 2 → ℝ | ∃ x : ι → ℝ, ∑ i, x i ^ 2 ≤ w 1 ∧ |f x| = w 0}

theorem exists_polynomial_growth {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : TauCeti.IsSemialgebraic {z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())})
    (hb : ∀ r : ℝ, ∃ B : ℝ, ∀ x : ι → ℝ, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) :
    ∃ (B : ℝ) (M : ℕ), ∀ x : ι → ℝ, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M

-- Semialgebraic/Interface/Growth.lean, namespace Semialgebraic.Interface
theorem growth {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    TauCeti.IsSemialgebraic {z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())} →
    (∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) →
    ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M :=
  fun hf hb => exists_polynomial_growth hf hb

-- SemialgebraicCheck/A3.lean
namespace BilevelShape
theorem hasGrowthBound : HasGrowthBound := ⟨Semialgebraic.Interface.growth⟩
end BilevelShape
#print axioms BilevelShape.hasGrowthBound
```

## Deviations from the brief

None. All required statements are verbatim. One addition: the public helper
`isSemialgebraic_setOf_exists_sq_sum_le_abs_eq` (step 1 of the brief's route, factored out). The check file
compiles with exactly the prescribed term.

## Proof route

As in the brief.
* G4: `isSemialgebraic_setOf_isLUB_fin_two`, membership `![s, t] ∈ G ↔ IsLUB … s` holds by `Iff.rfl`, fibres
  subsingleton by `IsLUB.unique`, then `exists_growth_of_subsingleton_fibres`.
* Helper: `S = A ∩ (B ∩ (C ∪ D))` over `Fin 2 ⊕ ι`, with `A` from `isSemialgebraic_eval_le (∑ X (inr i)^2) (X (inl 1))`,
  `B` from `isSemialgebraic_eval_le 0 (X (inl 0))`, `C = hf.preimage_comp (Sum.elim Sum.inr (fun _ : Unit => Sum.inl 0))`
  (closes definitionally, no `convert` needed), `D` from `hf.preimage_eval` with `-X (inl 0)` for the `Unit`
  coordinate; then `setOf_exists_sumElim (τ := ι)` and `abs_eq`.
* Main theorem: `ρ₁ := max t₀ c`, `B := max 0 B₁`, exponent `M + 1`, two cases `ρ ≤ ρ₁` / `ρ > ρ₁`; the fibre LUB comes
  from `Real.exists_isLUB` (nonempty via `x = 0`, bounded via `hb ρ`).

## Reusable helpers

`Semialgebraic.isSemialgebraic_setOf_exists_sq_sum_le_abs_eq` (above).

## Names / traps

* `simpa [map_sum] using isSemialgebraic_eval_le (∑ i, X (inr i) ^ 2) …` does not close the set equality (the sum is
  not pushed through `eval` inside the set-builder under `simpa`); `convert … using 1; ext v; simp` works.
* `abs_eq` (additive form of `mabs_eq`, `Mathlib/Algebra/Order/Group/Abs.lean`), `Real.exists_isLUB`
  (`Mathlib/Algebra/Order/Archimedean/Real/Basic.lean`), `TauCeti.IsSemialgebraic.preimage_comp`,
  `.preimage_eval`, `.setOf_exists_sumElim`, `.inter`, `.union`, `TauCeti.isSemialgebraic_eval_le` all as expected.
* `(Sum.elim w x) ∘ Sum.inr = x` and `![u, ρ] 0 = u`, `![u, ρ] 1 = ρ` hold by `rfl`.

## `#print axioms` (scratch file importing `SemialgebraicCheck.A3`, run with `lake env lean`)

```
'Semialgebraic.exists_growth_isLUB' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isSemialgebraic_setOf_exists_sq_sum_le_abs_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.exists_polynomial_growth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.Interface.growth' depends on axioms: [propext, Classical.choice, Quot.sound]
'BilevelShape.hasGrowthBound' depends on axioms: [propext, Classical.choice, Quot.sound]
```
