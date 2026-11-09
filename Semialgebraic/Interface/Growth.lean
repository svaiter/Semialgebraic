import Semialgebraic.Growth.Main

/-!
# Interface theorem A3: polynomial growth bound

This file provides, in TauCeti's vocabulary, the statement that HardnessBilevel assumes through the class
`Bilevel.HasGrowthBound` (assumption A3).

* `Semialgebraic.Interface.growth` : the interface theorem. Its statement is the field `growth` of
  `Bilevel.HasGrowthBound` with `Bilevel.IsSemialgebraic` replaced by `TauCeti.IsSemialgebraic` (same binders
  `{n : ℕ} {f : (Fin n → ℝ) → ℝ}`, same hypotheses, same conclusion). The two semialgebraicity predicates agree by
  `Iff.rfl` (see `Semialgebraic.isSemialgebraic_iff_mem_generateSetAlgebra`).

The proof is `Semialgebraic.exists_polynomial_growth` (plan §4.3) with `ι := Fin n`, which rests on G4
(`Semialgebraic.exists_growth_isLUB`).
-/

namespace Semialgebraic

namespace Interface

/-- **Interface theorem A3** (growth bound). -/
theorem growth {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    TauCeti.IsSemialgebraic {z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())} →
    (∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) →
    ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M :=
  fun hf hb => exists_polynomial_growth hf hb

end Interface

end Semialgebraic
