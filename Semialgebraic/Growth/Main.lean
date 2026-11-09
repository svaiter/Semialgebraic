import Semialgebraic.Growth.OneVar
import Semialgebraic.Growth.IsLUB

/-!
# Polynomial growth of semialgebraic functions (plan id G4, §4.3)

This file provides:

* `Semialgebraic.exists_growth_isLUB` (G4) : the fibrewise least upper bound of a semialgebraic subset of the plane
  (coordinate `0` = value, coordinate `1` = parameter) is bounded by `c * (1 + t) ^ M` for large parameters `t`.
  Proof: the graph of the fibrewise least upper bound is semialgebraic (G3,
  `isSemialgebraic_setOf_isLUB_fin_two`) with subsingleton fibres (`IsLUB.unique`), so G2
  (`exists_growth_of_subsingleton_fibres`) applies.
* `Semialgebraic.isSemialgebraic_setOf_exists_sq_sum_le_abs_eq` : for `f` with semialgebraic graph, the set
  `{w : Fin 2 → ℝ | ∃ x, ∑ i, x i ^ 2 ≤ w 1 ∧ |f x| = w 0}` is semialgebraic.
* `Semialgebraic.exists_polynomial_growth` (§4.3) : a real function on `ι → ℝ` (`ι` finite) with semialgebraic
  graph that is bounded on bounded sets satisfies `|f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M`.
  Proof: apply G4 to the set above; its fibre over `ρ ≥ 0` is nonempty and bounded above, so it has a least upper
  bound (`Real.exists_isLUB`) which dominates `|f x|` when `∑ i, x i ^ 2 ≤ ρ`. Only `IsLUB` is used, never `sSup`.

No deviation from the brief; the statements are exactly those of the brief. The helper
`isSemialgebraic_setOf_exists_sq_sum_le_abs_eq` is an addition.
-/

open MvPolynomial

namespace Semialgebraic

/-- G4. The fibrewise least upper bound of a semialgebraic subset of the plane grows polynomially near `+∞`.
Coordinate `0` is the value, coordinate `1` is the parameter. -/
theorem exists_growth_isLUB {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → IsLUB {u : ℝ | ![u, t] ∈ E} s → |s| ≤ c * (1 + t) ^ M := by
  -- the graph `G` of the fibrewise least upper bound is semialgebraic (G3)
  have hG := isSemialgebraic_setOf_isLUB_fin_two hE
  -- membership of `![s, t]` in `G` is the `IsLUB` statement
  have hmem : ∀ s t : ℝ, ![s, t] ∈ {z : Fin 2 → ℝ | IsLUB {u : ℝ | ![u, z 1] ∈ E} (z 0)} ↔
      IsLUB {u : ℝ | ![u, t] ∈ E} s := fun _ _ => Iff.rfl
  -- fibres of `G` are subsingletons since least upper bounds are unique; apply G2
  obtain ⟨c, M, t₀, hc, ht₀, h⟩ := exists_growth_of_subsingleton_fibres hG
    (fun s s' t hs hs' => ((hmem s t).1 hs).unique ((hmem s' t).1 hs'))
  exact ⟨c, M, t₀, hc, ht₀, fun s t ht hs => h s t ht ((hmem s t).2 hs)⟩

/-- For `f` with semialgebraic graph, the set of pairs `(u, ρ)` with `u = |f x|` for some `x` with
`∑ i, x i ^ 2 ≤ ρ` is semialgebraic (coordinate `0` = `u`, coordinate `1` = `ρ`). -/
theorem isSemialgebraic_setOf_exists_sq_sum_le_abs_eq {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : TauCeti.IsSemialgebraic {z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())}) :
    TauCeti.IsSemialgebraic {w : Fin 2 → ℝ | ∃ x : ι → ℝ, ∑ i, x i ^ 2 ≤ w 1 ∧ |f x| = w 0} := by
  -- the norm constraint `∑ i, v (inr i) ^ 2 ≤ v (inl 1)`
  have hA : TauCeti.IsSemialgebraic
      {v : Fin 2 ⊕ ι → ℝ | ∑ i, v (Sum.inr i) ^ 2 ≤ v (Sum.inl 1)} := by
    convert TauCeti.isSemialgebraic_eval_le
      (∑ i, (X (Sum.inr i) : MvPolynomial (Fin 2 ⊕ ι) ℝ) ^ 2) (X (Sum.inl 1)) using 1
    ext v
    simp
  -- the sign constraint `0 ≤ v (inl 0)`
  have hB : TauCeti.IsSemialgebraic {v : Fin 2 ⊕ ι → ℝ | 0 ≤ v (Sum.inl 0)} := by
    simpa using TauCeti.isSemialgebraic_eval_le (0 : MvPolynomial (Fin 2 ⊕ ι) ℝ) (X (Sum.inl 0))
  -- `f (v ∘ inr) = v (inl 0)`: pullback of the graph along a coordinate map
  have hC : TauCeti.IsSemialgebraic
      {v : Fin 2 ⊕ ι → ℝ | f (v ∘ Sum.inr) = v (Sum.inl 0)} :=
    hf.preimage_comp (Sum.elim Sum.inr (fun _ : Unit => Sum.inl 0))
  -- `f (v ∘ inr) = -v (inl 0)`: pullback of the graph along a polynomial map
  have hD : TauCeti.IsSemialgebraic
      {v : Fin 2 ⊕ ι → ℝ | f (v ∘ Sum.inr) = -v (Sum.inl 0)} := by
    have h := hf.preimage_eval
      (Sum.elim (fun i => (X (Sum.inr i) : MvPolynomial (Fin 2 ⊕ ι) ℝ))
        (fun _ : Unit => -X (Sum.inl 0)))
    convert h using 1
    ext v
    simp [Function.comp_def]
  -- the set `S` upstairs, and the projection forgetting the `ι` coordinates
  have hS := (hA.inter (hB.inter (hC.union hD))).setOf_exists_sumElim (τ := ι)
  convert hS using 1
  ext w
  simp only [Set.mem_ofPred, Set.mem_inter_iff, Set.mem_union, Sum.elim_inr, Sum.elim_inl]
  refine exists_congr fun x => and_congr Iff.rfl ?_
  -- `|a| = b ↔ 0 ≤ b ∧ (a = b ∨ a = -b)`
  have hx : (Sum.elim w x : Fin 2 ⊕ ι → ℝ) ∘ Sum.inr = x := rfl
  rw [hx]
  constructor
  · intro h
    exact ⟨h ▸ abs_nonneg _, (abs_eq (h ▸ abs_nonneg _)).1 h⟩
  · rintro ⟨h0, h⟩
    exact (abs_eq h0).2 h

/-- Polynomial growth of a real function with semialgebraic graph that is bounded on bounded sets. -/
theorem exists_polynomial_growth {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : TauCeti.IsSemialgebraic {z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())})
    (hb : ∀ r : ℝ, ∃ B : ℝ, ∀ x : ι → ℝ, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) :
    ∃ (B : ℝ) (M : ℕ), ∀ x : ι → ℝ, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M := by
  set E : Set (Fin 2 → ℝ) := {w | ∃ x : ι → ℝ, ∑ i, x i ^ 2 ≤ w 1 ∧ |f x| = w 0}
  have hE : TauCeti.IsSemialgebraic E := isSemialgebraic_setOf_exists_sq_sum_le_abs_eq hf
  -- the fibre of `E` over `ρ`
  have hfib : ∀ u ρ : ℝ, ![u, ρ] ∈ E ↔ ∃ x : ι → ℝ, ∑ i, x i ^ 2 ≤ ρ ∧ |f x| = u :=
    fun _ _ => Iff.rfl
  -- for `ρ ≥ 0` the fibre has a least upper bound dominating `|f x|` on `∑ i, x i ^ 2 ≤ ρ`
  have hlub : ∀ ρ : ℝ, 0 ≤ ρ → ∃ g : ℝ, IsLUB {u : ℝ | ![u, ρ] ∈ E} g := by
    intro ρ hρ
    obtain ⟨B, hB⟩ := hb ρ
    refine Real.exists_isLUB ⟨|f 0|, (hfib _ _).2 ⟨0, by simpa using hρ, rfl⟩⟩ ⟨B, ?_⟩
    rintro u hu
    obtain ⟨x, hx, rfl⟩ := (hfib u ρ).1 hu
    exact hB x hx
  -- the growth bound of G4
  obtain ⟨c, M, t₀, hc, ht₀, hgrowth⟩ := exists_growth_isLUB hE
  set ρ₁ := max t₀ c
  obtain ⟨B₁, hB₁⟩ := hb ρ₁
  refine ⟨max 0 B₁, M + 1, fun x => ?_⟩
  set ρ := ∑ i, x i ^ 2
  have hρ : 0 ≤ ρ := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hpow : 0 ≤ (1 + ρ) ^ (M + 1) := pow_nonneg (by linarith) _
  rcases le_or_gt ρ ρ₁ with hle | hgt
  · -- small `ρ`: the bound `B₁` on the ball of radius `ρ₁`
    have h1 : |f x| ≤ B₁ := hB₁ x hle
    have h2 : B₁ ≤ max 0 B₁ := le_max_right _ _
    linarith
  · -- large `ρ`: compare with the least upper bound `g` of the fibre over `ρ`
    obtain ⟨g, hg⟩ := hlub ρ hρ
    have h1 : |f x| ≤ g := hg.1 ((hfib _ _).2 ⟨x, le_rfl, rfl⟩)
    have ht : t₀ ≤ ρ := (le_max_left _ _).trans hgt.le
    have hcρ : c ≤ 1 + ρ := by linarith [le_max_right t₀ c]
    have h2 : |g| ≤ c * (1 + ρ) ^ M := hgrowth g ρ ht hg
    have h3 : c * (1 + ρ) ^ M ≤ (1 + ρ) ^ (M + 1) := by
      rw [pow_succ, mul_comm ((1 + ρ) ^ M)]
      exact mul_le_mul_of_nonneg_right hcρ (pow_nonneg (by linarith) _)
    have h4 : 0 ≤ max 0 B₁ := le_max_left _ _
    linarith [le_abs_self g]

end Semialgebraic
