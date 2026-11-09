import Semialgebraic.Growth.Main
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# The Łojasiewicz inequality on a closed semialgebraic set (plan ids F0, F1, F2, F3, L1)

This file provides (notation: `N(x) = ∑ i, x i ^ 2`):

* `Semialgebraic.exists_growth_of_bddAbove_fibres` (F0) : points of a semialgebraic planar set whose fibres are
  bounded above grow polynomially near `+∞` (coordinate `0` = value, `1` = parameter). Proof: G4
  (`exists_growth_isLUB`) applied to the least upper bound of the (nonempty, bounded) fibre (`Real.exists_isLUB`).
* `Semialgebraic.isSemialgebraic_lojasiewicz_aux` (F1) : the planar set
  `E = {w | ∃ x ∈ T, N(x) ≤ w 1 ∧ 1 ≤ w 1 * g(x)² ∧ w 0 * f(x)² = 1}` is semialgebraic (projection along the `ι`
  coordinates of four semialgebraic conditions in `Fin 2 ⊕ ι → ℝ`).
* `Semialgebraic.isCompact_setOf_sq_sum_le` (F2) : the sets `K_t = {x ∈ T | N(x) ≤ t ∧ 1 ≤ t * g(x)²}` are
  compact for closed `T` (closed subsets of a box).
* `Semialgebraic.lojasiewicz_arith` (F3, public) : the real arithmetic of Step 5 of the report.
* `Semialgebraic.exists_lojasiewicz` (L1) : if `f = 0 → g = 0` on the closed semialgebraic set `T`, then
  `g(x)^(2(M+1)) ≤ C f(x)² ((1 + N(x)) (1 + g(x)²))^(M+1)` on `T`.

The proof is `notes/research/route1-lojasiewicz.md` §3.1, Steps 1–5; the code follows its Appendix B prototype.
No deviation from the brief: the statements of F0, F1, F2, L1 are exactly those of the brief; F3 is stated as in
§4.1 of the report.
-/

open MvPolynomial

namespace Semialgebraic

/-- F0. Points of a semialgebraic planar set whose fibres are bounded above grow polynomially near `+∞`.
Coordinate `0` is the value, coordinate `1` is the parameter. -/
theorem exists_growth_of_bddAbove_fibres {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E)
    (hbdd : ∀ t : ℝ, BddAbove {u : ℝ | ![u, t] ∈ E}) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ u t : ℝ, t₀ ≤ t → ![u, t] ∈ E → u ≤ c * (1 + t) ^ M := by
  -- the growth bound for fibrewise least upper bounds (G4)
  obtain ⟨c, M, t₀, hc, ht₀, h⟩ := exists_growth_isLUB hE
  refine ⟨c, M, t₀, hc, ht₀, fun u t ht hu => ?_⟩
  -- the fibre over `t` contains `u` and is bounded above, so it has a least upper bound `s`
  obtain ⟨s, hs⟩ := Real.exists_isLUB ⟨u, hu⟩ (hbdd t)
  -- `u ≤ s ≤ |s| ≤ c (1 + t) ^ M`
  exact (hs.1 hu).trans ((le_abs_self s).trans (h s t ht hs))

/-- F1. The planar set of the Łojasiewicz argument is semialgebraic. -/
theorem isSemialgebraic_lojasiewicz_aux {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (f g : MvPolynomial ι ℝ) :
    TauCeti.IsSemialgebraic {w : Fin 2 → ℝ | ∃ x : ι → ℝ, x ∈ T ∧ ∑ i, x i ^ 2 ≤ w 1 ∧
      1 ≤ w 1 * MvPolynomial.eval x g ^ 2 ∧ w 0 * MvPolynomial.eval x f ^ 2 = 1} := by
  -- `z ∘ inr ∈ T`: pullback of `T` along a coordinate map
  have hA : TauCeti.IsSemialgebraic {z : Fin 2 ⊕ ι → ℝ | z ∘ Sum.inr ∈ T} :=
    hT.preimage_comp Sum.inr
  -- the norm constraint `N(z ∘ inr) ≤ z (inl 1)`
  have hB : TauCeti.IsSemialgebraic
      {z : Fin 2 ⊕ ι → ℝ | ∑ i, z (Sum.inr i) ^ 2 ≤ z (Sum.inl 1)} := by
    convert TauCeti.isSemialgebraic_eval_le
      (∑ i, X (Sum.inr i) ^ 2 : MvPolynomial (Fin 2 ⊕ ι) ℝ) (X (Sum.inl 1)) using 1
    ext z
    simp
  -- the constraint `1 ≤ z (inl 1) * g(z ∘ inr)²`
  have hC : TauCeti.IsSemialgebraic
      {z : Fin 2 ⊕ ι → ℝ | 1 ≤ z (Sum.inl 1) * eval (z ∘ Sum.inr) g ^ 2} := by
    convert TauCeti.isSemialgebraic_eval_le (1 : MvPolynomial (Fin 2 ⊕ ι) ℝ)
      (X (Sum.inl 1) * rename Sum.inr g ^ 2) using 1
    ext z
    simp [eval_rename]
  -- the constraint `z (inl 0) * f(z ∘ inr)² = 1`
  have hD : TauCeti.IsSemialgebraic
      {z : Fin 2 ⊕ ι → ℝ | z (Sum.inl 0) * eval (z ∘ Sum.inr) f ^ 2 = 1} := by
    convert TauCeti.isSemialgebraic_eval_eq (X (Sum.inl 0) * rename Sum.inr f ^ 2)
      (1 : MvPolynomial (Fin 2 ⊕ ι) ℝ) using 1
    ext z
    simp [eval_rename]
  -- project the intersection along the `ι` coordinates
  have h := (hA.inter (hB.inter (hC.inter hD))).setOf_exists_sumElim
  convert h using 1
  ext w
  simp [Set.mem_inter_iff]

/-- F2. The sets `K_t` are compact. -/
theorem isCompact_setOf_sq_sum_le {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)} (hT : IsClosed T)
    (g : MvPolynomial ι ℝ) (t : ℝ) :
    IsCompact {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * MvPolynomial.eval x g ^ 2} := by
  -- the set is closed: an intersection of `T` with two closed polynomial conditions
  have hcl : IsClosed {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * eval x g ^ 2} := by
    have h := hT.inter ((isClosed_le (f := fun x : ι → ℝ => ∑ i, x i ^ 2) (g := fun _ => t)
      (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const).inter
      (isClosed_le (f := fun _ : ι → ℝ => (1 : ℝ)) (g := fun x => t * eval x g ^ 2) continuous_const
        (continuous_const.mul ((MvPolynomial.continuous_eval g).pow 2))))
    convert h using 1
    ext x
    simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  -- it lies in the compact box `∏ i, [-(1 + |t|), 1 + |t|]`
  refine (isCompact_univ_pi fun _ : ι =>
    isCompact_Icc (a := -(1 + |t|)) (b := 1 + |t|)).of_isClosed_subset hcl ?_
  rintro x ⟨-, hx, -⟩ i -
  -- each coordinate satisfies `x i ^ 2 ≤ N(x) ≤ t`
  have hxi : x i ^ 2 ≤ t :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hx
  constructor <;> nlinarith [sq_nonneg (x i - 1), sq_nonneg (x i + 1), le_abs_self t]

/-- F3. Real arithmetic of Step 5 of the Łojasiewicz argument: from the growth bound at
`t = max t₀ (max N (1 / G²))` to the weighted inequality. -/
theorem lojasiewicz_arith {c t₀ N F G : ℝ} {M : ℕ} (hc : 0 ≤ c) (ht₀ : 0 ≤ t₀) (hN : 0 ≤ N)
    (hF : F ≠ 0) (hG : G ≠ 0)
    (h : 1 / F ^ 2 ≤ c * (1 + max t₀ (max N (1 / G ^ 2))) ^ M) :
    G ^ (2 * (M + 1)) ≤ c * (1 + t₀) ^ (M + 1) * F ^ 2 * ((1 + N) * (1 + G ^ 2)) ^ (M + 1) := by
  have hG2 : 0 < G ^ 2 := by positivity
  have hF2 : 0 < F ^ 2 := by positivity
  set t := max t₀ (max N (1 / G ^ 2)) with ht
  have ht0 : 0 ≤ t := le_max_of_le_left ht₀
  have ht1 : 1 ≤ 1 + t := by linarith
  have ha : 0 ≤ 1 / G ^ 2 := by positivity
  -- `t ≤ t₀ + N + 1 / G²`, all three summands being nonnegative
  have htle : t ≤ t₀ + N + 1 / G ^ 2 :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  -- key estimate `(1 + t) G² ≤ (1 + t₀) (1 + N) (1 + G²)`
  have hkey : (1 + t) * G ^ 2 ≤ (1 + t₀) * ((1 + N) * (1 + G ^ 2)) := by
    have h1 : (1 + t) * G ^ 2 ≤ (1 + (t₀ + N + 1 / G ^ 2)) * G ^ 2 := by gcongr
    have h2 : (1 + (t₀ + N + 1 / G ^ 2)) * G ^ 2 = (1 + t₀ + N) * G ^ 2 + 1 := by
      field_simp
      ring
    nlinarith [mul_nonneg ht₀ hN, mul_nonneg (mul_nonneg ht₀ hN) hG2.le, mul_nonneg ht₀ hG2.le,
      mul_nonneg hN hG2.le]
  -- multiply the growth bound by `F² (G²)^(M+1)` and apply the key estimate
  calc G ^ (2 * (M + 1)) = (G ^ 2) ^ (M + 1) := by rw [pow_mul]
    _ = 1 / F ^ 2 * F ^ 2 * (G ^ 2) ^ (M + 1) := by field_simp
    _ ≤ c * (1 + t) ^ M * F ^ 2 * (G ^ 2) ^ (M + 1) := by gcongr
    _ ≤ c * (1 + t) ^ (M + 1) * F ^ 2 * (G ^ 2) ^ (M + 1) := by
        gcongr
        · exact Nat.le_succ M
    _ = c * F ^ 2 * ((1 + t) * G ^ 2) ^ (M + 1) := by rw [mul_pow]; ring
    _ ≤ c * F ^ 2 * ((1 + t₀) * ((1 + N) * (1 + G ^ 2))) ^ (M + 1) := by gcongr
    _ = c * (1 + t₀) ^ (M + 1) * F ^ 2 * ((1 + N) * (1 + G ^ 2)) ^ (M + 1) := by
        rw [mul_pow]; ring

/-- L1. Łojasiewicz inequality, with polynomial weight, for polynomials on a closed semialgebraic set. -/
theorem exists_lojasiewicz {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (hTc : IsClosed T) (f g : MvPolynomial ι ℝ)
    (hfg : ∀ x ∈ T, MvPolynomial.eval x f = 0 → MvPolynomial.eval x g = 0) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ x ∈ T,
      MvPolynomial.eval x g ^ (2 * (M + 1)) ≤
        C * MvPolynomial.eval x f ^ 2 *
          ((1 + ∑ i, x i ^ 2) * (1 + MvPolynomial.eval x g ^ 2)) ^ (M + 1) := by
  -- Step 1: the planar set `E` is semialgebraic
  have hE := isSemialgebraic_lojasiewicz_aux hT f g
  -- Step 2: the fibres of `E` are bounded above
  have hbdd : ∀ t : ℝ, BddAbove {u : ℝ | ![u, t] ∈ {w : Fin 2 → ℝ | ∃ x : ι → ℝ, x ∈ T ∧
      ∑ i, x i ^ 2 ≤ w 1 ∧ 1 ≤ w 1 * eval x g ^ 2 ∧ w 0 * eval x f ^ 2 = 1}} := by
    intro t
    -- `K_t` is compact
    have hK := isCompact_setOf_sq_sum_le hTc g t
    -- `f ≠ 0` on `K_t`, since `f = 0` forces `g = 0` and then `1 ≤ t * 0` fails
    have hne : ∀ x ∈ {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * eval x g ^ 2},
        eval x f ^ 2 ≠ 0 := by
      rintro x ⟨hxT, -, hx⟩ h0
      have hg0 : eval x g = 0 := hfg x hxT (by simpa using h0)
      rw [hg0] at hx
      norm_num at hx
    -- so `1 / f²` is continuous on `K_t`, hence bounded above there
    have hcont : ContinuousOn (fun x : ι → ℝ => (eval x f ^ 2)⁻¹)
        {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * eval x g ^ 2} :=
      (((MvPolynomial.continuous_eval f).pow 2).continuousOn).inv₀ hne
    obtain ⟨B, hB⟩ := hK.bddAbove_image hcont
    -- each `u` in the fibre is `1 / f(x)²` for some `x ∈ K_t`
    refine ⟨B, ?_⟩
    rintro u ⟨x, hxT, hx1, hx2, hx3⟩
    have hu : u = (eval x f ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hx3
    rw [hu]
    exact hB ⟨x, ⟨hxT, hx1, hx2⟩, rfl⟩
  -- Step 3: polynomial growth of the points of `E` (F0)
  obtain ⟨c, M, t₀, hc, ht₀, hgrow⟩ := exists_growth_of_bddAbove_fibres hE hbdd
  refine ⟨c * (1 + t₀) ^ (M + 1), M, by positivity, fun x hxT => ?_⟩
  have hN : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hG : eval x g = 0
  · -- `g(x) = 0`: the left-hand side vanishes
    rw [hG]
    have h0 : (0 : ℝ) ^ (2 * (M + 1)) = 0 := by simp
    rw [h0]
    positivity
  · -- `g(x) ≠ 0`, hence `f(x) ≠ 0`; Step 4: the point `(1 / f(x)², max t₀ (max N(x) (1 / g(x)²)))` is in `E`
    have hF : eval x f ≠ 0 := fun h => hG (hfg x hxT h)
    -- Step 5: arithmetic (F3)
    refine lojasiewicz_arith hc ht₀ hN hF hG ?_
    refine hgrow _ _ (le_max_left _ _) ⟨x, hxT, ?_, ?_, ?_⟩
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · have h1 : 1 / eval x g ^ 2 ≤ max t₀ (max (∑ i, x i ^ 2) (1 / eval x g ^ 2)) :=
        (le_max_right _ _).trans (le_max_right _ _)
      have hG2 : 0 < eval x g ^ 2 := by positivity
      calc (1 : ℝ) = 1 / eval x g ^ 2 * eval x g ^ 2 := by field_simp
        _ ≤ _ := by gcongr; exact h1
    · show 1 / eval x f ^ 2 * eval x f ^ 2 = 1
      field_simp

end Semialgebraic
