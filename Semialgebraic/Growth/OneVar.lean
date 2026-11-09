import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import TauCeti.Geometry.RealAlgebraic.Semialgebraic.AlgebraicDependence

/-!
# Polynomial growth of one-variable semialgebraic fibres (plan ids G1, G2)

This file provides:

* `Semialgebraic.exists_growth_of_eval_eq_zero` : the real roots `s` of `P(·, t)` (`P` a nonzero polynomial in
  two variables, coordinate `0` = `s`, coordinate `1` = `t`) satisfy `|s| ≤ c (1 + t) ^ M` for `t ≥ t₀`.
* `Semialgebraic.exists_growth_of_interior_eq_empty` (G1) : the same bound on a semialgebraic subset of the plane
  with empty interior.
* `Semialgebraic.exists_growth_of_subsingleton_fibres` (G2) : the same bound when every fibre over `t` has at most
  one point.

Helper lemmas (public, reusable): `abs_le_of_sum_range_mul_pow_eq_zero` (an elementary Cauchy-type root bound),
`Polynomial`-level bounds `exists_le_abs_eval_of_ne_zero` and `abs_eval_le_sum_mul_one_add_pow`, and
`eval_uniqueAlgEquiv_fin_one`.

No deviation from the brief: the three statements are exactly those of `notes/briefs/P2-a-onevar.md`.
-/

namespace Semialgebraic

open Finset Filter

/-- Elementary root bound: if `∑_{i ≤ d} aᵢ sⁱ = 0` with `a_d ≠ 0` then `|s| ≤ 1 + (∑_{i < d} |aᵢ|) / |a_d|`. -/
theorem abs_le_of_sum_range_mul_pow_eq_zero {a : ℕ → ℝ} {d : ℕ} {s : ℝ} (hd : a d ≠ 0)
    (h : ∑ i ∈ range (d + 1), a i * s ^ i = 0) :
    |s| ≤ 1 + (∑ i ∈ range d, |a i|) / |a d| := by
  have hS : 0 ≤ (∑ i ∈ range d, |a i|) / |a d| :=
    div_nonneg (sum_nonneg fun i _ => abs_nonneg _) (abs_nonneg _)
  -- the case `|s| ≤ 1` is immediate
  rcases le_or_gt |s| 1 with hs | hs
  · linarith
  obtain _ | k := d
  · -- `d = 0`: the equation says `a 0 = 0`
    simp at h
    exact absurd h hd
  -- `d = k + 1`: isolate the leading term
  rw [sum_range_succ, add_eq_zero_iff_eq_neg] at h
  have hpos : 0 < |s| ^ k := pow_pos (by linarith) k
  have hlead : |a (k + 1)| * |s| ^ (k + 1) ≤ (∑ i ∈ range (k + 1), |a i|) * |s| ^ k := by
    calc |a (k + 1)| * |s| ^ (k + 1) = |∑ i ∈ range (k + 1), a i * s ^ i| := by
          rw [← abs_pow, ← abs_mul, h, abs_neg]
      _ ≤ ∑ i ∈ range (k + 1), |a i * s ^ i| := abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range (k + 1), |a i| * |s| ^ k := by
          refine sum_le_sum fun i hi => ?_
          rw [abs_mul, abs_pow]
          exact mul_le_mul_of_nonneg_left
            (pow_le_pow_right₀ hs.le (Nat.lt_succ_iff.mp (mem_range.mp hi))) (abs_nonneg _)
      _ = (∑ i ∈ range (k + 1), |a i|) * |s| ^ k := by rw [sum_mul]
  -- cancel `|s| ^ k`
  have hcancel : |a (k + 1)| * |s| ≤ ∑ i ∈ range (k + 1), |a i| := by
    rw [pow_succ', ← mul_assoc] at hlead
    exact le_of_mul_le_mul_right hlead hpos
  have had : 0 < |a (k + 1)| := abs_pos.mpr hd
  have : |s| ≤ (∑ i ∈ range (k + 1), |a i|) / |a (k + 1)| := by
    rw [le_div_iff₀ had, mul_comm]; exact hcancel
  linarith

/-- A nonzero univariate real polynomial is bounded away from `0` near `+∞`. -/
theorem exists_le_abs_eval_of_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ t, t₀ ≤ t → δ ≤ |p.eval t| := by
  rcases lt_or_ge 0 p.degree with hdeg | hdeg
  · -- nonconstant: `|p(t)| → ∞`
    obtain ⟨a, ha⟩ := eventually_atTop.mp ((Polynomial.abs_tendsto_atTop p hdeg).eventually_ge_atTop 1)
    exact ⟨1, one_pos, max a 0, le_max_right _ _, fun t ht => ha t (le_of_max_le_left ht)⟩
  · -- constant
    have hC := Polynomial.eq_C_of_degree_le_zero hdeg
    have h0 : p.coeff 0 ≠ 0 := by
      intro h; rw [h, map_zero] at hC; exact hp hC
    refine ⟨|p.coeff 0|, abs_pos.mpr h0, 0, le_rfl, fun t _ => ?_⟩
    rw [hC, Polynomial.eval_C, Polynomial.coeff_C_zero]

/-- A univariate real polynomial of degree `≤ N` grows at most like `(1 + t) ^ N` for `t ≥ 0`. -/
theorem abs_eval_le_sum_mul_one_add_pow {p : Polynomial ℝ} {N : ℕ} (hN : p.natDegree ≤ N) {t : ℝ}
    (ht : 0 ≤ t) :
    |p.eval t| ≤ (∑ i ∈ range (N + 1), |p.coeff i|) * (1 + t) ^ N := by
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hN), sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi => ?_)
  rw [abs_mul, abs_pow, abs_of_nonneg ht]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  calc t ^ i ≤ (1 + t) ^ i := pow_le_pow_left₀ ht (by linarith) i
    _ ≤ (1 + t) ^ N :=
      pow_le_pow_right₀ (by linarith) (Nat.lt_succ_iff.mp (mem_range.mp hi))

/-- Evaluating `q : MvPolynomial (Fin 1) ℝ` at `![t]` is evaluating its univariate image at `t`. -/
theorem eval_uniqueAlgEquiv_fin_one (q : MvPolynomial (Fin 1) ℝ) (t : ℝ) :
    (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) q).eval t = MvPolynomial.eval ![t] q := by
  induction q using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, Polynomial.eval_mul, hp, map_mul, Fin.fin_one_eq_zero i]
    simp

/-- The real roots `s` of `P(·, t)` are polynomially bounded in `t` near `+∞`, for any nonzero `P`. -/
theorem exists_growth_of_eval_eq_zero {P : MvPolynomial (Fin 2) ℝ} (hP : P ≠ 0) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → MvPolynomial.eval ![s, t] P = 0 → |s| ≤ c * (1 + t) ^ M := by
  -- view `P` as a polynomial in `s` with coefficients in `MvPolynomial (Fin 1) ℝ`
  set Q := MvPolynomial.finSuccEquiv ℝ 1 P with hQdef
  have hQ : Q ≠ 0 := (EmbeddingLike.map_ne_zero_iff).mpr hP
  set d := Q.natDegree
  -- the coefficients as univariate polynomials in `t`
  set u : ℕ → Polynomial ℝ := fun i => MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) (Q.coeff i) with hu
  have hud : u d ≠ 0 := by
    simp only [hu]
    exact (EmbeddingLike.map_ne_zero_iff).mpr (Polynomial.leadingCoeff_ne_zero.mpr hQ)
  -- the leading coefficient is bounded away from `0`
  obtain ⟨δ, hδ, t₀, ht₀, hδt⟩ := exists_le_abs_eval_of_ne_zero hud
  -- a common degree bound `N` and a common constant `K` for the lower coefficients
  set N := ∑ i ∈ range (d + 1), (u i).natDegree
  set K := ∑ i ∈ range d, ∑ j ∈ range (N + 1), |(u i).coeff j|
  have hK : 0 ≤ K := sum_nonneg fun _ _ => sum_nonneg fun _ _ => abs_nonneg _
  refine ⟨1 + K / δ, N, t₀, by positivity, ht₀, fun s t ht hst => ?_⟩
  have ht0 : 0 ≤ t := ht₀.trans ht
  -- the coefficient values at `t`
  set a : ℕ → ℝ := fun i => (u i).eval t with ha
  have hroot : ∑ i ∈ range (d + 1), a i * s ^ i = 0 := by
    have h1 : MvPolynomial.eval ![s, t] P =
        Polynomial.eval s (Polynomial.map (MvPolynomial.eval ![t]) Q) :=
      MvPolynomial.eval_eq_eval_mv_eval' ![t] s P
    rw [h1, Polynomial.eval_eq_sum_range'
      (Nat.lt_succ_of_le Polynomial.natDegree_map_le)] at hst
    simpa only [ha, hu, eval_uniqueAlgEquiv_fin_one, Polynomial.coeff_map] using hst
  have had : a d ≠ 0 := fun h => by
    have := hδt t ht; rw [show (u d).eval t = a d from rfl, h, abs_zero] at this; linarith
  have hbound := abs_le_of_sum_range_mul_pow_eq_zero had hroot
  -- bound the numerator
  have hnum : ∑ i ∈ range d, |a i| ≤ K * (1 + t) ^ N := by
    rw [sum_mul]
    refine sum_le_sum fun i hi => abs_eval_le_sum_mul_one_add_pow ?_ ht0
    exact single_le_sum (f := fun i => (u i).natDegree) (fun _ _ => Nat.zero_le _)
      (mem_range.mpr (Nat.lt_succ_of_lt (mem_range.mp hi)))
  have hfrac : (∑ i ∈ range d, |a i|) / |a d| ≤ K * (1 + t) ^ N / δ :=
    div_le_div₀ (by positivity) hnum hδ (hδt t ht)
  have hone : 1 ≤ (1 + t) ^ N := one_le_pow₀ (by linarith)
  calc |s| ≤ 1 + K * (1 + t) ^ N / δ := hbound.trans (by linarith)
    _ ≤ (1 + t) ^ N + K / δ * (1 + t) ^ N := by rw [mul_div_right_comm]; linarith
    _ = (1 + K / δ) * (1 + t) ^ N := by ring

/-- G1. A semialgebraic subset of the plane with empty interior has polynomially bounded fibres near `+∞`.
Coordinate `0` is the value `s`, coordinate `1` is the parameter `t`. -/
theorem exists_growth_of_interior_eq_empty {G : Set (Fin 2 → ℝ)} (hG : TauCeti.IsSemialgebraic G)
    (hint : interior G = ∅) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → ![s, t] ∈ G → |s| ≤ c * (1 + t) ^ M := by
  obtain ⟨P, hP, hPG⟩ := hG.exists_ne_zero_polynomial_of_interior_eq_empty hint
  obtain ⟨c, M, t₀, hc, ht₀, h⟩ := exists_growth_of_eval_eq_zero hP
  exact ⟨c, M, t₀, hc, ht₀, fun s t ht hst => h s t ht (hPG _ hst)⟩

/-- G2. Same conclusion when every fibre `{s | ![s, t] ∈ G}` has at most one point. -/
theorem exists_growth_of_subsingleton_fibres {G : Set (Fin 2 → ℝ)} (hG : TauCeti.IsSemialgebraic G)
    (hfib : ∀ s s' t : ℝ, ![s, t] ∈ G → ![s', t] ∈ G → s = s') :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → ![s, t] ∈ G → |s| ≤ c * (1 + t) ^ M := by
  refine exists_growth_of_interior_eq_empty hG (Set.eq_empty_of_forall_notMem fun z hz => ?_)
  -- a ball around an interior point `z` lies in `G`
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp isOpen_interior z hz
  have hz2 : (![z 0, z 1] : Fin 2 → ℝ) = z := by
    funext i; fin_cases i <;> rfl
  have hzG : (![z 0, z 1] : Fin 2 → ℝ) ∈ G := by
    rw [hz2]; exact interior_subset hz
  -- the shifted point `![z 0 + ε / 2, z 1]` is in the ball, hence in `G`
  have hwG : (![z 0 + ε / 2, z 1] : Fin 2 → ℝ) ∈ G := by
    refine interior_subset (hball ?_)
    rw [Metric.mem_ball, dist_pi_lt_iff hε, Fin.forall_fin_two]
    constructor
    · simp [abs_of_pos hε, half_lt_self hε]
    · simp [hε]
  -- two points in one fibre
  have := hfib _ _ _ hwG hzG
  linarith

end Semialgebraic
