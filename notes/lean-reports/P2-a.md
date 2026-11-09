# Report P2-a — `Semialgebraic/Growth/OneVar.lean` (plan ids G1, G2)

Build: `lake build Semialgebraic.Growth.OneVar` succeeds. No errors, no Lean warnings; the only messages are
Lake's "imports … designed for use with the module system" notices, which are expected because the standing rules
forbid the `module` keyword. No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe`.

## Final statements (copied from the file)

```lean
theorem exists_growth_of_eval_eq_zero {P : MvPolynomial (Fin 2) ℝ} (hP : P ≠ 0) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → MvPolynomial.eval ![s, t] P = 0 → |s| ≤ c * (1 + t) ^ M

theorem exists_growth_of_interior_eq_empty {G : Set (Fin 2 → ℝ)} (hG : TauCeti.IsSemialgebraic G)
    (hint : interior G = ∅) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → ![s, t] ∈ G → |s| ≤ c * (1 + t) ^ M

theorem exists_growth_of_subsingleton_fibres {G : Set (Fin 2 → ℝ)} (hG : TauCeti.IsSemialgebraic G)
    (hfib : ∀ s s' t : ℝ, ![s, t] ∈ G → ![s', t] ∈ G → s = s') :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → ![s, t] ∈ G → |s| ≤ c * (1 + t) ^ M
```

## Deviations from the brief

None. The three statements are verbatim those of the brief (the recommended intermediate statement was kept as is).

## Helper lemmas (public, reusable; all in `namespace Semialgebraic`)

```lean
theorem abs_le_of_sum_range_mul_pow_eq_zero {a : ℕ → ℝ} {d : ℕ} {s : ℝ} (hd : a d ≠ 0)
    (h : ∑ i ∈ range (d + 1), a i * s ^ i = 0) :
    |s| ≤ 1 + (∑ i ∈ range d, |a i|) / |a d|

theorem exists_le_abs_eval_of_ne_zero {p : Polynomial ℝ} (hp : p ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ t₀ : ℝ, 0 ≤ t₀ ∧ ∀ t, t₀ ≤ t → δ ≤ |p.eval t|

theorem abs_eval_le_sum_mul_one_add_pow {p : Polynomial ℝ} {N : ℕ} (hN : p.natDegree ≤ N) {t : ℝ}
    (ht : 0 ≤ t) :
    |p.eval t| ≤ (∑ i ∈ range (N + 1), |p.coeff i|) * (1 + t) ^ N

theorem eval_uniqueAlgEquiv_fin_one (q : MvPolynomial (Fin 1) ℝ) (t : ℝ) :
    (MvPolynomial.uniqueAlgEquiv ℝ (Fin 1) q).eval t = MvPolynomial.eval ![t] q
```

## Proof route actually used

* `Q := MvPolynomial.finSuccEquiv ℝ 1 P`, `d := Q.natDegree`; coefficients transported to `ℝ[X]` with
  `MvPolynomial.uniqueAlgEquiv ℝ (Fin 1)` (`Fin 1` is `Unique`), evaluation compatibility by
  `MvPolynomial.induction_on`.
* `MvPolynomial.eval_eq_eval_mv_eval' ![t] s P` (note `![s, t]` is definitionally `Fin.cons s ![t]`), then
  `Polynomial.eval_eq_sum_range'` with `Polynomial.natDegree_map_le`, so no degree computation of the specialised
  polynomial is needed; the case `d = 0` is handled inside the elementary root bound (no root exists).
* Lower bound on the leading coefficient: `Polynomial.abs_tendsto_atTop` or `Polynomial.eq_C_of_degree_le_zero`.
* Common exponent `N := ∑_{i ≤ d} natDegree (u i)`, constant `c := 1 + K / δ`.
* G2: ball around an interior point (`Metric.isOpen_iff`, `dist_pi_lt_iff`) contains `![z 0 + ε/2, z 1]` and
  `![z 0, z 1] = z`.

## Names

All names used were as expected (`MvPolynomial.uniqueAlgEquiv`, `MvPolynomial.eval_eq_eval_mv_eval'`,
`Polynomial.abs_tendsto_atTop`, `Polynomial.eval_eq_sum_range'`, `Polynomial.natDegree_map_le`, `div_le_div₀`,
`pow_le_pow_left₀`, `pow_le_pow_right₀`, `one_le_pow₀`, `dist_pi_lt_iff`, `Set.eq_empty_of_forall_notMem`,
`TauCeti.IsSemialgebraic.exists_ne_zero_polynomial_of_interior_eq_empty`). The Cauchy bound
(`Polynomial.IsRoot.norm_lt_cauchyBound`) was not used: an elementary real-valued root bound was simpler.

## `#print axioms` (scratch file `/tmp/p2a/ax.lean`, run with `lake env lean`)

```
'Semialgebraic.exists_growth_of_eval_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.exists_growth_of_interior_eq_empty' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.exists_growth_of_subsingleton_fibres' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.abs_le_of_sum_range_mul_pow_eq_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.exists_le_abs_eval_of_ne_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.abs_eval_le_sum_mul_one_add_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.eval_uniqueAlgEquiv_fin_one' depends on axioms: [propext, Classical.choice, Quot.sound]
```
