# Unit P2-a (writer): `Semialgebraic/Growth/OneVar.lean` — plan ids G1, G2

Read `notes/briefs/standing.md` and `PLAN.md` §4.2 first. You write exactly one file,
`Semialgebraic/Growth/OneVar.lean`, and the report `notes/lean-reports/P2-a.md`.

## Required public statements (namespace `Semialgebraic`; do not change them)

```lean
/-- G1. A semialgebraic subset of the plane with empty interior has polynomially bounded fibres near `+∞`.
Coordinate `0` is the value `s`, coordinate `1` is the parameter `t`. -/
theorem exists_growth_of_interior_eq_empty {G : Set (Fin 2 → ℝ)} (hG : TauCeti.IsSemialgebraic G)
    (hint : interior G = ∅) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → ![s, t] ∈ G → |s| ≤ c * (1 + t) ^ M

/-- G2. Same conclusion when every fibre `{s | ![s, t] ∈ G}` has at most one point. -/
theorem exists_growth_of_subsingleton_fibres {G : Set (Fin 2 → ℝ)} (hG : TauCeti.IsSemialgebraic G)
    (hfib : ∀ s s' t : ℝ, ![s, t] ∈ G → ![s', t] ∈ G → s = s') :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → ![s, t] ∈ G → |s| ≤ c * (1 + t) ^ M
```

Recommended intermediate statement (public, purely about polynomials; adjust its form if another is more
convenient, but keep a statement of this strength):

```lean
/-- The real roots `s` of `P(·, t)` are polynomially bounded in `t` near `+∞`, for any nonzero `P`. -/
theorem exists_growth_of_eval_eq_zero {P : MvPolynomial (Fin 2) ℝ} (hP : P ≠ 0) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → MvPolynomial.eval ![s, t] P = 0 → |s| ≤ c * (1 + t) ^ M
```

## Proof route

* G1 from the polynomial statement: `TauCeti.IsSemialgebraic.exists_ne_zero_polynomial_of_interior_eq_empty`
  (`TauCeti/Geometry/RealAlgebraic/Semialgebraic/AlgebraicDependence.lean`) gives `P ≠ 0` vanishing on `G`.
* Polynomial statement. View `P` as a polynomial in `s` with coefficients polynomial in `t`:
  `MvPolynomial.finSuccEquiv ℝ 1 : MvPolynomial (Fin 2) ℝ ≃ₐ[ℝ] Polynomial (MvPolynomial (Fin 1) ℝ)` (variable `0` becomes
  the polynomial variable; see `Mathlib/Algebra/MvPolynomial/Equiv.lean`, e.g. `MvPolynomial.eval_eq_eval_mv_eval'`,
  `finSuccEquiv_apply`, `natDegree_finSuccEquiv`), then the coefficients live in `MvPolynomial (Fin 1) ℝ`, which
  you may evaluate directly at `![t]`-like points or transport to `ℝ[X]` (`MvPolynomial.pUnitAlgEquiv`,
  `MvPolynomial.uniqueAlgEquiv`, or `finSuccEquiv ℝ 0` followed by `isEmptyAlgEquiv`). Any other route to
  "`P(s,t) = ∑_{i ≤ d} qᵢ(t) sⁱ` with `q_d ≠ 0` a univariate real polynomial" is fine (for instance working with
  `Polynomial (Polynomial ℝ)` and `Polynomial.eval₂`/`evalEval`), as long as the public statements are as above.
  Then:
  1. `q_d ≠ 0` univariate ⇒ `∃ δ > 0, ∃ t₀ ≥ 0, ∀ t ≥ t₀, δ ≤ |q_d(t)|` (if `q_d` is constant this is immediate,
     otherwise `Polynomial.abs_tendsto_atTop` in `Mathlib/Analysis/Polynomial/Basic.lean`; or use that a nonzero
     polynomial has finitely many roots together with its limit behaviour — any correct argument).
  2. every univariate real `q` satisfies `∃ C ≥ 0, ∀ t ≥ 0, |q(t)| ≤ C * (1 + t) ^ q.natDegree`
     (`Polynomial.eval_eq_sum_range`, triangle inequality, `t ^ i ≤ (1 + t) ^ natDegree`).
  3. if `∑_{i ≤ d} aᵢ sⁱ = 0` with `a_d ≠ 0` then `|s| ≤ 1 + (∑_{i < d} |aᵢ|) / |a_d|` (elementary: if `|s| ≥ 1`,
     divide by `|s|^{d-1}`; alternatively `Polynomial.IsRoot.norm_lt_cauchyBound` in
     `Mathlib/Analysis/Polynomial/CauchyBound.lean`). When `d = 0` there is no root at all.
  4. combine: for `t ≥ t₀`, `|s| ≤ 1 + (∑ Cᵢ (1+t)^{Mᵢ}) / δ ≤ c (1 + t)^M` with `M := max Mᵢ` (note `1 ≤ 1 + t`).
* G2 from G1: if `interior G` contained a point `z`, an open ball around `z` (sup metric on `Fin 2 → ℝ`) would lie
  in `G` and contain `![z 0 + ε, z 1]` and `![z 0, z 1]`, contradicting `hfib`. Use `![z 0, z 1] = z`
  (e.g. `List.ofFn`-free: `funext` + `Fin.forall_fin_two`).

Acceptance: the file builds with `lake build Semialgebraic.Growth.OneVar`; no forbidden token; axioms of the three
theorems are `[propext, Classical.choice, Quot.sound]`.
