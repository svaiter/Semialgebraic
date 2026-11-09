# Unit P3-a (writer): `Semialgebraic/Finiteness/Lojasiewicz.lean` — ids F0, F1, F2, F3, L1

Read `notes/briefs/standing.md`, `PLAN.md` §4.4, then `notes/research/route1-lojasiewicz.md` §3.1 (the proof, with
all constants), §4 (statements, dependency table with verified Mathlib/TauCeti names, risks) and its audit
`notes/audit/R1-lojasiewicz.md` (corrections there override the report). Appendix B of the report contains an
unaudited scratch prototype that elaborated at the pins; you may start from it, but your file must follow the
standing brief (specific imports instead of `Mathlib.Tactic`, header, namespace `Semialgebraic`, comments), and you
are responsible for every line.

You write exactly one Lean file, `Semialgebraic/Finiteness/Lojasiewicz.lean`, and the report
`notes/lean-reports/P3-a.md`. Your file imports `Semialgebraic.Growth.Main` (do not edit it).

## Required public statements (namespace `Semialgebraic`, `open MvPolynomial` allowed; do not change them)

```lean
/-- F0. Points of a semialgebraic planar set whose fibres are bounded above grow polynomially near `+∞`.
Coordinate `0` is the value, coordinate `1` is the parameter. -/
theorem exists_growth_of_bddAbove_fibres {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E)
    (hbdd : ∀ t : ℝ, BddAbove {u : ℝ | ![u, t] ∈ E}) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ u t : ℝ, t₀ ≤ t → ![u, t] ∈ E → u ≤ c * (1 + t) ^ M

/-- F1. The planar set of the Łojasiewicz argument is semialgebraic. -/
theorem isSemialgebraic_lojasiewicz_aux {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (f g : MvPolynomial ι ℝ) :
    TauCeti.IsSemialgebraic {w : Fin 2 → ℝ | ∃ x : ι → ℝ, x ∈ T ∧ ∑ i, x i ^ 2 ≤ w 1 ∧
      1 ≤ w 1 * MvPolynomial.eval x g ^ 2 ∧ w 0 * MvPolynomial.eval x f ^ 2 = 1}

/-- F2. The sets `K_t` are compact. -/
theorem isCompact_setOf_sq_sum_le {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)} (hT : IsClosed T)
    (g : MvPolynomial ι ℝ) (t : ℝ) :
    IsCompact {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * MvPolynomial.eval x g ^ 2}

/-- L1. Łojasiewicz inequality, with polynomial weight, for polynomials on a closed semialgebraic set. -/
theorem exists_lojasiewicz {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (hTc : IsClosed T) (f g : MvPolynomial ι ℝ)
    (hfg : ∀ x ∈ T, MvPolynomial.eval x f = 0 → MvPolynomial.eval x g = 0) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ x ∈ T,
      MvPolynomial.eval x g ^ (2 * (M + 1)) ≤
        C * MvPolynomial.eval x f ^ 2 *
          ((1 + ∑ i, x i ^ 2) * (1 + MvPolynomial.eval x g ^ 2)) ^ (M + 1)
```

The arithmetic step F3 (report §4.1, `lojasiewicz_arith`) may be public or private, in the form of the report or
any other form you find convenient.

Notes. The exponent is `M + 1`, not `M` (with exponent `0` the inequality is false at points where `f = g = 0`).
No `sSup`. The proof of L1 is §3.1 of the report, Steps 1–5.

Build: `lake build Semialgebraic.Finiteness.Lojasiewicz`. Acceptance: builds; no forbidden token; axioms of every
public theorem are `[propext, Classical.choice, Quot.sound]`.
