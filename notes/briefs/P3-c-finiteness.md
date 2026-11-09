# Unit P3-c (writer): finiteness theorem assembly — ids C1, L2, L3, interface theorem A2

Read `notes/briefs/standing.md`, `PLAN.md` §3 and §4.4, then `notes/research/route1-lojasiewicz.md` §3.2–3.3 and §4
and its audit `notes/audit/R1-lojasiewicz.md` (corrections there override the report), and the two files your unit
imports with their reports: `Semialgebraic/Finiteness/Lojasiewicz.lean` (`notes/lean-reports/P3-a.md`) and
`Semialgebraic/Finiteness/Cells.lean` (`notes/lean-reports/P3-b.md`). Do not edit those files. Appendix B of the
research report contains an unaudited scratch prototype; you may start from it, but your files must follow the
standing brief and you are responsible for every line.

You write exactly three Lean files and one report:

* `Semialgebraic/Finiteness/Main.lean`
* `Semialgebraic/Interface/Finiteness.lean`
* `SemialgebraicCheck/A2.lean`
* `notes/lean-reports/P3-c.md`

## `Semialgebraic/Finiteness/Main.lean` (namespace `Semialgebraic`) — required public statements

```lean
/-- C1. Between a basic set `{f = 0, g_j > 0}` and an open semialgebraic set containing it there is a basic
open set `{q > 0, g_j > 0}`. -/
theorem exists_pos_between {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) {k : ℕ} (f : MvPolynomial ι ℝ)
    (g : Fin k → MvPolynomial ι ℝ)
    (hB : {x : ι → ℝ | MvPolynomial.eval x f = 0 ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆ U) :
    ∃ q : MvPolynomial ι ℝ,
      {x : ι → ℝ | MvPolynomial.eval x f = 0 ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆
        {x | 0 < MvPolynomial.eval x q ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ∧
      {x : ι → ℝ | 0 < MvPolynomial.eval x q ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆ U

/-- L2. Finiteness theorem for open sets: an open semialgebraic set is a finite union of basic open sets. -/
theorem exists_eq_iUnion_iInter_pos {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) :
    ∃ (I J : ℕ) (Q : Fin I → Fin J → MvPolynomial ι ℝ),
      U = ⋃ i, ⋂ j, {x | 0 < MvPolynomial.eval x (Q i j)}

/-- L3. Finiteness theorem for closed sets: a closed semialgebraic set is a finite union of basic closed sets. -/
theorem exists_eq_iUnion_iInter_nonneg {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hs : TauCeti.IsSemialgebraic s) (hsc : IsClosed s) :
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}
```

Proofs: report §3.2 (C1 from `exists_lojasiewicz` applied to `T := Uᶜ ∩ ⋂ j, {0 ≤ g j}` and `∏ j, g j`; L2 from
`TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`, `exists_setOf_sign_eq_eq`, C1, reindexing of the finite set of
sign vectors `{ε // Φ ε}` to `Fin`), §3.3 (L3 from L2 applied to `sᶜ` and `compl_iUnion_iInter_pos`).

## `Semialgebraic/Interface/Finiteness.lean` (namespace `Semialgebraic.Interface`) — exact statement, do not alter

```lean
/-- **Interface theorem A2** (finiteness theorem). -/
theorem exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}
```

It must be `fun hs hc => Semialgebraic.exists_eq_iUnion_iInter_nonneg hs hc` (or equally direct). Header in the
style of `Semialgebraic/Interface/Growth.lean`.

## `SemialgebraicCheck/A2.lean` — in the style of `SemialgebraicCheck/A3.lean`

```lean
import Semialgebraic.Interface.Finiteness
import SemialgebraicCheck.Shape

namespace BilevelShape
theorem hasFinitenessTheorem : HasFinitenessTheorem := ⟨Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg⟩
end BilevelShape

#print axioms BilevelShape.hasFinitenessTheorem
```

with a docstring header. It must compile with exactly this term (no glue lemma). Do not edit
`SemialgebraicCheck/Shape.lean`.

Build with `lake build Semialgebraic.Finiteness.Main Semialgebraic.Interface.Finiteness SemialgebraicCheck.A2`.
Acceptance: all build; no forbidden token; axioms of `exists_pos_between`, `exists_eq_iUnion_iInter_pos`,
`exists_eq_iUnion_iInter_nonneg`, `Interface.exists_eq_iUnion_iInter_nonneg`, `BilevelShape.hasFinitenessTheorem`
are `[propext, Classical.choice, Quot.sound]`.
