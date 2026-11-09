import Semialgebraic.Finiteness.Main

/-!
# Interface theorem A2: the finiteness theorem

This file provides, in TauCeti's vocabulary, the statement that HardnessBilevel assumes through the class
`Bilevel.HasFinitenessTheorem` (assumption A2).

* `Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg` : the interface theorem. Its statement is the field
  `exists_eq_iUnion_iInter_nonneg` of `Bilevel.HasFinitenessTheorem` with `Bilevel.IsSemialgebraic` replaced by
  `TauCeti.IsSemialgebraic` (same binders `{ι : Type} [Fintype ι] {s : Set (ι → ℝ)}`, same hypotheses, same
  conclusion). The two semialgebraicity predicates agree by `Iff.rfl` (see
  `Semialgebraic.isSemialgebraic_iff_mem_generateSetAlgebra`).

The proof is `Semialgebraic.exists_eq_iUnion_iInter_nonneg` (plan §4.4, id L3, for `ι : Type*`), which rests on
the Łojasiewicz inequality L1 (`Semialgebraic.exists_lojasiewicz`) and thereby on G4
(`Semialgebraic.exists_growth_isLUB`).
-/

namespace Semialgebraic

namespace Interface

/-- **Interface theorem A2** (finiteness theorem). -/
theorem exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)} :=
  fun hs hc => _root_.Semialgebraic.exists_eq_iUnion_iInter_nonneg hs hc

end Interface

end Semialgebraic
