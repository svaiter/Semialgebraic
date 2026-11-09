import Semialgebraic.Finiteness.Cells
import Semialgebraic.Finiteness.Lojasiewicz
import Semialgebraic.Finiteness.Main
import Semialgebraic.Growth.IsLUB
import Semialgebraic.Growth.Main
import Semialgebraic.Growth.OneVar
import Semialgebraic.Interface.Finiteness
import Semialgebraic.Interface.Growth
import Semialgebraic.Interface.Projection

/-!
# Semialgebraic

A companion library to TauCeti's real algebraic geometry: results on real semialgebraic sets stated in TauCeti's
vocabulary (`TauCeti.IsSemialgebraic`). See `README.md` and `PLAN.md`.

* `Semialgebraic.Interface.image_comp_inl` — Tarski–Seidenberg, projection form (from TauCeti).
* `Semialgebraic.Interface.growth`, `Semialgebraic.exists_polynomial_growth` — polynomial growth of a function with
  semialgebraic graph that is bounded on bounded sets.
* `Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg`, `Semialgebraic.exists_eq_iUnion_iInter_nonneg`,
  `Semialgebraic.exists_eq_iUnion_iInter_pos` — the finiteness theorem for closed and for open semialgebraic sets.
* `Semialgebraic.exists_lojasiewicz` — a Łojasiewicz inequality with polynomial weight for polynomials on a closed
  semialgebraic set.
-/
