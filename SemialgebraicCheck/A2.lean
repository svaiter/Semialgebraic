import Semialgebraic.Interface.Finiteness
import SemialgebraicCheck.Shape

/-!
# Shape check for A2

`BilevelShape.HasFinitenessTheorem` (a verbatim copy of the HardnessBilevel class) is inhabited by the interface
theorem `Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg` with no glue; the two semialgebraicity predicates
agree by `Iff.rfl`.
-/

namespace BilevelShape

theorem hasFinitenessTheorem : HasFinitenessTheorem := ⟨Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg⟩

end BilevelShape

#print axioms BilevelShape.hasFinitenessTheorem
