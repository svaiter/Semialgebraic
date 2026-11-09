import Semialgebraic.Interface.Growth
import SemialgebraicCheck.Shape

/-!
# Shape check for A3

`BilevelShape.HasGrowthBound` (a verbatim copy of the HardnessBilevel class) is inhabited by the interface theorem
`Semialgebraic.Interface.growth` with no glue; the two semialgebraicity predicates agree by `Iff.rfl`.
-/

namespace BilevelShape

theorem hasGrowthBound : HasGrowthBound := ⟨Semialgebraic.Interface.growth⟩

end BilevelShape

#print axioms BilevelShape.hasGrowthBound
