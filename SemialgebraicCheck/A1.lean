import Semialgebraic.Interface.Projection
import SemialgebraicCheck.Shape

/-!
# Shape check for A1

`BilevelShape.HasSemialgebraicProjections` (a verbatim copy of the HardnessBilevel class) is inhabited by the
interface theorem with no glue; the two semialgebraicity predicates agree by `Iff.rfl`.
-/

namespace BilevelShape

/-- The copy of `Bilevel.IsSemialgebraic` and `TauCeti.IsSemialgebraic` agree definitionally. -/
theorem isSemialgebraic_iff {ι : Type*} (s : Set (ι → ℝ)) :
    IsSemialgebraic s ↔ TauCeti.IsSemialgebraic s := Iff.rfl

theorem hasSemialgebraicProjections : HasSemialgebraicProjections :=
  ⟨Semialgebraic.Interface.image_comp_inl⟩

end BilevelShape

#print axioms BilevelShape.hasSemialgebraicProjections
