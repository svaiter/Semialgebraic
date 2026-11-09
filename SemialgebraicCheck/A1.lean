import Semialgebraic.Interface.Projection

/-!
# Shape check for A1

A verbatim copy of `Bilevel.IsSemialgebraic` and of the class `Bilevel.HasSemialgebraicProjections` from
`HardnessBilevel/Semialgebraic/Basic.lean` and `HardnessBilevel/Assumptions/Classes.lean` (namespace renamed to
`BilevelShape`; this library does not depend on HardnessBilevel). The class is inhabited by the interface theorem
with no glue, which certifies at compile time that the interface theorem has the shape of the class field.
The inhabitant is a `theorem`, not an `instance`.
-/

open MeasureTheory

namespace BilevelShape

def IsSemialgebraic {ι : Type*} (s : Set (ι → ℝ)) : Prop :=
  s ∈ generateSetAlgebra
    (Set.range (fun p : MvPolynomial ι ℝ => {x | MvPolynomial.eval x p = 0}) ∪
     Set.range (fun p : MvPolynomial ι ℝ => {x | 0 < MvPolynomial.eval x p}))

set_option linter.concreteInstances false

class HasSemialgebraicProjections : Prop where
  image_comp_inl {α β : Type} [Fintype α] [Finite β] {S : Set (α ⊕ β → ℝ)} :
    IsSemialgebraic S → IsSemialgebraic ((fun z : α ⊕ β → ℝ => z ∘ Sum.inl) '' S)

/-- The two predicates agree definitionally. -/
theorem isSemialgebraic_iff {ι : Type*} (s : Set (ι → ℝ)) :
    IsSemialgebraic s ↔ TauCeti.IsSemialgebraic s := Iff.rfl

theorem hasSemialgebraicProjections : HasSemialgebraicProjections :=
  ⟨Semialgebraic.Interface.image_comp_inl⟩

end BilevelShape

#print axioms Semialgebraic.Interface.image_comp_inl
#print axioms BilevelShape.hasSemialgebraicProjections
