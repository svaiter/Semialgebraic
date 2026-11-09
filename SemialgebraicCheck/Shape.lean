import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Verbatim copies of the HardnessBilevel assumption classes

This file copies, character for character except for the namespace (`BilevelShape` instead of `Bilevel`) and for
`MvPolynomial.eval` written in full, the definition `Bilevel.IsSemialgebraic`
(`HardnessBilevel/Semialgebraic/Basic.lean`) and the three classes of `HardnessBilevel/Assumptions/Classes.lean`
(HardnessBilevelProgramming commit `84fba77`). It imports only Mathlib: this library does not depend on
HardnessBilevel, and the copies do not depend on TauCeti.

The files `SemialgebraicCheck/A1.lean`, `A2.lean`, `A3.lean` inhabit each class with the corresponding interface
theorem and no glue, which certifies at compile time that the interface theorems have the shape of the class
fields. The inhabitants are `theorem`s, never `instance`s.
-/

open MeasureTheory

namespace BilevelShape

def IsSemialgebraic {ι : Type*} (s : Set (ι → ℝ)) : Prop :=
  s ∈ generateSetAlgebra
    (Set.range (fun p : MvPolynomial ι ℝ => {x | MvPolynomial.eval x p = 0}) ∪
     Set.range (fun p : MvPolynomial ι ℝ => {x | 0 < MvPolynomial.eval x p}))

set_option linter.concreteInstances false

/-- A1 (Tarski–Seidenberg). -/
class HasSemialgebraicProjections : Prop where
  image_comp_inl {α β : Type} [Fintype α] [Finite β] {S : Set (α ⊕ β → ℝ)} :
    IsSemialgebraic S → IsSemialgebraic ((fun z : α ⊕ β → ℝ => z ∘ Sum.inl) '' S)

/-- A2 (finiteness theorem). -/
class HasFinitenessTheorem : Prop where
  exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}

/-- A3 (growth bound). -/
class HasGrowthBound : Prop where
  growth {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    IsSemialgebraic {z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())} →
    (∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) →
    ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M

end BilevelShape
