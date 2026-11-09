import Semialgebraic

/-!
Axiom check of the interface theorems. Run with `lake env lean scripts/CheckAxioms.lean` (or `scripts/check.sh`).
Every line must print exactly `[propext, Classical.choice, Quot.sound]`.
-/

#print axioms Semialgebraic.Interface.image_comp_inl
