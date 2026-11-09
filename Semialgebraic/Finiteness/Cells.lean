import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Basic.Sign.Basic

/-!
# Sign cells and complements of basic open sets (plan ids C2, L3a)

This file is purely combinatorial; it provides two set identities used in the proof of the finiteness theorem
for open and closed semialgebraic sets (`PLAN.md` §4.4, research note `notes/research/route1-lojasiewicz.md`
§3.2–§3.3).

* `Semialgebraic.exists_setOf_sign_eq_eq` (C2) : a sign cell `{x | ∀ i, sign (p i x) = ε i}` of `m` polynomials
  is the zero set of one polynomial `f` cut by `m` strict inequalities `0 < g j`.
  Proof: `f := ∑ i, if ε i = 0 then p i ^ 2 else 0` (a sum of squares vanishes iff each term does) and
  `g i := 1, p i, -p i` according to `ε i = 0, 1, -1`.
* `Semialgebraic.compl_iUnion_iInter_pos` (L3a) : the complement of `⋃ i, ⋂ j, {0 < Q i j}` is
  `⋃ k, ⋂ i, {0 ≤ -Q i (φ_k i)}`, where `φ_k := finFunctionFinEquiv.symm k` runs over all choice functions
  `Fin I → Fin J`.
  Proof: pointwise, `x ∉ ⋃ i, ⋂ j, {0 < Q i j} ↔ ∀ i, ∃ j, Q i j x ≤ 0 ↔ ∃ φ, ∀ i, 0 ≤ -Q i (φ i) x`.

No deviation from the brief: the statements are exactly those of the brief.
-/

open MvPolynomial

namespace Semialgebraic

/-- C2. A sign cell of `m` polynomials is the zero set of one polynomial cut by `m` strict inequalities. -/
theorem exists_setOf_sign_eq_eq {ι : Type*} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ)
    (ε : Fin m → SignType) :
    ∃ (f : MvPolynomial ι ℝ) (g : Fin m → MvPolynomial ι ℝ),
      {x : ι → ℝ | ∀ i, SignType.sign (MvPolynomial.eval x (p i)) = ε i} =
        {x | MvPolynomial.eval x f = 0 ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} := by
  classical
  -- the equation collects the squares of the polynomials whose prescribed sign is `0`;
  -- the inequalities are `1 > 0`, `p i > 0` or `-p i > 0` according to the prescribed sign
  refine ⟨∑ i, if ε i = 0 then p i ^ 2 else 0,
    fun i => if ε i = 0 then 1 else if ε i = 1 then p i else -p i, ?_⟩
  ext x
  -- a sum of squares vanishes iff each of its terms vanishes
  have hsum : MvPolynomial.eval x (∑ i, if ε i = 0 then p i ^ 2 else 0) = 0 ↔
      ∀ i, ε i = 0 → MvPolynomial.eval x (p i) = 0 := by
    rw [map_sum, Finset.sum_eq_zero_iff_of_nonneg]
    · refine forall_congr' fun i => ?_
      by_cases h : ε i = 0 <;> simp [h]
    · intro i _
      by_cases h : ε i = 0 <;> simp [h, sq_nonneg]
  simp only [Set.mem_ofPred_eq, hsum, ← forall_and]
  -- compare coordinate by coordinate, in the three cases of the prescribed sign
  refine forall_congr' fun i => ?_
  rcases h : ε i with _ | _ | _
  · simp [sign_eq_zero_iff]
  · simp [sign_eq_neg_one_iff]
  · simp [sign_eq_one_iff]

/-- L3a. The complement of a finite union of basic open sets is a finite union of basic closed sets. -/
theorem compl_iUnion_iInter_pos {ι : Type*} {I J : ℕ} (Q : Fin I → Fin J → MvPolynomial ι ℝ) :
    (⋃ i, ⋂ j, {x : ι → ℝ | 0 < MvPolynomial.eval x (Q i j)})ᶜ =
      ⋃ k : Fin (J ^ I), ⋂ i : Fin I,
        {x | 0 ≤ MvPolynomial.eval x (-Q i (finFunctionFinEquiv.symm k i))} := by
  ext x
  -- pointwise: `∀ i, ∃ j, Q i j x ≤ 0` on the left, `∃ k, ∀ i, Q i (φ_k i) x ≤ 0` on the right
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq, not_exists,
    not_forall, not_lt, map_neg, neg_nonneg]
  constructor
  · -- choose a bad index `φ i` in each row and encode the choice function `φ` as `k`
    intro h
    choose φ hφ using h
    exact ⟨finFunctionFinEquiv φ, fun i => by simpa using hφ i⟩
  · -- the choice function `finFunctionFinEquiv.symm k` gives a bad index in each row
    rintro ⟨k, hk⟩ i
    exact ⟨_, hk i⟩

end Semialgebraic
