import Semialgebraic.Finiteness.Lojasiewicz
import Semialgebraic.Finiteness.Cells
import Mathlib.SetTheory.Cardinal.NatCard

/-!
# The finiteness theorem for open and closed semialgebraic sets (plan ids C1, L2, L3)

This file provides (notation: `N(x) = ∑ i, x i ^ 2`):

* `Semialgebraic.exists_pos_between` (C1) : if `U` is open semialgebraic and the basic set
  `B = {f = 0, g_j > 0 ∀ j}` lies in `U`, there is a polynomial `q` with `B ⊆ {q > 0, g_j > 0 ∀ j} ⊆ U`.
  Proof: the Łojasiewicz inequality L1 (`exists_lojasiewicz`) on the closed semialgebraic set
  `T := Uᶜ ∩ ⋂ j, {0 ≤ g j}` with `g := ∏ j, g j` gives `C, M`, and
  `q := g ^ (2(M+1)) - C f² ((1 + N) (1 + g²)) ^ (M+1)`.
* `Semialgebraic.exists_eq_iUnion_iInter_pos` (L2) : an open semialgebraic set is a finite union of basic open
  sets `⋂ j, {0 < Q i j}`. Proof: sign normal form (`TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`); each
  sign cell contained in `U` is a basic set `{f = 0, g_j > 0}` (C2, `exists_setOf_sign_eq_eq`), and C1 puts a
  basic open set between it and `U`; the finitely many sign vectors are reindexed by `Fin`.
* `Semialgebraic.exists_eq_iUnion_iInter_nonneg` (L3) : a closed semialgebraic set is a finite union of basic
  closed sets `⋂ j, {0 ≤ P i j}`. Proof: L2 for the complement and `compl_iUnion_iInter_pos` (L3a).

The proofs are `notes/research/route1-lojasiewicz.md` §3.2–§3.3; the code follows its Appendix B prototype.
No deviation from the brief: the three statements are exactly those of `notes/briefs/P3-c-finiteness.md`.
-/

open MvPolynomial

namespace Semialgebraic

/-- C1. Between a basic set `{f = 0, g_j > 0}` and an open semialgebraic set containing it there is a basic
open set `{q > 0, g_j > 0}`. -/
theorem exists_pos_between {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) {k : ℕ} (f : MvPolynomial ι ℝ)
    (g : Fin k → MvPolynomial ι ℝ)
    (hB : {x : ι → ℝ | MvPolynomial.eval x f = 0 ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆ U) :
    ∃ q : MvPolynomial ι ℝ,
      {x : ι → ℝ | MvPolynomial.eval x f = 0 ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆
        {x | 0 < MvPolynomial.eval x q ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ∧
      {x : ι → ℝ | 0 < MvPolynomial.eval x q ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆ U := by
  -- the closed semialgebraic set `T = Uᶜ ∩ {g_j ≥ 0 ∀ j}`
  have hTsa : TauCeti.IsSemialgebraic (Uᶜ ∩ ⋂ j, {x : ι → ℝ | 0 ≤ eval x (g j)}) :=
    hU.compl.inter
      (TauCeti.IsSemialgebraic.iInter fun j => TauCeti.isSemialgebraic_eval_nonneg (g j))
  have hTc : IsClosed (Uᶜ ∩ ⋂ j, {x : ι → ℝ | 0 ≤ eval x (g j)}) :=
    (isClosed_compl_iff.2 hUo).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (MvPolynomial.continuous_eval (g j)))
  -- on `T`, `f = 0` forces `∏ g_j = 0`: otherwise every `g_j > 0` and the point lies in `B ⊆ U`
  have hfg : ∀ x ∈ Uᶜ ∩ ⋂ j, {x : ι → ℝ | 0 ≤ eval x (g j)},
      eval x f = 0 → eval x (∏ j, g j) = 0 := by
    rintro x ⟨hxU, hx⟩ hf0
    by_contra hP
    rw [eval_prod] at hP
    have hP' := Finset.prod_ne_zero_iff.1 hP
    exact hxU (hB ⟨hf0, fun j =>
      lt_of_le_of_ne (Set.mem_iInter.1 hx j) (Ne.symm (hP' j (Finset.mem_univ j)))⟩)
  -- the Łojasiewicz inequality on `T`
  obtain ⟨C, M, -, hL⟩ := exists_lojasiewicz hTsa hTc f (∏ j, g j) hfg
  refine ⟨(∏ j, g j) ^ (2 * (M + 1)) -
    MvPolynomial.C C * f ^ 2 * ((1 + ∑ i, X i ^ 2) * (1 + (∏ j, g j) ^ 2)) ^ (M + 1), ?_, ?_⟩
  · -- on `B`, `q = (∏ g_j) ^ (2(M+1)) > 0`
    rintro x ⟨hf0, hg⟩
    refine ⟨?_, hg⟩
    have hP : 0 < eval x (∏ j, g j) := by
      rw [eval_prod]; exact Finset.prod_pos fun j _ => hg j
    simp only [map_sub, map_mul, map_pow, eval_C, hf0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul, sub_zero]
    positivity
  · -- a point of `{q > 0, g_j > 0}` outside `U` lies in `T`, where L1 says `q ≤ 0`
    rintro x ⟨hq, hg⟩
    by_contra hxU
    have hxT : x ∈ Uᶜ ∩ ⋂ j, {x : ι → ℝ | 0 ≤ eval x (g j)} :=
      ⟨hxU, Set.mem_iInter.2 fun j => (hg j).le⟩
    have h := hL x hxT
    simp only [map_sub, map_mul, map_pow, map_add, map_one, map_sum, eval_C, eval_X] at hq
    linarith

/-- L2. Finiteness theorem for open sets: an open semialgebraic set is a finite union of basic open sets. -/
theorem exists_eq_iUnion_iInter_pos {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) :
    ∃ (I J : ℕ) (Q : Fin I → Fin J → MvPolynomial ι ℝ),
      U = ⋃ i, ⋂ j, {x | 0 < MvPolynomial.eval x (Q i j)} := by
  classical
  -- sign normal form `U = {x | Φ (sign ∘ p)(x)}`
  obtain ⟨m, p, Φ, hUeq⟩ := hU.exists_eq_setOf_sign_eval
  -- for each admissible sign vector, a basic open set between its cell and `U`
  have key : ∀ ε : {ε : Fin m → SignType // Φ ε}, ∃ Q : Fin (m + 1) → MvPolynomial ι ℝ,
      {x : ι → ℝ | ∀ i, SignType.sign (eval x (p i)) = ε.1 i} ⊆ ⋂ j, {x | 0 < eval x (Q j)} ∧
      (⋂ j, {x : ι → ℝ | 0 < eval x (Q j)}) ⊆ U := by
    rintro ⟨ε, hε⟩
    -- the cell is a basic set (C2) contained in `U`
    obtain ⟨f, g, hcell⟩ := exists_setOf_sign_eq_eq p ε
    have hsub : {x : ι → ℝ | eval x f = 0 ∧ ∀ j, 0 < eval x (g j)} ⊆ U := by
      rw [← hcell, hUeq]
      intro x hx
      have hx' : (fun i => SignType.sign (eval x (p i))) = ε := funext hx
      show Φ fun i => SignType.sign (eval x (p i))
      rw [hx']; exact hε
    -- C1, and the `m + 1` polynomials `q, g_1, …, g_m`
    obtain ⟨q, h1, h2⟩ := exists_pos_between hU hUo f g hsub
    refine ⟨Fin.cons q g, ?_, ?_⟩
    · rw [hcell]
      intro x hx
      obtain ⟨hq, hg⟩ := h1 hx
      refine Set.mem_iInter.2 (Fin.cases ?_ ?_)
      · simpa using hq
      · intro j; simpa using hg j
    · intro x hx
      rw [Set.mem_iInter] at hx
      exact h2 ⟨by simpa using hx 0, fun j => by simpa using hx j.succ⟩
  choose Q hQ1 hQ2 using key
  -- reindex the finite set of admissible sign vectors by `Fin`
  refine ⟨Nat.card {ε : Fin m → SignType // Φ ε}, m + 1,
    fun i => Q ((Finite.equivFin {ε : Fin m → SignType // Φ ε}).symm i), ?_⟩
  rw [(Finite.equivFin {ε : Fin m → SignType // Φ ε}).symm.surjective.iUnion_comp
    (fun ε => ⋂ j, {x : ι → ℝ | 0 < eval x (Q ε j)})]
  apply Set.Subset.antisymm
  · -- every point of `U` lies in the cell of its own sign vector
    intro x hx
    have hΦ : Φ fun i => SignType.sign (eval x (p i)) := by rw [hUeq] at hx; exact hx
    exact Set.mem_iUnion.2 ⟨⟨_, hΦ⟩, hQ1 ⟨_, hΦ⟩ (fun i => rfl)⟩
  · exact Set.iUnion_subset fun ε => hQ2 ε

/-- L3. Finiteness theorem for closed sets: a closed semialgebraic set is a finite union of basic closed sets. -/
theorem exists_eq_iUnion_iInter_nonneg {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hs : TauCeti.IsSemialgebraic s) (hsc : IsClosed s) :
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)} := by
  -- L2 for the open semialgebraic complement
  obtain ⟨I, J, Q, hQ⟩ := exists_eq_iUnion_iInter_pos hs.compl hsc.isOpen_compl
  -- complement and distributivity (L3a)
  refine ⟨J ^ I, I, fun k i => -Q i (finFunctionFinEquiv.symm k i), ?_⟩
  rw [← compl_iUnion_iInter_pos Q, ← hQ, compl_compl]

end Semialgebraic
