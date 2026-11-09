# Lean report P3-a — `Semialgebraic/Finiteness/Lojasiewicz.lean` (ids F0, F1, F2, F3, L1)

Status: **builds** (`lake build Semialgebraic.Finiteness.Lojasiewicz`: success). No `sorry`/`admit`/`axiom`/
`native_decide`/`unsafe`. `lake env lean` on the file prints no message. The only build warnings are Lake's
"imports `Mathlib.Tactic.*` … designed for use with the module system; consider adding `module`" notes, one per
tactic import; they are emitted for every non-`module` file importing Mathlib and the standing brief forbids the
`module` keyword, so they are left as is.

Imports: `Semialgebraic.Growth.Main`, `Mathlib.Topology.Algebra.MvPolynomial`, `Mathlib.Topology.Order.Compact`,
`Mathlib.Topology.Algebra.GroupWithZero`, `Mathlib.Tactic.{Linarith, Positivity, GCongr, FieldSimp, Ring, NormNum}`.

## Final statements (copied from the file)

```lean
theorem exists_growth_of_bddAbove_fibres {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E)
    (hbdd : ∀ t : ℝ, BddAbove {u : ℝ | ![u, t] ∈ E}) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ u t : ℝ, t₀ ≤ t → ![u, t] ∈ E → u ≤ c * (1 + t) ^ M

theorem isSemialgebraic_lojasiewicz_aux {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (f g : MvPolynomial ι ℝ) :
    TauCeti.IsSemialgebraic {w : Fin 2 → ℝ | ∃ x : ι → ℝ, x ∈ T ∧ ∑ i, x i ^ 2 ≤ w 1 ∧
      1 ≤ w 1 * MvPolynomial.eval x g ^ 2 ∧ w 0 * MvPolynomial.eval x f ^ 2 = 1}

theorem isCompact_setOf_sq_sum_le {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)} (hT : IsClosed T)
    (g : MvPolynomial ι ℝ) (t : ℝ) :
    IsCompact {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * MvPolynomial.eval x g ^ 2}

theorem lojasiewicz_arith {c t₀ N F G : ℝ} {M : ℕ} (hc : 0 ≤ c) (ht₀ : 0 ≤ t₀) (hN : 0 ≤ N)
    (hF : F ≠ 0) (hG : G ≠ 0)
    (h : 1 / F ^ 2 ≤ c * (1 + max t₀ (max N (1 / G ^ 2))) ^ M) :
    G ^ (2 * (M + 1)) ≤ c * (1 + t₀) ^ (M + 1) * F ^ 2 * ((1 + N) * (1 + G ^ 2)) ^ (M + 1)

theorem exists_lojasiewicz {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (hTc : IsClosed T) (f g : MvPolynomial ι ℝ)
    (hfg : ∀ x ∈ T, MvPolynomial.eval x f = 0 → MvPolynomial.eval x g = 0) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ x ∈ T,
      MvPolynomial.eval x g ^ (2 * (M + 1)) ≤
        C * MvPolynomial.eval x f ^ 2 *
          ((1 + ∑ i, x i ^ 2) * (1 + MvPolynomial.eval x g ^ 2)) ^ (M + 1)
```

All in `namespace Semialgebraic` with `open MvPolynomial`.

## Deviations from the brief

None. F0, F1, F2, L1 are character-for-character the brief's statements. F3 (`lojasiewicz_arith`) is public and
stated exactly as in report §4.1.

## Helper lemmas reusable by others

* `lojasiewicz_arith` (F3), public.
* The proof of L1 yields the explicit constant `C = c * (1 + t₀) ^ (M + 1)` from F0's output `(c, M, t₀)`.

## Names not as expected

None; every name of report §4.3 used here resolved as listed (`Set.mem_ofPred_eq`, `continuous_finsetSum`,
`ContinuousOn.inv₀`, `IsCompact.bddAbove_image`, `eq_inv_of_mul_eq_one_left`, `Real.exists_isLUB`,
`isCompact_univ_pi`, `IsCompact.of_isClosed_subset`, `Finset.single_le_sum`, `eval_rename`,
`TauCeti.IsSemialgebraic.setOf_exists_sumElim`, `.preimage_comp`, `TauCeti.isSemialgebraic_eval_le/_eq`).
Narrowing `Mathlib.Tactic` to the six tactic modules above caused no change in the `simp` normal forms of F1.
One change from the prototype: in L1, Step 4, `gcongr` no longer closes the side goal
`1 / g² ≤ ![_, t] 1` by assumption (the `![…] 1` is not reduced), so it is closed with `exact h1`.

## `#print axioms` (scratch file `/tmp/p3a/Ax.lean`, `lake env lean`)

```
'Semialgebraic.exists_growth_of_bddAbove_fibres' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isSemialgebraic_lojasiewicz_aux' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.isCompact_setOf_sq_sum_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.lojasiewicz_arith' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.exists_lojasiewicz' depends on axioms: [propext, Classical.choice, Quot.sound]
```
