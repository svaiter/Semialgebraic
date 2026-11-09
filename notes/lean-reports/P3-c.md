# Lean report P3-c — finiteness theorem assembly (ids C1, L2, L3, interface theorem A2)

Files: `Semialgebraic/Finiteness/Main.lean`, `Semialgebraic/Interface/Finiteness.lean`, `SemialgebraicCheck/A2.lean`.

Status: **builds** (`lake build Semialgebraic.Finiteness.Main Semialgebraic.Interface.Finiteness
SemialgebraicCheck.A2`: "Build completed successfully"). No `sorry`/`admit`/`axiom`/`native_decide`/`unsafe` (grep:
only the `#print axioms` line of `A2.lean`). `lake env lean` on `Main.lean` and `Interface/Finiteness.lean` prints
no message (no linter or deprecation warning). The only build warnings are Lake's "imports … designed for use with
the module system; consider adding `module`" notes, which the standing brief makes unavoidable.

Imports of `Main.lean`: `Semialgebraic.Finiteness.Lojasiewicz`, `Semialgebraic.Finiteness.Cells`,
`Mathlib.SetTheory.Cardinal.NatCard` (`Finite.equivFin`). `Interface/Finiteness.lean` imports only
`Semialgebraic.Finiteness.Main`; `A2.lean` imports `Semialgebraic.Interface.Finiteness` and `SemialgebraicCheck.Shape`.

## Final statements (copied from the files)

`Semialgebraic/Finiteness/Main.lean`, namespace `Semialgebraic` (`open MvPolynomial`):

```lean
theorem exists_pos_between {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) {k : ℕ} (f : MvPolynomial ι ℝ)
    (g : Fin k → MvPolynomial ι ℝ)
    (hB : {x : ι → ℝ | MvPolynomial.eval x f = 0 ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆ U) :
    ∃ q : MvPolynomial ι ℝ,
      {x : ι → ℝ | MvPolynomial.eval x f = 0 ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆
        {x | 0 < MvPolynomial.eval x q ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ∧
      {x : ι → ℝ | 0 < MvPolynomial.eval x q ∧ ∀ j, 0 < MvPolynomial.eval x (g j)} ⊆ U

theorem exists_eq_iUnion_iInter_pos {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) :
    ∃ (I J : ℕ) (Q : Fin I → Fin J → MvPolynomial ι ℝ),
      U = ⋃ i, ⋂ j, {x | 0 < MvPolynomial.eval x (Q i j)}

theorem exists_eq_iUnion_iInter_nonneg {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hs : TauCeti.IsSemialgebraic s) (hsc : IsClosed s) :
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}
```

`Semialgebraic/Interface/Finiteness.lean`, namespace `Semialgebraic.Interface`:

```lean
/-- **Interface theorem A2** (finiteness theorem). -/
theorem exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)} :=
  fun hs hc => _root_.Semialgebraic.exists_eq_iUnion_iInter_nonneg hs hc
```

`SemialgebraicCheck/A2.lean`:

```lean
theorem hasFinitenessTheorem : HasFinitenessTheorem := ⟨Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg⟩
```

(exactly the term of the brief, no glue lemma).

## Deviations from the brief

None. All statements are character for character those of `notes/briefs/P3-c-finiteness.md`. Proofs follow
report §3.2–§3.3 and the Appendix B prototype (C1: L1 on `Uᶜ ∩ ⋂ j, {0 ≤ g j}` with `∏ j, g j` and
`q := (∏ g_j)^(2(M+1)) - C f² ((1 + ∑ X_i²)(1 + (∏ g_j)²))^(M+1)`; L2: sign normal form, C2, C1, `Fin.cons q g`,
reindexing by `Finite.equivFin`; L3: L2 on `sᶜ`, `compl_iUnion_iInter_pos`, `compl_compl`). Self-reference is
avoided in the interface file by `_root_.Semialgebraic.exists_eq_iUnion_iInter_nonneg`.

## Helper lemmas reusable by others

None new (no private or public helpers besides the three required theorems). `exists_pos_between` (C1) is itself
reusable.

## Names not as expected

None. Used and verified: `TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`, `.compl`, `.inter`, `.iInter`,
`TauCeti.isSemialgebraic_eval_nonneg`, `Finite.equivFin` (`Mathlib/SetTheory/Cardinal/NatCard.lean:39`),
`Function.Surjective.iUnion_comp`, `isClosed_compl_iff`, `isClosed_iInter`, `isClosed_le`,
`MvPolynomial.continuous_eval`, `eval_prod`, `Finset.prod_ne_zero_iff`, `Finset.prod_pos`, `finFunctionFinEquiv`.
The prototype's proofs went through unchanged under the narrowed imports.

## `#print axioms`

Scratch file (`lake env lean`) and the `#print axioms` line of `SemialgebraicCheck/A2.lean`:

```
'Semialgebraic.exists_pos_between' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.exists_eq_iUnion_iInter_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.exists_eq_iUnion_iInter_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]
'BilevelShape.hasFinitenessTheorem' depends on axioms: [propext, Classical.choice, Quot.sound]
```
