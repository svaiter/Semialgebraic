# Audit P3-c (C1, L2, L3, A2) — verdict: ACCEPT

1. Build: `lake build Semialgebraic.Finiteness.Main Semialgebraic.Interface.Finiteness SemialgebraicCheck.A2` succeeds; only the module-system import warnings.
2. Forbidden tokens: grep for sorry/admit/axiom/native_decide/unsafe/implemented_by/extern/opaque/set_option/instance in the three files: only the `#print axioms` line in A2.lean. No set_option. No instance.
3. Axioms (scratch /tmp/audit-p3c/T.lean): exists_pos_between, exists_eq_iUnion_iInter_pos, exists_eq_iUnion_iInter_nonneg, Interface.exists_eq_iUnion_iInter_nonneg, BilevelShape.hasFinitenessTheorem: all [propext, Classical.choice, Quot.sound].
4. Faithfulness: `example : <verbatim brief statement> := theorem` compiles for C1, L2, L3 (universe-polymorphic ι : Type*). Statements match the brief symbol by symbol; no deviations.
5. No new defs. Non-vacuity: s = ∅ instance checked in Lean (Fin 1, via the interface theorem). Informally: s = univ (I=J=1... P=1), s = [0,∞) in Fin 1 → ℝ (P = X 0), ι empty (ℝ^0 a point; s = ∅ or univ, both fine). Hypotheses are not contradictory.
6. Interface: Interface.exists_eq_iUnion_iInter_nonneg has binders {ι : Type} [Fintype ι] {s}, hypotheses `IsSemialgebraic s → IsClosed s →`, conclusion identical to the class field (non-strict `0 ≤`; closed form). Class field in HardnessBilevel Classes.lean, the copy in Shape.lean, and the interface theorem agree except for the predicate (TauCeti vs Bilevel/BilevelShape, agreeing by Iff.rfl, which the build confirms). IsClosed uses the default product topology (no letI/haveI/local instance). A2.lean uses exactly `⟨Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg⟩`, no glue. Shape.lean: `git diff --stat` empty, git status clean. In C1/L2 the open form uses strict `0 <`.
7. Hygiene: proofs commented, no non-terminal bare simp problems noted; no slow declarations observed.

Required fixes: none.
Remarks: Shape.lean header cites HardnessBilevel commit 84fba77, current HEAD is 521c0d6 (class text compared directly and is identical). The Fin-1 empty-set scratch `simpa` gave a linter hint (scratch only).
