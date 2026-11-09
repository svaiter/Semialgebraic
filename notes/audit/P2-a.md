# Audit P2-a — `Semialgebraic/Growth/OneVar.lean` (G1, G2)

**Verdict: ACCEPT.** Required fixes: none.

1. **Build.** `lake build Semialgebraic.Growth.OneVar` succeeds (4484 jobs). Only warnings: the expected
   "designed for use with the module system" import notices (3 imports). No deprecations, no other warnings.
2. **Forbidden tokens.** grep for `sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque|set_option|instance|def|abbrev|structure|class|notation`
   finds nothing in the file (no new definitions, no instances, no `set_option`).
3. **Axioms** (scratch `/tmp/audit-p2a/ax.lean`): all seven public declarations depend on exactly
   `[propext, Classical.choice, Quot.sound]`: `exists_growth_of_eval_eq_zero`, `exists_growth_of_interior_eq_empty`,
   `exists_growth_of_subsingleton_fibres`, `abs_le_of_sum_range_mul_pow_eq_zero`, `exists_le_abs_eval_of_ne_zero`,
   `abs_eval_le_sum_mul_one_add_pow`, `eval_uniqueAlgEquiv_fin_one`.
4. **Faithfulness.** The three statements (G1, G2 and the intermediate polynomial statement) were compared with the
   brief and PLAN §4.2 symbol by symbol: identical binders, implicit/explicit status, types, hypotheses and conclusion.
   Decisive test: `example : <statement copied verbatim from the brief> := <theorem> …` for all three elaborates and
   is closed with no errors. No strengthening, no deviation.
5. **No definitional cheating.** No new def/structure/class/notation. Sanity instances:
   * G1: `G = {z | z 0 = z 1 ^ 2}` (parabola, semialgebraic, empty interior) is non-vacuous; bound `|s| ≤ (1+t)^2` for `t ≥ 0`.
   * G2: `G = {z | z 0 = z 1}` (graph of a function, all fibres singletons); hypothesis satisfiable, bound `|s| ≤ 1+t`.
   * Polynomial statement: `P = s - t`, `d = 1`; `P = 1` (d = 0) has no roots, handled by the `d = 0` case.
   Hypotheses are not contradictory (`hP : P ≠ 0`, `interior G = ∅`, fibre uniqueness all hold in the examples).
6. **Interface theorem.** Not applicable.
7. **Proof hygiene** (non-blocking). Proofs are commented and moderate in length; the main theorem is ~45 lines with
   step comments. `simp` without `only` appears in terminal positions only (`simp at h` followed by `exact absurd h hd`
   in the `d = 0` case is a mild exception; harmless). `open Finset Filter` is scoped to the namespace section, not
   global `Classical`. No slow declarations observed (build of the file fast). The `Filter` open appears to be needed
   only for `eventually_atTop`; fine.

Writer's report (`notes/lean-reports/P2-a.md`) matches the file: statements, axioms output and "no deviation" claim verified.
