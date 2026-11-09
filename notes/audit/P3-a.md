# Audit P3-a: Semialgebraic/Finiteness/Lojasiewicz.lean

Verdict: **ACCEPT**. Required fixes: none.

1. Build: `lake build Semialgebraic.Finiteness.Lojasiewicz` succeeds. Warnings are only the expected "designed for use with the module system" import notes. No deprecations.
2. Forbidden tokens: grep finds no sorry/admit/axiom/native_decide/unsafe/implemented_by/extern/opaque, no `set_option`, no instance, no new def/abbrev/structure/class (the only grep hit is the word "notation" in the header comment).
3. Axioms (scratch /tmp/audit-p3a/A.lean), all five public theorems: [propext, Classical.choice, Quot.sound].
4. Faithfulness: for F0, F1, F2, L1 I wrote `example : <brief statement verbatim> := fun .. => theorem ..` and each elaborates with no error; the statements in the file also match the brief text symbol by symbol. F3 (`lojasiewicz_arith`) is an extra public lemma, allowed by the brief. No deviation, no added hypothesis.
5. Vacuity: no new definitions. Hypotheses are satisfiable:
   - T = {0} in ℝ, f = g = X: hfg holds; the conclusion at x = 0 reads 0 ≤ C * 0 * 1 with exponent M+1 >= 1, true (0^(2(M+1)) = 0).
   - T = univ, f = X, g = X^2: hfg holds (x = 0 gives g = 0). Need x^(4(M+1)) ≤ C x^2 ((1+x^2)(1+x^4))^(M+1); true for M=0, C=1 since x^4 ≤ x^2 (1+x^2)(1+x^4) when |x| >= 1, and trivially for the rest after adjusting C. Non-vacuous.
   - T = {x | 1 ≤ x0 x1 ∧ 0 ≤ x0}, f = X1, g = 1: f has no zero on T (x1 > 0), so hfg is vacuously satisfied; the conclusion 1 ≤ C x1^2 ((1+|x|^2)·2)^(M+1) holds with C = 1 since x1 ≥ 1/x0 and the weight grows; T is closed, semialgebraic, and unbounded, so the compactness step F2 is genuinely used (K_t is bounded by the norm constraint).
   F0: E with bounded fibres, e.g. E = {(u,t) | u ≤ t^2}, gives c=1, M=2. F1 and F2 are unconditional structural statements, F2 non-vacuous for any closed T.
6. Interface theorem: not applicable.
7. Hygiene (non-blocking): proofs are commented; `simp` non-terminal uses are in `convert ... using 1; ext; simp` closing positions; the file imports specific Mathlib modules; no global Classical. Nothing slow observed (build replay fast).

Non-blocking remarks: none beyond the above.
