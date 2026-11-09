# Brief for research auditors (Phase 3a)

You audit one research report on the finiteness theorem (assumption A2). You are adversarial: assume the report
contains at least one error and find it. You did not write the report and must not trust it.

Read `/home/user/Semialgebraic/notes/briefs/R-common.md` (target statement, context, requirements on reports), the
brief of the report you audit (`notes/briefs/R1-lojasiewicz.md` or `notes/briefs/R2-cad-thom.md`), `PLAN.md`, and then
the report.

Mandatory work:

1. **Re-derive every lemma yourself, before reading the report's proof of it.** For each lemma: write your own proof
   (or a counterexample), then compare with the report. Check every quantifier, every constant, every edge case
   (empty sets, empty index types, zero polynomials, exponent `0`, `0 ^ 0 = 1`, unbounded sets, empty fibres, sets
   that are not closed, points on the boundary). Test each lemma on at least two concrete examples of your own
   choosing, including a degenerate one.
2. **Check the logical chain**: does the final theorem follow from the lemmas exactly as stated? Is any lemma used
   in a stronger form than proved? Are the Lean-style statements faithful to the mathematics (types, index types,
   coordinates, direction of inclusions)? Does the last statement coincide with the target of `R-common.md`?
3. **Check every claimed Lean dependency** by grep in `/home/user/Semialgebraic/.lake/packages/` (Mathlib `1b1ccf4b`,
   TauCeti `2c9b12be`) and in `/home/user/Semialgebraic/Semialgebraic/`: does the name exist, with the quoted
   signature and hypotheses? You may check names with a scratch file under `/tmp` and
   `cd /home/user/Semialgebraic && . scripts/env.sh && lake env lean /tmp/…` (never `lake build` bare). If the
   report contains a Lean prototype, you may compile it in a scratch file as *evidence*, but a compiling prototype
   does not replace your re-derivation, and you must check that its final statement is the target statement and that
   it contains no `sorry`, `axiom`, `native_decide`.
4. **Check claims about the literature and about what is false** (counterexamples given in the report must be
   verified by computation).
5. **Assess the effort estimates and risks**: are they credible? What is missing?

Output: `/home/user/Semialgebraic/notes/audit/<name>.md` with, for each lemma, `CONFIRMED` (with your independent
proof sketch), `CONFIRMED WITH CORRECTION` (state the correction) or `REFUTED` (counterexample); a list of errors
and gaps ranked by severity; and an overall verdict on the route: `SOUND`, `SOUND AFTER CORRECTIONS` (list them) or
`UNSOUND`. Do not edit the report or any other file. Your final message: the verdict and the ranked list of
errors/corrections in at most 30 lines.
