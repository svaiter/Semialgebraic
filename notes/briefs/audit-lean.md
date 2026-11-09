# Brief for Lean auditors (Sonnet)

Read `notes/briefs/standing.md` (environment and rules) and `PLAN.md`. You audit one unit: its brief
(`notes/briefs/<unit>-*.md`), its Lean files, and the writer's report (`notes/lean-reports/<unit>.md`).
You do not edit any file of the library; scratch files go under `/tmp`. Your output is `notes/audit/<unit>.md`.

Checks, all mandatory:

1. **Build.** `cd /home/user/Semialgebraic && . scripts/env.sh && lake build <the unit's modules>` succeeds with no
   error. Report warnings (deprecations must be fixed; the "designed for use with the module system" import warning
   is expected and can be ignored).
2. **Forbidden tokens.** No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `extern`,
   `opaque` in the unit's files (grep; mentions inside comments are fine but report them). No `instance` of a class
   named `HasSemialgebraicProjections`, `HasFinitenessTheorem`, `HasGrowthBound`. No `set_option` that disables
   checking (`debug.skipKernelTC`, …); list every `set_option` used.
3. **Axioms.** Write a scratch file that imports the unit's modules and runs `#print axioms` on every public
   (non-`private`) theorem and definition of the unit; each must depend only on a subset of
   `[propext, Classical.choice, Quot.sound]`. Paste the output.
4. **Faithfulness.** For each statement required by the unit's brief: copy the required statement from the brief and
   the actual statement from the file, compare them symbol by symbol (binders, implicit/explicit, types, universe
   levels, hypotheses, conclusion). Any difference must be a declared strengthening; an added hypothesis, a weakened
   conclusion or a changed definition is a REJECT. Check with `#check` in the scratch file that each required
   statement elaborates when stated verbatim and is closed by `exact <the theorem>` (write `example : <required
   statement> := <theorem>` for each one; this is the decisive test).
5. **No definitional cheating.** Any new `def`/`abbrev`/`structure`/`class`/notation in the unit: does it change the
   meaning of a required statement? Are statements vacuous (contradictory hypotheses, empty index types,
   `False`-implies)? Give one sanity instance per main theorem (for instance a concrete set or function to which it
   applies non-vacuously) — argue informally, no need to formalize.
6. **Interface theorems** (if the unit has one): the `SemialgebraicCheck/A*.lean` file must inhabit the copied class
   with `⟨Semialgebraic.Interface.<name>⟩` and no glue, and `SemialgebraicCheck/Shape.lean` must be unmodified
   (`git diff --stat SemialgebraicCheck/Shape.lean`). Compare the class field in
   `/home/user/HardnessBilevelProgramming/HardnessBilevel/Assumptions/Classes.lean` with the copy in `Shape.lean`
   and with the interface theorem, symbol by symbol.
7. **Proof hygiene** (non-blocking, report only): very long tactic blocks without comments, `simp` without `only` at
   non-terminal positions, unused hypotheses, `Classical` opened globally, slow declarations (>20 s).

Verdict: `ACCEPT` only if 1–6 pass. Otherwise `REJECT` with a numbered list of required fixes, each precise enough
for the writer to act on. Your final message: the verdict and the list of required fixes (or "none").
