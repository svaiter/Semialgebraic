# Standing brief for every agent working in this repository

Repository: `/home/user/Semialgebraic` (Lake package `Semialgebraic`). Read `PLAN.md` first.

## Environment

* Before any `lake` or `lean` command: `cd /home/user/Semialgebraic && . scripts/env.sh`
  (puts elan on `PATH` and makes Lake fetch TauCeti modules from TauCeti's olean cache).
* Build only your own modules: `lake build Semialgebraic.<Module>` (several modules may be listed).
  Never run a bare `lake build`, `lake update`, `lake clean` or `lake exe cache get`: other agents build at the
  same time. Quick iteration on one file: `lake env lean Semialgebraic/Path/File.lean` (its imports must already be
  built with `lake build`).
* Filter build output, it is long: `lake build Semialgebraic.X 2>&1 | grep -v '^trace\|Fetched\|✔' | tail -40`.
* Sources to read (do not edit): Mathlib at `.lake/packages/mathlib`, TauCeti at `.lake/packages/TauCeti`
  (real algebraic geometry under `TauCeti/Geometry/RealAlgebraic/`). Signature summaries of TauCeti's semialgebraic
  modules: `notes/api/`. `python3 scripts/api_summary.py FILE...` prints the signatures of any Lean file.
* Pins: Lean `v4.36.0-rc2`, Mathlib `1b1ccf4b`, TauCeti `2c9b12be`. Search for names with grep in the checkouts;
  do not trust memory of Mathlib names.

## Rules

1. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`. Do not leave a file that does not compile.
2. Never weaken a statement to make it provable (no added hypothesis, no weakened conclusion, no changed
   definition). Strengthening is allowed and must be declared in the file header. If a statement of your brief is
   false or unprovable as written, stop and report it with a counterexample or the precise obstruction.
3. Edit only the files of your assignment. Never edit `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`,
   `Semialgebraic.lean`, `scripts/`, `PLAN.md`, or another unit's files. Do not commit or push; the orchestrator does.
4. Files of this library are ordinary Lean files (no `module` keyword); `import` lines come first, then a `/-! … -/`
   header that states what the file provides, the plan ids (G1, …) it implements, and every deviation or
   strengthening. All declarations live in `namespace Semialgebraic`. `autoImplicit` is off.
5. Import the specific Mathlib and TauCeti modules you need, not `Mathlib` as a whole.
6. Every public theorem must satisfy `#print axioms … = [propext, Classical.choice, Quot.sound]` (or a subset).
7. Traps at these pins: `push_neg` is deprecated (use `push Not`); `if_pos`/`if_neg`/`if_true` and
   `Set.mem_setOf_eq` are deprecated; `continuous_finset_sum` is now `continuous_finsetSum`; a parameter-free
   `Prop`-class used as a binder triggers `linter.concreteInstances`. The build must have no errors; avoid
   warnings where reasonable (deprecations must be fixed).
8. Keep proofs readable: name intermediate facts, add a one-line comment per proof step of a long proof.

## Reports

Writers: when done, write `notes/lean-reports/<unit>.md` with: the final statements (copied from the file), every
deviation from the brief, helper lemmas that others may reuse, Mathlib/TauCeti names that were not as expected, and
the output of `#print axioms` for each public theorem. Your final message is a short summary of that report.

Auditors: write `notes/audit/<unit>.md` with a verdict `ACCEPT` or `REJECT`, and for each public declaration:
builds (yes/no), axioms, faithfulness to the plan (statement compared symbol by symbol), and a list of required
fixes. Auditors do not edit Lean files of the library; they may create scratch files under `/tmp` or the scratchpad.
