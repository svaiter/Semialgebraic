# Phase 3a research: common brief (finiteness theorem, assumption A2)

No Lean code is written in this phase. You produce one markdown report.

## Target statement (must be proved exactly in this form in the end)

```lean
theorem Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}
```

(the finiteness theorem: a closed semialgebraic subset of `ℝ^ι` is a finite union of basic closed sets; paper
Prop 2.4, Bochnak–Coste–Roy Thm 2.7.2, Schweighofer's lecture notes §6.3). The topology on `ι → ℝ` is the product
topology (sup metric in Mathlib).

## Context to read

* `/home/user/Semialgebraic/PLAN.md` (whole file; §4.2 lists lemmas G1–G4 that are being formalized now and may be
  assumed available; §4.4 is a *candidate* route written by the orchestrator, unverified).
* `/home/user/HardnessBilevelProgramming/blueprint.md` §4.B.4 (lines ~766–790) and §4.G.4 (lines ~1451–1560): how
  A2 is consumed, and the remark on the weaker statement FT′.
* TauCeti sources at `/home/user/Semialgebraic/.lake/packages/TauCeti/TauCeti/Geometry/RealAlgebraic/` (pinned commit
  `2c9b12be`) and Mathlib at `/home/user/Semialgebraic/.lake/packages/mathlib` (pinned `1b1ccf4b`). Signature
  summaries: `/home/user/Semialgebraic/notes/api/`; `python3 /home/user/Semialgebraic/scripts/api_summary.py FILE...`
  prints the signatures of any Lean file. Do not edit anything under `.lake/`.
* Literature: M. Schweighofer, *Real Algebraic Geometry, Positivity and Convexity* (lecture notes; try arXiv
  2205.04211) §6.2–6.3; Bochnak–Coste–Roy, *Real Algebraic Geometry*, §2.5–2.7, §7; Basu–Pollack–Roy, *Algorithms in
  Real Algebraic Geometry*. Network access goes through a proxy; `curl -sSL` works for arxiv.org. If a source cannot
  be fetched, reconstruct the argument yourself and say so; never cite a statement you did not check or re-derive.

## Requirements on the report

1. Every mathematical claim is proved in the report in enough detail to be formalized (no "it is well known", no
   "similarly"); every claim taken from a source is re-derived or its proof is reproduced and checked.
2. Every Lean dependency is cited with its file path and exact name, **verified by grep at the pinned commits**
   (quote the signature). State clearly what is missing and must be written.
3. A decomposition into lemmas with Lean-style statements (binders, types, index types), a dependency order, and an
   effort estimate per lemma (lines of Lean, S/M/L/XL), plus the main formalization risks.
4. Mark explicitly anything you could not establish, and anything that is false as commonly stated (with a
   counterexample).
5. Do not write to any file other than your report. Do not run `lake build` (other agents are building); reading
   sources with grep is enough. `lake env lean` on a scratch file under `/tmp` is allowed for checking that a name or
   signature exists (first `cd /home/user/Semialgebraic && . scripts/env.sh`).

Your final message: a summary of at most 30 lines (verdict on the route, lemma list, total effort, top risks).
