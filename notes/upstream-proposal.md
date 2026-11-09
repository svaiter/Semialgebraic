# Proposal: what could be offered to TauCeti (for the user to decide; nothing was filed)

No pull request, issue or roadmap was opened on TauCeti. This note lists what looks worth upstreaming and what it
would take.

## Candidates, in order of interest

| statement (this library) | file | why it fits TauCeti |
|---|---|---|
| `exists_eq_iUnion_iInter_nonneg`, `exists_eq_iUnion_iInter_pos` — finiteness theorem: closed (open) semialgebraic subsets of `ℝ^ι` are finite unions of basic closed (open) sets | `Finiteness/Main.lean` | TauCeti's completed real-algebraic-geometry roadmap stops at CAD and quantifier elimination; no roadmap mentions the finiteness theorem (BCR 2.7.2, BPR 2.x). |
| `exists_lojasiewicz` — Łojasiewicz inequality with polynomial weight for polynomials on a closed semialgebraic set | `Finiteness/Lojasiewicz.lean` | TauCeti has Łojasiewicz-type statements only in Morse theory and triangulation; none for semialgebraic sets. |
| `exists_growth_isLUB`, `exists_growth_of_interior_eq_empty`, `exists_polynomial_growth` — polynomial growth of one-parameter semialgebraic families and of locally bounded semialgebraic functions | `Growth/*.lean` | the standard "semialgebraic functions of one variable grow polynomially" (BCR 2.6.1), absent from TauCeti. |
| `isSemialgebraic_setOf_isLUB` — the fibrewise supremum of a semialgebraic family is semialgebraic | `Growth/IsLUB.lean` | small, general, reusable. |
| `exists_setOf_sign_eq_eq` — a sign cell is one equation and `m` strict inequalities | `Finiteness/Cells.lean` | bridges TauCeti's sign normal form with the textbook "basic set" form. |

## What upstreaming would require

* TauCeti files use the Lean module system (`module`, `public import`, `public section`); this library's files are
  ordinary files. Each file would need the module header and an explicit public/private split.
* TauCeti enforces its own style (header with copyright and authors, `warningAsError`, `mathlibStandardSet` linters,
  new files at most 1000 lines, declaration naming, documentation lint). The files here were not run through
  TauCeti's `lake lint`.
* Generality: everything here is over `ℝ`. The growth lemma uses the order topology of `ℝ` only through
  `Real.exists_isLUB`, limits of polynomials at `+∞` and TauCeti's `exists_ne_zero_polynomial_of_interior_eq_empty`
  (itself stated over `ℝ`); compactness is used in `exists_lojasiewicz`. A version over a general real closed field
  would need a different argument (transfer or a definable-compactness substitute) and is not attempted.
* Statements would move to the `TauCeti` namespace with dot-notation names (`TauCeti.IsSemialgebraic.…`).
* TauCeti's contribution process is driven by roadmaps and a worker CLI (see its `AGENTS.md`); a contribution of
  this kind normally starts with a roadmap entry. Whether to file one is the user's decision.

## Not worth upstreaming

The interface theorems (`Semialgebraic/Interface/*.lean`) and the shape checks (`SemialgebraicCheck/`) exist only
to match the classes of HardnessBilevel.
