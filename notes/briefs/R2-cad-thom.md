# Research agent R2: the route through cylindrical decomposition and Thom encodings, and other routes

Read `/home/user/Semialgebraic/notes/briefs/R-common.md` first. Write your report to
`/home/user/Semialgebraic/notes/research/route2-cad-thom.md`.

## Task

The hypothesis to examine: *the finiteness theorem can be proved from TauCeti's cylindrical algebraic decomposition
and Thom-encoding machinery, e.g. through decompositions adapted to derivative-closed families of polynomials, where
the closure of a cell is obtained by relaxing its strict sign conditions.* This is a hypothesis, not a known fact.
Establish whether it is correct and complete, and what it would cost.

1. **Mathematics.** State precisely what is true:
   * Thom's lemma in one variable (a family closed under derivation: sign conditions define points/intervals and
     closures are obtained by relaxing strict inequalities) — proof.
   * What fails in several variables: give explicit counterexamples to "the closure of a sign-condition cell is the
     relaxed sign condition" and to "the closure of a CAD cell is a union of cells / is given by relaxed conditions"
     (for instance the cell decompositions around `x t = 0`, Whitney-umbrella-like examples, bad cylindrical cells
     whose closure is not a union of cells).
   * What repairs it: the generalized Thom lemma / stratifying families (Bochnak–Coste–Roy §2.5, §9.1; Coste's
     lecture notes on semialgebraic geometry; Basu–Pollack–Roy ch. 5): exact hypotheses (closed under derivation in
     the last variable, *and* the lower-dimensional family stratifying, quasi-monic after a linear change of
     coordinates, …), exact conclusion, and a complete proof that the finiteness theorem follows. Determine whether
     a change of coordinates is unavoidable and what it costs.
   * Any other route you know (real spectrum and constructible topology — BCR ch. 7; induction on dimension using
     `dim (closure S \ S) < dim S`; separation of closed semialgebraic sets; …): for each, the statement chain and
     what infrastructure it needs.
2. **TauCeti inventory.** Read the actual statements TauCeti provides (do not trust file names): `CAD/Basic.lean`,
   `CAD/Existence.lean`, `CAD/Partition.lean`, `Semialgebraic/Thom.lean`, `SignDetermination/Thom.lean`, `Stack/*`,
   `Projection/*`, `Semialgebraic/Dimension/*` (`Closure.lean`, `Strata.lean`, …), `Semialgebraic/Topology.lean`,
   `Semialgebraic/Components.lean`, `Nash/*`. For each ingredient of each viable route say whether TauCeti has it
   (file, name, quoted signature) or what is missing. In particular: does TauCeti's CAD expose cells with explicit
   sign-condition descriptions? adapted to a given finite family? with any control of closures or of the frontier
   condition? Is there a multivariate Thom lemma? a dimension theory with `dim (frontier S) < dim S`?
3. **Verdict.** For each route: correct and complete (yes/no/unknown), list of lemmas to write with Lean-style
   statements, effort estimate, risks. Compare with the route through the Łojasiewicz inequality as sketched in
   `PLAN.md` §4.4 (another agent studies that route in depth; you only need its outline for the comparison).
