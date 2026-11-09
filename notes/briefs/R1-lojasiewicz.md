# Research agent R1: the route through the Łojasiewicz inequality

Read `/home/user/Semialgebraic/notes/briefs/R-common.md` first. Write your report to
`/home/user/Semialgebraic/notes/research/route1-lojasiewicz.md`.

## Task

1. **Textbook chain.** Reconstruct, with complete proofs, the textbook route to the finiteness theorem: one-variable
   growth of semialgebraic functions; the Łojasiewicz inequality on compact sets; the weighted Łojasiewicz
   inequality on closed (unbounded) semialgebraic sets; the finiteness theorem for open sets, then for closed sets.
   Follow Schweighofer §6.2–6.3 and Bochnak–Coste–Roy §2.6–2.7; say precisely where the two differ and where the
   uniformity in parameters enters (it is the usual dominant cost).
2. **Candidate shortcut.** `PLAN.md` §4.4 claims that the weighted closed inequality needed for the finiteness
   theorem follows in one step from one-variable growth of a fibrewise supremum (G4), through the one-parameter
   family `K_t = {x ∈ T | ‖x‖² ≤ t ∧ 1 ≤ t |g x|}`, with no uniformity-in-parameters argument. This is an unverified
   claim by the orchestrator. Try to break it: look for gaps (emptiness of `K_t`, compactness, attainment, the range
   `1 ≤ t ≤ t₀`, the passage from `t` to `(x, g x)`, the choice of exponents, the case `f = 0`, the case of an empty
   set of strict inequalities, `ι` empty), and for errors in L2 (is `B ⊆ B' ⊆ U` really proved? is `B'` open and
   basic? is every point of `U` in some cell `B ⊆ U`?) and L3. Either give a counterexample or a complete rigorous
   proof with all constants explicit. If it is correct, say whether a simpler or more robust variant exists.
3. **Cheapest correct variant for Lean.** Choose the variant of route 1 that is cheapest to formalize on top of
   TauCeti + Mathlib + G1–G4, and decompose it as required by the common brief. For each lemma give the exact Lean
   statement you recommend (index types `ι` with `[Fintype ι]`, polynomials as `MvPolynomial ι ℝ`, the sign normal
   form available as `TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`), and the Mathlib/TauCeti lemmas for:
   compactness of closed bounded subsets of `ι → ℝ`, continuity of `MvPolynomial.eval`, extreme values on compact
   sets, existence of least upper bounds in `ℝ`, the projection/quantifier lemmas of TauCeti, reindexing of finite
   index types to `Fin`.
4. **FT′.** Record precisely the weaker statement FT′ ("every closed semialgebraic `K` is
   `{x | ∃ z ∈ [0,1/2]^k, R(x,z) = 0}` for a polynomial `R`"), why it suffices for Theorem 2.15 and not for
   Theorem 2.20 of the paper (HardnessBilevel `blueprint.md` §4.B.4, §4.G.4), and whether FT′ would be materially
   cheaper to prove than the full theorem on this route.
