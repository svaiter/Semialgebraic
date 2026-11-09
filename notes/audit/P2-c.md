# Audit P2-c (G4, §4.3, interface theorem A3) — verdict: ACCEPT

1. Build: `lake build Semialgebraic.Growth.Main Semialgebraic.Interface.Growth SemialgebraicCheck.A3` succeeds, no errors.
   Only the expected "module system" import warnings (from OneVar and Shape, not from the unit's own files).
2. Forbidden tokens: grep over the three files finds none (`sSup` appears once, in the header comment saying it is not used).
   No `instance`, no `set_option`, no `opaque/extern/implemented_by`. `Shape.lean` unmodified (`git diff --stat` empty).
3. Axioms (scratch /tmp/audit-p2c/T.lean), all `[propext, Classical.choice, Quot.sound]`:
   exists_growth_isLUB, isSemialgebraic_setOf_exists_sq_sum_le_abs_eq, exists_polynomial_growth, Interface.growth,
   BilevelShape.hasGrowthBound.
4. Faithfulness: `example : <brief statement verbatim> := <theorem>` elaborates and is closed for `exists_growth_isLUB`,
   `exists_polynomial_growth` (ι : Type) and `Interface.growth`. Statements match the brief symbol by symbol.
5. No new defs/classes. Sanity instance: f x = x 0 ^ 2 on Fin 1 (graph is the zero set of a polynomial, locally bounded);
   the theorem gives |x²| ≤ B + (1+x²)^M with M = 1. Not vacuous: hypotheses are satisfiable, ι may be empty
   (then f is constant, still fine), and the proof of the main theorem uses the genuine LUB of the fibre over ρ ≥ 0
   (nonempty via x = 0, bounded via hb ρ); no sSup, so no junk values. The helper set E has the right fibres
   (u = |f x| for some x with Σx² ≤ ρ); proof checked by reading and by the build.
6. Interface: the field `growth` of `Bilevel.HasGrowthBound` in HardnessBilevel/Assumptions/Classes.lean, the copy in
   `SemialgebraicCheck/Shape.lean`, and `Interface.growth` agree symbol by symbol (binders `{n : ℕ} {f : (Fin n → ℝ) → ℝ}`,
   graph set `{z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())}`, local-boundedness hypothesis, conclusion
   `∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M`); only the predicate differs (TauCeti vs the
   `generateSetAlgebra` definition), and the check `⟨Semialgebraic.Interface.growth⟩` compiles with no glue.
   Shape's `IsSemialgebraic` was compared with `Bilevel.IsSemialgebraic` in Basic.lean: identical body.
7. Hygiene: proofs commented and short; no issues. Helper theorem is public (declared in header and report).

Required fixes: none.
