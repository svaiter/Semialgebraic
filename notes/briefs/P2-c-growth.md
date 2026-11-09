# Unit P2-c (writer): A3 assembly — plan ids G4, §4.3, interface theorem A3

Read `notes/briefs/standing.md` and `PLAN.md` §4.2–4.3 first, then the two files your unit imports and their
reports: `Semialgebraic/Growth/OneVar.lean` (`notes/lean-reports/P2-a.md`) and `Semialgebraic/Growth/IsLUB.lean`
(`notes/lean-reports/P2-b.md`). Do not edit those two files.

You write exactly three Lean files and one report:

* `Semialgebraic/Growth/Main.lean`
* `Semialgebraic/Interface/Growth.lean`
* `SemialgebraicCheck/A3.lean`
* `notes/lean-reports/P2-c.md`

## `Semialgebraic/Growth/Main.lean` (namespace `Semialgebraic`) — required public statements

```lean
/-- G4. The fibrewise least upper bound of a semialgebraic subset of the plane grows polynomially near `+∞`.
Coordinate `0` is the value, coordinate `1` is the parameter. -/
theorem exists_growth_isLUB {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → IsLUB {u : ℝ | ![u, t] ∈ E} s → |s| ≤ c * (1 + t) ^ M

/-- Polynomial growth of a real function with semialgebraic graph that is bounded on bounded sets. -/
theorem exists_polynomial_growth {ι : Type*} [Fintype ι] {f : (ι → ℝ) → ℝ}
    (hf : TauCeti.IsSemialgebraic {z : ι ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())})
    (hb : ∀ r : ℝ, ∃ B : ℝ, ∀ x : ι → ℝ, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) :
    ∃ (B : ℝ) (M : ℕ), ∀ x : ι → ℝ, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
```

Proof route.

* G4: `G := {z : Fin 2 → ℝ | IsLUB {u | ![u, z 1] ∈ E} (z 0)}` is semialgebraic
  (`isSemialgebraic_setOf_isLUB_fin_two`), its fibres are subsingletons (`IsLUB.unique`), so
  `exists_growth_of_subsingleton_fibres` applies; `![s, t] ∈ G` unfolds to `IsLUB {u | ![u, t] ∈ E} s` by `simp`.
* `exists_polynomial_growth`:
  1. `E := {w : Fin 2 → ℝ | ∃ x : ι → ℝ, ∑ i, x i ^ 2 ≤ w 1 ∧ |f x| = w 0}` is semialgebraic: it is
     `{w | ∃ x, Sum.elim w x ∈ S}` for `S ⊆ (Fin 2 ⊕ ι → ℝ)` defined by a polynomial inequality
     (`TauCeti.isSemialgebraic_eval_le` with `∑ i, X (inr i) ^ 2` and `X (inl 1)`; `MvPolynomial.eval` of a sum of
     squares by `simp`) and by `|f x| = u ↔ 0 ≤ u ∧ (f x = u ∨ f x = -u)`, where `{v | f (v ∘ inr) = v (inl 0)}` is
     the pullback of `hf` along a coordinate map (`TauCeti.IsSemialgebraic.preimage_comp`) and
     `{v | f (v ∘ inr) = -v (inl 0)}` is the pullback of `hf` along a polynomial map
     (`TauCeti.IsSemialgebraic.preimage_eval`). Then `TauCeti.IsSemialgebraic.setOf_exists_sumElim` (`τ := ι`).
  2. For `ρ ≥ 0` the fibre `{u | ![u, ρ] ∈ E}` contains `|f 0|` and is bounded above by the `B` of `hb ρ`, so it
     has a least upper bound `g` (`Real.exists_isLUB`), and `|f x| ≤ g` whenever `∑ i, x i ^ 2 ≤ ρ`.
  3. With `c, M, t₀` from G4 put `ρ₁ := max t₀ c` and take `B₁` from `hb ρ₁`. Claim:
     `|f x| ≤ max 0 B₁ + (1 + ∑ i, x i ^ 2) ^ (M + 1)`. If `ρ := ∑ i, x i ^ 2 ≤ ρ₁`: `|f x| ≤ B₁ ≤ max 0 B₁` and the
     power is nonnegative. Otherwise `ρ > ρ₁ ≥ t₀` and `ρ ≥ c`, so `|f x| ≤ g ρ ≤ |g ρ| ≤ c (1+ρ)^M ≤ (1+ρ)(1+ρ)^M`.
  No `sSup`/`Real.sSup` anywhere (it has junk values); only `IsLUB`.

## `Semialgebraic/Interface/Growth.lean` (namespace `Semialgebraic.Interface`) — exact statement, do not alter

```lean
/-- **Interface theorem A3** (growth bound). -/
theorem growth {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
    TauCeti.IsSemialgebraic {z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())} →
    (∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) →
    ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
```

It must be `fun hf hb => exists_polynomial_growth hf hb` (or equally direct). Header in the style of
`Semialgebraic/Interface/Projection.lean`.

## `SemialgebraicCheck/A3.lean` — in the style of `SemialgebraicCheck/A1.lean`

```lean
import Semialgebraic.Interface.Growth
import SemialgebraicCheck.Shape

namespace BilevelShape
theorem hasGrowthBound : HasGrowthBound := ⟨Semialgebraic.Interface.growth⟩
end BilevelShape

#print axioms BilevelShape.hasGrowthBound
```

with a docstring header. It must compile with exactly this term (no glue lemma); if it does not, the interface
theorem's shape is wrong — fix the interface theorem, not the check. Do not edit `SemialgebraicCheck/Shape.lean`.

Build with `lake build Semialgebraic.Growth.Main Semialgebraic.Interface.Growth SemialgebraicCheck.A3`.
Acceptance: all three build; no forbidden token; axioms of `exists_growth_isLUB`, `exists_polynomial_growth`,
`Interface.growth`, `BilevelShape.hasGrowthBound` are `[propext, Classical.choice, Quot.sound]`.
