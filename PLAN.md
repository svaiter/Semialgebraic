# Plan: discharging A1, A2, A3 of HardnessBilevel on top of TauCeti

This is the execution plan of the library `Semialgebraic` (repository `svaiter/Semialgebraic`). It is kept up to
date: the status table in §8 is edited after every audited unit.

## 1. Goal

`svaiter/HardnessBilevelProgramming` formalizes arXiv:2407.12372 with three real-algebraic-geometry facts taken as
hypotheses through `Prop`-classes that have no instance:

| id | class (namespace `Bilevel`) | content |
|---|---|---|
| A1 | `HasSemialgebraicProjections` | Tarski–Seidenberg, projection form |
| A2 | `HasFinitenessTheorem` | a closed semialgebraic set is a finite union of finite intersections of `{p ≥ 0}` |
| A3 | `HasGrowthBound` | a semialgebraic function bounded on bounded sets is polynomially bounded |

This library proves the three statements over `ℝ`, in TauCeti's vocabulary, so that HardnessBilevel can declare
proved instances in a separate target. It does not depend on HardnessBilevel.

## 2. Pins (verified 2026-11-09 by building)

| item | value |
|---|---|
| Lean | `leanprover/lean4:v4.36.0-rc2` |
| TauCeti | `2c9b12be26ca8efd0c54851aead7b7a6553f7f5c` (HEAD of `main` on 2026-11-09) |
| Mathlib | `1b1ccf4b088b32fa3f23f2de1127433254a81e1e` (the commit in TauCeti's manifest at that TauCeti commit) |

Facts checked at these pins:

* `TauCeti.IsSemialgebraic` has the same body as `Bilevel.IsSemialgebraic` at `R := ℝ`; the bridge is `Iff.rfl`
  (compiled: `SemialgebraicCheck/A1.lean`).
* `TauCeti.IsSemialgebraic.image_comp_inl` needs only `[Finite τ]` and `[TauCeti.HasSemialgebraicProjections R]`;
  the instance over `ℝ` is `TauCeti.instHasSemialgebraicProjectionsReal`.
* **Olean cache for a downstream project.** TauCeti publishes a Lake artifact cache. A downstream project fetches
  the input-to-output mappings of the TauCeti package once
  (`lake cache get --package=TauCeti --service tauceti-public --repo TauCetiProject/TauCeti --mappings-only`, with
  `LAKE_CONFIG=scripts/lake-cache.toml`) and then builds with `LAKE_ARTIFACT_CACHE=true`; Lake downloads the
  artifacts of exactly the imported TauCeti modules instead of compiling them. `scripts/setup.sh` does the one-time
  part, `scripts/env.sh` sets the environment. Without the environment TauCeti modules compile from source (correct
  but slow).
* TauCeti has `IsSemialgebraic.exists_ne_zero_polynomial_of_interior_eq_empty` (`Semialgebraic/AlgebraicDependence.lean`):
  a semialgebraic set with empty interior lies in the zero set of a nonzero polynomial. This replaces the blueprint's
  `sa.thin_set`.

## 3. Architecture

* Lake package `Semialgebraic`, library `Semialgebraic` (default target), requiring TauCeti and Mathlib at the pins
  above. A second library `SemialgebraicCheck` holds compile-time shape checks and is not imported by anything.
* Namespace `Semialgebraic` for every declaration of this library (no declaration is added to the `TauCeti`
  namespace, so a later TauCeti bump cannot clash). Statements use `TauCeti.IsSemialgebraic` and TauCeti's function
  vocabulary; general statements are over `ℝ` and arbitrary finite index types where the proof allows.
* **Interface theorems** (`Semialgebraic/Interface/*.lean`, namespace `Semialgebraic.Interface`): one per assumption,
  with the statement of the class field in which `Bilevel.IsSemialgebraic` is replaced by `TauCeti.IsSemialgebraic`
  — same binders, same universe `Type`, same conclusion.

  ```lean
  theorem Interface.image_comp_inl {α β : Type} [Fintype α] [Finite β] {S : Set (α ⊕ β → ℝ)} :
      TauCeti.IsSemialgebraic S → TauCeti.IsSemialgebraic ((fun z : α ⊕ β → ℝ => z ∘ Sum.inl) '' S)

  theorem Interface.exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
      TauCeti.IsSemialgebraic s → IsClosed s →
      ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
        s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}

  theorem Interface.growth {n : ℕ} {f : (Fin n → ℝ) → ℝ} :
      TauCeti.IsSemialgebraic {z : Fin n ⊕ Unit → ℝ | f (z ∘ Sum.inl) = z (Sum.inr ())} →
      (∀ r : ℝ, ∃ B : ℝ, ∀ x, ∑ i, x i ^ 2 ≤ r → |f x| ≤ B) →
      ∃ (B : ℝ) (M : ℕ), ∀ x, |f x| ≤ B + (1 + ∑ i, x i ^ 2) ^ M
  ```
* **Shape checks** (`SemialgebraicCheck/A{1,2,3}.lean`): a verbatim copy of `Bilevel.IsSemialgebraic` and of the
  class, in namespace `BilevelShape`, inhabited by `⟨Semialgebraic.Interface.…⟩` with no glue (a `theorem`, never an
  `instance`). If the interface theorem drifted from the class field, the file would not compile.
* **Integration** happens last, in HardnessBilevel (Phase 4): the companion becomes a dependency, HardnessBilevel's
  Mathlib pin moves to the companion's, and a separate `lean_lib` `HardnessBilevelUnconditional` declares the three
  proved instances and the assumption-free corollaries. The core library keeps its binder-form statements.

## 4. Mathematics

Notation: `‖x‖² = ∑ i, x i ^ 2`; "sa" = semialgebraic.

### 4.1 A1 (Phase 1) — done by TauCeti

`Interface.image_comp_inl := TauCeti.IsSemialgebraic.image_comp_inl`.

### 4.2 Shared core: fibrewise suprema grow polynomially (Phase 2, used by A3 and A2)

* **G1 `exists_growth_of_interior_eq_empty`.** `G ⊆ (Fin 2 → ℝ)` sa with `interior G = ∅`. Then
  `∃ c M t₀, 0 ≤ c ∧ 0 ≤ t₀ ∧ ∀ s t, t₀ ≤ t → ![s, t] ∈ G → |s| ≤ c * (1 + t) ^ M`.
  *Proof.* TauCeti gives `P ≠ 0` in `MvPolynomial (Fin 2) ℝ` vanishing on `G`. Write `P = ∑_{i ≤ d} qᵢ(t) sⁱ` with
  `q_d ≠ 0` (`MvPolynomial.finSuccEquiv`, variable `0` is the polynomial variable; then `MvPolynomial (Fin 1) ℝ ≃ ℝ[X]`).
  A nonzero univariate polynomial is bounded away from `0` near `+∞` (constant, or `Polynomial.abs_tendsto_atTop`),
  so `|q_d(t)| ≥ δ > 0` for `t ≥ t₀`. A root `s` of a polynomial with leading coefficient `a_d ≠ 0` satisfies
  `|s| ≤ 1 + ∑_{i<d} |aᵢ| / |a_d|` (elementary, or `Polynomial.IsRoot.norm_lt_cauchyBound`). Each `|qᵢ(t)|` is at
  most `Cᵢ (1 + t)^{deg qᵢ}` for `t ≥ 0`. If `d = 0` the fibre of `G` over `t ≥ t₀` is empty.
* **G2 `exists_growth_of_subsingleton_fibres`.** Same conclusion when every fibre `{s | ![s, t] ∈ G}` is a
  subsingleton (an open set of `ℝ²` contains two points with the same `t`).
* **G3 `isSemialgebraic_setOf_isLUB`.** For `E ⊆ (σ ⊕ Unit → ℝ)` sa, the set
  `{z | IsLUB {u | Sum.elim (z ∘ Sum.inl) (fun _ => u) ∈ E} (z (Sum.inr ()))}` is sa (`σ` arbitrary).
  *Proof.* `IsLUB A s ↔ (∀ u ∈ A, u ≤ s) ∧ ∀ s' < s, ∃ u ∈ A, s' < u`; two applications of TauCeti's
  `setOf_forall_sumElim` / `setOf_exists_sumElim` after pulling `E` back along coordinate maps.
* **G4 `exists_growth_isLUB`.** For `E ⊆ (Fin 2 → ℝ)` sa (coordinate `0` = value, `1` = parameter):
  `∃ c M t₀, 0 ≤ c ∧ 0 ≤ t₀ ∧ ∀ s t, t₀ ≤ t → IsLUB {u | ![u, t] ∈ E} s → |s| ≤ c * (1 + t) ^ M`.
  (G3 + G2: least upper bounds are unique.)

### 4.3 A3 (Phase 2)

`f : (Fin n → ℝ) → ℝ` with sa graph, bounded on every `{‖x‖² ≤ r}`.
`E := {(u, ρ) | ∃ x, ‖x‖² ≤ ρ ∧ |f x| = u}` is sa (projection of a set built from the graph of `f`).
For `ρ ≥ 0` the fibre `E_ρ` is nonempty (`x = 0`) and bounded above (hypothesis), so it has a least upper bound
`g ρ` (`Real.exists_isLUB`), and `|f x| ≤ g ‖x‖²`. By G4, `g ρ ≤ c (1 + ρ)^M` for `ρ ≥ t₀`. Put
`ρ₁ := max t₀ c`: for `ρ ≥ ρ₁`, `c (1 + ρ)^M ≤ (1 + ρ)^{M+1}`; for `‖x‖² ≤ ρ₁`, `|f x| ≤ B(ρ₁)`. Hence
`|f x| ≤ max 0 B(ρ₁) + (1 + ‖x‖²)^{M+1}`. No `Real.sSup` is used, so no junk values.

### 4.4 A2 (Phases 3a, 3b) — original candidate route (superseded: the audited route, with four corrections to this sketch, is `notes/finiteness-report.md` §3)

Hörmander-style reduction of the weighted closed Łojasiewicz inequality to one-variable growth:

* **L1 (weighted Łojasiewicz for polynomials on a closed sa set).** `T ⊆ (ι → ℝ)` closed sa, `f g` polynomials,
  `∀ x ∈ T, f x = 0 → g x = 0`. Then `∃ c > 0, ∃ M, ∀ x ∈ T, c |g x|^M ≤ |f x| ((1 + ‖x‖²)(1 + |g x|))^M`.
  *Proof idea.* `K_t := {x ∈ T | ‖x‖² ≤ t ∧ 1 ≤ t |g x|}` is compact and `f ≠ 0` on it, so
  `E := {(u, t) | 1 ≤ t ∧ ∃ x ∈ K_t, u |f x| = 1}` has bounded fibres; G4 bounds `sup E_t = max_{K_t} 1/|f|` by
  `c (1 + t)^M` for `t ≥ t₀`, and `K_t` is increasing in `t`, so the bound extends to `t ≥ 1` after enlarging `c`.
  For `x ∈ T` with `g x ≠ 0` take `t := max 1 (max ‖x‖² (1/|g x|))`.
* **L2 (open sets).** `U` open sa. For every sign cell `B = {f = 0, g₁ > 0, …, g_k > 0} ⊆ U` of a sign normal form
  of `U` there is a basic open `B' = {g_j > 0 ∀ j, c² g^{2M} > f² (…)^{2M}}` with `B ⊆ B' ⊆ U` (L1 on
  `T := Uᶜ ∩ {g_j ≥ 0 ∀ j}` with `g := ∏ g_j`). So `U` is a finite union of finite intersections of `{q > 0}`.
* **L3 (closed sets, the interface form).** Complement of L2 and distributivity:
  `(⋃ i, ⋂ j, {q i j > 0})ᶜ = ⋃ φ : Fin I → Fin J, ⋂ i, {0 ≤ -q i (φ i)}`, reindexed to `Fin`.

The alternative route through cylindrical decomposition and Thom encodings is examined in Phase 3a.

## 5. Phases, units, gates

| phase | unit | files | writer | gate |
|---|---|---|---|---|
| 0 | setup | `lakefile.toml`, `lean-toolchain`, `scripts/*`, `PLAN.md` | orchestrator | a file importing `TauCeti.Geometry.RealAlgebraic.CAD.Existence` builds from caches |
| 1 | P1 | `Interface/Projection.lean`, `SemialgebraicCheck/A1.lean` | orchestrator | axioms of `Interface.image_comp_inl` exactly `[propext, Classical.choice, Quot.sound]` |
| 2 | P2-a | `Growth/OneVar.lean` (G1, G2) | Opus | build, audit ACCEPT |
| 2 | P2-b | `Growth/IsLUB.lean` (G3) | Opus | build, audit ACCEPT |
| 2 | P2-c (after a, b) | `Growth/Main.lean` (G4, §4.3), `Interface/Growth.lean`, `SemialgebraicCheck/A3.lean` | Opus | axioms of `Interface.growth` clean |
| 3a | research | `notes/research/*.md`, `notes/audit/*.md`, `notes/finiteness-report.md` | Fable (high) research, Opus (high) audit | audited report with recommendation and risks |
| 3b | P3-a, P3-b, P3-c | `Finiteness/Lojasiewicz.lean`, `Finiteness/Cells.lean`, `Finiteness/Main.lean`, `Interface/Finiteness.lean`, `SemialgebraicCheck/A2.lean` | Opus | axioms of `Interface.exists_eq_iUnion_iInter_nonneg` clean |
| 4 | integration | in HardnessBilevel: `lakefile.toml`, `HardnessBilevelUnconditional/*`, `scripts/*`, `README.md`, `PLAN.md` | orchestrator + Opus | `scripts/check.sh` passes; unconditional corollaries have clean axioms |

Each Lean unit is audited by a Sonnet auditor; fixes go back to the writer until the verdict is ACCEPT. The
orchestrator runs the full build and `scripts/check.sh` between waves, then commits and pushes.

## 6. Roles and process

* Research agents: Fable, high effort. Research audits: Opus, high effort, adversarial, re-deriving every lemma.
* Lean writers: Opus. Lean auditors: Sonnet. One writer per unit, then one auditor per unit.
* Auditors check: the unit's modules build; no forbidden token; `#print axioms` of every public declaration;
  statement-by-statement faithfulness against this plan (no added hypothesis, no weakened conclusion, no changed
  definition); interface theorems equal the class fields after unfolding (shape-check file compiles with no glue).
* Reports go to `notes/lean-reports/` (writers), `notes/audit/` (auditors), `notes/research/` (research).
* The standing brief for all agents is `notes/briefs/standing.md`; API summaries are in `notes/api/`.

## 7. Rules

1. No `sorry`, `admit`, `axiom`, `native_decide`, `unsafe`.
2. Never weaken a statement to make it provable. Strengthening is allowed and declared in the file header.
3. An agent builds only its own modules (`lake build Semialgebraic.<Module>`), never a bare `lake build`; it never
   edits a file outside its assignment, nor `lakefile.toml`, `lean-toolchain`, the root module, `scripts/`.
4. Every `lake` command is run after `. scripts/env.sh`.
5. Known traps at these pins: `push_neg` is deprecated (use `push Not`); `if_pos`/`if_neg`/`if_true` and
   `Set.mem_setOf_eq` are deprecated; `stdSimplex` and its lemmas are deprecated; `ContDiff ℝ ⊤` means analytic;
   `continuous_finset_sum` is now `continuous_finsetSum`; a parameter-free `Prop`-class used as a binder triggers
   `linter.concreteInstances`. In a root module, `import` lines precede the docstring. TauCeti files use the module
   system; files of this library are ordinary (non-`module`) files that `import` them.
6. No pull request or issue on TauCeti; upstreaming proposals are written to `notes/` for the user.

## 8. Status

| phase | status | notes |
|---|---|---|
| 0 setup | done | caches hit; smoke test built |
| 1 A1 | done | `Semialgebraic.Interface.image_comp_inl`, axioms clean |
| 2 A3 | done | `Semialgebraic.Interface.growth` (`Interface/Growth.lean`), from `exists_polynomial_growth` (`Growth/Main.lean`); units P2-a, P2-b, P2-c audited ACCEPT; axioms clean |
| 3a A2 research | done | `notes/finiteness-report.md`; research R1, R2 with Opus audits (SOUND; SOUND AFTER CORRECTIONS); route 1 (Łojasiewicz, streamlined) chosen, route 2 (Thom lemma) documented as fallback |
| 3b A2 implementation | done | `Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg` (`Interface/Finiteness.lean`), from `exists_lojasiewicz`, `exists_eq_iUnion_iInter_pos` (`Finiteness/*.lean`); units P3-a, P3-b, P3-c audited ACCEPT; axioms clean |
| 4 integration | in progress | in HardnessBilevel: library `HardnessBilevelUnconditional` |
