# Route 1 — the finiteness theorem through the Łojasiewicz inequality

Research report R1 (Phase 3a). Author: research agent R1. Date: 2026-11-09.
Pins: Lean `v4.36.0-rc2`, Mathlib `1b1ccf4b088b32fa3f23f2de1127433254a81e1e`, TauCeti
`2c9b12be26ca8efd0c54851aead7b7a6553f7f5c` (both checked with `git rev-parse HEAD` in `.lake/packages/`).

## 0. Verdicts

1. **Textbook chain (Schweighofer §6.2–6.3).** Correct. Read in the source (arXiv 2205.04211v1, pp. 103–107) and
   re-derived below over `ℝ`. Over `ℝ` it needs no uniformity in several parameters; its cost in Lean is the
   calculus of continuous semialgebraic *functions* (absolute values, quotients, composition with the shrinking
   map) and the extension-by-zero argument on the sphere at infinity. Estimated 1100–1500 lines (L–XL).
2. **Candidate shortcut (`PLAN.md` §4.4).** Correct after one repair: the exponent `M` returned by G4 must be
   raised to `M + 1` (with `M = 0` the proof idea of L1 fails at points where `f = g = 0`; the *statement* of L1
   is true). No other gap was found: emptiness of `K_t`, compactness, the range `t < t₀`, `f = 0`, no strict
   inequality, `ι` empty, `U = ∅`, `U = univ` are all handled by the general argument. L2 and L3 are correct as
   stated. The shortcut is the classical Hörmander device (one real parameter exhausting the closed set by
   compact sets on which `f ≠ 0`); it is the textbook proof with its three applications of one-variable growth
   merged into one.
3. **Recommended variant.** The squared, purely polynomial form of the shortcut (§4): ten small lemmas, about
   250–350 lines of Lean on top of G4, effort S–M in total.
4. **Machine check.** Beyond checking names, I elaborated the whole chain in a scratch file outside the repository
   (`lake env lean`, no `lake build`): the target statement compiles from G4 with axioms
   `[propext, Classical.choice, Quot.sound]`. This goes further than the brief's "checking that a name or signature
   exists"; it was done to make the adversarial examination conclusive. The listing is in Appendix B. It is a
   prototype, not a deliverable: it has not been audited and does not follow the library's file conventions.
5. **FT′.** Not materially cheaper on this route: it needs the same Łojasiewicz step and the same open-set
   theorem; it only saves the 14-line distributivity lemma and costs a gadget lemma instead (§5).

## 1. Setting

`ι` is a finite type, `x ∈ ℝ^ι`, `N(x) := ∑ i, x i ^ 2`. The topology on `ι → ℝ` is the product topology.
"sa" means semialgebraic (`TauCeti.IsSemialgebraic`). For a polynomial `p : MvPolynomial ι ℝ` I write `p(x)` for
`MvPolynomial.eval x p`.

Target:

```lean
theorem Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}
```

Available and used (Phase 2, files present in the repository, audits `notes/audit/P2-{a,b,c}.md` all ACCEPT):

```lean
-- Semialgebraic/Growth/Main.lean  (G4)
theorem Semialgebraic.exists_growth_isLUB {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ s t : ℝ, t₀ ≤ t → IsLUB {u : ℝ | ![u, t] ∈ E} s → |s| ≤ c * (1 + t) ^ M
```

(signature printed by `#check` in the scratch session). G4 is the only result of Phase 2 that route 1 uses.

## 2. The textbook chain

Source actually read: M. Schweighofer, *Real Algebraic Geometry, Positivity and Convexity*, arXiv 2205.04211v1
(PDF fetched, "Version of Tuesday 10th May, 2022"), Prop. 6.2.1, Thm 6.2.2, Lemma 6.2.3, Cor. 6.2.4, Thm 6.3.3
(pp. 103–107), and Thm 6.1.18 (p. 102). Bochnak–Coste–Roy could **not** be fetched (book; Coste's lecture notes
were also unreachable through the proxy). Everything said about BCR in §2.5 is from memory and is marked as such;
no proof in this report depends on it.

Schweighofer works over a real closed field `R` with a subfield `K`; below `R = K = ℝ`.

### 2.1 One-variable growth (Schweighofer 6.2.1; BCR 2.6.1)

**T1.** Let `h : (a, ∞) → ℝ` have a sa graph. Then there are `b ≥ a` and `N ∈ ℕ` with `|h(t)| ≤ t^N` for `t > b`.

*Proof (as in the source, with the first step replaced by the TauCeti lemma).* The graph `Γ ⊆ ℝ²` has empty
interior, because a nonempty open subset of `ℝ²` contains two points with the same abscissa. A sa set with empty
interior lies in the zero set of a nonzero polynomial `P(t, s)`: write `Γ` as a finite union of nonempty sign
cells; a cell all of whose equations are the zero polynomial is defined by strict inequalities only, hence open
and nonempty, which is excluded; so each cell has an equation `p = 0` with `p ≠ 0`, and `P` is the product of
these. (This is `TauCeti.IsSemialgebraic.exists_ne_zero_polynomial_of_interior_eq_empty`.) Write
`P = ∑_{i ≤ d} q_i(t) s^i` with `q_d ≠ 0`. A nonzero univariate polynomial has finitely many roots and is either
constant or unbounded at `+∞`, so there are `δ > 0`, `t₀` with `|q_d(t)| ≥ δ` for `t ≥ t₀`. If `d = 0`, `P(t, s) =
q_0(t) ≠ 0` for `t ≥ t₀`, so `Γ` has no point above `t ≥ t₀`, contradiction with `h` being defined there; so
`d ≥ 1`. For `t ≥ t₀` the number `s = h(t)` is a root of `∑ q_i(t) s^i`, and a root of a polynomial with leading
coefficient `a_d ≠ 0` satisfies `|s| ≤ 1 + ∑_{i<d} |a_i| / |a_d|` (if `|s| > 1`: `|a_d| |s|^d ≤ ∑_{i<d} |a_i|
|s|^i ≤ (∑_{i<d} |a_i|) |s|^{d-1}`). Each `|q_i(t)| ≤ C_i (1 + t)^{deg q_i}` for `t ≥ 0`. Hence
`|h(t)| ≤ c (1 + t)^M` for `t ≥ t₀`, and `c (1 + t)^M ≤ c 2^M t^M ≤ t^{M+1}` for `t ≥ max(1, c 2^M)`. ∎

Schweighofer's own first step is: write `Γ` in the normal form 6.1.1 with nonempty pieces; every `f_i` has
positive degree in `Y` (otherwise a piece would contain a vertical segment); take `∏ f_i`. Same argument.

In this library T1 is available in the stronger "fibrewise supremum" form G4 (§1), proved from G1–G3 exactly
along these lines. G4 is the form used below, also in the re-derivation of the textbook proofs: it removes the
need to prove that an extremal-value function has a sa graph.

### 2.2 The Łojasiewicz inequality on a compact set (Schweighofer 6.2.2)

**T2.** Let `A ⊆ ℝⁿ` be compact and sa, `f, g : A → ℝ` continuous with sa graphs, and
`∀ x ∈ A, f(x) = 0 → g(x) = 0`. Then there are `N ≥ 1` and `C ≥ 0` with `|g(x)|^N ≤ C |f(x)|` on `A`.

*Proof.* For `t > 0` put `A_t := {x ∈ A | |g(x)| = 1/t}`, a closed subset of `A`, hence compact. On `A_t`,
`f ≠ 0` (if `f(x) = 0` then `g(x) = 0 ≠ 1/t`). Let `I := {t > 0 | A_t ≠ ∅}` and, for `t ∈ I`,
`f_t := min_{A_t} |f| > 0` (extreme value theorem). The set
`E := {(u, t) | t > 0 ∧ ∃ x ∈ A, t |g(x)| = 1 ∧ u |f(x)| = 1}` is sa (projection), and for `t ∈ I` its fibre is
`{1/|f(x)| : x ∈ A_t}`, whose supremum is `1/f_t`. By T1/G4 there are `c, M, t₀` with `1/f_t ≤ c (1 + t)^M` for
`t ∈ I`, `t ≥ t₀`; hence there are `b ≥ 1` and `N ≥ 1` with `1/f_t ≤ t^N` for `t ∈ I`, `t > b`. The set
`B := {x ∈ A | |g(x)| ≥ 1/b}` is compact and `f ≠ 0` on it, so `|g|^N / |f|` is continuous on `B` and bounded
there by some `C ≥ 1`. Let `x ∈ A`. If `g(x) = 0` the inequality holds because `N ≥ 1`. Otherwise
`t := 1/|g(x)| ∈ I` and `x ∈ A_t`. If `t > b`: `|g(x)|^N = t^{-N} ≤ f_t ≤ |f(x)| ≤ C |f(x)|`. If `t ≤ b`:
`x ∈ B`. ∎

(Schweighofer states that `t ↦ 1/f_t`, extended by `0` off `I`, is semialgebraic and applies 6.2.1 to it; the
existence of the minimum is his 6.1.18 + 6.1.19(b). Over `ℝ` this is the extreme value theorem.)

### 2.3 Shrinking map and the weighted inequality on a closed set (Schweighofer 6.2.3, 6.2.4)

Here `‖·‖` is the Euclidean norm, `𝔹` the open unit ball, `S` the unit sphere,
`φ(x) := x / √(1 + ‖x‖²)`, `ψ(y) := y / √(1 − ‖y‖²)`.

**Lemma (6.2.3).** `φ : ℝⁿ → 𝔹` and `ψ : 𝔹 → ℝⁿ` are continuous, sa, and inverse to each other; for `A ⊆ ℝⁿ`,
`A` is closed iff `φ(A) ∪ S` is compact.

*Proof.* `ψ(φ(x)) = x` and `φ(ψ(y)) = y` by direct computation (`1 − ‖φ(x)‖² = 1/(1 + ‖x‖²)`,
`1 + ‖ψ(y)‖² = 1/(1 − ‖y‖²)`). If `A` is closed: `φ(A) ∪ S` is bounded; if `y_k ∈ φ(A) ∪ S` converges to `y`,
either `‖y‖ = 1` and `y ∈ S`, or `‖y‖ < 1`, then eventually `y_k ∈ 𝔹`, so `y_k ∈ φ(A)`, `ψ(y_k) → ψ(y)`,
`ψ(y_k) ∈ A`, hence `ψ(y) ∈ A` and `y ∈ φ(A)`. Conversely `A = φ⁻¹((φ(A) ∪ S) ∩ 𝔹)` is closed. ∎

**T3 (6.2.4).** Let `A ⊆ ℝⁿ` be closed and sa, `f, g : A → ℝ` continuous with sa graphs, `f = 0 → g = 0` on
`A`. Then there are `N ≥ 1`, `k ∈ ℕ`, `C ≥ 0` with `|g(x)|^N ≤ C (1 + ‖x‖²)^k |f(x)|` on `A`.

*Proof.* If `A` is bounded this is T2. In general: (1) by G4 applied to
`{(u, t) | ∃ x ∈ A, ‖x‖² = t² ∧ t ≥ 0 ∧ u = |f(x)|}` (fibres bounded above: `|f|` is bounded on the compact
set `A ∩ {‖x‖ = t}`) and to the same set for `g`, there are `b ≥ 1` and `ℓ` with `|f(x)|, |g(x)| ≤ (1 + ‖x‖²)^ℓ`
for `x ∈ A`, `‖x‖ > b`. (2) Put `f₀ := f / (1 + ‖x‖²)^{ℓ+1}`, `g₀ := g / (1 + ‖x‖²)^{ℓ+1}`: continuous, sa,
same zeros, and `|f₀(x)|, |g₀(x)| ≤ 1/(1 + ‖x‖²)` for `‖x‖ > b`. (3) `Ã := φ(A) ∪ S` is compact and sa. Define
`f̃ := f₀ ∘ ψ` on `φ(A)` and `f̃ := 0` on `S`; likewise `g̃`. `f̃` is continuous on the relatively open subset
`φ(A) = Ã ∩ 𝔹`. At `y₀ ∈ S`: given `ε > 0` choose `r ≥ b` with `1/(1 + r²) < ε` and put `ρ := r/√(1 + r²) < 1`;
if `y ∈ Ã` and `‖y − y₀‖ < 1 − ρ` then either `y ∈ S` and `f̃(y) = 0`, or `y ∈ φ(A)` with `‖y‖ > ρ`, so
`‖ψ(y)‖ > r` (`‖φ(x)‖ = ‖x‖/√(1 + ‖x‖²)` is increasing in `‖x‖`) and `|f̃(y)| ≤ 1/(1 + ‖ψ(y)‖²) < ε`. (4)
`f̃ = 0 → g̃ = 0` on `Ã`. By T2, `|g̃|^N ≤ C |f̃|` on `Ã`, hence `|g₀|^N ≤ C |f₀|` on `A`, i.e.
`|g|^N ≤ C (1 + ‖x‖²)^{(N−1)(ℓ+1)} |f|`. ∎

### 2.4 The finiteness theorem (Schweighofer 6.3.3)

**T4.** An open sa set `U ⊆ ℝⁿ` is a finite union of sets `{g_1 > 0, …, g_m > 0}`; a closed sa set is a finite
union of sets `{g_1 ≥ 0, …, g_m ≥ 0}`.

*Proof (source).* The closed case follows from the open case by complement and distributivity. For `U` open write
`U = ⋃_i {f_i = 0, g_{i1} > 0, …, g_{im} > 0}` and fix `i`. On the closed set `A := ℝⁿ ∖ U` take
`f := f_i²` and `g := ∏_j (|g_{ij}| + g_{ij})`. If `x ∈ A` and `f(x) = 0` then some `g_{ij}(x) ≤ 0` (otherwise
`x` is in the `i`-th piece, hence in `U`), so `g(x) = 0`. T3 gives `|g|^N ≤ C (1 + ‖x‖²)^k f` on `A`. The basic
open set `V := {C (1 + ∑ x_j²)^k f_i² < (2^m ∏_j g_{ij})^N, g_{i1} > 0, …, g_{im} > 0}` does not meet `A`, and
contains the `i`-th piece (there `f_i = 0` and the right-hand side is positive). ∎

### 2.5 Schweighofer versus Bochnak–Coste–Roy; where uniformity in parameters enters

BCR, **from memory and unverified** (I could not open the book): Prop. 2.6.1 is T1; Prop. 2.6.2 bounds a
continuous sa function on a closed sa set by `c (1 + ‖x‖²)^p` (supremum over sphere sections + 2.6.1);
Prop. 2.6.4 says that for `f` continuous sa on a locally closed `A` and `g` continuous sa on `{f ≠ 0}`, the
function `f^N g` extended by `0` is continuous for large `N`; Thm 2.6.6 is the division form "`g^N = h f` with
`h` continuous sa" and Cor. 2.6.7 the inequality on closed bounded sets; Thm 2.7.2 is the finiteness theorem,
proved from 2.6.6 and 2.6.2 on the closed set `T = Uᶜ ∩ {g_j ≥ 0}` with `g = ∏ g_j`. My recollection is that the
proof of 2.6.4 uses the family `A_{x,u} = {y ∈ A | ‖y − x‖ ≤ 1, u |f(y)| = 1}` indexed by the base point `x` as
well as by `u`, and needs the exponent given by 2.6.1 to be independent of `x`.

What can be said rigorously, independently of the exact text:

* **Schweighofer.** Uniformity in several parameters enters only in Thm 6.1.18 (the image of a semialgebraically
  compact set under a continuous sa map is semialgebraically compact), which is proved for an arbitrary real
  closed field by transferring from `ℝ` a statement quantified over all coefficient tuples of bounded complexity.
  Over `ℝ` this theorem is the Heine–Borel theorem plus continuity, and the uniformity disappears. In 6.2.2 and
  6.2.4 the only families are indexed by one real parameter (`{|g| = 1/t}`, sphere sections), and the uniformity
  needed is exactly T1 applied to the fibrewise extremum. So over `ℝ` the dominant cost of Schweighofer's chain is
  not uniformity; it is (a) a calculus of continuous sa functions on sa sets (absolute value, division by
  `(1 + ‖x‖²)^{ℓ+1}`, composition with `ψ`, piecewise definition) — TauCeti has `IsSemialgebraicOn` with `add`,
  `mul`, `sub`, `comp`, `eval_comp`, `glue`, but I found no absolute value, quotient or square root lemma; (b) the
  shrinking map and the continuity of the extension by zero; (c) three applications of T1.
* **A local formulation** (continuity of `f^N g` at every zero of `f`, as in my recollection of BCR 2.6.4)
  genuinely needs an exponent that is uniform in the base point. With TauCeti's tools this would require a
  parametric version of the algebraic-dependence lemma with a degree bound independent of the parameter. This is
  the "uniformity in parameters" cost; it is avoidable.
* **The global weighted formulation on a closed set needs one real parameter only.** This is what the shortcut
  exploits (§3): the family `K_t = {x ∈ T | ‖x‖² ≤ t, 1 ≤ t g(x)²}` exhausts `T ∖ {g = 0}` by compact sets on
  which `f ≠ 0`; it plays at once the role of the level sets `{|g| = 1/t}` of 6.2.2 and of the sphere sections
  of 6.2.4.

Differences in the last step: Schweighofer applies the inequality on `A = Uᶜ` to the non-polynomial function
`g = ∏ (|g_j| + g_j)`; the variant on `T = Uᶜ ∩ {g_j ≥ 0}` with the polynomial `g = ∏ g_j` (used in `PLAN.md`
L2, and I believe in BCR) needs the inequality for polynomials only. For Lean the second is strictly cheaper.

| | Schweighofer | shortcut (§3) |
|---|---|---|
| functions `f, g` | continuous sa | polynomials |
| domain | compact, then closed via shrinking map | closed, directly |
| uses of one-variable growth | 3 | 1 |
| conclusion | `\|g\|^N ≤ C (1+‖x‖²)^k \|f\|` | `g^{2N} ≤ C f² ((1+‖x‖²)(1+g²))^N` |

For polynomial `g` of degree `d` with coefficient sum `L := ∑ |coeff|` one has `|g(x)| ≤ L (1 + ‖x‖²)^d`, so the
right-hand form implies the left-hand one (`1 + g² ≤ (1 + L²)(1 + ‖x‖²)^{2d}`). The finiteness theorem needs
neither normalisation.

## 3. The candidate shortcut: adversarial examination

### 3.1 The inequality (L1), repaired and squared

**L1.** Let `T ⊆ ℝ^ι` be closed and sa, `f, g` polynomials with `∀ x ∈ T, f(x) = 0 → g(x) = 0`. Then there are
`C ≥ 0` and `M ∈ ℕ` such that for all `x ∈ T`

`g(x)^{2(M+1)} ≤ C · f(x)² · ((1 + N(x)) (1 + g(x)²))^{M+1}`.

Explicitly: if `(c, M, t₀)` is the output of G4 for the set `E` below, then `C = c (1 + t₀)^{M+1}` works.

*Proof.*

*Step 1 (the planar set).* Let
`E := {w ∈ ℝ² | ∃ x ∈ T, N(x) ≤ w₁ ∧ 1 ≤ w₁ g(x)² ∧ w₀ f(x)² = 1}` (coordinate `0` is the value `u`,
coordinate `1` the parameter `t`). `E` is sa: in `ℝ^{Fin 2 ⊕ ι}` the set
`{z | z∘inr ∈ T} ∩ {∑_i X_{inr i}² ≤ X_{inl 1}} ∩ {1 ≤ X_{inl 1} · (rename inr g)²} ∩ {X_{inl 0} · (rename inr f)² = 1}`
is sa (pull-back of `T` along a coordinate map; three polynomial conditions), and `E` is its projection along
the `ι` coordinates.

*Step 2 (fibres are bounded above).* Fix `t ∈ ℝ` and put `K_t := {x ∈ T | N(x) ≤ t ∧ 1 ≤ t g(x)²}`.
`K_t` is closed (`T` is closed, the two conditions are closed because polynomials are continuous) and contained
in the compact box `∏_i [−(1 + |t|), 1 + |t|]` (if `N(x) ≤ t` then `x_i² ≤ t`, and
`±x_i ≤ (x_i² + 1)/2 ≤ (t + 1)/2 ≤ 1 + |t|`), so `K_t` is compact. On `K_t`, `f ≠ 0`: if `f(x) = 0` then
`g(x) = 0` and `1 ≤ t · 0`. Hence `x ↦ (f(x)²)⁻¹` is continuous on `K_t` and its image is bounded above by some
`B`. If `u ∈ E_t := {u | (u, t) ∈ E}` with witness `x`, then `x ∈ K_t` and `u f(x)² = 1`, so
`u = (f(x)²)⁻¹ ≤ B`. (If `K_t = ∅` then `E_t = ∅`; no case distinction is needed.)

*Step 3 (growth).* By G4 there are `c ≥ 0`, `M`, `t₀ ≥ 0` such that `|s| ≤ c (1 + t)^M` whenever `t ≥ t₀` and
`s` is a least upper bound of `E_t`. If `t ≥ t₀` and `u ∈ E_t`, then `E_t` is nonempty and bounded above, so it
has a least upper bound `s` (`Real.exists_isLUB`), and `u ≤ s ≤ |s| ≤ c (1 + t)^M`.

*Step 4 (choice of `t`).* Let `x ∈ T`. If `g(x) = 0` the left-hand side is `0` (the exponent `2(M+1)` is
positive) and the right-hand side is `≥ 0`. Otherwise `f(x) ≠ 0`. Put `a := 1/g(x)² > 0` and
`t := max(t₀, N(x), a)`. Then `N(x) ≤ t`, `1 = a g(x)² ≤ t g(x)²`, and `u := 1/f(x)²` satisfies `u f(x)² = 1`:
so `(u, t) ∈ E` with `t ≥ t₀`, and by Step 3

`1/f(x)² ≤ c (1 + t)^M ≤ c (1 + t)^{M+1}` (as `1 + t ≥ 1`, `c ≥ 0`).

*Step 5 (arithmetic).* `t ≤ t₀ + N(x) + a` (all three are `≥ 0`), so
`(1 + t) g(x)² ≤ (1 + t₀ + N(x)) g(x)² + 1 ≤ (1 + t₀)(1 + N(x))(1 + g(x)²)`
(expand the right-hand side: it exceeds the middle term by `t₀ + N + t₀ N + t₀ N g² ≥ 0`). Multiplying the
inequality of Step 4 by `f(x)² (g(x)²)^{M+1} > 0`:

`g(x)^{2(M+1)} ≤ c f(x)² ((1 + t) g(x)²)^{M+1} ≤ c (1 + t₀)^{M+1} f(x)² ((1 + N(x))(1 + g(x)²))^{M+1}`. ∎

Steps 1–5 are checked by Lean in the scratch prototype (Appendix B: `isSemialgebraic_lojasiewicz_aux`,
`isCompact_setOf_sq_sum_le`, `exists_growth_of_bddAbove_fibres`, `exists_lojasiewicz`, `lojasiewicz_arith`).

### 3.2 Open sets (L2)

**C1 (a basic open set between a cell and `U`).** Let `U ⊆ ℝ^ι` be open and sa, `f`, `g_1, …, g_k` polynomials
with `B := {f = 0, g_1 > 0, …, g_k > 0} ⊆ U`. Then there is a polynomial `q` with
`B ⊆ B' := {q > 0, g_1 > 0, …, g_k > 0} ⊆ U`.

*Proof.* `T := Uᶜ ∩ ⋂_j {g_j ≥ 0}` is closed (complement of an open set, closed conditions) and sa. Put
`g := ∏_j g_j`. If `x ∈ T`, `f(x) = 0` and `g(x) ≠ 0`, then every `g_j(x) ≠ 0`, hence `g_j(x) > 0`, so `x ∈ B ⊆
U`, contradicting `x ∈ Uᶜ`. So L1 applies to `(T, f, g)` and gives `C, M`. Put

`q := g^{2(M+1)} − C · f² · ((1 + ∑_i X_i²)(1 + g²))^{M+1}`.

If `x ∈ B`: `f(x) = 0` and `g(x) > 0`, so `q(x) = g(x)^{2(M+1)} > 0`; thus `B ⊆ B'`. If `x ∈ B'` and `x ∉ U`:
then `x ∈ T` (as `g_j(x) > 0 ≥ 0`), and L1 says `q(x) ≤ 0`, contradiction; thus `B' ⊆ U`. ∎

`B'` is basic (a finite intersection of sets `{p > 0}`), which is all that is used; it is also open, which is not
used. For `k = 0`, `g = 1`, `T = Uᶜ`, and the hypothesis of L1 reads "`f ≠ 0` on `Uᶜ`", true because
`{f = 0} = B ⊆ U`.

**C2 (a sign cell is of the form `B`).** For `p : Fin m → MvPolynomial ι ℝ` and `ε : Fin m → SignType`,
`{x | ∀ i, sign(p_i(x)) = ε_i} = {f_ε = 0, g_{ε,1} > 0, …, g_{ε,m} > 0}` with
`f_ε := ∑_i (if ε_i = 0 then p_i² else 0)` and `g_{ε,i} := 1` if `ε_i = 0`, `p_i` if `ε_i = 1`, `−p_i` if
`ε_i = −1`. *Proof.* A sum of squares vanishes iff each term does, so `f_ε(x) = 0 ↔ ∀ i, ε_i = 0 → p_i(x) = 0`;
then compare coordinate by coordinate in the three cases of `ε_i`. ∎ (Padding with the constant `1` gives every
cell exactly `m` strict inequalities, so no ragged index types appear.)

**L2.** An open sa set `U` is `⋃_{i : Fin I} ⋂_{j : Fin J} {Q_{ij} > 0}`.

*Proof.* By `TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`, `U = {x | Φ(σ(x))}` where
`σ(x) := (sign p_i(x))_i`. For each sign vector `ε` with `Φ(ε)` the cell `Z_ε := {σ = ε}` is contained in `U`
(if `σ(x) = ε` then `Φ(σ(x))`). By C2 and C1 there is `q_ε` with `Z_ε ⊆ B'_ε ⊆ U`, where `B'_ε` is cut out by
the `m + 1` polynomials `q_ε, g_{ε,1}, …, g_{ε,m}`. Every `x ∈ U` lies in `Z_{σ(x)}` and `Φ(σ(x))` holds, so
`U ⊆ ⋃_{ε : Φ ε} B'_ε ⊆ U`. The index set `{ε // Φ ε}` is finite; reindex it by `Fin (Nat.card _)`, and take
`J = m + 1`. ∎

### 3.3 Closed sets (L3)

If `sᶜ = ⋃_{i : Fin I} ⋂_{j : Fin J} {Q_{ij} > 0}`, then `x ∈ s ↔ ∀ i, ∃ j, Q_{ij}(x) ≤ 0 ↔ ∃ φ : Fin I → Fin
J, ∀ i, 0 ≤ −Q_{i,φ(i)}(x)` (choice over the finite set `Fin I`). With the bijection
`finFunctionFinEquiv : (Fin I → Fin J) ≃ Fin (J ^ I)` this is the target with `I' = J^I`, `J' = I`,
`P k i := −Q i (finFunctionFinEquiv.symm k i)`. Edge cases: `I = 0` gives `sᶜ = ∅`, `I' = J^0 = 1`, the single
empty intersection is `univ`; `J = 0 < I` gives `sᶜ = univ`, `I' = 0`, empty union. ∎

### 3.4 The attack list of the brief

| point | outcome |
|---|---|
| `K_t = ∅` | harmless: then `E_t = ∅`, there is no least upper bound and G4 says nothing; the proof only uses `t` for which the given `x` lies in `K_t`. |
| compactness of `K_t` | closed (`T` closed, polynomial conditions) and inside the box `[−(1+\|t\|), 1+\|t\|]^ι`. Holds for every real `t`, also `t ≤ 0` (then `K_t = ∅`). |
| attainment | not needed: only boundedness of `1/f²` on `K_t` (`IsCompact.bddAbove_image`). |
| the range `1 ≤ t ≤ t₀` | not needed: `t := max(t₀, N(x), 1/g(x)²)` is always `≥ t₀`. The plan's "`K_t` is increasing, enlarge `c`" is correct (for `1 ≤ t ≤ t₁ := max(1, t₀)`: `K_t ⊆ K_{t₁}`, so the bound at `t₁` holds on `K_t`, and `c (1+t₁)^M ≤ c (1+t₁)^M (1+t)^M`) but superfluous. The restriction `1 ≤ t` in the plan's `E` is also superfluous. |
| passage from `t` to `(x, g x)` | Step 5 of §3.1, constant `(1 + t₀)^{M+1}`. |
| exponents | **gap in the plan's proof idea**: with the `M` of G4 and a point `x ∈ T` where `g(x) = f(x) = 0`, the plan's inequality `c \|g x\|^M ≤ \|f x\| (…)^M` reads `c ≤ 0` when `M = 0` (in Lean `0 ^ 0 = 1`). G4 may return `M = 0` (example: `T = {0} ⊆ ℝ`, `f = g = X`; then `E = ∅` and `(c, M, t₀) = (0, 0, 0)` is a legitimate output). Repair: use the exponent `M + 1`. The plan's *statement* of L1 is true. |
| positivity of `c` | the plan wants `c > 0` on the left; G4 gives `c ≥ 0` on the right. Writing the constant on the right-hand side (`C ≥ 0`) removes the issue; for the plan's form take `1/(C + 1)`. |
| `f = 0` | hypothesis forces `g = 0` on `T`; `E = ∅`; conclusion `0 ≤ 0`. In C1 this is a cell without equation: `q = g^{2(M+1)}` and `B' = B`. |
| no strict inequality (`k = 0`) | `g = 1` (empty product), see C1. |
| `ι` empty | `ℝ^ι` is a point, `N = 0`; nothing in the proof distinguishes this case. |
| `U = ∅`, `U = univ` | `U = ∅`: every cell with `Φ ε` is empty, C1 still yields `B' ⊆ ∅`. `U = univ`: `T = ∅`, L1 is vacuous. |
| is `B ⊆ B' ⊆ U` proved? | yes, C1. |
| is `B'` open and basic? | basic by construction; openness is true and unused. |
| is every point of `U` in a cell `B ⊆ U`? | yes, the cell of its own sign vector, L2. |
| L3 | correct, including `I = 0` and `J = 0`. |

One more trap, not in the plan: the reciprocal in `E` (`u f(x)² = 1`) is essential. Applying G4 to
`{(u, t) | ∃ x ∈ K_t, u = −f(x)²}` bounds `min_{K_t} f²` from *above*, which is useless.

### 3.5 Is there a simpler or more robust variant?

The variant of §3.1–3.3 is already the simplification I recommend over the plan's text:

* squares instead of absolute values, so that `E` and `q` are given by polynomials with no case distinction;
* no restriction `1 ≤ t` and no monotonicity argument;
* the constant on the right-hand side;
* a wrapper around G4 that hides `IsLUB` (lemma F0 in §4);
* cells padded to exactly `m` strict inequalities.

An equivalent alternative merges L1 and C1 into one "separation" statement without the product `∏ g_j`: with
`K_t := {x ∈ Uᶜ | N(x) ≤ t ∧ ∀ j, 1 ≤ t g_j(x)}` one gets
`∏_j g_j^M ≤ C f² ((1 + N) ∏_j (1 + g_j))^M` on `Uᶜ ∩ {g_j > 0}`. Same size; I prefer L1 because it is a
recognisable theorem (a Łojasiewicz inequality for polynomials on a closed sa set) that the library may reuse.

L1 extends verbatim to continuous `f, g` with sa graphs (only Step 1 changes). Not needed here.

### 3.6 Statements that are false as commonly (or carelessly) stated

1. *Unweighted inequality on a closed unbounded set.* `T = {(x, y) | x y = 1, x ≥ 0}`, `f = y`, `g = 1`:
   `f ≠ 0` on `T`, but `1 ≤ C |y|` fails as `x → ∞`. The weight `(1 + ‖x‖²)^k` is necessary.
2. *Exponent `0`.* "`∃ N ∈ ℕ, |g|^N ≤ C |f|`" is true only because `N ≥ 1` can be chosen; any proof that
   may output `N = 0` is wrong (§3.4). Schweighofer's `ℕ` starts at `1`.
3. *Relaxing strict inequalities.* `{x²(x − 1) > 0} = (1, ∞)` has closure `[1, ∞)`, but
   `{x²(x − 1) ≥ 0} = {0} ∪ [1, ∞)`. The closure of a basic set is not the relaxed set.
4. *A basic description need not exist.* Schweighofer's Example 6.3.4 (slashed square) is an open sa set that is
   not basic open; unions are necessary in the theorem.
5. *L1 without closedness of `T`.* `T = (0, 1] × (0, 1] ⊆ ℝ²`, `f = X`, `g = Y`: `f ≠ 0` on `T`, so the
   hypothesis holds, but `y^{2(M+1)} ≤ C x² ((1 + x² + y²)(1 + y²))^{M+1}` fails at `(x, 1)` as `x → 0`.
6. *C1 without openness of `U`.* `U = B = {0} ⊆ ℝ` (`f = X`, no strict inequality): a set `{q > 0}` is open, so
   it cannot contain `0` and be contained in `{0}`. Openness of `U` is used exactly once, to make `T` closed.

## 4. Cheapest correct variant for Lean

### 4.1 Lemma list (statements elaborated at the pins; see Appendix B)

Namespace `Semialgebraic`, `open MvPolynomial`. Names are suggestions.

```lean
/-- F0. G4 without `IsLUB`: points of a sa planar set with fibres bounded above grow polynomially. -/
theorem exists_growth_of_bddAbove_fibres {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E)
    (hbdd : ∀ t : ℝ, BddAbove {u : ℝ | ![u, t] ∈ E}) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ u t : ℝ, t₀ ≤ t → ![u, t] ∈ E → u ≤ c * (1 + t) ^ M

/-- F1. The planar set of the Łojasiewicz argument is semialgebraic. -/
theorem isSemialgebraic_lojasiewicz_aux {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (f g : MvPolynomial ι ℝ) :
    TauCeti.IsSemialgebraic {w : Fin 2 → ℝ | ∃ x : ι → ℝ, x ∈ T ∧ ∑ i, x i ^ 2 ≤ w 1 ∧
      1 ≤ w 1 * eval x g ^ 2 ∧ w 0 * eval x f ^ 2 = 1}

/-- F2. The sets `K_t` are compact. -/
theorem isCompact_setOf_sq_sum_le {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)} (hT : IsClosed T)
    (g : MvPolynomial ι ℝ) (t : ℝ) :
    IsCompact {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * eval x g ^ 2}

/-- F3. Real arithmetic of Step 5 (may be private). -/
theorem lojasiewicz_arith {c t₀ N F G : ℝ} {M : ℕ} (hc : 0 ≤ c) (ht₀ : 0 ≤ t₀) (hN : 0 ≤ N)
    (hF : F ≠ 0) (hG : G ≠ 0)
    (h : 1 / F ^ 2 ≤ c * (1 + max t₀ (max N (1 / G ^ 2))) ^ M) :
    G ^ (2 * (M + 1)) ≤ c * (1 + t₀) ^ (M + 1) * F ^ 2 * ((1 + N) * (1 + G ^ 2)) ^ (M + 1)

/-- L1. Łojasiewicz inequality for polynomials on a closed semialgebraic set. -/
theorem exists_lojasiewicz {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (hTc : IsClosed T) (f g : MvPolynomial ι ℝ)
    (hfg : ∀ x ∈ T, eval x f = 0 → eval x g = 0) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ x ∈ T,
      eval x g ^ (2 * (M + 1)) ≤
        C * eval x f ^ 2 * ((1 + ∑ i, x i ^ 2) * (1 + eval x g ^ 2)) ^ (M + 1)

/-- C1. A basic open set between a basic set and an open semialgebraic set containing it. -/
theorem exists_pos_between {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) {k : ℕ} (f : MvPolynomial ι ℝ)
    (g : Fin k → MvPolynomial ι ℝ)
    (hB : {x : ι → ℝ | eval x f = 0 ∧ ∀ j, 0 < eval x (g j)} ⊆ U) :
    ∃ q : MvPolynomial ι ℝ,
      {x : ι → ℝ | eval x f = 0 ∧ ∀ j, 0 < eval x (g j)} ⊆
        {x | 0 < eval x q ∧ ∀ j, 0 < eval x (g j)} ∧
      {x : ι → ℝ | 0 < eval x q ∧ ∀ j, 0 < eval x (g j)} ⊆ U

/-- C2. A sign cell is the common zero set of one polynomial cut by `m` strict inequalities. -/
theorem exists_setOf_sign_eq_eq {ι : Type*} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ)
    (ε : Fin m → SignType) :
    ∃ (f : MvPolynomial ι ℝ) (g : Fin m → MvPolynomial ι ℝ),
      {x : ι → ℝ | ∀ i, SignType.sign (eval x (p i)) = ε i} =
        {x | eval x f = 0 ∧ ∀ j, 0 < eval x (g j)}

/-- L2. Finiteness theorem, open sets. -/
theorem exists_eq_iUnion_iInter_pos {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) :
    ∃ (I J : ℕ) (Q : Fin I → Fin J → MvPolynomial ι ℝ),
      U = ⋃ i, ⋂ j, {x | 0 < eval x (Q i j)}

/-- L3a. Complement of a finite union of basic open sets. -/
theorem compl_iUnion_iInter_pos {ι : Type*} {I J : ℕ} (Q : Fin I → Fin J → MvPolynomial ι ℝ) :
    (⋃ i, ⋂ j, {x : ι → ℝ | 0 < eval x (Q i j)})ᶜ =
      ⋃ k : Fin (J ^ I), ⋂ i : Fin I,
        {x | 0 ≤ eval x (-Q i (finFunctionFinEquiv.symm k i))}

/-- L3. The interface theorem (namespace `Semialgebraic.Interface`). -/
theorem exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}
```

### 4.2 Dependency order, proofs, effort

Order: `F0 → {F1, F2, F3} → L1 → C1; C2; {C1, C2} → L2 → L3a → L3`.

| id | proof | lines in prototype | effort |
|---|---|---|---|
| F0 | G4, `Real.exists_isLUB`, `le_abs_self` | 9 | S |
| F1 | four sa sets in `Fin 2 ⊕ ι → ℝ` (`preimage_comp Sum.inr`, `isSemialgebraic_eval_le` twice, `isSemialgebraic_eval_eq`), then `setOf_exists_sumElim`; each identification by `convert … using 1; ext; simp [eval_rename]` | 26 | S |
| F2 | closed: `IsClosed.inter`, `isClosed_le`; inside `Set.pi univ (fun _ => Icc (-(1+\|t\|)) (1+\|t\|))`: `isCompact_univ_pi`, `isCompact_Icc`, `IsCompact.of_isClosed_subset`, `Finset.single_le_sum`, `nlinarith` | 17 | S |
| F3 | `max_le`, `gcongr`, `field_simp`, `nlinarith` | 29 | S |
| L1 | §3.1; `ContinuousOn.inv₀`, `IsCompact.bddAbove_image`, `eq_inv_of_mul_eq_one_left` | 46 | S–M |
| C1 | §3.2; `eval_prod`, `Finset.prod_ne_zero_iff`, `Finset.prod_pos`, `isClosed_iInter`, `IsSemialgebraic.iInter` | 39 | S |
| C2 | `Finset.sum_eq_zero_iff_of_nonneg`, case split on `ε i`, `sign_eq_zero_iff`, `sign_eq_one_iff`, `sign_eq_neg_one_iff` | 23 | S |
| L2 | `exists_eq_setOf_sign_eval`, `choose`, `Fin.cons`, `Finite.equivFin`, `Function.Surjective.iUnion_comp` | 39 | S–M |
| L3a | pointwise, `choose`, `finFunctionFinEquiv` | 14 | S |
| L3 | L2 on `sᶜ`, L3a, `compl_compl` | 9 | S |
| shape check `SemialgebraicCheck/A2.lean` | `⟨Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg⟩` | ~10 | S |

Total: about 250 lines of proof in the prototype; with headers, docstrings and step comments 300–350 lines.
Overall effort **S–M**: one writer unit (or two: `Finiteness/Lojasiewicz.lean` = F0–L1,
`Finiteness/Open.lean` = C1, C2, L2, and `Interface/Finiteness.lean` = L3a, L3).

### 4.3 Lean dependencies, verified at the pins

All names below were found by grep in the checkouts and resolved by `#check` in a scratch file
(`lake env lean`); signatures are quoted from the `#check` output or the source line.
Paths are relative to `.lake/packages/mathlib/` resp. `.lake/packages/TauCeti/`.

**TauCeti** (`TauCeti/Geometry/RealAlgebraic/Semialgebraic/…`)

| name | location | signature |
|---|---|---|
| `TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval` | `Basic.lean:383` | `{s : Set (σ → R)} (hs : IsSemialgebraic s) : ∃ (m : ℕ) (p : Fin m → MvPolynomial σ R) (Φ : (Fin m → SignType) → Prop), s = {x \| Φ fun i => SignType.sign (eval x (p i))}` |
| `TauCeti.IsSemialgebraic.setOf_exists_sumElim` | `Image.lean:154` | `[HasSemialgebraicProjections R] [Finite τ] {s : Set (σ ⊕ τ → R)} (hs : IsSemialgebraic s) : IsSemialgebraic {x : σ → R \| ∃ y : τ → R, Sum.elim x y ∈ s}` |
| `TauCeti.IsSemialgebraic.setOf_forall_sumElim` | `Image.lean:166` | same with `∀` (not used) |
| `TauCeti.IsSemialgebraic.preimage_comp` | `Basic.lean:318` | `{s : Set (τ → R)} (hs : IsSemialgebraic s) (f : τ → σ) : IsSemialgebraic ((fun x : σ → R => x ∘ f) ⁻¹' s)` |
| `TauCeti.isSemialgebraic_eval_le` | `Basic.lean:233` | `[IsOrderedAddMonoid R] (p q : MvPolynomial σ R) : IsSemialgebraic {x : σ → R \| eval x p ≤ eval x q}` |
| `TauCeti.isSemialgebraic_eval_eq` | `Basic.lean:204` | `(p q : MvPolynomial σ R) : IsSemialgebraic {x : σ → R \| eval x p = eval x q}` |
| `TauCeti.isSemialgebraic_eval_nonneg` | `Basic.lean:223` | `(p : MvPolynomial σ R) : IsSemialgebraic {x : σ → R \| 0 ≤ eval x p}` |
| `TauCeti.IsSemialgebraic.compl`, `.inter`, `.iInter` | `Basic.lean:144, 165, 192` | `IsSemialgebraic s → IsSemialgebraic sᶜ`; `… (s ∩ t)`; `[Finite ι] (hs : ∀ i, IsSemialgebraic (s i)) : IsSemialgebraic (⋂ i, s i)` |
| instance `TauCeti.HasSemialgebraicProjections ℝ` | `CAD/Existence.lean:102` | resolved by `inferInstance` after `import Semialgebraic.Growth.Main` |

Universe levels: `σ τ R : Type*` independently, so `σ := Fin 2`, `τ := ι : Type u` is fine.

**Mathlib**

| purpose | name | location | signature |
|---|---|---|---|
| continuity of `eval` | `MvPolynomial.continuous_eval` | `Mathlib/Topology/Algebra/MvPolynomial.lean:31` | `(p : MvPolynomial σ X) : Continuous fun x ↦ eval x p` |
| compact boxes | `isCompact_univ_pi` | `Mathlib/Topology/Compactness/Compact.lean:1172` | `(h : ∀ i, IsCompact (s i)) : IsCompact (pi univ s)` |
| | `isCompact_Icc` | `Mathlib/Topology/Order/Compact.lean:53` (field of `CompactIccSpace`) | `IsCompact (Icc a b)` |
| closed in compact | `IsCompact.of_isClosed_subset` | `Mathlib/Topology/Compactness/Compact.lean:105` | `(hs : IsCompact s) (ht : IsClosed t) (h : t ⊆ s) : IsCompact t` |
| Heine–Borel (alternative, unused) | `Metric.isCompact_of_isClosed_isBounded`, `pi_properSpace` | `Mathlib/Topology/MetricSpace/Bounded.lean:320`, `…/ProperSpace.lean:132` | `[ProperSpace α] (hc : IsClosed s) (hb : IsBounded s) : IsCompact s` |
| extreme values | `IsCompact.bddAbove_image` | `Mathlib/Topology/Order/Compact.lean:359` | `(hK : IsCompact K) (hf : ContinuousOn f K) : BddAbove (f '' K)` |
| | `IsCompact.exists_isMinOn` (alternative, unused) | `…/Compact.lean:255` | `(hs : IsCompact s) (ne_s : s.Nonempty) {f : β → α} (hf : ContinuousOn f s) : ∃ x ∈ s, IsMinOn f s x` |
| suprema in `ℝ` | `Real.exists_isLUB` | `Mathlib/Algebra/Order/Archimedean/Real/Basic.lean:55` | `(hne : s.Nonempty) (hbdd : BddAbove s) : ∃ x, IsLUB s x` |
| closed sets | `isClosed_le` | `Mathlib/Topology/Order/OrderClosed.lean:444` | `(hf : Continuous f) (hg : Continuous g) : IsClosed {b \| f b ≤ g b}` |
| | `isClosed_iInter`, `IsClosed.inter`, `isClosed_compl_iff` | `Mathlib/Topology/Basic.lean:159, 176, 167` | `(h : ∀ i, IsClosed (f i)) : IsClosed (⋂ i, f i)`; …; `IsClosed sᶜ ↔ IsOpen s` |
| continuity | `ContinuousOn.inv₀` | `Mathlib/Topology/Algebra/GroupWithZero.lean:128` | `(hf : ContinuousOn f s) (h0 : ∀ x ∈ s, f x ≠ 0) : ContinuousOn f⁻¹ s` |
| | `continuous_finsetSum` | `to_additive` of `continuous_finsetProd`, `Mathlib/Topology/Algebra/Monoid.lean:959` | `(s : Finset ι) : (∀ i ∈ s, Continuous (f i)) → Continuous fun a => ∑ i ∈ s, f i a` |
| | `continuous_apply`, `Continuous.pow` | `Mathlib/Topology/Constructions.lean:783`, `…/Monoid.lean:831` | |
| polynomials | `MvPolynomial.eval_rename` | `Mathlib/Algebra/MvPolynomial/Rename.lean:244` | `eval g (rename k p) = eval (g ∘ k) p` |
| | `MvPolynomial.eval_prod`, `eval_sum`, `eval_C`, `eval_X`, `eval_pow` | `Mathlib/Algebra/MvPolynomial/Eval.lean:299, 295, 271, 275, 292` | |
| finite sums and products | `Finset.prod_pos` | `Mathlib/Algebra/Order/BigOperators/GroupWithZero/Finset.lean:160` | `(h0 : ∀ i ∈ s, 0 < f i) : 0 < ∏ i ∈ s, f i` |
| | `Finset.prod_ne_zero_iff` | `Mathlib/Algebra/BigOperators/GroupWithZero/Finset.lean:63` | `∏ x ∈ s, f x ≠ 0 ↔ ∀ a ∈ s, f a ≠ 0` |
| | `Finset.sum_eq_zero_iff_of_nonneg` | `to_additive` of `prod_eq_one_iff_of_one_le`, `Mathlib/Algebra/Order/BigOperators/Group/Finset.lean:240` | `(∀ i ∈ s, 0 ≤ f i) → (∑ i ∈ s, f i = 0 ↔ ∀ i ∈ s, f i = 0)` |
| | `Finset.single_le_sum` | `to_additive` of `single_le_prod`, same file `:276` | `(hf : ∀ i ∈ s, 0 ≤ f i) {a} (h : a ∈ s) : f a ≤ ∑ x ∈ s, f x` |
| signs | `sign_eq_zero_iff`, `sign_eq_one_iff`, `sign_eq_neg_one_iff` | `Mathlib/Basic/Sign/Defs.lean:311, 286, 292` | `sign a = 0 ↔ a = 0`; `sign a = 1 ↔ 0 < a`; `sign a = -1 ↔ a < 0` |
| | `Fintype SignType` | `Mathlib/Basic/Sign/Defs.lean:32` (`deriving`) | |
| reindexing | `Finite.equivFin` | `Mathlib/SetTheory/Cardinal/NatCard.lean:39` | `(α : Type*) [Finite α] : α ≃ Fin (Nat.card α)` |
| | `Fintype.equivFin` (alternative) | `Mathlib/Data/Fintype/EquivFin.lean:80` | `(α) [Fintype α] : α ≃ Fin (card α)` |
| | `Subtype.finite` | `Mathlib/Data/Fintype/EquivFin.lean:195` | `[Finite α] {p : α → Prop} : Finite {x // p x}` |
| | `finFunctionFinEquiv` | `Mathlib/Algebra/BigOperators/Fin.lean:577` | `{m n : ℕ} : (Fin n → Fin m) ≃ Fin (m ^ n)` |
| | `Function.Surjective.iUnion_comp`, `.iInter_comp` | `Mathlib/Data/Set/Lattice/Bounded.lean:648, 651` | `(hf : Surjective f) (g : ι₂ → Set α) : ⋃ x, g (f x) = ⋃ y, g y` |
| | `Fin.cons_zero`, `Fin.cons_succ` | `Mathlib/Data/Fin/Tuple/Basic.lean:129, 121` | |
| set algebra | `Set.compl_iUnion`, `Set.compl_iInter` | `Mathlib/Data/Set/Lattice/Indexed.lean:322, 329` | (the prototype proves L3a pointwise instead) |
| | `iInf_iSup_eq` | `Mathlib/Order/CompleteBooleanAlgebra.lean:295` | `(⨅ a, ⨆ b, f a b) = ⨆ g : ∀ a, κ a, ⨅ a, f a (g a)` (alternative for L3a) |
| | `Set.mem_ofPred_eq` | `Mathlib/Data/Set/Operations.lean:74` | replaces the deprecated `Set.mem_setOf_eq` |
| algebra | `eq_inv_of_mul_eq_one_left` | `Mathlib/Algebra/Group/DivInvMonoid.lean:339` | `(h : a * b = 1) : a = b⁻¹` |
| choice | `Classical.skolem` | Lean core `Init/Classical.lean:125` | (the prototype uses the `choose` tactic) |

**Missing names.** `Set.iInter_iUnion_distr` does not exist (I guessed it; `#check` fails). Nothing else is
missing: no lemma has to be added to Mathlib or TauCeti. What must be written is exactly the list of §4.1.

**Missing in TauCeti/Mathlib as mathematics.** No Łojasiewicz inequality for sa sets, no finiteness theorem, no
notion of basic open/closed set (grep for `ojasiewicz`, `basic closed`, `basic open` in TauCeti: only unrelated
hits in `Geometry/Manifold/Morse` and bibliography entries; none in Mathlib).

### 4.4 Formalisation risks

1. **Set-builder is no longer transparent at this Mathlib pin.** `IsClosed.inter hT (…)` does not unify with
   `IsClosed {x | x ∈ T ∧ …}`, and `Set.mem_setOf_eq` is deprecated in favour of `Set.mem_ofPred_eq`. In the
   prototype the pattern `have h := …; convert h using 1; ext x; simp only [Set.mem_inter_iff,
   Set.mem_ofPred_eq]` works; a bare `simp` there produced a non-closing normal form. Low risk, already solved.
2. **`simp` through `eval` under a set-builder** (reported by the P2-c writer). `convert … using 1; ext z;
   simp [eval_rename]` works for F1.
3. **Arithmetic** (F3): `gcongr` closes the monotonicity goals; `field_simp` needs a following `ring` in one
   place. Solved in the prototype.
4. **Import hygiene.** The prototype imports `Mathlib.Tactic`; the standing brief asks for specific imports. The
   writer must narrow them (the proofs use `nlinarith`, `positivity`, `gcongr`, `field_simp`, `norm_num`,
   `choose`, `convert`).
5. **Dependence on G4.** Present and audited (ACCEPT). The route uses nothing else from Phase 2.
6. **Statement drift of the interface.** The prototype's last theorem has the target statement character for
   character (`{ι : Type}`, `MvPolynomial.eval x (P i j)`); the shape check file remains to be written.

No mathematical risk remains for `ℝ`.

## 5. FT′

**Statement.** FT′: for every closed sa `K ⊆ ℝ^ι` there are `k` and a polynomial `R` in the variables
`ι ⊕ Fin k` with

`K = {x | ∃ z ∈ [0, 1/2]^k, R(x, z) = 0}`.

(HardnessBilevel `blueprint.md` writes the box as `[0,1]^k` at line 780 and as `[0,½]^k` at line 1261; the two
are equivalent by `z ↦ z/2`.) In Lean:

```lean
theorem exists_eq_setOf_exists_box_eval_eq_zero {ι : Type} [Fintype ι] {s : Set (ι → ℝ)}
    (hs : TauCeti.IsSemialgebraic s) (hc : IsClosed s) :
    ∃ (k : ℕ) (R : MvPolynomial (ι ⊕ Fin k) ℝ),
      s = {x | ∃ z : Fin k → ℝ, (∀ l, z l ∈ Set.Icc (0 : ℝ) (1 / 2)) ∧
        MvPolynomial.eval (Sum.elim x z) R = 0}
```

(this statement was not elaborated in Lean).

**FT ⇒ FT′** (blueprint `gad.G6`, `gad.G7`, lines 1236–1261; re-derived). For real `p`,
`(∃ z ∈ [0, ½], p = (p² + 1) z) ↔ 0 ≤ p`: if `p = (p² + 1) z` with `z ≥ 0` then `p ≥ 0`; if `p ≥ 0` take
`z := p/(p² + 1)`, which is `≥ 0` and `≤ ½` because `2p ≤ p² + 1`. With `G(p, z) := (p − (p² + 1) z)² ≥ 0`, a
set `⋃_i ⋂_j {P_{ij} ≥ 0}` equals `{x | ∃ z ∈ [0,½]^{I×J}, ∏_i ∑_j G(P_{ij}(x), z_{ij}) = 0}` (a product of
nonnegative numbers vanishes iff one factor does; a sum of nonnegative numbers vanishes iff all terms do; the
`z_{ij}` of the other blocks are chosen `0`).

**Why FT′ suffices for Theorem 2.15** (blueprint §4.F, lines 1263–1318; logic checked). `t215.core` consumes the
closed sa epigraph `E` of `f` only through hypothesis (★★): a function `R ≥ 0`, polynomial in `(x, t, z)`, and a
bounded box `Z` with `E(x, t·w(x)) ↔ ∃ z ∈ Z, R(x, t, z) = 0`. Given FT′ for `E` with polynomial `R₀(x, τ, z)`,
`R(x, t, z) := R₀(x, t·w(x), z)²` is such a function. The lower-level problem of Theorem 2.15 has no convexity
requirement, so nothing else is needed.

**Why FT′ does not suffice for Theorem 2.20** (blueprint §4.G.4, lines 1463–1535; logic checked).
`t220.core` needs a finite family of *basic closed* sets `B_l = ⋂_k {R_{lk} ≥ 0}` with polynomials `p_l` such
that `f(x) = min {p_l(x) | x ∈ B_l}`: the lower-level objective is
`Q(x, (s, z)) = (1 − ∑ s_l)² − ∑_l ∑_k R_{lk}(x) z_{lk}`, affine in `z`, and the union over `l` is handled in the
upper objective `P = ∑_l p_l s_l ∏_k z_{lk}`. The class of Theorem 2.20 requires `Q(x, ·)` convex. FT′ describes
`D_i = {f ≤ p_i}` as the projection of the zero set of a polynomial that is not convex in `z` (a product over the
union index, in either normal form) and gives no decomposition of `D_i` into basic closed pieces. Moreover, on
that route the hypothesis of `t220.core` for all lsc piecewise polynomial functions is *equivalent* to the
finiteness theorem: for `D` closed sa, `f := 1_{Dᶜ}` is lsc, and `f(x) = min {p_l(x) | x ∈ B_l}` gives
`D = {f ≤ 0} = ⋃_l (B_l ∩ {−p_l ≥ 0})`, a finite union of basic closed sets (I checked this argument).

**Is FT′ cheaper on this route?** No.

* A direct proof of FT′ from L2 exists and skips L3: from `Kᶜ = ⋃_i ⋂_j {Q_{ij} > 0}`,
  `K = ⋂_i ⋃_j {−Q_{ij} ≥ 0} = {x | ∃ z ∈ [0,½]^{I×J}, ∑_i ∏_j G(−Q_{ij}(x), z_{ij}) = 0}`. It saves L3a (14
  lines) and the exponential index `J^I`, and costs the gadget lemma (blueprint estimate M; I estimate 60–80
  lines). F0–L2, that is all the analysis, are needed unchanged.
* I know no proof of FT′ that avoids a Łojasiewicz-type separation. The formal shortcut — every sa set is a
  projection of an algebraic set (`g > 0 ↔ ∃ y, g y² = 1`), then compactify the fibre — fails:
  for `C = {x²(x − 1) > 0} = (1, ∞)` the compactified lift `{x²(x − 1) = z², z ∈ [0, 1]}` projects onto
  `{0} ∪ [1, x₁]`, which contains the spurious point `0` (the relaxed set of §3.6, item 3). That no cheaper proof
  exists is an opinion, not a theorem.

Since the full theorem costs about 300 lines on this route and is required for Theorem 2.20, FT′ should not be
a separate target; if HardnessBilevel wants it, it is the corollary `gad.G7` there.

## 6. Not established, not verified

* **Bochnak–Coste–Roy was not consulted.** The numbering and content attributed to BCR §2.6–2.7 in §2.5, and in
  particular the description of the proof of Prop. 2.6.4, are from memory. Nothing in §3–§5 depends on them.
* **Schweighofer.** §6.2–6.3 and Thm 6.1.18 were read in arXiv v1. The results it refers to outside §6 (1.5.3,
  1.8.x: sign of a polynomial near infinity, normal form, quantifier elimination) were not re-read; their
  content is re-derived or replaced by TauCeti lemmas above. Basu–Pollack–Roy was not consulted.
* **The textbook chain T2–T4 was not formalised or elaborated**, only re-derived on paper; its Lean cost
  (1100–1500 lines) is an estimate. The absence of absolute-value/quotient/root lemmas for `IsSemialgebraicOn`
  and `IsSemialgebraicMap` in TauCeti is based on the signature summaries in `notes/api/` and on a grep of the
  whole TauCeti checkout for `IsSemialgebraicOn.{abs,inv,div,sqrt,max,min,norm}` and the `Map` analogues (no
  hit); a lemma under another name could have been missed.
* **The scratch prototype** (Appendix B) was elaborated with `lake env lean` on a file under the session scratch
  directory, against the built `Semialgebraic.Growth.Main`; it was not built with `lake build`, not audited, and
  its `#print axioms` output is the only check of its soundness. The FT′ Lean statement in §5 was not
  elaborated.
* **Constants.** `C` and `M` in L1 are explicit in terms of the output `(c, M, t₀)` of G4, which is itself not
  effective (it comes from an unspecified nonzero polynomial vanishing on the graph of the fibrewise supremum).
* **Attribution.** Calling the one-parameter exhaustion "Hörmander's device" is from memory (Hörmander's proof
  of the division of distributions by polynomials); I did not check a source for it.
* **Optimality claims** ("cheapest", "no cheaper proof of FT′") are judgements.
* HardnessBilevel's Lean sources were not read beyond locating the class
  (`HardnessBilevel/Assumptions/Classes.lean:38`); §5 relies on `blueprint.md`.

## Appendix A. Scratch checks performed

1. `#check` of every name of §4.3 (one unknown constant: `Set.iInter_iUnion_distr`, a wrong guess of mine).
2. Elaboration of the statements of §4.1.
3. Full elaboration of the prototype below; last line of output:
   `'Scratch.exists_eq_iUnion_iInter_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]`,
   no error, no warning.

Command: `cd /home/user/Semialgebraic && . scripts/env.sh && lake env lean <scratch file>` (about 5 s).

## Appendix B. Scratch prototype (not a deliverable)

Compiles at the pins against `Semialgebraic.Growth.Main`. To be rewritten by the Phase 3b writer under the
library's conventions (namespace `Semialgebraic`, specific imports, docstrings, step comments).

```lean
import Semialgebraic.Growth.Main
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.Order.Compact
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open MvPolynomial

namespace Scratch

/-- F0 -/
theorem exists_growth_of_bddAbove_fibres {E : Set (Fin 2 → ℝ)} (hE : TauCeti.IsSemialgebraic E)
    (hbdd : ∀ t : ℝ, BddAbove {u : ℝ | ![u, t] ∈ E}) :
    ∃ (c : ℝ) (M : ℕ) (t₀ : ℝ), 0 ≤ c ∧ 0 ≤ t₀ ∧
      ∀ u t : ℝ, t₀ ≤ t → ![u, t] ∈ E → u ≤ c * (1 + t) ^ M := by
  obtain ⟨c, M, t₀, hc, ht₀, h⟩ := Semialgebraic.exists_growth_isLUB hE
  refine ⟨c, M, t₀, hc, ht₀, fun u t ht hu => ?_⟩
  obtain ⟨s, hs⟩ := Real.exists_isLUB ⟨u, hu⟩ (hbdd t)
  exact (hs.1 hu).trans ((le_abs_self s).trans (h s t ht hs))

/-- F1 -/
theorem isSemialgebraic_lojasiewicz_aux {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (f g : MvPolynomial ι ℝ) :
    TauCeti.IsSemialgebraic {w : Fin 2 → ℝ | ∃ x : ι → ℝ, x ∈ T ∧ ∑ i, x i ^ 2 ≤ w 1 ∧
      1 ≤ w 1 * eval x g ^ 2 ∧ w 0 * eval x f ^ 2 = 1} := by
  have hA : TauCeti.IsSemialgebraic {z : Fin 2 ⊕ ι → ℝ | z ∘ Sum.inr ∈ T} :=
    hT.preimage_comp Sum.inr
  have hB : TauCeti.IsSemialgebraic
      {z : Fin 2 ⊕ ι → ℝ | ∑ i, z (Sum.inr i) ^ 2 ≤ z (Sum.inl 1)} := by
    convert TauCeti.isSemialgebraic_eval_le
      (∑ i, X (Sum.inr i) ^ 2 : MvPolynomial (Fin 2 ⊕ ι) ℝ) (X (Sum.inl 1)) using 1
    ext z; simp
  have hC : TauCeti.IsSemialgebraic
      {z : Fin 2 ⊕ ι → ℝ | 1 ≤ z (Sum.inl 1) * eval (z ∘ Sum.inr) g ^ 2} := by
    convert TauCeti.isSemialgebraic_eval_le (1 : MvPolynomial (Fin 2 ⊕ ι) ℝ)
      (X (Sum.inl 1) * rename Sum.inr g ^ 2) using 1
    ext z; simp [eval_rename]
  have hD : TauCeti.IsSemialgebraic
      {z : Fin 2 ⊕ ι → ℝ | z (Sum.inl 0) * eval (z ∘ Sum.inr) f ^ 2 = 1} := by
    convert TauCeti.isSemialgebraic_eval_eq (X (Sum.inl 0) * rename Sum.inr f ^ 2)
      (1 : MvPolynomial (Fin 2 ⊕ ι) ℝ) using 1
    ext z; simp [eval_rename]
  have h := (hA.inter (hB.inter (hC.inter hD))).setOf_exists_sumElim
  convert h using 1
  ext w
  simp [Set.mem_inter_iff]

/-- F2 -/
theorem isCompact_setOf_sq_sum_le {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)} (hT : IsClosed T)
    (g : MvPolynomial ι ℝ) (t : ℝ) :
    IsCompact {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * eval x g ^ 2} := by
  have hcl : IsClosed {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * eval x g ^ 2} := by
    have h := hT.inter ((isClosed_le (f := fun x : ι → ℝ => ∑ i, x i ^ 2) (g := fun _ => t)
      (continuous_finsetSum _ fun i _ => (continuous_apply i).pow 2) continuous_const).inter
      (isClosed_le (f := fun _ : ι → ℝ => (1 : ℝ)) (g := fun x => t * eval x g ^ 2) continuous_const
        (continuous_const.mul ((MvPolynomial.continuous_eval g).pow 2))))
    convert h using 1
    ext x; simp only [Set.mem_inter_iff, Set.mem_ofPred_eq]
  refine (isCompact_univ_pi fun _ : ι => isCompact_Icc (a := -(1 + |t|)) (b := 1 + |t|)).of_isClosed_subset
    hcl ?_
  rintro x ⟨-, hx, -⟩ i -
  have hxi : x i ^ 2 ≤ t :=
    (Finset.single_le_sum (fun j _ => sq_nonneg (x j)) (Finset.mem_univ i)).trans hx
  constructor <;> nlinarith [sq_nonneg (x i - 1), sq_nonneg (x i + 1), le_abs_self t]

/-- F3 (arithmetic) -/
theorem lojasiewicz_arith {c t₀ N F G : ℝ} {M : ℕ} (hc : 0 ≤ c) (ht₀ : 0 ≤ t₀) (hN : 0 ≤ N)
    (hF : F ≠ 0) (hG : G ≠ 0)
    (h : 1 / F ^ 2 ≤ c * (1 + max t₀ (max N (1 / G ^ 2))) ^ M) :
    G ^ (2 * (M + 1)) ≤ c * (1 + t₀) ^ (M + 1) * F ^ 2 * ((1 + N) * (1 + G ^ 2)) ^ (M + 1) := by
  have hG2 : 0 < G ^ 2 := by positivity
  have hF2 : 0 < F ^ 2 := by positivity
  set t := max t₀ (max N (1 / G ^ 2)) with ht
  have ht0 : 0 ≤ t := le_max_of_le_left ht₀
  have ht1 : 1 ≤ 1 + t := by linarith
  have ha : 0 ≤ 1 / G ^ 2 := by positivity
  have htle : t ≤ t₀ + N + 1 / G ^ 2 :=
    max_le (by linarith) (max_le (by linarith) (by linarith))
  have hkey : (1 + t) * G ^ 2 ≤ (1 + t₀) * ((1 + N) * (1 + G ^ 2)) := by
    have h1 : (1 + t) * G ^ 2 ≤ (1 + (t₀ + N + 1 / G ^ 2)) * G ^ 2 := by gcongr
    have h2 : (1 + (t₀ + N + 1 / G ^ 2)) * G ^ 2 = (1 + t₀ + N) * G ^ 2 + 1 := by
      field_simp; ring
    nlinarith [mul_nonneg ht₀ hN, mul_nonneg (mul_nonneg ht₀ hN) hG2.le, mul_nonneg ht₀ hG2.le,
      mul_nonneg hN hG2.le]
  calc G ^ (2 * (M + 1)) = (G ^ 2) ^ (M + 1) := by rw [pow_mul]
    _ = 1 / F ^ 2 * F ^ 2 * (G ^ 2) ^ (M + 1) := by field_simp
    _ ≤ c * (1 + t) ^ M * F ^ 2 * (G ^ 2) ^ (M + 1) := by gcongr
    _ ≤ c * (1 + t) ^ (M + 1) * F ^ 2 * (G ^ 2) ^ (M + 1) := by
        gcongr
        · exact Nat.le_succ M
    _ = c * F ^ 2 * ((1 + t) * G ^ 2) ^ (M + 1) := by rw [mul_pow]; ring
    _ ≤ c * F ^ 2 * ((1 + t₀) * ((1 + N) * (1 + G ^ 2))) ^ (M + 1) := by gcongr
    _ = c * (1 + t₀) ^ (M + 1) * F ^ 2 * ((1 + N) * (1 + G ^ 2)) ^ (M + 1) := by
        rw [mul_pow]; ring

/-- L1 -/
theorem exists_lojasiewicz {ι : Type*} [Fintype ι] {T : Set (ι → ℝ)}
    (hT : TauCeti.IsSemialgebraic T) (hTc : IsClosed T) (f g : MvPolynomial ι ℝ)
    (hfg : ∀ x ∈ T, eval x f = 0 → eval x g = 0) :
    ∃ (C : ℝ) (M : ℕ), 0 ≤ C ∧ ∀ x ∈ T,
      eval x g ^ (2 * (M + 1)) ≤
        C * eval x f ^ 2 * ((1 + ∑ i, x i ^ 2) * (1 + eval x g ^ 2)) ^ (M + 1) := by
  have hE := isSemialgebraic_lojasiewicz_aux hT f g
  have hbdd : ∀ t : ℝ, BddAbove {u : ℝ | ![u, t] ∈ {w : Fin 2 → ℝ | ∃ x : ι → ℝ, x ∈ T ∧
      ∑ i, x i ^ 2 ≤ w 1 ∧ 1 ≤ w 1 * eval x g ^ 2 ∧ w 0 * eval x f ^ 2 = 1}} := by
    intro t
    have hK := isCompact_setOf_sq_sum_le hTc g t
    have hne : ∀ x ∈ {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * eval x g ^ 2},
        eval x f ^ 2 ≠ 0 := by
      rintro x ⟨hxT, -, hx⟩ h0
      have hg0 : eval x g = 0 := hfg x hxT (by simpa using h0)
      rw [hg0] at hx
      norm_num at hx
    have hcont : ContinuousOn (fun x : ι → ℝ => (eval x f ^ 2)⁻¹)
        {x : ι → ℝ | x ∈ T ∧ ∑ i, x i ^ 2 ≤ t ∧ 1 ≤ t * eval x g ^ 2} :=
      (((MvPolynomial.continuous_eval f).pow 2).continuousOn).inv₀ hne
    obtain ⟨B, hB⟩ := hK.bddAbove_image hcont
    refine ⟨B, ?_⟩
    rintro u ⟨x, hxT, hx1, hx2, hx3⟩
    have hu : u = (eval x f ^ 2)⁻¹ := eq_inv_of_mul_eq_one_left hx3
    rw [hu]
    exact hB ⟨x, ⟨hxT, hx1, hx2⟩, rfl⟩
  obtain ⟨c, M, t₀, hc, ht₀, hgrow⟩ := exists_growth_of_bddAbove_fibres hE hbdd
  refine ⟨c * (1 + t₀) ^ (M + 1), M, by positivity, fun x hxT => ?_⟩
  have hN : 0 ≤ ∑ i, x i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  by_cases hG : eval x g = 0
  · rw [hG]
    have : (0 : ℝ) ^ (2 * (M + 1)) = 0 := by simp
    rw [this]
    positivity
  · have hF : eval x f ≠ 0 := fun h => hG (hfg x hxT h)
    refine lojasiewicz_arith hc ht₀ hN hF hG ?_
    refine hgrow _ _ (le_max_left _ _) ⟨x, hxT, ?_, ?_, ?_⟩
    · exact (le_max_left _ _).trans (le_max_right _ _)
    · have h1 : 1 / eval x g ^ 2 ≤ max t₀ (max (∑ i, x i ^ 2) (1 / eval x g ^ 2)) :=
        (le_max_right _ _).trans (le_max_right _ _)
      have hG2 : 0 < eval x g ^ 2 := by positivity
      calc (1 : ℝ) = 1 / eval x g ^ 2 * eval x g ^ 2 := by field_simp
        _ ≤ _ := by gcongr; exact h1
    · show 1 / eval x f ^ 2 * eval x f ^ 2 = 1
      field_simp

/-- L2-core -/
theorem exists_pos_between {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) {k : ℕ} (f : MvPolynomial ι ℝ)
    (g : Fin k → MvPolynomial ι ℝ)
    (hB : {x : ι → ℝ | eval x f = 0 ∧ ∀ j, 0 < eval x (g j)} ⊆ U) :
    ∃ q : MvPolynomial ι ℝ,
      {x : ι → ℝ | eval x f = 0 ∧ ∀ j, 0 < eval x (g j)} ⊆
        {x | 0 < eval x q ∧ ∀ j, 0 < eval x (g j)} ∧
      {x : ι → ℝ | 0 < eval x q ∧ ∀ j, 0 < eval x (g j)} ⊆ U := by
  have hTsa : TauCeti.IsSemialgebraic (Uᶜ ∩ ⋂ j, {x : ι → ℝ | 0 ≤ eval x (g j)}) :=
    hU.compl.inter (TauCeti.IsSemialgebraic.iInter fun j => TauCeti.isSemialgebraic_eval_nonneg (g j))
  have hTc : IsClosed (Uᶜ ∩ ⋂ j, {x : ι → ℝ | 0 ≤ eval x (g j)}) :=
    (isClosed_compl_iff.2 hUo).inter
      (isClosed_iInter fun j => isClosed_le continuous_const (MvPolynomial.continuous_eval (g j)))
  have hfg : ∀ x ∈ Uᶜ ∩ ⋂ j, {x : ι → ℝ | 0 ≤ eval x (g j)},
      eval x f = 0 → eval x (∏ j, g j) = 0 := by
    rintro x ⟨hxU, hx⟩ hf0
    by_contra hP
    rw [eval_prod] at hP
    have hP' := Finset.prod_ne_zero_iff.1 hP
    exact hxU (hB ⟨hf0, fun j =>
      lt_of_le_of_ne (Set.mem_iInter.1 hx j) (Ne.symm (hP' j (Finset.mem_univ j)))⟩)
  obtain ⟨C, M, hC, hL⟩ := exists_lojasiewicz hTsa hTc f (∏ j, g j) hfg
  refine ⟨(∏ j, g j) ^ (2 * (M + 1)) -
    MvPolynomial.C C * f ^ 2 * ((1 + ∑ i, X i ^ 2) * (1 + (∏ j, g j) ^ 2)) ^ (M + 1), ?_, ?_⟩
  · rintro x ⟨hf0, hg⟩
    refine ⟨?_, hg⟩
    have hP : 0 < eval x (∏ j, g j) := by
      rw [eval_prod]; exact Finset.prod_pos fun j _ => hg j
    simp only [map_sub, map_mul, map_pow, eval_C, hf0]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero, zero_mul, sub_zero]
    positivity
  · rintro x ⟨hq, hg⟩
    by_contra hxU
    have hxT : x ∈ Uᶜ ∩ ⋂ j, {x : ι → ℝ | 0 ≤ eval x (g j)} :=
      ⟨hxU, Set.mem_iInter.2 fun j => (hg j).le⟩
    have h := hL x hxT
    simp only [map_sub, map_mul, map_pow, map_add, map_one, map_sum, eval_C, eval_X] at hq
    linarith

/-- cells -/
theorem exists_setOf_sign_eq_eq {ι : Type*} {m : ℕ} (p : Fin m → MvPolynomial ι ℝ)
    (ε : Fin m → SignType) :
    ∃ (f : MvPolynomial ι ℝ) (g : Fin m → MvPolynomial ι ℝ),
      {x : ι → ℝ | ∀ i, SignType.sign (eval x (p i)) = ε i} =
        {x | eval x f = 0 ∧ ∀ j, 0 < eval x (g j)} := by
  classical
  refine ⟨∑ i, if ε i = 0 then p i ^ 2 else 0,
    fun i => if ε i = 0 then 1 else if ε i = 1 then p i else -p i, ?_⟩
  ext x
  have hsum : eval x (∑ i, if ε i = 0 then p i ^ 2 else 0) = 0 ↔
      ∀ i, ε i = 0 → eval x (p i) = 0 := by
    rw [map_sum, Finset.sum_eq_zero_iff_of_nonneg]
    · refine forall_congr' fun i => ?_
      by_cases h : ε i = 0 <;> simp [h]
    · intro i _
      by_cases h : ε i = 0 <;> simp [h, sq_nonneg]
  simp only [Set.mem_ofPred_eq, hsum, ← forall_and]
  refine forall_congr' fun i => ?_
  rcases h : ε i with _ | _ | _
  · simp [sign_eq_zero_iff]
  · simp [sign_eq_neg_one_iff]
  · simp [sign_eq_one_iff]

/-- L2 -/
theorem exists_eq_iUnion_iInter_pos {ι : Type*} [Fintype ι] {U : Set (ι → ℝ)}
    (hU : TauCeti.IsSemialgebraic U) (hUo : IsOpen U) :
    ∃ (I J : ℕ) (Q : Fin I → Fin J → MvPolynomial ι ℝ),
      U = ⋃ i, ⋂ j, {x | 0 < eval x (Q i j)} := by
  classical
  obtain ⟨m, p, Φ, hUeq⟩ := hU.exists_eq_setOf_sign_eval
  have key : ∀ ε : {ε : Fin m → SignType // Φ ε}, ∃ Q : Fin (m + 1) → MvPolynomial ι ℝ,
      {x : ι → ℝ | ∀ i, SignType.sign (eval x (p i)) = ε.1 i} ⊆ ⋂ j, {x | 0 < eval x (Q j)} ∧
      (⋂ j, {x : ι → ℝ | 0 < eval x (Q j)}) ⊆ U := by
    rintro ⟨ε, hε⟩
    obtain ⟨f, g, hcell⟩ := exists_setOf_sign_eq_eq p ε
    have hsub : {x : ι → ℝ | eval x f = 0 ∧ ∀ j, 0 < eval x (g j)} ⊆ U := by
      rw [← hcell, hUeq]
      intro x hx
      have hx' : (fun i => SignType.sign (eval x (p i))) = ε := funext hx
      show Φ fun i => SignType.sign (eval x (p i))
      rw [hx']; exact hε
    obtain ⟨q, h1, h2⟩ := exists_pos_between hU hUo f g hsub
    refine ⟨Fin.cons q g, ?_, ?_⟩
    · rw [hcell]
      intro x hx
      obtain ⟨hq, hg⟩ := h1 hx
      refine Set.mem_iInter.2 (Fin.cases ?_ ?_)
      · simpa using hq
      · intro j; simpa using hg j
    · intro x hx
      rw [Set.mem_iInter] at hx
      refine h2 ⟨by simpa using hx 0, fun j => by simpa using hx j.succ⟩
  choose Q hQ1 hQ2 using key
  refine ⟨Nat.card {ε : Fin m → SignType // Φ ε}, m + 1,
    fun i => Q ((Finite.equivFin {ε : Fin m → SignType // Φ ε}).symm i), ?_⟩
  rw [(Finite.equivFin {ε : Fin m → SignType // Φ ε}).symm.surjective.iUnion_comp
    (fun ε => ⋂ j, {x : ι → ℝ | 0 < eval x (Q ε j)})]
  apply Set.Subset.antisymm
  · intro x hx
    have hΦ : Φ fun i => SignType.sign (eval x (p i)) := by rw [hUeq] at hx; exact hx
    exact Set.mem_iUnion.2 ⟨⟨_, hΦ⟩, hQ1 ⟨_, hΦ⟩ (fun i => rfl)⟩
  · exact Set.iUnion_subset fun ε => hQ2 ε

/-- L3 set identity -/
theorem compl_iUnion_iInter_pos {ι : Type*} {I J : ℕ} (Q : Fin I → Fin J → MvPolynomial ι ℝ) :
    (⋃ i, ⋂ j, {x : ι → ℝ | 0 < eval x (Q i j)})ᶜ =
      ⋃ k : Fin (J ^ I), ⋂ i : Fin I,
        {x | 0 ≤ eval x (-Q i (finFunctionFinEquiv.symm k i))} := by
  ext x
  simp only [Set.mem_compl_iff, Set.mem_iUnion, Set.mem_iInter, Set.mem_ofPred_eq, not_exists,
    not_forall, not_lt, map_neg, neg_nonneg]
  constructor
  · intro h
    choose φ hφ using h
    exact ⟨finFunctionFinEquiv φ, fun i => by simpa using hφ i⟩
  · rintro ⟨k, hk⟩ i
    exact ⟨_, hk i⟩

/-- interface -/
theorem exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)} := by
  intro hs hc
  obtain ⟨I, J, Q, hQ⟩ := exists_eq_iUnion_iInter_pos hs.compl hc.isOpen_compl
  refine ⟨J ^ I, I, fun k i => -Q i (finFunctionFinEquiv.symm k i), ?_⟩
  rw [← compl_iUnion_iInter_pos Q, ← hQ, compl_compl]

end Scratch

#print axioms Scratch.exists_eq_iUnion_iInter_nonneg
```
