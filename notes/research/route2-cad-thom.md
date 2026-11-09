# Route 2: cylindrical decomposition, Thom's lemma, and other routes to the finiteness theorem

Research agent R2, Phase 3a. Pins: Lean `v4.36.0-rc2`, Mathlib `1b1ccf4b`, TauCeti `2c9b12be`.
No Lean code of the library was written. Every Lean name quoted below was found by grep in the checkouts at
these pins; the names of §7.3 were also resolved by `lake env lean` on a scratch file (see §11).

## 0. Verdict in one page

1. **The hypothesis as stated is false.** "Take a CAD adapted to a family closed under derivation; the closure of a
   cell is obtained by relaxing its strict sign conditions" fails in several variables:
   * for families closed under `∂/∂t` in the fibre variable only (`{xt, x}`, §3 E2);
   * for families closed under **all** partial derivatives (`g = y(2x² + 3xy + 2y²)`, §3 E3, found by computer
     search and verified by hand);
   * for families that are monic and derivative-closed in the fibre variable (Whitney umbrella, §3 E4);
   * and TauCeti's CAD cells have no sign-condition description and no closure control at all (§7.1): a CAD that
     `TauCeti.exists_isCAD_signInvariant` may return for `{X₀·X₁}` has a cell whose closure is not a union of cells
     (§3 E6).
2. **A repaired statement is true, and it is much cheaper than the textbook "stratifying family" theorem.**
   Theorem C (§4): if `G ⊆ ℝ[x'][t]` is finite, every member has a nonzero *constant* leading coefficient in `t`,
   and `G` is closed under `∂/∂t` up to zero, then for every sign assignment `ε`

       closure A_ε(G) = Ā_ε(G) ∩ π⁻¹( closure π(A_ε(G)) ),

   where `A_ε` is the sign-condition set, `Ā_ε` the relaxed one and `π` forgets `t`. The proof uses only the
   one-variable Thom lemma in a "relaxed endpoints" form (Lemma T, §2), a Cauchy root bound and compactness of
   `[-M, M]`. No CAD, no continuity of roots, no connectedness, no subresultants.
3. **The finiteness theorem follows by induction on the number of variables** (§5): put the defining polynomials in
   `t`-monic form by a polynomial automorphism (Mathlib already has it:
   `NoetherNormalization.varChange_leadingCoeff_isUnit`), close under `∂/∂t`, apply Theorem C, and apply the induction
   hypothesis to the closed semialgebraic sets `closure π(A_ε)` (Tarski–Seidenberg and closure from TauCeti).
   The route is **correct and complete**; every step is proved in this report.
4. **What TauCeti contributes**: sign normal form, Tarski–Seidenberg (`HasSemialgebraicProjections ℝ`, itself proved
   through CAD), `IsSemialgebraic.closure`. Its CAD cells, delineations, Thom encodings and dimension theory are
   *not* used. Missing and to be written: Lemma T, Theorem C, bookkeeping for finite unions of basic closed sets.
5. **Cost**: about 1000–1300 lines of Lean in 10 units, largest unit L (§8). Independent of G1–G4.
6. **A change of coordinates is unavoidable for Theorem C** (counterexamples E2, E5) but costs about 100 lines
   because the finiteness theorem is invariant under polynomial automorphisms and Mathlib has the automorphism.
7. Other routes (§9): the literal CAD-cell route (true statement exists, XL, not recommended); Łojasiewicz
   (PLAN §4.4; viable, studied by R1); real spectrum (circular in the source checked, or needs transfer to real closed
   extensions: not viable); induction on dimension (no complete argument known to me; TauCeti lacks
   `dim (closure S \ S) < dim S`).

## 1. Notation and target

`sign : ℝ → {-1, 0, 1}` (`SignType.sign`). For a family `F = (f_k)_{k∈κ}` of polynomials on `ℝ^m` and
`ε : κ → {-1,0,1}`:

* cell `A_ε(F) = {x | ∀ k, sign f_k(x) = ε_k}`;
* relaxed cell `Ā_ε(F) = {x | ∀ k, f_k(x) = 0 ∨ sign f_k(x) = ε_k}`.

`Ā_ε(F)` is a *basic closed* set: the condition for `k` is `f_k ≥ 0` if `ε_k = 1`, `-f_k ≥ 0` if `ε_k = -1`, and
`f_k ≥ 0 ∧ -f_k ≥ 0` if `ε_k = 0`. Always `A_ε ⊆ closure A_ε ⊆ Ā_ε`.

`BC(S)` abbreviates "`S` is a finite union of basic closed sets", i.e. the conclusion of the target

```lean
theorem Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}
```

Coordinates follow TauCeti: in `Fin (n+1) → ℝ` the fibre variable `t` is coordinate `0`, the base point is
`x' = Fin.tail y`, and `π = Fin.tail`. A polynomial `g` in `n+1` variables is read as a polynomial in `t` with
coefficients in `ℝ[x']` through `MvPolynomial.finSuccEquiv ℝ n`; its fibre at `x'` is the univariate polynomial
`g_{x'} = (finSuccEquiv ℝ n g).map (eval x')`, and `g(t, x') = g_{x'}(t)`.

## 2. Thom's lemma in one variable

A family `(P_k)_{k∈κ}` in `ℝ[t]` is *closed under derivation up to zero* if for every `k`, `P_k' = 0` or
`P_k' = P_l` for some `l`. (Indexed families: repetitions are allowed, which matters after specialization.)

### Lemma T (relaxed endpoints)

Let `(P_k)_{k∈κ}` (any index set) be nonzero polynomials, closed under derivation up to zero, and
`ε : κ → {-1,0,1}`. Let `a < b` with `a, b ∈ R̄ := {t | ∀ k, P_k(t) = 0 ∨ sign P_k(t) = ε_k}`. Then
`(a, b) ⊆ R° := {t | ∀ k, sign P_k(t) = ε_k}`.

*Proof.* By strong induction on `d`, we prove: for every `k` with `deg P_k = d` and every `t ∈ (a,b)`,
`sign P_k(t) = ε_k`.

* `d = 0`: `P_k = c`, a nonzero constant. From `a ∈ R̄`: `c = 0` or `sign c = ε_k`; hence `sign c = ε_k`, at
  every `t`.
* `d ≥ 1`: `P_k' ≠ 0` (characteristic 0), so `P_k' = P_l` with `deg P_l = d - 1`. By induction
  `sign P_l(t) = ε_l` for all `t ∈ (a,b)`. If `ε_l = 0`, `P_l` vanishes on the infinite set `(a,b)`, so `P_l = 0`,
  excluded. So `P_k'` has a constant strict sign on `(a,b) = interior [a,b]`, and `P_k` is continuous on `[a,b]`:
  `P_k` is strictly monotone on `[a,b]`. Say `ε_l = 1` (increasing; the other case is symmetric):
  `P_k(a) < P_k(t) < P_k(b)` for `t ∈ (a,b)`.
  - `ε_k = 1`: `a ∈ R̄` gives `P_k(a) ≥ 0`, so `P_k(t) > 0`.
  - `ε_k = -1`: `b ∈ R̄` gives `P_k(b) ≤ 0`, so `P_k(t) < 0`.
  - `ε_k = 0`: `a, b ∈ R̄` give `P_k(a) = 0 = P_k(b)`, contradicting `P_k(a) < P_k(b)`; the case is void. ∎

### Corollary (Thom's lemma, classical form; cf. Bochnak–Coste–Roy Prop. 2.5.4, Basu–Pollack–Roy Prop. 2.27)

With the hypotheses of Lemma T and `κ` finite:

1. `R°` is empty, a point, or an open interval.
2. If `R° ≠ ∅` then `closure R° = R̄`.
3. If `R° = ∅` then `R̄` has at most one point.

*Proof.* `R° ⊆ R̄`, and `R̄` is closed.
(3) Two points of `R̄` would give a nonempty `(a,b) ⊆ R°`.
(2) `closure R° ⊆ R̄`. Conversely let `c ∈ R̄`. If `R̄ = {c}` then `R° = {c}`. Otherwise pick `c' ∈ R̄`,
`c' ≠ c`; the open interval between them lies in `R°` and has `c` in its closure.
(1) `R°` is order-convex by Lemma T. If it has two points it is infinite, so no `ε_k` is `0` (a nonzero polynomial
has finitely many roots), so `R°` is open (finitely many strict inequalities). ∎

Only Lemma T is used below. Two remarks that matter for the several-variable case:

* **Nonzero is needed.** With a zero member `P_k = 0` and `ε_k ≠ 0`, `R° = ∅` while `R̄` can be an interval.
* **(2) needs `R° ≠ ∅`.** For `(t², 2t, 2)` and `ε = (-1, 1, 1)`: `R° = ∅`, `R̄ = {0}`. So "the closure of a cell
  is the relaxed cell" is false for empty cells even in one variable; a relaxed cell can contain a "ghost" point.

## 3. What fails in several variables: explicit counterexamples

All verified by hand; E3 was found by a computer search (§11) and then verified by hand.

**E1 (one variable, not derivative-closed).** `F = {x²(x-1)}`, `ε = 1`: `A = (1, ∞)`, `Ā = {0} ∪ [1, ∞)`.

**E2 (closed under `∂/∂t` only; nullification).** `F = {xt, x}` on `ℝ²` (`∂_t(xt) = x`, `∂_t x = 0`).
`ε = (0, 1)`: `A = {t = 0, x > 0}`, `closure A = {t = 0, x ≥ 0}`, but
`Ā = {xt = 0, x ≥ 0} = {t = 0, x ≥ 0} ∪ {x = 0}`: the whole `t`-axis is added. Mechanism: over the base point
`x = 0` the fibre polynomial of `xt` is the zero polynomial.
Also `π(A) = (0, ∞)`, so `Ā ∩ π⁻¹(closure π(A)) = Ā`: the formula of Theorem C fails without monicity.

**E3 (closed under all partial derivatives).** `g = 2x²y + 3xy² + 2y³ = y(2x² + 3xy + 2y²)` on `ℝ²`,
`F` = all nonzero partial derivatives of `g`:

    g,  g_x = y(4x + 3y),  g_y = 2x² + 6xy + 6y²,  g_xx = 4y,  g_xy = 4x + 6y,  g_yy = 6x + 12y,  4, 6, 12.

`2x² + 3xy + 2y²` and `g_y` are positive definite (discriminants `9 - 16`, `36 - 48`). Take
`ε = (g: 1, g_x: -1, g_y: 1, g_xx: 1, g_xy: 1, g_yy: 1, constants: 1)`. Then

    A = {y > 0, 4x + 3y < 0, 2x + 3y > 0, x + 2y > 0} = {y > 0, -3y/2 < x < -3y/4}

(nonempty: `(-1, 1)` gives values `1, -1, 2, 4, 2, 6`), an open cone with
`closure A = {y ≥ 0, -3y/2 ≤ x ≤ -3y/4}`, which meets `{y = 0}` only at the origin. At `p = (1, 0)` the values are
`g = 0, g_x = 0, g_y = 2, g_xx = 0, g_xy = 4, g_yy = 6`, all compatible with the relaxation of `ε`. So
`p ∈ Ā \ closure A`; in fact `Ā = closure A ∪ {(x, 0) | x ≥ 0}`. Mechanism: `g`, `g_x`, `g_xx` vanish identically
on the line `y = 0`, i.e. in the direction `x` the family is nullified over `y = 0`. Closure under all partial
derivatives does not help.

**E4 (monic and `∂/∂t`-closed, Whitney umbrella).** On `ℝ³` with fibre variable `x` and base `(y, z)`:
`G = {x² - zy², 2x, 2}`, `ε = (0, 1, 1)`. `A = {x² = zy², x > 0} = {x = |y|√z, y ≠ 0, z > 0}` (two sheets: cells of
such families need not be connected). `closure A = {x = |y|√z, z ≥ 0}`, but
`Ā = {x² = zy², x ≥ 0} = closure A ∪ {x = y = 0, z < 0}`: the handle of the umbrella. So monic and derivative-closed
in the fibre variable is still not enough for `closure A = Ā`; here `π(A) = {y ≠ 0, z > 0}` and
`Ā ∩ π⁻¹(closure π(A)) = Ā ∩ {z ≥ 0} = closure A`, as Theorem C predicts. The base must be controlled.

**E5 (degree drop without nullification of the given polynomial).**
`g = t² - (2/3)x t³ + (1/6)x² t⁴`, `G = {g, ∂_t g, ∂_t² g, ∂_t³ g, ∂_t⁴ g, x}` with

    ∂_t g = 2t(1 - xt + x²t²/3),  ∂_t² g = 2(1 - xt)²,  ∂_t³ g = -4x(1 - xt),  ∂_t⁴ g = 4x².

`G` is closed under `∂_t` up to zero. With `u = xt`: `1 - u + u²/3 > 0` and `1 - (2/3)u + u²/6 > 0` for all `u`
(discriminants `1 - 4/3`, `4/9 - 2/3`). For `ε = (1,1,1,1,1,1)`:
`A = {x > 0, t ≠ 0, t > 0, xt ≠ 1, x(xt - 1) > 0} = {x > 0, t > 1/x}`, which is closed in `ℝ²` and misses `{x = 0}`.
But at `x = 0` the relaxed conditions read `t² ≥ 0, 2t ≥ 0, 2 ≥ 0, 0 ≥ 0, 0 ≥ 0, 0 ≥ 0`, so
`Ā ∩ {x = 0} = {t ≥ 0}`, and `0 ∈ closure π(A) = [0, ∞)`. Theorem C's formula fails. Here `g(0, t) = t²` is not
nullified, but its degree drops, so its higher `t`-derivatives are nullified and the roots `1/x` escape to infinity.

**E6 (a CAD in TauCeti's sense whose cell closures are not unions of cells).** Let `𝒟` be the CAD of `ℝ¹` with cells
`{x < 0}, {0}, {x > 0}` (`TauCeti.isCAD_stackCells_const` with `c = ![0]`). Over `{x < 0}` and `{x > 0}` take the
stack with the single section `θ = 0`, over `{0}` the empty stack (`TauCeti.isSemialgebraicStack_eval`).
`TauCeti.IsCAD.succ` gives a CAD of `ℝ²` (coordinates `(t, x)`) with 7 cells, on each of which `X₀·X₁` is
sign-invariant; the cell over `{0}` is the whole line `{x = 0}`. This is the decomposition one gets from the roots
of `{X₀X₁}` and it satisfies the conclusion of `TauCeti.exists_isCAD_signInvariant` for `F = {X₀X₁}`. The cell
`E = {t = 0, x > 0}` has `closure E = E ∪ {(0,0)}`, and `{(0,0)}` is a proper subset of the cell `{x = 0}`. So the
closure of a cell is not a union of cells, and `E = A_{(0,1)}({xt, x})` is the cell of E2.

**E7 (ghost points).** `(t², 2t, 2)`, `ε = (-1, 1, 1)` (§2): empty cell, nonempty relaxed cell.

Consequences. (a) A statement "closure = relaxed" must exclude empty cells or carry a correction term.
(b) The fibre family must not be nullified, and must not drop degree, over the closure of the base cell (E2, E5).
(c) The base must be controlled (E4). (d) Closure under more derivatives does not replace (b), (c) (E3).

## 4. The repair: Theorem C (closure formula)

Call `g ∈ ℝ[x'][t]` *`t`-monic up to a constant* if its leading coefficient as a polynomial in `t` is a nonzero
constant `a ∈ ℝ` (degree `0` allowed: then `g` is a nonzero constant).

### Theorem C

Let `G = (g_k)_{k∈κ}`, `κ` finite, be polynomials on `ℝ^{n+1} = ℝ_t × ℝ^n_{x'}` such that

* (M) every `g_k` is `t`-monic up to a constant;
* (D) for every `k`: `∂g_k/∂t = 0` or `∂g_k/∂t = g_l` for some `l`.

Then for every `ε : κ → {-1,0,1}`, with `A = A_ε(G)`, `Ā = Ā_ε(G)`, `π(t, x') = x'`:

    closure A = Ā ∩ π⁻¹(closure π(A)).

(For `A = ∅` both sides are empty, so no nonemptiness hypothesis is needed; compare E7.)

*Proof.* `⊆`: `Ā` is closed and contains `A`; `π` is continuous, so `π(closure A) ⊆ closure π(A)`.

`⊇`: let `(c, p') ∈ Ā` with `p' ∈ closure π(A)`. Put `P_k := (g_k)_{p'} ∈ ℝ[t]`. By (M) the leading coefficient
survives specialization: `P_k ≠ 0`, `deg P_k = deg_t g_k`. Specialization commutes with `d/dt`, so by (D) the family
`(P_k)` is closed under derivation up to zero. Let

    R̄ := {t | (t, p') ∈ Ā} = {t | ∀ k, P_k(t) = 0 ∨ sign P_k(t) = ε_k},      T := {t | (t, p') ∈ closure A}.

`c ∈ R̄`, `T ⊆ R̄` (as `closure A ⊆ Ā`), and we must show `c ∈ T`.

*Case 1: `R̄` contains some `c' ≠ c`.* Let `a < b` be `c, c'` in order. By Lemma T, for every `t ∈ (a,b)` and every
`k`, `sign P_k(t) = ε_k`, i.e. `(t, p') ∈ A`. The map `t ↦ (t, p')` is continuous and `c ∈ closure (a,b)`, hence
`(c, p') ∈ closure A`.

*Case 2: `R̄ = {c}`.* It suffices to show `T ≠ ∅`, because `T ⊆ R̄ = {c}`.

(i) *Uniform root bound.* Write `g_k = a_k t^{d_k} + Σ_{j<d_k} c_{kj}(x') t^j` with `a_k ≠ 0` constant. The
`c_{kj}` are continuous, so there are a neighbourhood `U` of `p'` and `C` with `|c_{kj}(x')| ≤ C` on `U` for all
`k, j` (`κ` finite). By Cauchy's bound every real root `t` of `(g_k)_{x'}`, `x' ∈ U`, has
`|t| < M := 1 + C / min_k |a_k|`.

(ii) *Bounded representatives.* Let `x' ∈ U ∩ π(A)` and `(t, x') ∈ A`. If `t > M`, no `(g_k)_{x'}` has a root in
`[M, t]`, so each has the same sign at `M` and at `t` (intermediate value theorem), so `(M, x') ∈ A`; similarly
`(-M, x') ∈ A` if `t < -M`. Hence every `x' ∈ U ∩ π(A)` has some `t' ∈ [-M, M]` with `(t', x') ∈ A`.

(iii) *Compactness.* Choose `x'_j ∈ π(A)`, `x'_j → p'` (first countability); for large `j`, `x'_j ∈ U`; choose
`t_j ∈ [-M, M]` with `(t_j, x'_j) ∈ A`. A subsequence of `(t_j)` converges to some `c₀ ∈ [-M, M]`, and then
`(t_j, x'_j) → (c₀, p')` along it. So `c₀ ∈ T`. ∎

Where each hypothesis is used: (D) and nonvanishing of fibres in Lemma T; (M) for nonvanishing of the fibres at
`p'`, which may lie outside `π(A)`, and for the root bound near `p'`; `p' ∈ closure π(A)` only in Case 2.

### Necessity of the hypotheses, and the role of a change of coordinates

* Without (M): E2 (a member nullified over `closure π(A) \ π(A)`) and E5 (degree drop: the roots escape to infinity
  and the top derivatives are nullified) violate the formula. What the proof really needs is: *for every
  `p' ∈ closure π(A)` no `g_k` has zero fibre at `p'` and the degrees do not drop at `p'`*. For a `∂_t`-closed family
  these two requirements are the same (the top `t`-derivative of `g_k` is `d_k!` times its leading coefficient), and
  the practical way to guarantee them at unknown points `p'` is (M).
* Without the factor `π⁻¹(closure π(A))`: E4.
* Without (D): E1.
* (M) cannot be obtained in given coordinates (E2: `xt` is not `t`-monic and no enlargement of the family repairs the
  nullification). It is obtained after an automorphism of the polynomial ring:
  - *linear*: for nonzero `f_1, …, f_m` of total degrees `d_i` with top homogeneous parts `f_i^{top}`, the
    polynomial `c ↦ ∏_i f_i^{top}(1, c)` is nonzero (dehomogenization is injective on homogeneous polynomials of a
    fixed degree), so some `c ∈ ℝ^n` makes all of them nonzero, and `f_i(t, x' + c t)` has `t`-degree `d_i` with
    constant leading coefficient `f_i^{top}(1, c)`;
  - *triangular (Nagata)*: `x_i ↦ x_i + t^{r_i}`. This is in Mathlib:
    `NoetherNormalization.varChange f : MvPolynomial (Fin (n+1)) k ≃ₐ[k] MvPolynomial (Fin (n+1)) k` and
    `NoetherNormalization.varChange_leadingCoeff_isUnit (fne : f ≠ 0) :
    IsUnit (finSuccEquiv k n (varChange f f)).leadingCoeff`. Applied to `f = ∏ f_i` it makes every `f_i` monic up to
    a constant (the leading coefficient of a product is the product of the leading coefficients, and a factor of a
    unit is a unit).
* The finiteness theorem and "closure = relaxed" statements are invariant under polynomial automorphisms `e`: with
  `φ_e(x) := (eval x (e X_i))_i` one has `eval x (e p) = eval (φ_e x) p`, `φ_e` is continuous and
  `φ_e ∘ φ_{e⁻¹} = id`. So the change of coordinates is unavoidable for Theorem C but costs only the transport
  lemma M2 of §8 (about 100 lines with M1).

A heuristic numerical test of the formula on random `t`-monic families in two variables (300 random `g` of degree
2 to 4 in `t`, 7 base points each) found no violation; the same harness reports violations for non-monic families.
This is a sanity check, not evidence used in the proof.

## 5. The finiteness theorem from Theorem C

**Theorem FT.** For every `n` and every closed semialgebraic `S ⊆ ℝ^n`: `BC(S)`.

*Proof.* Induction on `n`. `n = 0`: `ℝ⁰` is a point, `S = ∅` (empty union) or `S = ℝ⁰` (one empty intersection).

Step `n → n+1`. Let `S ⊆ ℝ^{n+1}` be closed and semialgebraic.

1. *Sign normal form.* `S = {x | Φ((sign f_i(x))_{i<m})}` for polynomials `f_i` and a predicate `Φ`
   (`TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`). Replacing each zero `f_i` by the constant `1` and adjusting
   `Φ` (`Φ'(σ) := Φ(i ↦ if f_i = 0 then 0 else σ_i)`), assume all `f_i ≠ 0`.
2. *Monic form.* Let `e` be an automorphism with every `g_i := e(f_i)` `t`-monic up to a constant (§4). Put
   `S' := φ_e⁻¹(S) = {x | Φ((sign g_i(x))_i)}`. `S'` is closed (`φ_e` continuous). If `S' = ⋃_a ⋂_b {P_ab ≥ 0}` then
   `S = φ_{e⁻¹}⁻¹(S') = ⋃_a ⋂_b {e⁻¹(P_ab) ≥ 0}`. So it suffices to prove `BC(S')`.
3. *Derivative closure.* Let `G` be the family of all nonzero iterated `t`-derivatives `∂_t^j g_i`. It is finite,
   contains the `g_i`, satisfies (D) by construction, and (M): if `q` has `t`-degree `d ≥ 1` and leading coefficient
   the constant `a ≠ 0`, then `∂_t q` has leading coefficient `d·a ≠ 0`; if `d = 0`, `∂_t q = 0` is not in `G`.
4. *`S'` is a union of `G`-cells.* The `G`-sign vector `ε(x)` of a point determines the signs of the `g_i`, hence
   whether `x ∈ S'`. With `E := {ε | the g_i-part of ε satisfies Φ}` (finite): `S' = ⋃_{ε∈E} A_ε(G)`.
5. *Closedness.* `S'` closed gives `closure A_ε(G) ⊆ S'` for `ε ∈ E`, so `S' = ⋃_{ε∈E} closure A_ε(G)`.
6. *Theorem C.* `closure A_ε(G) = Ā_ε(G) ∩ π⁻¹(closure π(A_ε(G)))`.
7. *Induction hypothesis.* `A_ε(G)` is semialgebraic, so `π(A_ε(G)) ⊆ ℝ^n` is semialgebraic (Tarski–Seidenberg), so
   its closure is semialgebraic (`TauCeti.IsSemialgebraic.closure`) and closed: `BC(closure π(A_ε(G)))`. Pulling the
   polynomials back along `π` (rename variables) gives `BC(π⁻¹(closure π(A_ε(G))))`.
8. *Assembly.* `Ā_ε(G)` is basic closed; an intersection of two finite unions of basic closed sets is one; a finite
   union of such is one. Hence `BC(S')`. ∎

For a finite index type `ι`, transport along `ι ≃ Fin n` (`Fintype.equivFin`, `MvPolynomial.rename`,
`TauCeti.isSemialgebraic_preimage_comp_equiv`).

Remarks.

* The proof gives `S' = ⋃_{ε∈E} (Ā_ε(G) ∩ π⁻¹(closure π(A_ε(G))))`: the recursion is on the closures of the
  projected cells, not on a cell decomposition of the base.
* Compactness of `[-M, M]` and first countability are used, so the argument is specific to `ℝ` (the target is over
  `ℝ`). Over a general real closed field Case 2 would need a different argument.

## 6. Optional strengthening: Thom families and the frontier condition (not needed for the target)

Say a finite family `F` on `ℝ^m` *has property (T)* if `closure A_ε(F) = Ā_ε(F)` for every `ε` with
`A_ε(F) ≠ ∅`. Then the closure of every nonempty cell is a union of cells (those of the specializations of `ε`),
i.e. the cells satisfy the frontier condition, and every closed union of cells is a finite union of relaxed cells.
Property (T) is invariant under polynomial automorphisms but **not** monotone in `F` (`{1}` has it, `{1, x²(x-1)}`
does not).

**Theorem C′ (relative form).** Under (M), (D), for every `B ⊆ π(A_ε(G))`:
`closure (A_ε(G) ∩ π⁻¹B) = Ā_ε(G) ∩ π⁻¹(closure B)`.
*Proof.* As for Theorem C with `x'_j ∈ B`; in Case 1, `R°` is infinite so all `ε_k ≠ 0`, hence for `t ∈ (a,b)` the
set `U_t = {x' | ∀ k, sign g_k(t, x') = ε_k}` is an open neighbourhood of `p'`, it meets `B` in points converging to
`p'`, and `(t, x') ∈ A_ε(G) ∩ π⁻¹B` for those points. ∎

**Theorem (Thom families exist).** Every finite `F₀ ⊆ ℝ[x_1..x_m]` is contained in a finite family with (T).
*Proof.* Induction on `m`. Make the nonzero members of `F₀` `t`-monic by an automorphism `e`; let `G` be the
`∂_t`-closure of `e(F₀)`; each `π(A_ε(G))` is semialgebraic, hence a sign condition on a finite `H_ε ⊆ ℝ[x']`; let
`K ⊇ ⋃_ε H_ε` have (T) in `m - 1` variables; then each `π(A_ε(G))` is a union of `K`-cells. A nonempty cell of
`G ∪ K` is `A_ε(G) ∩ π⁻¹B` with `B = A_δ(K) ≠ ∅` meeting, hence contained in, `π(A_ε(G))`; by Theorem C′ and (T)
for `K` its closure is `Ā_ε(G) ∩ π⁻¹(Ā_δ(K))`, the relaxed cell. So `G ∪ K` has (T); pull back by `e⁻¹`
(`φ_e` is a homeomorphism with inverse `φ_{e⁻¹}`). Zero members of `F₀` can be added back: a zero polynomial
changes neither the nonempty cells nor their relaxations. ∎

This is the content of the textbook "generalized Thom lemma / stratifying families" (BCR §9.1, Coste's notes) minus
connectedness and smoothness of the cells. It costs about 250 more lines than §5 (the relative form, the
homeomorphism transport, sign normal forms of the projections) and gives nothing more for the target.

## 7. Inventory

### 7.1 TauCeti (`.lake/packages/TauCeti/TauCeti/`, commit `2c9b12be`)

| question of the brief | answer | evidence |
|---|---|---|
| CAD cells with explicit sign descriptions? | **No.** | `Geometry/RealAlgebraic/CAD/Basic.lean:150` `inductive IsCAD : (n : ℕ) → Set (Set (Fin n → ℝ)) → Prop`; cells are sections/sectors of continuous functions with `IsSemialgebraic` images (`structure IsSemialgebraicStack`, `:97`). No polynomial description is stored. |
| adapted to a given finite family? | **Yes**, sign-invariance only. | `CAD/Existence.lean:63` `theorem exists_isCAD_signInvariant (F : Finset (MvPolynomial (Fin n) ℝ)) : ∃ 𝒞, IsCAD n 𝒞 ∧ ∀ f ∈ F, ∀ E ∈ 𝒞, SignInvariant (fun x ↦ eval x f) E`; `:90` `IsSemialgebraic.exists_isCAD_subset_or_disjoint`. Variants with analytic cells: `CAD/Lazard/Existence.lean:65` `exists_isCAD_lazardValuationReindex_eq`, `CAD/McCallum/*`. |
| control of closures / frontier condition? | **None.** | Topological facts about cells are only: `IsCAD.isConnected` (`:203`), `IsCAD.isLocallyClosed` (`:213`), `IsCAD.exists_injective_isOpenEmbedding_comp` (`:234`), `IsCAD.exists_continuous_cons_mem`. E6 shows the frontier condition fails for CADs satisfying the existence theorem's conclusion. |
| multivariate Thom lemma? | **Only fibrewise, exact signs, no closure.** | `Geometry/RealAlgebraic/Stack/Delineation.lean:426` `Delineation.root_notMem_uIcc_of_sign_eval_eq`, `:454` `mk_mem_sectionSet_iff_of_sign_eval_eq`, `:467` `mk_mem_sectorSet_iff_of_sign_eval_eq` (hypothesis `hder : ∀ k, derivative (P k x) = 0 ∨ ∃ l, P l x = derivative (P k x)`): two points of one fibre with equal signs lie in the same stack cell. These are leaf lemmas (no use elsewhere in TauCeti) and are not exposed through `IsCAD`. |
| univariate Thom lemma? | **Exact-sign form for one polynomial and its derivatives; no relaxed/closure form.** | `Algebra/Polynomial/Thom/Basic.lean:55` `derivativeSign`, `:366` `derivativeSign_eq_on_Icc`, `:377` `ordConnected_preimage_derivativeSign`, `:399` `eval_ne_zero_of_derivativeSign_eq`; `Thom/Interval.lean:66` `theorem preimage_derivativeSign_subsingleton_or_eq_Ioo (p : R[X]) (σ : ℕ → SignType) : (derivativeSign p ⁻¹' {σ}).Subsingleton ∨ ∃ (a : WithBot R) (b : WithTop R), derivativeSign p ⁻¹' {σ} = {x : R \| a < x ∧ x < b}`. `grep closure` in `Algebra/Polynomial/Thom/` has no hit. |
| Thom encodings | Root encodings and semialgebraicity of root regions, not closures. | `Geometry/RealAlgebraic/Semialgebraic/Thom.lean:286` `isSemialgebraic_setOf_exists_root_derivative_signs_eq`, `:507` `isSemialgebraic_setOf_lt_root_card_roots_lt`, …; `SignDetermination/Thom.lean` (`signCount_iterate_derivative`, `fullInverse_mulVec_thomEncoding`); `Algebra/Polynomial/Thom/Roots.lean` (`ThomLT`, `thomEncodingEquiv`, `lt_iff_thomLT`). |
| dimension with `dim (frontier S) < dim S`? | **No.** | `Semialgebraic/Dimension/Basic.lean:76` `semialgebraicDim`, `:248` `IsSemialgebraic.semialgebraicDim_union`; `Dimension/Closure.lean:47` `theorem IsSemialgebraic.semialgebraicDim_closure (hs : IsSemialgebraic s) : semialgebraicDim (closure s) = semialgebraicDim s`; `Dimension/{Projection,Product,Stack,Strata,Fiber/*}`. `grep -rn "semialgebraicDim.*<\|< semialgebraicDim"` over TauCeti returns no statement. |
| finiteness theorem, Łojasiewicz inequality, real spectrum of a ring? | **Absent.** | grep for `finiteness`, `Lojasiewicz`/`Łojasiewicz` (only bibliography of triangulation files), `RealSpectrum`/`PrimeCone` (only operator-theoretic hits). |

Ingredients of the recommended route that TauCeti **has**:

* `Geometry/RealAlgebraic/Semialgebraic/Basic.lean:383`
  `theorem IsSemialgebraic.exists_eq_setOf_sign_eval {s : Set (σ → R)} (hs : IsSemialgebraic s) :
  ∃ (m : ℕ) (p : Fin m → MvPolynomial σ R) (Φ : (Fin m → SignType) → Prop),
  s = {x | Φ fun i => SignType.sign (eval x (p i))}`
* `…/Basic.lean:247` `theorem isSemialgebraic_setOf_sign_eval {ι : Type*} [Finite ι] (p : ι → MvPolynomial σ R)
  (Φ : (ι → SignType) → Prop) : IsSemialgebraic {x : σ → R | Φ fun i => SignType.sign (eval x (p i))}`
* `…/Basic.lean:414` `class HasSemialgebraicProjections : Prop where isSemialgebraic_image_tail {n : ℕ}
  {s : Set (Fin (n + 1) → R)} : IsSemialgebraic s → IsSemialgebraic (Fin.tail '' s)`, with
  `CAD/Existence.lean:102` `instance : HasSemialgebraicProjections ℝ`
* `Semialgebraic/Topology.lean:142` `theorem IsSemialgebraic.closure [Finite σ] {s : Set (σ → ℝ)}
  (hs : IsSemialgebraic s) : IsSemialgebraic (closure s)`
* `…/Basic.lean:302` `IsSemialgebraic.preimage_eval`, `:318` `IsSemialgebraic.preimage_comp`,
  `:325` `theorem isSemialgebraic_preimage_comp_equiv {s : Set (τ → R)} (e : τ ≃ σ) :
  IsSemialgebraic ((fun x : σ → R => x ∘ e) ⁻¹' s) ↔ IsSemialgebraic s`
* `Algebra/MvPolynomial/Equiv.lean:200` `theorem polynomial_eval_map_finSuccEquiv (φ : R →+* S) (s : Fin n → S)
  (y : S) (f : MvPolynomial (Fin (n + 1)) R) : ((finSuccEquiv R n f).map (eval₂Hom φ s)).eval y =
  eval₂ φ (Fin.cons y s) f`; `:148` `finSuccEquiv'_pderiv`; `:143` `finSuccEquiv'_zero`
* `Algebra/Polynomial/RealClosed/Sign.lean:35` `theorem sign_eval_const (p : R[X]) {a b : R} (hab : a ≤ b)
  (hz : ∀ x ∈ Set.Icc a b, p.eval x ≠ 0) : SignType.sign (p.eval a) = SignType.sign (p.eval b)`

**Missing in TauCeti and to be written**: Lemma T; the uniform root bound; Theorem C; the monic normal form of a
family; all bookkeeping for finite unions of basic closed sets; the theorem itself.

Other directories read and found irrelevant to every route considered: `Stack/*` (stacks, delineations, analytic
delineability, Puiseux, discriminant order), `Projection/*` (Collins, McCallum, Lazard projections),
`CAD/{Partition,Restrict,Projection}.lean`, `Semialgebraic/{Components,Connected,LocallyConnected,Local}.lean`
(finitely many connected components, local versions), `Semialgebraic/{Function,Image,Derivative,RootCount,
FamilyRoots,SharedRoots,RegionBetween}.lean`, `Nash/*` (Nash germs; note
`Nash/OfSemialgebraic.lean:42 IsSemialgebraicOn.exists_ne_zero_polynomial_relation`, a nonzero polynomial relation
for a semialgebraic function, which the Łojasiewicz route could use), `DelineatingSet/*`, `OrderInvariant.lean`,
`LazardInvariant.lean`, `SquarefreeBasis.lean`.

### 7.2 Mathlib (`.lake/packages/mathlib/Mathlib/`, commit `1b1ccf4b`)

* `RingTheory/NoetherNormalization.lean:90` `noncomputable abbrev varChange := AlgEquiv.ofAlgHom (T1 f 1) (T1 f (-1)) …`
  (type `MvPolynomial (Fin (n + 1)) k → MvPolynomial (Fin (n + 1)) k ≃ₐ[k] MvPolynomial (Fin (n + 1)) k`, `k` a
  field, `f` the polynomial to normalize), and `:149`
  `lemma varChange_leadingCoeff_isUnit (fne : f ≠ 0) : IsUnit (finSuccEquiv k n (varChange f f)).leadingCoeff`.
  Both are public; the auxiliary lemmas of that file are private and are not needed.
* `Algebra/Divisibility/Units.lean:129` `isUnit_of_dvd_unit`;
  `Algebra/BigOperators/Group/Finset/Piecewise.lean:231` `Finset.dvd_prod_of_mem`;
  `Order/Filter/Finite.lean:247` `Filter.eventually_all`; `Topology/Order/DenselyOrdered.lean:63` `closure_Ioo`,
  `:107` `interior_Icc`; `Order/Interval/Set/Infinite.lean:47` `Set.Ioo_infinite`;
  `FieldTheory/IsRealClosed/Real.lean:15` `instance : IsRealClosed ℝ`.
* `Algebra/MvPolynomial/Equiv.lean:606` `def finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R)`;
  `:669` `theorem eval_eq_eval_mv_eval' (s : Fin n → R) (y : R) (f : MvPolynomial (Fin (n + 1)) R) :
  eval (Fin.cons y s : Fin (n + 1) → R) f = Polynomial.eval y (Polynomial.map (eval s) (finSuccEquiv R n f))`;
  `:772` `natDegree_finSuccEquiv`.
* `Algebra/MvPolynomial/Nilpotent.lean:88` `theorem isUnit_iff_eq_C_of_isReduced [IsReduced R] :
  IsUnit P ↔ ∃ r, IsUnit r ∧ P = C r`.
* `Algebra/Polynomial/BigOperators.lean:412` `theorem leadingCoeff_prod : (∏ i ∈ s, f i).leadingCoeff = ∏ i ∈ s, (f i).leadingCoeff`.
* `Algebra/Polynomial/Eval/Degree.lean:180` `natDegree_map_of_leadingCoeff_ne_zero (f : R →+* S)
  (hf : f (leadingCoeff p) ≠ 0) : natDegree (p.map f) = natDegree p`; `:184` `leadingCoeff_map_of_leadingCoeff_ne_zero`.
* `Algebra/Polynomial/Derivative.lean:249` `derivative_map`; `:260` `iterate_derivative_map`; `:446`
  `lemma leadingCoeff_derivative (p : R[X]) : leadingCoeff (derivative p) = leadingCoeff p * p.natDegree`; `:114`
  `derivative_of_natDegree_zero`; `:204` `iterate_derivative_eq_zero {p : R[X]} {x : ℕ} (hx : p.natDegree < x)`.
* `Algebra/Polynomial/Roots.lean:171` `theorem eq_zero_of_infinite_isRoot (p : R[X]) (h : Set.Infinite {x | IsRoot p x}) : p = 0`.
* `Analysis/Polynomial/CauchyBound.lean:37` `noncomputable def cauchyBound (p : K[X]) : ℝ≥0 :=
  sup (range p.natDegree) (‖p.coeff ·‖₊) / ‖p.leadingCoeff‖₊ + 1`; `:78`
  `theorem IsRoot.norm_lt_cauchyBound {p : K[X]} (hp : p ≠ 0) {a : K} (h : p.IsRoot a) : ‖a‖₊ < cauchyBound p`.
* `Analysis/Calculus/Deriv/MeanValue.lean:378` `theorem strictMonoOn_of_deriv_pos {D : Set ℝ} (hD : Convex ℝ D)
  {f : ℝ → ℝ} (hf : ContinuousOn f D) (hf' : ∀ x ∈ interior D, 0 < deriv f x) : StrictMonoOn f D`; `:446`
  `strictAntiOn_of_deriv_neg`; `Analysis/Calculus/Deriv/Polynomial.lean:108`
  `protected theorem deriv : deriv (fun x => p.eval x) x = p.derivative.eval x`.
* `Topology/Algebra/MvPolynomial.lean:31` `theorem MvPolynomial.continuous_eval : Continuous fun x ↦ eval x p`.
* `Topology/Sequences.lean:108` `mem_closure_iff_seq_limit [FrechetUrysohnSpace X]`; `:298`
  `IsCompact.tendsto_subseq`; `Topology/Constructions.lean:977` `Filter.Tendsto.finCons`;
  alternative to sequences: `Topology/Maps/Proper/Basic.lean:337` `isClosedMap_snd_of_compactSpace`.
* `Algebra/MvPolynomial/Rename.lean:244` `theorem eval_rename (g : τ → R) (p : MvPolynomial σ R) :
  eval g (rename k p) = eval (g ∘ k) p`; `Algebra/MvPolynomial/Eval.lean:600` `aeval_unique`;
  `Algebra/MvPolynomial/Monad.lean:254` `aeval_bind₁`.

### 7.3 Scratch checks performed

`lake env lean` on two scratch files under `/tmp` (not part of the repository): `#check` succeeded for every name
in the list "ingredients that TauCeti has" of §7.1, for every Mathlib name of §7.2 and of the proof notes of §8
(`sign_eq_one_iff`, `Fin.cons_self_tail`, `closure_minimal`, `image_closure_subset_closure_image`,
`Finite.induction_empty_option`, `Fintype.equivFin`, `Finset.prod_ne_zero_iff`, `isCompact_Icc`, `Continuous.finCons`,
`Polynomial.natDegree_derivative_lt`, `Polynomial.eq_C_of_natDegree_eq_zero`, …), and for
`TauCeti.exists_isCAD_signInvariant`, `TauCeti.Delineation.mk_mem_sectorSet_iff_of_sign_eval_eq`,
`Polynomial.derivativeSign_eq_on_Icc`. The remaining entries of the inventory table (`Thom/Interval.lean`,
`Dimension/*`, `CAD/Lazard`, `Nash`) were verified by reading the source only, because their `.olean` files are not
in the local cache. Two shape tests compiled:

```lean
example {σ : Type*} (e : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ) (x : σ → ℝ) (p : MvPolynomial σ ℝ) :
    eval x (e p) = eval (fun i => eval x (e (X i))) p := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

example {n : ℕ} (f g : MvPolynomial (Fin (n + 1)) ℝ)
    (h : IsUnit (finSuccEquiv ℝ n (f * g)).leadingCoeff) : IsUnit (finSuccEquiv ℝ n f).leadingCoeff := by
  rw [map_mul, Polynomial.leadingCoeff_mul] at h
  exact isUnit_of_mul_isUnit_left h
```

So a plain (non-`module`) file can use `NoetherNormalization.varChange_leadingCoeff_isUnit` without unfolding
`varChange`. Nothing else was compiled.

## 8. Lemma decomposition for Lean (recommended route)

Namespace `Semialgebraic`; `open MvPolynomial Polynomial`. Sizes: S < 60 lines, M 60–150, L 150–300, XL > 300.
The statements are recommendations; they were not compiled.

### Unit A, `Finiteness/BasicClosed.lean` (M–L, about 220 lines)

```lean
/-- B0. A finite union of basic closed sets. -/
def IsBasicClosedUnion {σ : Type*} (s : Set (σ → ℝ)) : Prop :=
  ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial σ ℝ), s = ⋃ i, ⋂ j, {x | 0 ≤ eval x (P i j)}

/-- B1. Any finite index types (pad with the polynomial `1`, reindex by `Fintype.equivFin`). -/
theorem isBasicClosedUnion_of_fintype {σ : Type*} {α : Type*} [Finite α] {β : α → Type*} [∀ a, Finite (β a)]
    (P : ∀ a, β a → MvPolynomial σ ℝ) :
    IsBasicClosedUnion (⋃ a, ⋂ b, {x : σ → ℝ | 0 ≤ eval x (P a b)})

theorem isBasicClosedUnion_setOf_nonneg {σ : Type*} (p : MvPolynomial σ ℝ) :
    IsBasicClosedUnion {x : σ → ℝ | 0 ≤ eval x p}                                           -- B2
theorem IsBasicClosedUnion.union {σ : Type*} {s t : Set (σ → ℝ)} :
    IsBasicClosedUnion s → IsBasicClosedUnion t → IsBasicClosedUnion (s ∪ t)                -- B3
theorem IsBasicClosedUnion.inter {σ : Type*} {s t : Set (σ → ℝ)} :
    IsBasicClosedUnion s → IsBasicClosedUnion t → IsBasicClosedUnion (s ∩ t)                -- B4
theorem IsBasicClosedUnion.iUnion {σ α : Type*} [Finite α] {s : α → Set (σ → ℝ)} :
    (∀ a, IsBasicClosedUnion (s a)) → IsBasicClosedUnion (⋃ a, s a)                         -- B5
theorem IsBasicClosedUnion.iInter {σ α : Type*} [Finite α] {s : α → Set (σ → ℝ)} :
    (∀ a, IsBasicClosedUnion (s a)) → IsBasicClosedUnion (⋂ a, s a)                         -- B6
/-- B7. Preimage under a polynomial map (`bind₁ f`), as in `TauCeti.IsSemialgebraic.preimage_eval`. -/
theorem IsBasicClosedUnion.preimage_eval {σ τ : Type*} {s : Set (τ → ℝ)} (hs : IsBasicClosedUnion s)
    (f : τ → MvPolynomial σ ℝ) : IsBasicClosedUnion ((fun x i => eval x (f i)) ⁻¹' s)
/-- B8. A relaxed sign condition is basic closed. -/
theorem isBasicClosedUnion_setOf_relaxed {σ κ : Type*} [Finite κ] (G : κ → MvPolynomial σ ℝ)
    (ε : κ → SignType) :
    IsBasicClosedUnion {x : σ → ℝ | ∀ k, eval x (G k) = 0 ∨ SignType.sign (eval x (G k)) = ε k}
```

Proof notes. B1 is the only place with `Fin` arithmetic; B3–B6 follow from B1 with sum and product index types
(`(⋃_a ⋂_b) ∩ (⋃_{a'} ⋂_{b'}) = ⋃_{(a,a')} ⋂_{b ⊕ b'}`; B6 by `Finite.induction_empty_option` or via
`⋂_a ⋃_i = ⋃_{φ : ∀ a, I a} ⋂_a`). B8: by cases on `ε k`, the set is `{0 ≤ g}`, `{0 ≤ -g}` or their intersection
(`sign_eq_one_iff`, `sign_eq_neg_one_iff`, `sign_eq_zero_iff`), then B6.

### Unit B, `Finiteness/ThomOneVar.lean` (M, about 100 lines)

```lean
/-- T. Lemma T of §2. No finiteness of `κ` is needed. -/
theorem sign_eval_eq_of_mem_Ioo_of_relaxed {κ : Type*} (P : κ → ℝ[X]) (ε : κ → SignType)
    (hne : ∀ k, P k ≠ 0)
    (hder : ∀ k, derivative (P k) = 0 ∨ ∃ l, P l = derivative (P k))
    {a b t : ℝ} (ht : t ∈ Set.Ioo a b)
    (ha : ∀ k, (P k).eval a = 0 ∨ SignType.sign ((P k).eval a) = ε k)
    (hb : ∀ k, (P k).eval b = 0 ∨ SignType.sign ((P k).eval b) = ε k) (k : κ) :
    SignType.sign ((P k).eval t) = ε k
```

Proof: strong induction on `(P k).natDegree` generalizing `k` and `t`; `strictMonoOn_of_deriv_pos (convex_Icc a b)`
with `interior_Icc`, `Polynomial.deriv`, `Polynomial.continuous`; `Polynomial.eq_zero_of_infinite_isRoot` with
`Set.Ioo_infinite` to exclude `ε l = 0`; `natDegree_derivative_lt`; `Polynomial.derivative_of_natDegree_zero` /
`eq_C_of_natDegree_eq_zero` for the base case.

### Unit C, `Finiteness/ClosureFormula.lean` (L, about 320 lines in three lemmas)

```lean
/-- C1 (S). A sign vector realized somewhere is realized in `[-M, M]` if all roots lie in `(-M, M)`. -/
theorem exists_mem_Icc_forall_sign_eval_eq {κ : Type*} (P : κ → ℝ[X]) {M : ℝ} (hM : 0 ≤ M)
    (hroot : ∀ k t, (P k).eval t = 0 → |t| < M) (t : ℝ) :
    ∃ t' ∈ Set.Icc (-M) M, ∀ k, SignType.sign ((P k).eval t') = SignType.sign ((P k).eval t)

/-- C2 (M). Uniform root bound near a base point for a family that is monic up to constants. -/
theorem exists_eventually_forall_root_abs_lt {n : ℕ} {κ : Type*} [Finite κ]
    (Q : κ → (MvPolynomial (Fin n) ℝ)[X])
    (hmonic : ∀ k, ∃ a : ℝ, a ≠ 0 ∧ (Q k).leadingCoeff = MvPolynomial.C a) (p : Fin n → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ x in nhds p, ∀ k t, ((Q k).map (MvPolynomial.eval x)).eval t = 0 → |t| < M

/-- C3 (L). Theorem C. -/
theorem closure_setOf_sign_eval_eq {n : ℕ} {κ : Type*} [Finite κ]
    (G : κ → MvPolynomial (Fin (n + 1)) ℝ) (ε : κ → SignType)
    (hmonic : ∀ k, ∃ a : ℝ, a ≠ 0 ∧ (finSuccEquiv ℝ n (G k)).leadingCoeff = MvPolynomial.C a)
    (hder : ∀ k, derivative (finSuccEquiv ℝ n (G k)) = 0 ∨
      ∃ l, finSuccEquiv ℝ n (G l) = derivative (finSuccEquiv ℝ n (G k))) :
    closure {y : Fin (n + 1) → ℝ | ∀ k, SignType.sign (eval y (G k)) = ε k} =
      {y | ∀ k, eval y (G k) = 0 ∨ SignType.sign (eval y (G k)) = ε k} ∩
        Fin.tail ⁻¹' closure (Fin.tail '' {y | ∀ k, SignType.sign (eval y (G k)) = ε k})
```

Proof notes. C1: `Polynomial.sign_eval_const` (TauCeti; `IsRealClosed ℝ` from `Mathlib.FieldTheory.IsRealClosed.Real`)
on `[M, t]` or `[t, -M]`. C2: `Polynomial.IsRoot.norm_lt_cauchyBound`, `natDegree_map_of_leadingCoeff_ne_zero`,
`leadingCoeff_map_of_leadingCoeff_ne_zero`, continuity of `x ↦ eval x ((Q k).coeff j)`, `Filter.eventually_all`
(finite `κ`, finite `j < natDegree`); fallback if the `ℝ≥0` `Finset.sup` is awkward: prove directly that
`|t| ≥ 1 + (Σ_j |c_j|)/|a|` implies `p(t) ≠ 0` (about 40 lines). C3: the bridge
`eval y (G k) = ((finSuccEquiv ℝ n (G k)).map (eval (Fin.tail y))).eval (y 0)` is `eval_eq_eval_mv_eval'` after
`Fin.cons_self_tail`; `⊆` by `closure_minimal` (the relaxed set is an intersection of closed sets) and
`image_closure_subset_closure_image`; `⊇` as in §4: Case 1 by Lemma T at `x := Fin.tail y` with
`derivative_map`, then `Continuous.finCons`/`closure_Ioo`; Case 2 by C2, C1, `mem_closure_iff_seq_limit`,
`isCompact_Icc.tendsto_subseq`, `Filter.Tendsto.finCons`.

### Unit D, `Finiteness/Monic.lean` (M, about 200 lines in three lemmas)

```lean
/-- M1 (S). Simultaneous monic form after a polynomial automorphism. -/
theorem exists_algEquiv_forall_leadingCoeff_eq_C {n m : ℕ} (f : Fin m → MvPolynomial (Fin (n + 1)) ℝ)
    (hf : ∀ i, f i ≠ 0) :
    ∃ e : MvPolynomial (Fin (n + 1)) ℝ ≃ₐ[ℝ] MvPolynomial (Fin (n + 1)) ℝ,
      ∀ i, ∃ a : ℝ, a ≠ 0 ∧ (finSuccEquiv ℝ n (e (f i))).leadingCoeff = MvPolynomial.C a

/-- M2 (M). Polynomial automorphisms act on points; transport of `IsBasicClosedUnion`. -/
def polyMap {σ : Type*} (e : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ) (x : σ → ℝ) : σ → ℝ :=
  fun i => eval x (e (X i))
theorem eval_algHom_apply {σ : Type*} (e : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ) (x : σ → ℝ)
    (p : MvPolynomial σ ℝ) : eval x (e p) = eval (polyMap e x) p
theorem continuous_polyMap {σ : Type*} (e : MvPolynomial σ ℝ →ₐ[ℝ] MvPolynomial σ ℝ) :
    Continuous (polyMap e)                       -- `continuous_pi`, `MvPolynomial.continuous_eval`
theorem polyMap_polyMap_symm {σ : Type*} (e : MvPolynomial σ ℝ ≃ₐ[ℝ] MvPolynomial σ ℝ) (x : σ → ℝ) :
    polyMap (e : _ →ₐ[ℝ] _) (polyMap (e.symm : _ →ₐ[ℝ] _) x) = x
theorem IsBasicClosedUnion.of_preimage_polyMap {σ : Type*} (e : MvPolynomial σ ℝ ≃ₐ[ℝ] MvPolynomial σ ℝ)
    {s : Set (σ → ℝ)} (h : IsBasicClosedUnion (polyMap (e : _ →ₐ[ℝ] _) ⁻¹' s)) : IsBasicClosedUnion s

/-- M3 (M). The `∂/∂X₀`-closure of a monic family. -/
theorem exists_derivative_closed_family {n m : ℕ} (g : Fin m → MvPolynomial (Fin (n + 1)) ℝ)
    (hg : ∀ i, ∃ a : ℝ, a ≠ 0 ∧ (finSuccEquiv ℝ n (g i)).leadingCoeff = MvPolynomial.C a) :
    ∃ (κ : Type) (_ : Fintype κ) (G : κ → MvPolynomial (Fin (n + 1)) ℝ),
      (∀ i, ∃ k, G k = g i) ∧
      (∀ k, ∃ a : ℝ, a ≠ 0 ∧ (finSuccEquiv ℝ n (G k)).leadingCoeff = MvPolynomial.C a) ∧
      (∀ k, derivative (finSuccEquiv ℝ n (G k)) = 0 ∨
        ∃ l, finSuccEquiv ℝ n (G l) = derivative (finSuccEquiv ℝ n (G k)))
```

Proof notes. M1: `e := NoetherNormalization.varChange (∏ i, f i)`; `varChange_leadingCoeff_isUnit`
(`Finset.prod_ne_zero_iff`), `map_prod`, `Polynomial.leadingCoeff_prod`, `isUnit_of_dvd_unit` with
`Finset.dvd_prod_of_mem`, `MvPolynomial.isUnit_iff_eq_C_of_isReduced`. M2: the first lemma is the shape test of §7.3;
`polyMap_polyMap_symm` is `eval_algHom_apply` for `e.symm` at `p = e (X i)`; the transport is B7 with
`f i := e.symm (X i)`. M3: with `q i := finSuccEquiv ℝ n (g i)` and `D := sup (q i).natDegree`, take
`κ := {p : Fin m × Fin (D + 1) // derivative^[p.2] (q p.1) ≠ 0}` and
`G p := (finSuccEquiv ℝ n).symm (derivative^[p.1.2] (q p.1.1))`. The invariant
"`r = 0 ∨ ∃ a ≠ 0, r.leadingCoeff = C a`" is preserved by `derivative` (`leadingCoeff_derivative`,
`derivative_of_natDegree_zero`); (D) holds because a nonzero `derivative^[j+1]` forces `j + 1 ≤ natDegree ≤ D`
(`iterate_derivative_eq_zero`).

### Unit E, `Finiteness/Main.lean` and `Interface/Finiteness.lean` (L, about 260 lines)

```lean
/-- M4 (L). Theorem FT on `Fin n → ℝ`, by induction on `n` as in §5. -/
theorem isBasicClosedUnion_of_isClosed_fin :
    ∀ (n : ℕ) {s : Set (Fin n → ℝ)}, TauCeti.IsSemialgebraic s → IsClosed s → IsBasicClosedUnion s
/-- M5 (S). Any finite index type. -/
theorem isBasicClosedUnion_of_isClosed {ι : Type*} [Finite ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s → IsBasicClosedUnion s
/-- Interface (S): `Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg`, by unfolding B0. -/
```

Dependency order: A, B independent; C needs B; D needs A; E needs A, C, D. Units A, B, C1–C2 and D can be written in
parallel.

| unit | content | lines (estimate) | size |
|---|---|---|---|
| A | B0–B8 | 220 | M–L |
| B | Lemma T | 100 | M |
| C | C1 35, C2 80, C3 200 | 320 | L |
| D | M1 45, M2 75, M3 80 | 200 | M |
| E | M4 200, M5 + interface 60 | 260 | L |
| total | | about 1100 (range 900–1400) | |

### Formalization risks

1. `finSuccEquiv` / `Fin.cons` / `Fin.tail` plumbing in C3 and M3 (medium; mitigated by stating hypotheses at the
   `Polynomial (MvPolynomial (Fin n) ℝ)` level and using `eval_eq_eval_mv_eval'` once).
2. `cauchyBound` lives in `ℝ≥0` with a `Finset.sup` (medium; direct fallback given under C2).
3. Finite-union bookkeeping (B1) with `Fin` indices and padding (medium, purely mechanical; the Łojasiewicz route
   needs comparable bookkeeping for its distributivity step L3).
4. The subtype index `κ` in M3 needs a `Fintype`/`Finite` instance (`Subtype.fintype` needs decidability; use
   `Finite` and `Fintype.ofFinite`, or keep `[Finite κ]` everywhere, which C3 allows).
5. The target fixes `ι : Type`; keep internal lemmas universe-polymorphic or in `Type` consistently.
6. `NoetherNormalization.varChange` is an `abbrev` whose body uses a private lemma; do not unfold it. Only
   `varChange_leadingCoeff_isUnit` and the generic M2 lemmas are needed (checked in §7.3).
7. No mathematical risk is known to me: every step of §§2, 4, 5 is proved above.

## 9. Other routes

### 9.1 The literal hypothesis: closures of TauCeti CAD cells by relaxing sign conditions

Not correct as stated (§3, §7.1). A true statement of this type exists (the textbook generalized Thom lemma: after a
change of coordinates there is a family containing the given one whose nonempty sign conditions are connected cells
of a CAD, with closure equal to the relaxed condition and equal to a union of cells). To formalize *that* on TauCeti
one would have to redo the induction of `exists_isCAD_signInvariant` with a stronger invariant: families that are
monic, `∂_t`-closed and closed under the Collins projection; cells equal to sign conditions (via
`Delineation.mk_mem_sectionSet_iff_of_sign_eval_eq` and `mk_mem_sectorSet_iff_of_sign_eval_eq`); closure of each
cell. None of this is exposed by `IsCAD`, which hides the delineations behind an existential. Estimate: XL
(1500–3000 lines), with real risk in the interaction with TauCeti's private projection machinery. §6 obtains the
frontier condition without CAD cells, and §5 obtains the target without either. **Not recommended.**

### 9.2 Łojasiewicz route (PLAN §4.4; outline only, R1 studies it)

Chain: G1–G4 (one-variable growth of a fibrewise least upper bound) → L1 (weighted closed Łojasiewicz inequality
for polynomials on a closed semialgebraic set) → L2 (each sign cell `{f = 0, g_j > 0} ⊆ U` of an open
semialgebraic `U` lies in a basic open subset of `U`) → L3 (complement and distributivity). This is the scheme of
Schweighofer's finiteness theorem for semialgebraic sets (`\label{finthm}` in the TeX source of arXiv 2205.04211,
§6.3, which I read; the blueprint cites it as 6.3.3): it reduces the closed case to the open case and applies his
corollary of the Łojasiewicz inequality on the closed set `A = ℝⁿ \ S` to `f = f_i²` and
`g = ∏_j (|g_ij| + g_ij)`.

Comparison.

| | Thom closure-formula route (§§4–5) | Łojasiewicz route (PLAN §4.4) |
|---|---|---|
| status of the mathematics | complete proofs in this report | L1's one-parameter shortcut is unverified (R1) |
| TauCeti input | sign normal form, projection, closure | sign normal form, projection/quantifier lemmas (through G3) |
| dependence on Phase 2 | none | needs G4 |
| analysis used | monotonicity from the sign of the derivative, Cauchy bound, compactness of an interval | compactness of `K_t`, attained extrema, least upper bounds, power inequalities with explicit exponents |
| shape of the result | closed form directly | open form, then complement + distributivity |
| change of coordinates | yes (Mathlib `varChange`) | no |
| size | about 1100 lines | to be estimated by R1 (PLAN suggests three lemmas L1–L3 on top of G1–G4) |
| reuse | Theorem C and Lemma T are of independent interest (frontier condition, §6) | L1 is a Łojasiewicz inequality of independent interest |

The two routes are independent; either can serve as a fallback for the other.

### 9.3 Real spectrum and constructible topology

Chain: real spectrum `Sper ℝ[x]`; constructible topology is compact; `S ↦ S̃`; `S` open ⇒ `S̃` open in the spectral
topology; then `S̃` is a union of basic open constructible sets, finitely many by compactness. In the one source I
could read (Schweighofer, Theorem `finthmabstract` and Remark `finthmabstractmotivates` in §6.3), the implication
"`S` open ⇒ `S̃` open" is **derived from** the finiteness theorem, so that presentation is circular for our purpose.
A non-circular proof needs the characterization of open constructible sets by stability under generization, plus
transfer of openness to real closed extension fields (Tarski–Seidenberg over arbitrary real closed fields and
convex valuation rings). TauCeti has no real spectrum of a ring, and `HasSemialgebraicProjections` has an instance
only for `ℝ`. **Not viable** (XL several times over).

### 9.4 Induction on dimension with `dim (closure S \ S) < dim S`

I could not find a complete argument. The natural attempt: for a piece `T = {f = 0, g_j > 0} ⊆ S`, the relaxed set
`T̂ = {f = 0, g_j ≥ 0}` satisfies `T̂ = T ∪ Z`, `Z = T̂ ∩ {∏ g_j = 0}`, and `S ∩ Z` is closed semialgebraic. Even
when `dim Z < dim T` (false in general: E2 has `dim Z = dim T`), the induction hypothesis handles `S ∩ Z` but one
still needs basic closed sets between `T` and `S ∩ T̂`, i.e. a polynomial inequality that holds on `T` and cuts
`Z \ S` away. That separation is exactly what the Łojasiewicz inequality or Theorem C provides; dimension alone does
not. In addition TauCeti has `semialgebraicDim (closure s) = semialgebraicDim s` but not the strict inequality for
`closure s \ s`. **Not established; not a route.**

### 9.5 Separation of closed semialgebraic sets

Separating a basic set from the complement of an open set by a polynomial inequality is the content of L2 (§9.2);
separation of two disjoint closed semialgebraic sets by a single polynomial is false in general and by Nash
functions is a deeper theorem. No independent route.

## 10. Recommendation

* The route "TauCeti CAD cells + relaxed sign conditions" must not be attempted as stated.
* The corrected route (Lemma T → Theorem C → induction on the number of variables, §§2, 4, 5, decomposition §8) is
  correct, complete, self-contained on TauCeti + Mathlib at the pins, and independent of Phase 2. I recommend it
  either as the primary route for A2 or as the fallback if R1 finds a gap in PLAN §4.4; the choice between the two
  should be made on R1's line estimate, since both now look feasible.
* Possible upstreaming note for the user: Lemma T, Theorem C and §6 fill a gap in TauCeti (no closure statement for
  sign conditions exists there).

## 11. What was not verified

1. **No proof was compiled in Lean.** Only name resolution and the two shape tests of §7.3. The line estimates are
   estimates.
2. **Bochnak–Coste–Roy, Basu–Pollack–Roy and Coste's notes could not be consulted** (not on arXiv; the Rennes
   server refused the connection). Their numbering (BCR Prop. 2.5.4, §2.7, §9.1; BPR Prop. 2.27) is quoted from
   the brief, from TauCeti docstrings and from memory. All statements and proofs in §§2–6 are my own derivations and
   do not rely on those texts. In particular I do not claim that Theorem C appears in this form in the literature,
   nor which proof BCR uses for their Theorem 2.7.2.
3. **Schweighofer's notes** (arXiv 2205.04211, TeX source): I read §5.4 and §6.3 only. §5.4 ("finiteness theorem for
   semialgebraic classes") is a compactness statement, not the theorem needed here. §6.2 (Łojasiewicz) was not
   checked; that is R1's task.
4. The counterexample search and the numerical test of Theorem C are heuristic (grid sampling, floating point). The
   counterexamples E1–E7 themselves are verified by hand in §3; Theorem C is proved in §4.
5. E6 asserts that the 7-cell decomposition is a CAD satisfying the *conclusion* of
   `exists_isCAD_signInvariant {X₀X₁}`. I did not determine which CAD the existential proof in TauCeti actually
   produces (it is not observable from the statement).
6. Whether every CAD can be refined, in the same coordinates, to one satisfying the frontier condition was not
   investigated; it is irrelevant to the recommended route.
7. Section 9.2's comparison uses only the outline of PLAN §4.4; no claim is made about the correctness or the size
   of that route.
