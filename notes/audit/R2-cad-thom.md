# Audit of research report R2 (`notes/research/route2-cad-thom.md`)

Auditor: adversarial research auditor (Phase 3a). Pins as in `PLAN.md` (Mathlib `1b1ccf4b`, TauCeti `2c9b12be`).
Documents read: `notes/briefs/audit-research.md`, `R-common.md`, `R2-cad-thom.md`, `PLAN.md`, the report (all 729
lines), §0 and the estimates of `route1-lojasiewicz.md` (for the comparison only), the TauCeti sources quoted below,
`Mathlib/RingTheory/NoetherNormalization.lean`, and Schweighofer's TeX source (arXiv 2205.04211, fetched to a
scratch directory, lines 5595–5745).

Method. For every lemma I wrote my own proof (or checked the counterexample) before comparing with the report.
I checked the counterexamples by hand and again by exact rational arithmetic in a scratch Python script. I checked
every Lean name by grep, and resolved all of them by `lake env lean` on a scratch file. I also compiled three
prototypes as evidence (scratch files outside the repository, no `sorry`, axioms
`[propext, Classical.choice, Quot.sound]`):

* Lemma T exactly as in §8 Unit B (argument order slightly permuted): **95 lines, compiles**.
* M1 (`exists_algEquiv_forall_leadingCoeff_eq_C`) through `NoetherNormalization.varChange`: **12 lines, compiles**.
* `eval_algHom_apply` and `polyMap_polyMap_symm` (M2): compile.

No repository file was edited apart from this audit. No `lake build` was run.

---

## 1. Verdicts per item

### 1.1 Lemma T (one-variable Thom lemma with relaxed endpoints): CONFIRMED

*My proof (written before reading §2).* Use strong induction on `d = deg P_k`, generalizing `k`, and prove that
`sign P_k(t) = ε_k` for all `t ∈ (a,b)`.

* `d = 0`: `P_k = c ≠ 0`. From `a ∈ R̄`, either `c = 0` (excluded) or `sign c = ε_k`.
* `d ≥ 1`: `P_k' ≠ 0` (characteristic 0), so `P_k' = P_l` with `deg P_l = d-1`. The induction hypothesis holds for
  `l` because `a, b ∈ R̄` is a hypothesis on all indices. If `ε_l = 0`, then `P_l` vanishes on the infinite set
  `(a,b)`, so `P_l = 0`, which is excluded. Hence `P_k` is strictly monotone on `[a,b]`. In the increasing case
  `P_k(a) < P_k(t) < P_k(b)`, and the relaxed conditions at `a` and `b` give the three subcases. In particular,
  `ε_k = 0` would force `P_k(a) = 0 = P_k(b)`, which is impossible.

This is the report's proof. Edge cases: `κ` empty is trivial; finiteness of `κ` is not needed (correct); the
hypothesis `a < b` is implied by `t ∈ Ioo a b`; repeated indices are harmless.

Tests:
* `(t², 2t, 2)` with `ε = (1, 1, 1)`, `a = 0`, `b = 1` gives `(0,1) ⊆ R°`. Correct.
* Degenerate test `{5}` with `ε = 1` gives `R° = ℝ`.
* With `a = b` the lemma is vacuous.

**Lean evidence.** The Unit B statement compiles with a complete proof of 95 lines (Mathlib only:
`strictMonoOn_of_deriv_pos`, `strictAntiOn_of_deriv_neg`, `interior_Icc`, `Polynomial.deriv`,
`eq_zero_of_infinite_isRoot`, `Set.Ioo_infinite`, `natDegree_derivative_lt`, `derivative_eq_zero`). The estimate of
100 lines is accurate. Remark: TauCeti's `PolynomialRolle.strictMonoOn/antitoneOn`
(`Algebra/Polynomial/Rolle.lean`) would be an alternative; it is not needed.

### 1.2 Corollary (classical Thom lemma) and the two remarks: CONFIRMED

* (1): two points of `R°` give an infinite `R°`, hence all `ε_k ≠ 0`, hence `R°` is open and order-convex.
* (3): two points of `R̄` would make `R°` nonempty.
* (2): checked.

The ghost-point example `(t², 2t, 2)` with `ε = (-1, 1, 1)` gives `R° = ∅` and `R̄ = {0}`. I verified this.

### 1.3 Counterexamples E1–E7: all CONFIRMED (by hand and by exact computation)

| ex | what I checked |
|---|---|
| E1 | `x²(x-1) > 0 ⇔ x > 1`, and `≥ 0 ⇔ x ∈ {0} ∪ [1,∞)`. |
| E2 | `{xt=0, x≥0} = {t=0, x≥0} ∪ {x=0}`. The closure of `A = {t=0, x>0}` misses `(t,0)` for `t ≠ 0`. `Ā ⊆ π⁻¹[0,∞)`, so Theorem C's formula fails without (M). The family is `∂_t`-closed, and `xt` has leading coefficient `x`, which is not constant. |
| E3 | The derivative family is closed under all partials: 9 members `g, g_x, g_y, g_xx = 4y, g_xy, g_yy, 4, 6, 12`, recomputed. Both discriminants are negative. Values at `(-1,1)` are `1,-1,2,4,2,6` and at `(1,0)` are `0,0,2,0,4,6`. On the grid `(¼ℤ)² ∩ [-6,6]²` (exact rationals), the cell equals the open cone `{y>0, -3y/2 < x < -3y/4}`, and the relaxed set equals `closure A ∪ {y=0, x≥0}` at every grid point. |
| E4 | The closure of the graph of `|y|√z` over the dense subset `{y≠0, z>0}` of `{z≥0}` is the graph over `{z≥0}`. For `z < 0`, `x² = zy²` forces `x = y = 0`. The integer-grid check finds exactly the handle points `(0,0,z<0)`. Theorem C's formula holds here, as claimed. |
| E5 | I recomputed `∂_t g = 2t(1 - xt + x²t²/3)`, `∂²_t g = 2(1-xt)²`, `∂³_t g = -4x(1-xt)` and `∂⁴_t g = 4x²`, and checked both discriminants. On the grid the cell is `{x>0, t>1/x}`. At `x = 0` the relaxed fibre is `{t ≥ 0}`. Minor imprecision: "the roots `1/x` escape to infinity" refers to roots of `∂²_t g` and `∂³_t g`. For `x ≠ 0` the only real root of `g` itself is `t = 0`. |
| E6 | `isCAD_stackCells_const` (`CAD/Basic.lean:414`) with `c = ![0]` gives the 1-dimensional CAD. `isSemialgebraicStack_eval` (`:115`) with `k = 1`, `p = C 0`, and with `k = 0` over `{0}`, satisfies the hypotheses of `IsCAD.succ` (`:154`). New coordinate 0 is `t`. `X₀X₁ = tx` is sign-invariant on all 7 cells. `closure {t=0, x>0} ∋ (0,0)`, and `(0,0)` lies in the cell `{x=0}` but is a proper subset of it. Correct. |
| E7 | Same as §1.2. |

Consequences (a)–(d) of §3 follow.

### 1.4 Theorem C (closure formula): CONFIRMED

*My proof (written before reading §4).*
* `⊆`: `Ā` is closed, and `π(closure A) ⊆ closure π(A)`.
* `⊇`: let `(c,p') ∈ Ā` with `p' ∈ closure π(A)`.
  * Fibres at `p'`: by (M) every `P_k = (g_k)_{p'}` is nonzero, with `deg P_k = deg_t g_k`, because the constant
    leading coefficient survives `map (eval p')`. Specialization commutes with `d/dt` (`derivative_map`), so `(P_k)`
    is derivative-closed up to zero. Note that `P_k` can be nonzero for every `k` even when `p' ∉ π(A)`; this is
    exactly where (M) is needed.
  * If the relaxed fibre `R̄` has a second point `c'`, Lemma T gives that the open interval between `c` and `c'` is
    in the fibre of `A`, so `(c,p') ∈ closure A`. This case does not even use `p' ∈ closure π(A)`.
  * If `R̄ = {c}`: by Cauchy, uniformly on a neighbourhood `U` of `p'`, every real root of every fibre `(g_k)_{x'}`
    lies in `(-M,M)` with `M = 1 + C/min|a_k| ≥ 1`. Degree-0 members are nonzero constants and have no roots.
    Every point of `A` over `x' ∈ U` can be pushed to `t' ∈ [-M,M]` (no root on `[M,t]`, IVT). A sequence
    `x'_j → p'` in `π(A)`, a compactness subsequence, and a limit `(c₀,p') ∈ closure A ⊆ Ā` give `c₀ ∈ R̄`, so
    `c₀ = c`.

The report's proof is the same. I checked the edge cases:
* `A = ∅`: both sides are empty because `π(A) = ∅`. This handles ghost points such as E7 in several variables, e.g.
  `{t², 2t, 2}` on `ℝ_t × ℝ_x` with `ε = (-1,1,1)`.
* `κ = ∅`: both sides are `ℝ^{n+1}`.
* `n = 0`: the formula reduces to Corollary (2) for nonempty cells.
* Roots escaping to infinity: excluded by the constant leading coefficient, which is the content of (M).
* Zero members: excluded by (M).
* Constants: allowed (degree 0).

Own tests on `G = {t² - x, 2t, 2}`, which is monic and `∂_t`-closed:
* `ε = (0,1,1)`, `(-1,-1,1)`, `(1,0,1)`, `(-1,0,1)`, `(0,0,1)`: in each case both sides agree (closure of the upper
  half-parabola, of the region `-√x < t < 0`, of `{t=0, x<0}`, of `{t=0, x>0}`, and the origin).
* `ε = (-1,1,-1)`: both sides are empty.

### 1.5 Necessity of the hypotheses: CONFIRMED, with one wording correction

E2 and E5 show that (M) cannot simply be dropped. E4 shows that the factor `π⁻¹(closure π(A))` is needed. E1 shows
that (D) is needed.

The remark "for a `∂_t`-closed family, non-nullification and no degree drop at `p'` are the same requirement" is
correct: the top `t`-derivative `d_k!·lc(g_k)` is a member of the family.

**Correction (minor).** §0 item 6 says "A change of coordinates is needed". What is established is only that
(M) is a property of each member and is not reached by enlarging the family. The report itself says (§4) that it
"did not investigate whether some other device could replace the change of coordinates". The brief's question
"is a change of coordinates unavoidable?" therefore stays open as far as this route is concerned. It is not
unavoidable for the finiteness theorem itself: route 1 uses none. §0 item 6 should read "needed for Theorem C as
formulated".

### 1.6 Monic form: CONFIRMED

* **Linear version.** In `f(t, x'+ct)` the coefficient of `t^d` is `f^top(1,c)`. A nonzero polynomial over `ℝ` has a
  non-root. Correct (not used in Lean).
* **Nagata/Mathlib version.** I read `NoetherNormalization.lean:60–160`. `varChange f` fixes `X 0` and sends
  `X i ↦ X i + X 0^{r_i}`, and `varChange_leadingCoeff_isUnit` concerns `finSuccEquiv k n`, whose polynomial
  variable is `X 0`. This is the same convention as `Fin.tail`/`Fin.cons` in TauCeti. Leading coefficients
  multiply (the coefficient ring is a domain), and a divisor of a unit is a unit
  (`MvPolynomial.isUnit_iff_eq_C_of_isReduced`). The case `m = 0` is fine: the empty product is `1 ≠ 0`.
* **Prototype.** M1 compiles in 12 lines without unfolding `varChange`. The report's 45 lines is an overestimate.

### 1.7 Transport along automorphisms (M2): CONFIRMED

With `φ_e x = (eval x (e X_i))_i`:
* `eval x (e p) = eval (φ_e x) p`, by `MvPolynomial.induction_on`; compiled.
* `φ_e(φ_{e⁻¹} x)_i = eval x (e⁻¹(e X_i)) = x_i`; compiled as `polyMap_polyMap_symm`.

Hence `S = φ_{e⁻¹}⁻¹(S')`. Closedness of `S'` follows from continuity of `φ_e`. Basic closed sets come back as
`{e⁻¹(P) ≥ 0}` (B7 with `f i := e.symm (X i)`). Semialgebraicity of `S'` is not needed, because step 7 only needs
`A_ε(G)` semialgebraic, which is `isSemialgebraic_setOf_sign_eval`.

### 1.8 Derivative closure (M3): CONFIRMED

* The invariant "zero, or leading coefficient a nonzero constant" is preserved by `∂_t` (`leadingCoeff_derivative`;
  I checked that its `[HasUniqueDiv R]` instance is found for `MvPolynomial (Fin n) ℝ`).
* The index subtype `{(i,j) : Fin m × Fin (D+1) // ∂^j q_i ≠ 0}` is closed under (D), because `∂^{j+1} q ≠ 0`
  forces `j+1 ≤ natDegree ≤ D`.
* `g_i` is the member `(i,0)`; it is nonzero by (M).

### 1.9 Theorem FT (induction on the number of variables): CONFIRMED

I re-derived steps 1–8 independently.
* Base `n = 0`: `S = ∅` with `I = 0`, or `S = univ` with one empty intersection or the polynomial `1`.
* The adjustment `Φ'(σ) = Φ(i ↦ if f_i = 0 then 0 else σ_i)` with `f_i := 1` is correct.
* `S' = ⋃_{ε∈E} A_ε(G)` with `E` finite; `κ → SignType` is a `Fintype`.
* Closedness of `S'` gives `S' = ⋃ closure A_ε`. Theorem C applies, since its hypotheses are exactly the outputs of
  M1 and M3.
* `π(A_ε) ⊆ Fin n → ℝ` is semialgebraic (instance `HasSemialgebraicProjections ℝ`, `CAD/Existence.lean:102`). Its
  closure is semialgebraic (`Topology.lean:142`, `[Finite σ]`) and closed, so the induction hypothesis applies in
  exactly `n` variables.
* Pullback along `Fin.tail` is `rename Fin.succ` (`eval_rename`).
* Assembly uses B4, B5 and B8.

The final statement (M5, then the interface) coincides with the target of `R-common.md`: `IsBasicClosedUnion`
unfolds to the same `∃ I J P, s = ⋃ i, ⋂ j, {x | 0 ≤ eval x (P i j)}`. No lemma is used in a stronger form than
it is proved.

### 1.10 §6 (Theorem C′, Thom families, frontier condition): CONFIRMED (not needed for the target)

* **Theorem C′.** In case 1, `R°` is infinite, so all `ε_k ≠ 0`. Then `U_t` is an open neighbourhood of `p'` and
  meets `B` near `p'`. Case 2 is as before, with the representatives taken in `B`.
* **Thom families.** The induction is correct: `A_δ(K) ⊆ π(A_ε(G))` because `π(A_ε(G))` is a union of `K`-cells,
  and the pullback by `e⁻¹` is a homeomorphism.
* **Non-monotonicity example** `{1}` versus `{1, x²(x-1)}`: correct.

### 1.11 TauCeti inventory (§7.1): CONFIRMED

Every quoted name and line number was checked by grep:
* `Semialgebraic/Basic.lean` `:247`, `:302`, `:318`, `:325`, `:383`, `:414`;
* `CAD/Existence.lean` `:63`, `:90`, `:102`;
* `CAD/Basic.lean` `:97`, `:150`, `:203`, `:213`, `:234`, `:257`;
* `Stack/Delineation.lean` `:426`, `:454`, `:467`. These are used nowhere else, so "leaf lemmas" is correct.
* `Thom/Basic.lean` `:55`, `:366`, `:377`, `:399`; `Thom/Interval.lean:66`;
* `Semialgebraic/Thom.lean` `:286`, `:507`;
* `Dimension/Basic.lean:76`, `:248`; `Dimension/Closure.lean:47`;
* `Nash/OfSemialgebraic.lean:42`;
* `RealClosed/Sign.lean:35` (needs `[IsRealClosed R]`, which ℝ has);
* `MvPolynomial/Equiv.lean` `:143`, `:148`, `:200`.

The negative claims also hold:
* no closure or frontier statement about sign conditions or CAD cells;
* no strict dimension drop: `grep` finds no `semialgebraicDim … <`;
* no Łojasiewicz inequality, finiteness theorem or real spectrum, whether in `Geometry/RealAlgebraic` or in
  `Geometry/RealAnalytic/Semianalytic`.

Missed items, none of which gives a cheaper route:
* `PolynomialRolle.strictMonoOn/monotoneOn` (`Algebra/Polynomial/Rolle.lean`), usable for Lemma T;
* `IsSemialgebraic.exists_ne_zero_polynomial_of_interior_eq_empty` (`Semialgebraic/AlgebraicDependence.lean`), which
  is route 1's tool;
* `IsSemialgebraic.frontier`/`interior` (`Topology.lean`);
* the directory `Geometry/RealAnalytic/Semianalytic/*`, which the report did not list (nothing relevant there).

I looked specifically for anything that would give the finiteness theorem or closure control of cells more cheaply
and found nothing.

### 1.12 Mathlib dependencies (§7.2, §7.3): CONFIRMED

All 40 names quoted resolve at the pin (scratch `#check` file). One minor inaccuracy: the quoted signature of
`Polynomial.leadingCoeff_derivative` omits its `[HasUniqueDiv R]` hypothesis. The instance is found for
`MvPolynomial (Fin n) ℝ`, which I checked by compiling the M3 invariant step.

### 1.13 Other routes (§9): CONFIRMED

* **Literal CAD-cell route.** "Not correct as stated" is supported by E3, E4 and E6. The XL guess is labelled as a
  guess.
* **Real spectrum.** I read Schweighofer's TeX (lines 5672–5740). The direction "`S` open ⇒ `S̃` open" of Thm
  `finthmabstract` is proved by invoking `finthm`, and Remark `finthmabstractmotivates` derives `finthm` from it.
  The presentation is therefore circular for our purpose, as the report says. "Not viable at the present state of
  the libraries" is justified: there is no `Sper` in TauCeti, and the projection instance exists only for ℝ.
* **Induction on dimension.** E2 indeed has `dim Z = dim T = 1`, with `Z = {x = 0}`. "Not established" is an honest
  verdict.
* **Separation.** No claim is made.
* **Description of Schweighofer's Thm 6.3.3.** The functions `f = f_i²` and `g = ∏(|g_ij|+g_ij)` on
  `A = ℝⁿ \ S` are verified in the source.

### 1.14 Lean decomposition (§8): CONFIRMED with remarks

* The statements are faithful: coordinate 0 is `t`, `Fin.tail` is `π`, `finSuccEquiv` is consistent with
  `eval_eq_eval_mv_eval'`, and the inclusions go in the right direction.
* The dependency order is correct.
* Risks 1–6 are real. Risk 7 ("no mathematical risk") I agree with.

### 1.15 Effort estimate: CREDIBLE, somewhat optimistic in the large units

Calibration from my prototypes:
* Unit B (Lemma T) is 95 lines. The report says 100: exact.
* M1 is 12 lines. The report says 45: overestimated.

Probably underestimated:
* C3 (Theorem C, 200 lines): sequences, `Fin.cons` limits, two cases, the fibre bridge.
* M4 (200 lines): sign normal form, zero replacement, automorphism transport, derivative closure, cell union,
  closures, induction hypothesis, assembly.
* B1 (finite-union reindexing to `Fin I × Fin J` with padding).

My estimate is 1100–1600 lines (centre about 1300), all units M or L, no XL. The order of magnitude is right.

### 1.16 Comparison with the Łojasiewicz route (§9.2): CORRECTION NEEDED

The comparison table is out of date, and on two rows it is no longer fair:

* **"Dependence on Phase 2: none" versus "needs G4".** Presented as an advantage of route 2. `PLAN.md` §8 records
  Phase 2 as done: G4 is formalized and audited ACCEPT. Independence from G1–G4 is therefore worth nothing now.
* **"L1's one-parameter shortcut is unverified (R1)".** R1 now reports the shortcut correct after one repair
  (exponent `M → M+1`). R1 also reports that it elaborated the whole chain from G4 to the target in a scratch file,
  with clean axioms, in about 250–350 lines. That report is being audited separately, and I have not checked it.
* **Size.** Route 2 costs about 1100–1600 lines, against about 300 for the route 1 shortcut. If R1's audit passes,
  route 1 is 3–5 times cheaper and has a compiled prototype.

Route 2 keeps two real advantages: its mathematics is fully verified, here and by my prototypes of the key lemmas,
and it is independent of the analytic estimates. That makes it an excellent fallback.

---

## 2. Errors and gaps, ranked by severity

No mathematical error was found in Lemma T, Theorem C, the monic form, the transport, the derivative closure, the
induction FT, Theorem C′ or the Thom-family theorem. All counterexamples are correct.

1. **(Moderate; affects the recommendation, not the mathematics.)** The comparison in §9.2 and §10 relies on
   claims that are out of date: Phase 2 is done, so "independent of G1–G4" is no advantage, and the L1 shortcut is
   now verified by R1 with a reported ~300-line compiled prototype. §10's "primary route" recommendation should
   become "fallback route", conditional on the audit of R1.
2. **(Minor.)** §0 item 6 overstates the result: the change of coordinates is shown necessary only for Theorem C
   as formulated, not for the route or the theorem. The report itself says it did not investigate alternatives.
3. **(Minor.)** The effort distribution is off. M1 is about 15 lines, not 45. C3, M4 and B1 are likely
   underestimated. A realistic total is 1100–1600 lines rather than 900–1400.
4. **(Minor, citation.)** §7.2 quotes `Polynomial.leadingCoeff_derivative` without its `[HasUniqueDiv R]`
   hypothesis. The hypothesis is harmless here because the instance exists.
5. **(Cosmetic.)** E5 says "the roots `1/x`" where it means the roots of `∂²_t g` and `∂³_t g`. The inventory omits
   `PolynomialRolle.*` and `Geometry/RealAnalytic/*`; neither is relevant.

## 3. Overall verdict

**SOUND AFTER CORRECTIONS.** The corrections are 1 (comparison and recommendation) and 2 (wording of the
coordinate-change claim), plus the minor items 3–5. The repaired route (Lemma T → Theorem C → induction on the
number of variables) is correct and complete, and its final statement is the target. The diagnosis that the
literal hypothesis is false is correct.

**Auditor's opinion on which route to implement.** Implement route 1, the squared polynomial form of the Łojasiewicz
shortcut, provided its audit confirms R1's compiled prototype. It builds on G4, which is already done, and is about
4 times smaller. Keep route 2 (§§2, 4, 5, decomposition §8) as the documented fallback: it needs no new analysis,
and its riskiest pieces (Lemma T, M1, M2) are already confirmed by compiling prototypes. If R1's audit finds a gap
that is not repairable, route 2 should be implemented as decomposed in §8, budgeted at about 1300 lines.
