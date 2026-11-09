# Audit of research report R1 (route 1, Łojasiewicz) — Phase 3a

Audited: `notes/research/route1-lojasiewicz.md` (brief `notes/briefs/R1-lojasiewicz.md`). Auditor: adversarial research
auditor (brief `notes/briefs/audit-research.md`). Date: 2026-11-09. Pins: Mathlib `1b1ccf4b`, TauCeti `2c9b12be`.

**Overall verdict on the route: SOUND.** The recommended decomposition (F0, F1, F2, F3, L1, C1, C2, L2, L3a, L3)
is correct as stated, the final statement is the target of `R-common.md` character for character, and the Lean
prototype elaborates with clean axioms. I found no error in a lemma statement, constant, exponent or quantifier
of the recommended route. The errors found are in the report's prose (one inaccurate grep summary, one
mis-stated counterexample construction in §5, two overstatements); none changes a lemma or the plan for
Phase 3b. They are listed in §5 below and should be fixed in the final report `notes/finiteness-report.md`.

## 0. Method

1. Before reading each proof I derived the lemma myself (sketches below), then compared.
2. Read Schweighofer arXiv 2205.04211v1 myself (fetched with `curl` from arxiv.org, converted with `pdftotext`):
   Thm 6.1.18, Prop 6.2.1, Thm 6.2.2, Lemma 6.2.3, Cor 6.2.4, Thm 6.3.3, Example 6.3.4 (pp. 102–108).
   Bochnak–Coste–Roy not available (as for the report).
3. Extracted Appendix B verbatim into a scratch file in the session scratchpad (under `/tmp`) and ran
   `cd /home/user/Semialgebraic && . scripts/env.sh && lake env lean <file>`: no error, no warning, output
   `'Scratch.exists_eq_iUnion_iInter_nonneg' depends on axioms: [propext, Classical.choice, Quot.sound]`.
   Grep of the file for `sorry|admit|axiom|native_decide`: only the final `#print axioms` line. The
   `Growth/Main.olean` used is newer than `Growth/Main.lean` (20:25:32 vs 20:25:27), so the G4 that was linked is
   the current source.
4. `#check`ed every name of §4.3 in a second scratch file (all resolve, signatures as quoted) and spot-checked
   ~35 cited file/line locations by `sed -n` (all correct).
5. Numerical checks (Python, scratchpad) of the lemmas on concrete examples and of every counterexample of §3.6
   and §5 (all confirmed; details in the lemma sections).
6. Read the HardnessBilevel blueprint §4.B.4, §4.F (gad.G6, gad.G7, t215.core, t215.supset) and §4.G.4.

## 1. Textbook chain (report §2)

**T1 (Schweighofer 6.2.1). CONFIRMED.** Own proof: graph `Γ` of `h` has empty interior (an open box contains two
points with the same abscissa), so `P(t,s) ≠ 0` vanishes on `Γ` (TauCeti
`IsSemialgebraic.exists_ne_zero_polynomial_of_interior_eq_empty`, checked:
`TauCeti.IsSemialgebraic s → interior s = ∅ → ∃ p, p ≠ 0 ∧ ∀ x ∈ s, eval x p = 0`, over `ℝ` only). `P = ∑ q_i(t) s^i`,
`q_d ≠ 0`; `|q_d| ≥ δ` for `t ≥ t₀`; `d = 0` contradicts nonempty fibres above `t₀` (needs `t₀ > a`, harmless);
Cauchy bound `|s| ≤ 1 + ∑_{i<d} |q_i(t)|/δ ≤ c(1+t)^M`; `c(1+t)^M ≤ c 2^M t^M ≤ t^{M+1}` for `t ≥ max(1, c2^M)`.
Matches the report and the source (the source rescales so that `p_d > 1`; same thing).
Examples: `h(t) = t³` (`P = s − t³`, bound `t^3`); degenerate `h ≡ 0` (`P = s`, `d = 1`, all `q_i = 0` for `i < d`).

**T2 (6.2.2). CONFIRMED.** Own proof as in the source: `A_t = {|g| = 1/t}` compact, `f ≠ 0` there, fibrewise
supremum of `1/|f|` bounded by `t^N` for `t > b` (T1/G4), compact remainder `B = {|g| ≥ 1/b}` with `C ≥ 1`. The
report needs `C ≥ 1` in the case `t > b` and states it. Source matches (it uses min `f_t`, 6.1.18).
Examples: `A = [-1,1]`, `f = x², g = x` (`N = 2`, `C = 1`); degenerate `A = {0}`, `f = g = 0` (any `N ≥ 1`;
`N = 0` would fail, which is why `ℕ` starts at 1 in the source — checked: Schweighofer writes `ℕ₀` for the
naturals with 0).

**Lemma 6.2.3 (shrinking map). CONFIRMED.** Own check: `1 − ‖φ(x)‖² = 1/(1+‖x‖²)`, `1 + ‖ψ(y)‖² = 1/(1−‖y‖²)`;
closedness of `φ(A) ∪ S` by the sequence argument; converse because `φ(A) ∪ S` meets `𝔹` in `φ(A)`. The report's
sequence proof differs from the source's (which goes through `C ∩ 𝔹`) but is correct.

**T3 (6.2.4). CONFIRMED.** Own check of each step: (1) sphere-section suprema via G4 give
`|f|, |g| ≤ (1+‖x‖²)^ℓ` for `‖x‖ > b` (using `(1+t) ≤ 2(1+t²)` and enlarging the exponent by one); (2)
`|f₀| ≤ 1/(1+‖x‖²)`; (3) continuity at `y₀ ∈ S` with `δ = 1−ρ`, `ρ = r/√(1+r²)`: `‖y‖ > ρ ⇔ ‖ψ(y)‖ > r` because
`‖φ(x)‖` is increasing in `‖x‖`; (4) T2 on `Ã`, back-substitution
`|g|^N ≤ C(1+‖x‖²)^{(N−1)(ℓ+1)}|f|`. The source sets `k := max{1,(N−1)(ℓ+1)}` because its `ℕ` excludes `0`; the
report's `k ∈ ℕ` (possibly `0`) is equally correct. The report replaces the source's compact set `B` by an
explicit radius; correct.
Examples: `A = ℝ`, `f = x`, `g = x` (`N = 1`, `k = 0`); `A = {xy = 1, x ≥ 0}`, `f = y`, `g = 1` (`k ≥ 1` needed).

**T4 (6.3.3). CONFIRMED.** Checked against the source line by line: `A = ℝⁿ∖U`, `f = f_i²`,
`g = ∏(|g_ij| + g_ij)`, `V = {C(1+∑x_j²)^k f_i² < (2^m ∏g_ij)^N, g_ij > 0}`; on `V` all `g_ij > 0` so
`g = 2^m ∏ g_ij`; `V ∩ A = ∅` by the strict inequality; the piece lies in `V` because `f_i = 0` and the right side
is `> 0`. `m = 0`: `g = 1`, fine.

**§2.5 (where uniformity enters).** The claim that, in Schweighofer, uniformity over coefficient tuples enters
only in the proof of Thm 6.1.18 (transfer from `ℝ`) is **confirmed** by the source (p. 102–103: "We fix a
complexity bound N … By 1.8.5, (∗) now holds either for all or for no real closed field R"). The BCR part is from
memory and correctly labelled unverified; nothing depends on it. The table entry "uses of one-variable growth: 3"
is a fair count (6.2.2 once, 6.2.4 for `f̊` and `g̊`).
The remark "the right-hand form implies the left-hand one" (`1 + g² ≤ (1+L²)(1+‖x‖²)^{2d}`) is correct; taking
the square root produces a half-integer exponent of `1+‖x‖²`, which is absorbed because the base is `≥ 1`. Not
used.

## 2. The candidate shortcut (report §3)

### 2.1 The plan's L1 (PLAN §4.4), as stated

My own derivation of the plan's idea, before reading §3: `K_t = {x ∈ T | N(x) ≤ t ∧ 1 ≤ t|g x|}` is closed and
bounded, `f ≠ 0` on it; `E_t = {1/|f(x)| : x ∈ K_t}` is bounded; G4 bounds its least upper bound for `t ≥ t₀`.
For `x ∈ T`, `g(x) ≠ 0`, put `t = max(t₀, N(x), 1/|g(x)|)` (no need for the monotonicity of `K_t`), then
`1/|f| ≤ c(1+t)^M` and `1+t ≤ (1+t₀)(1+N)(1+|g|)/|g|`, so `|g|^M ≤ c(1+t₀)^M |f| ((1+N)(1+|g|))^M`. At a point
with `g(x) = 0` (hence possibly `f(x) = 0`) the left side is `c·0^M`, which is `c > 0` when `M = 0`
(`0^0 = 1`): the inequality fails if `f(x) = 0`. Raising to `M+1` repairs it, since `|g| ≤ 1+|g| ≤` weight. I
reached exactly the report's diagnosis independently. **The plan's statement of L1 is true** (deduce it from
the report's squared L1: `|g|^{M'} ≤ √C |f| ((1+N)(1+g²))^{M'/2} ≤ √C |f| ((1+N)(1+|g|))^{M'}`, and
`c := 1/(C+1)` works since `√C ≤ C+1`); the report's "take `1/(C+1)`" is right but this square-root step is not
written out.

The report's witness that G4 may return `M = 0` (`T = {0}`, `f = g = X`, `E = ∅`) is correct: `K_t` needs
`1 ≤ t·0`, so `E = ∅` and every triple is a valid G4 output.

### 2.2 The report's L1 (squared form). CONFIRMED.

Statement: `∃ C ≥ 0, M, ∀ x ∈ T, g^{2(M+1)} ≤ C f² ((1+N)(1+g²))^{M+1}`, with `C = c(1+t₀)^{M+1}`.
Own check of each step: Step 2, box `|x_i| ≤ (x_i²+1)/2 ≤ (t+1)/2 ≤ 1+|t|` (valid for every real `t`; for `t < 0`
the set is empty). Step 4, `x ∈ K_t` for `t = max(t₀, N, 1/g²)` because `t·g² ≥ (1/g²)·g² = 1`. Step 5,
`(1+t)g² ≤ (1+t₀+N)g² + 1 ≤ (1+t₀)(1+N)(1+g²)`: the difference is `t₀ + N + t₀N + t₀Ng² ≥ 0` (expanded by hand).
The factor `(1+t)^M ≤ (1+t)^{M+1}` and the case `g(x) = 0` (`0^{2(M+1)} = 0` since `2(M+1) ≥ 2`) are right. The
hypothesis `F ≠ 0` of F3 is necessary (in Lean `1/0 = 0` would make `h` vacuous). The weight `(1+g²)` instead of
`(1+|g|)` is what makes `q` in C1 a polynomial; correct.

Tests (numerical, 10⁴ random points each):
* `T = ℝ`, `f = X²`, `g = X`: `sup E_t = t²` for `t ≥ 1`, so `(c, M, t₀) = (1, 2, 1)` is a valid G4 output and
  `C = 8`; `x⁶ ≤ 8x⁴((1+x²)²)³` holds. With exponent `1` (i.e. G4 returning `M = 0`) it fails at `x = 10⁻³`, which
  confirms that the exponent must come from G4 and cannot be fixed a priori.
* `T = {xy = 1, x ≥ 0}`, `f = Y`, `g = 1` (unbounded): `sup E_t ≤ t`, `(1,1,0)` valid, `C = 1`;
  `1 ≤ y²(2(1+x²+y²))²` holds for `x ∈ [e⁻⁸, e⁸]`.
* degenerate `T = {0}`, `f = g = X`: conclusion `0 ≤ 0`.

### 2.3 C1 (basic open set between a cell and `U`). CONFIRMED.

Own proof: `T = Uᶜ ∩ ⋂_j {g_j ≥ 0}` closed sa; `x ∈ T`, `f(x)=0`, `∏g_j(x) ≠ 0` forces every `g_j(x) > 0`, so
`x ∈ B ⊆ U`, contradiction; L1 gives `C, M`; `q = g^{2(M+1)} − C f²((1+∑X_i²)(1+g²))^{M+1}`; on `B`, `q = g^{2(M+1)} > 0`;
on `B' ∖ U`, `x ∈ T` and L1 gives `q ≤ 0`. `k = 0`: `g = 1`, hypothesis "`f ≠ 0` on `Uᶜ`" holds. `f = 0`: `B' = B`.
`C = 0` is a legitimate L1 output (e.g. when `g = 0` on `T`) and C1 still works.
Tests: `U = ℝ²∖{0}`, cell `{X = 0, Y > 0}`: `T = {0}`, `C = 0` allowed, `B' = {Y > 0} ⊆ U`.
`U = {Y(1+X²) < 1}`, cell `{Y = 0}` (`f = Y²`, `k = 0`, `T` unbounded and asymptotic to `B`): `1/y⁴ ≤ (1+x²)⁴ ≤
(1+t)⁴` on `K_t`, `(1,4,0)` valid, `C = 1`, `q = 1 − Y⁴(2(1+X²+Y²))⁵`; on 2·10⁵ random points `q > 0 ⇒ y(1+x²) < 1`.
Degenerate: `U = univ` (`T = ∅`), `U = ∅` (the cell is empty, `B' ⊆ ∅` because `T = {g_j ≥ 0}` and L1 forces
`q ≤ 0` there).

### 2.4 C2 (sign cell = one equation + `m` strict inequalities). CONFIRMED.

`f_ε = ∑_{ε_i = 0} p_i²` vanishes iff each such `p_i` does; `g_{ε,i} = 1, p_i, −p_i`; `sign a = 0 ↔ a = 0`,
`= 1 ↔ 0 < a`, `= −1 ↔ a < 0` (checked in Mathlib, `Mathlib/Basic/Sign/Defs.lean:311, 286, 292`). Examples: `m = 0`
(`f = 0`, cell = univ), `p = (X)`, `ε = (−1)` (`{−X > 0}`).

### 2.5 L2 (open sets). CONFIRMED.

TauCeti's normal form (checked at `Basic.lean:383`): `∃ m p Φ, s = {x | Φ (fun i => sign (eval x (p i)))}` with
`Φ` an arbitrary predicate (no finiteness or decidability needed: `Fin m → SignType` is a `Fintype`). Every
`x ∈ U` lies in the cell of its own sign vector, which satisfies `Φ`; each such cell is `⊆ U`; C1 gives `B'_ε`
with `m+1` polynomials (`Fin.cons q g`); `U = ⋃_ε B'_ε`; reindex `{ε // Φ ε}` by `Finite.equivFin`. Uniform `J = m+1`
by construction, so no padding problem. The passage from sign cells to the open case has no gap.

### 2.6 L3a / L3 (complement, distributivity, `Fin` reindexing). CONFIRMED.

`x ∉ ⋃_i ⋂_j {Q_ij > 0} ⇔ ∀ i ∃ j, Q_ij(x) ≤ 0 ⇔ ∃ φ : Fin I → Fin J, ∀ i, 0 ≤ −Q_{i,φ i}(x)`;
`finFunctionFinEquiv : (Fin n → Fin m) ≃ Fin (m ^ n)` (checked, `Mathlib/Algebra/BigOperators/Fin.lean:577`) with
`n = I`, `m = J` gives `Fin (J^I)`; `P k i = −Q i (e.symm k i)`, so `I' = J^I`, `J' = I`. Edge cases checked by
enumeration for `I, J ∈ {0,…,3}` (`|Fin I → Fin J| = J^I`, `0^0 = 1`): `I = 0` ⇒ `s = univ` = one empty
intersection; `J = 0 < I` ⇒ `s = ∅` = empty union; `I = J = 0` ⇒ `s = univ`, `J^I = 1`. Direction of the
inclusions and of the sign (`0 ≤ −Q`) correct. L3 = L2 on `sᶜ` (`hs.compl`, `hc.isOpen_compl`) + L3a +
`compl_compl`.

### 2.7 Plan's L2/L3 "correct as stated" — CONFIRMED WITH CORRECTION (prose only)

PLAN §4.4 writes `B' = {g_j > 0 ∀ j, c² g^{2M} > f² (…)^{2M}}` with `(…) = (1+‖x‖²)(1+|g|)`. Literally this is
**not** a polynomial inequality (`(1+|g|)^{2M}` is not a polynomial), so `B'` as written is not basic. It becomes
basic after replacing `|g|` by `g` (legitimate on `{g_j > 0}`, where `g > 0`) or by the report's `(1+g²)` weight.
The report's verdict "L2 and L3 are correct as stated" (§0 item 2, §3.4) should say "correct after replacing
`|g|` by `g` in `B'` (or using the squared form)". The recommended variant already does this, so the route is
unaffected.

### 2.8 §3.4 attack table and §3.5 variant

Every row checked; all correct (emptiness of `K_t`/`E_t`: G4 is vacuous on empty fibres since `IsLUB ∅ s` is
impossible in `ℝ`, and the proof only evaluates G4 at a `t` whose fibre contains `1/f(x)²`; compactness for all
real `t`; the range `0 ≤ t < t₀` is bypassed by `max` with `t₀`; the plan's monotonicity argument is also valid
because `K_t ⊆ K_{t'}` for `0 ≤ t ≤ t'`; `ι` empty). The remark that `{(u,t) | u = −f(x)²}` is useless is right.
The merged variant of §3.5 (`K_t = {x ∈ Uᶜ | N ≤ t ∧ ∀ j, 1 ≤ t g_j}`,
`∏ g_j^M ≤ C f² ((1+N)∏(1+g_j))^M` on `Uᶜ ∩ {g_j > 0}`) is correct by the same computation; notably it does not
need the `M+1` repair because its domain excludes `g_j = 0`.

### 2.9 §3.6 counterexamples — all CONFIRMED by computation

1. `T = {xy = 1, x ≥ 0}`, `f = y`, `g = 1`: `C ≥ x → ∞` needed without weight.
2. Exponent 0: correct in substance (slight overstatement: a proof outputting `N = 0` is wrong only when `f` has
   zeros on the set).
3. `{x²(x−1) ≥ 0} = {0} ∪ [1,∞)` vs closure `[1,∞)` of `{x²(x−1) > 0}` (grid check).
4. Slashed square: confirmed in the source (Example 6.3.4, p. 107–108).
5. `T = (0,1]²`, `f = X`, `g = Y`: right side at `(10⁻⁶, 1)` is `≈ C·4^{M+1}·10⁻¹²` for every `M`; fails.
6. `U = {0}`: `{q > 0}` is open; correct.

## 3. Lemma list (report §4.1), Lean-level faithfulness

| id | verdict | note |
|---|---|---|
| F0 | CONFIRMED | `u ≤ s ≤ |s| ≤ c(1+t)^M` with `s` from `Real.exists_isLUB`; `hbdd` must hold for all `t` and does (empty fibres are bounded). |
| F1 | CONFIRMED | `![u,t] 0 = u`, `![u,t] 1 = t` matches G4's convention (coordinate 0 value, 1 parameter); projection by `setOf_exists_sumElim` with `τ := ι` (`[Finite τ]`). |
| F2 | CONFIRMED | box argument valid for all real `t`; `ι` empty fine. |
| F3 | CONFIRMED | hypotheses `F ≠ 0`, `G ≠ 0`, `0 ≤ c, t₀, N` are exactly what is needed. |
| L1 | CONFIRMED | see §2.2. |
| C1 | CONFIRMED | see §2.3. |
| C2 | CONFIRMED | no `[Fintype ι]` needed; fine. |
| L2 | CONFIRMED | see §2.5. |
| L3a | CONFIRMED | see §2.6. |
| L3 | CONFIRMED | statement identical to the target of `R-common.md` (`{ι : Type}`, `[Fintype ι]`, `MvPolynomial.eval x (P i j)`). |

No lemma is used in a stronger form than stated (checked in the prototype: C1 calls L1 with `g := ∏ j, g j`, L2
calls C1 and C2 exactly as stated, L3 calls L2 and L3a). The dependency order of §4.2 is right (F1–F3 do not depend
on F0; the arrow `F0 → {F1,F2,F3}` is only an ordering, harmless).

## 4. Lean dependencies (report §4.3)

All 45 names `#check`ed at the pins: every one resolves, with the quoted hypotheses (e.g. `isCompact_univ_pi`,
`IsCompact.bddAbove_image [ClosedIciTopology α] [Nonempty α]`, `ContinuousOn.inv₀`,
`Finset.sum_eq_zero_iff_of_nonneg`, `Finite.equivFin`, `finFunctionFinEquiv {m n} : (Fin n → Fin m) ≃ Fin (m ^ n)`,
`Function.Surjective.iUnion_comp`, `Set.mem_ofPred_eq`, the TauCeti `exists_eq_setOf_sign_eval`,
`setOf_exists_sumElim [HasSemialgebraicProjections R] [Finite τ]`, `preimage_comp`, `isSemialgebraic_eval_le
[IsOrderedAddMonoid R]`, `isSemialgebraic_eval_eq`, `isSemialgebraic_eval_nonneg`, `compl`, `inter`,
`iInter [Finite ι]`, instance `HasSemialgebraicProjections ℝ` at `CAD/Existence.lean:102`). Universe levels of the
TauCeti lemmas are independent (`u_1, u_2, u_3`), as claimed. ~35 file:line locations spot-checked by `sed`: all
correct. `Set.iInter_iUnion_distr` indeed does not exist (no grep hit for `iInter_iUnion_distr` in Mathlib).
TauCeti has `IsSemialgebraicOn.{add, mul, sub, neg, comp, glue}` and no `abs`/`inv`/`div`/`sqrt` analogue (grep),
as the report says.

**Inaccuracy:** "grep for `ojasiewicz` … in TauCeti: only unrelated hits in `Geometry/Manifold/Morse` and
bibliography entries". The grep actually hits 93 lines in 44 files, including theorems in
`Analysis/Calculus/Morse/Basic.lean:459`, `Analysis/Calculus/Morse/Linearization.lean:432` (Morse form of the
gradient inequality), and Łojasiewicz's triangulation lemmas (`Topology/Order/RegionBetween.lean:134,172`,
`Analysis/Convex/SimplicialComplex/Rectilinear.lean:607`, `…/PartiallySemialgebraic/NonsingularDirection.lean:135,165`).
I read every hit: none is a Łojasiewicz inequality for semialgebraic sets/functions, and there is no finiteness
theorem or notion of basic open/closed set in TauCeti. So the conclusion stands; the description of the grep is
wrong.

## 5. FT′ (report §5)

* **FT ⇒ FT′ gadget. CONFIRMED.** `(∃ z ∈ [0,½], p = (p²+1)z) ↔ 0 ≤ p` (checked numerically, 10⁴ samples);
  `⋃_i ⋂_j {P_ij ≥ 0} = {∃ z ∈ [0,½]^{I×J}, ∏_i ∑_j G(P_ij, z_ij) = 0}`, including `I = 0` (`∏ = 1`, empty) and
  `J = 0` (`∑ = 0`, univ). Agrees with blueprint gad.G6/G7 (lines 1236–1261). `[0,1]^k` vs `[0,½]^k` equivalent.
* **Direct FT′ from L2. CONFIRMED.** `K = ⋂_i ⋃_j {−Q_ij ≥ 0} = {∃ z, ∑_i ∏_j G(−Q_ij, z_ij) = 0}` (the
  "intersection of unions" gadget, a different gadget from gad.G7; `J = 0` gives `∑_i 1 = I`, correct).
* **FT′ suffices for Thm 2.15. CONFIRMED.** `t215.core` (blueprint 1265–1283) uses `E` only through (★★); with
  `R₀` from FT′, `R(x,t,z) := R₀(x, t·w(x), z)²` is `≥ 0` and polynomial because `w` is a polynomial (step 1 of
  `t215.supset`).
* **FT′ does not suffice for Thm 2.20. CONFIRMED, on the `t220.core` route.** The argument
  (`f = 1_{Dᶜ}` lsc, `D = {f ≤ 0} = ⋃_l (B_l ∩ {−p_l ≥ 0})`) is correct, so on that route the hypothesis is
  equivalent to the full finiteness theorem. That no *other* route to 2.20 could use FT′ is not shown (the
  blueprint itself says "unclear"); the report's heading should carry the qualifier "on this route".
* **Error in the "formal shortcut fails" illustration.** The report describes the shortcut as "`g > 0 ↔ ∃ y,
  g y² = 1`, then compactify the fibre" and then exhibits the lift `{x²(x−1) = z², z ∈ [0,1]}`. That lift is the
  lift of `g ≥ 0` (`g = z²`), not of `g y² = 1`. A faithful compactification of `g y² = 1` (e.g.
  `z = 1/(1+y²) ∈ (0,1]`, i.e. `g(1−z) = z`, closed up to `z ∈ [0,1]`) projects onto `{g ≥ 0} = {0} ∪ [1,∞)`,
  which also contains the spurious point `0`. So the conclusion ("the formal shortcut fails") is right but the
  displayed set is the wrong one. (The report's displayed projection `{0} ∪ [1, x₁]`, `x₁²(x₁−1) = 1`, is itself
  correct for the displayed lift: grid check gives `{0} ∪ [1, 1.465]`.)
* **Cost judgement** (FT′ not materially cheaper; all of F0–L2 needed). Agreed; it is an opinion, labelled as such.

## 6. Prototype (Appendix B)

Compiles at the pins (26 s wall clock with caches), no `sorry`/`admit`/`axiom`/`native_decide`, axioms
`[propext, Classical.choice, Quot.sound]`; the last theorem's statement equals the target (namespace `Scratch`
instead of `Semialgebraic.Interface`). It confirms the lemma statements of §4.1 elaborate and chain. It is evidence
only; my verdicts above rest on the re-derivations.

## 7. Effort and risks (report §4.2, §4.4)

* Effort S–M, 250–350 lines: **credible** — a complete compiling prototype of ~270 lines exists. Expect overhead
  for the library's conventions (specific imports instead of `Mathlib.Tactic`, docstrings, namespace), perhaps
  +30–50%.
* Risks listed are real and already solved in the prototype. Missing, low: (a) the prototype's `simp` calls in F1,
  C1 (`simp [eval_rename]`, `simp only [... zero_pow ...]`) are normal-form dependent and may need adjusting when
  imports are narrowed; (b) narrowing `import Mathlib.Tactic` may require several tactic imports
  (`Mathlib.Tactic.Positivity`, `GCongr`, `FieldSimp`, `Linarith`, `Ring`) — not a mathematical risk; (c) the
  shape-check file for A2 is not yet written. "No mathematical risk remains for ℝ": agreed.

## 8. Errors and corrections, ranked by severity

None is a mathematical error in the recommended route. All are report-text corrections.

1. **(minor, factual)** §4.3 "Missing in TauCeti/Mathlib as mathematics": the description of the `ojasiewicz` grep
   is wrong (many hits outside `Geometry/Manifold/Morse`, including theorems: the Morse form of the gradient
   inequality and Łojasiewicz's triangulation lemmas). The conclusion (no semialgebraic Łojasiewicz inequality, no
   finiteness theorem, no basic sets in TauCeti) is correct.
2. **(minor, mathematical prose)** §5 "formal shortcut" illustration: the displayed lift `{x²(x−1) = z²}` is the
   lift of `g ≥ 0`, not of `g y² = 1`; replace by `{g(1−z) = z, z ∈ [0,1]}`, whose projection `{0} ∪ [1,∞)` still
   shows the spurious point `0`.
3. **(minor, overstatement)** §0 item 2 / §3.4: the plan's L2 is "correct as stated" only after `|g|` is replaced by
   `g` in `B'` (the plan's `(1+|g|)^{2M}` is not a polynomial). The recommended squared form already fixes it.
4. **(minor, gap in prose)** §3.4 "for the plan's form take `1/(C+1)`": correct, but the passage from the squared
   inequality to the plan's unsquared one (`√` and `(1+g²)^{1/2} ≤ 1+|g|`, `√C ≤ C+1`) is not written.
5. **(cosmetic)** §5 heading "FT′ does not suffice for Theorem 2.20" should read "on the `t220.core` route"
   (the body says so). §3.6 item 2 slightly overstated. §4.2 order "F0 → {F1, F2, F3}" is not a dependency.

**Verdict: SOUND.** The route F0 → F1, F2, F3 → L1 → C1; C2 → L2 → L3a → L3 can be implemented in Phase 3b as
specified in §4.1 of the report, with the Lean statements given there unchanged.
