# Phase 3a report: choosing a proof route for the finiteness theorem (A2)

Orchestrator's consolidation of two research reports and their independent audits.

| document | author | content |
|---|---|---|
| `notes/research/route1-lojasiewicz.md` | research agent R1 | the route through the Łojasiewicz inequality |
| `notes/audit/R1-lojasiewicz.md` | Opus auditor | adversarial audit of R1 — verdict **SOUND** |
| `notes/research/route2-cad-thom.md` | research agent R2 | cylindrical decomposition, Thom's lemma, other routes |
| `notes/audit/R2-cad-thom.md` | Opus auditor | adversarial audit of R2 — verdict **SOUND AFTER CORRECTIONS** |

Target (the field of `Bilevel.HasFinitenessTheorem`, in TauCeti's vocabulary):

```lean
theorem Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg {ι : Type} [Fintype ι] {s : Set (ι → ℝ)} :
    TauCeti.IsSemialgebraic s → IsClosed s →
    ∃ (I J : ℕ) (P : Fin I → Fin J → MvPolynomial ι ℝ),
      s = ⋃ i, ⋂ j, {x | 0 ≤ MvPolynomial.eval x (P i j)}
```

## 1. Recommendation

**Implement route 1 in its streamlined form** (R1 §3–4): the finiteness theorem for open sets from a weighted
Łojasiewicz inequality for polynomials on a closed semialgebraic set, itself obtained in one step from the growth
lemma G4 of Phase 2 through a one-parameter exhaustion. About 300–350 lines of Lean in three small units; nothing
has to be added to Mathlib or TauCeti; the only Phase 2 input is `Semialgebraic.exists_growth_isLUB`, already
audited.

Route 2 (repaired Thom-lemma route, R2 §4–5, §8) is kept as the documented fallback: independent of G1–G4, about
1100 lines.

## 2. The routes compared

| | route 1, textbook (Schweighofer §6.2–6.3) | route 1, streamlined (chosen) | route 2, as hypothesised | route 2, repaired | real spectrum | induction on dimension |
|---|---|---|---|---|---|---|
| correct | yes (re-derived by R1 and by the auditor) | yes (R1, auditor; now proved in Lean) | **no** (counterexamples) | yes (R2 and its auditor) | circular in the source checked | no complete argument found |
| needs from TauCeti | projection, sign normal form | projection, sign normal form, empty-interior ⇒ hypersurface (via G1) | — | projection, closure, sign normal form | real spectrum (absent) | `dim (closure S \ S) < dim S` (absent) |
| needs from Phase 2 | G1/G2 | G4 | — | nothing | — | — |
| extra infrastructure | calculus of continuous semialgebraic functions (abs, quotient, shrinking map, extension by zero) | none | — | one-variable Thom lemma with relaxed endpoints, closure formula, monic form by a polynomial automorphism, bookkeeping of basic closed sets | large | large |
| estimated Lean size | 1100–1500 lines | 300–350 lines | — | about 1300 lines (1100–1600 after audit) | not estimated | not estimated |
| main risk | size | none mathematical; set-builder and `simp` friction (solved in the prototype) | — | `finSuccEquiv`/`Fin.cons` plumbing, root bounds, union bookkeeping | — | — |

### 2.1 The hypothesis on cylindrical decomposition is false as stated

"The closure of a cell of a decomposition adapted to a derivative-closed family is obtained by relaxing its strict
sign conditions" fails in several variables (R2 §3, each verified by hand there):

* `{x t, x}`, closed under `∂/∂t`: the cell `{t = 0, x > 0}` relaxes to a set containing the whole `t`-axis.
* `g = y (2x² + 3xy + 2y²)` with all its partial derivatives: `(1, 0)` lies in a relaxed cell but not in the closure
  of the cell. Closure under all partial derivatives does not help.
* The Whitney umbrella family `{x² − z y², 2x, 2}`, monic and derivative-closed in the fibre variable: the relaxed
  cell still contains the handle.
* A 7-cell decomposition adapted to `{X₀ X₁}` that satisfies TauCeti's `IsCAD` has a cell whose closure is not a
  union of cells. TauCeti's CAD cells are abstract (locally closed, connected); they carry no sign description and no
  control of closures or frontiers, and TauCeti has no multivariate Thom lemma in closure form.

### 2.2 What repairs it (R2 §4–5)

For a finite family that is closed under `∂/∂t` up to zero and whose members have nonzero *constant* leading
coefficient in `t`: `closure A_ε = Ā_ε ∩ π⁻¹(closure π(A_ε))` (cell, relaxed cell, projection forgetting `t`). The
finiteness theorem then follows by induction on the number of variables, after a polynomial change of coordinates
(Mathlib's `NoetherNormalization.varChange_leadingCoeff_isUnit`); monicity cannot be dropped. This uses none of
TauCeti's CAD beyond Tarski–Seidenberg itself.

## 3. The chosen route: statements and proof

Notation `N(x) = ∑ i, x i ^ 2`. All statements are over `ι` with `[Fintype ι]`, polynomials in `MvPolynomial ι ℝ`.

* **F0** (`exists_growth_of_bddAbove_fibres`). `E ⊆ ℝ²` semialgebraic with every fibre `{u | (u, t) ∈ E}` bounded
  above ⇒ `∃ c ≥ 0, M, t₀ ≥ 0, ∀ t ≥ t₀, (u, t) ∈ E → u ≤ c (1 + t)^M`. (G4 and `Real.exists_isLUB`.)
* **L1** (`exists_lojasiewicz`). `T` closed semialgebraic, `f = 0 → g = 0` on `T` ⇒
  `∃ C ≥ 0, M, ∀ x ∈ T, g(x)^{2(M+1)} ≤ C f(x)² ((1 + N(x))(1 + g(x)²))^{M+1}`.
  *Proof.* `E := {(u, t) | ∃ x ∈ T, N(x) ≤ t ∧ 1 ≤ t g(x)² ∧ u f(x)² = 1}` is semialgebraic (projection, F1).
  `K_t := {x ∈ T | N(x) ≤ t ∧ 1 ≤ t g(x)²}` is compact (F2) and `f ≠ 0` on it, so the fibre `E_t` is bounded above.
  F0 gives `(c, M, t₀)`. For `x ∈ T` with `g(x) ≠ 0`, `t := max(t₀, N(x), 1/g(x)²)` puts `(1/f(x)², t)` in `E`, so
  `1/f(x)² ≤ c (1 + t)^M`, and `(1 + t) g(x)² ≤ (1 + t₀)(1 + N(x))(1 + g(x)²)` (F3). `C := c (1 + t₀)^{M+1}`.
  For `g(x) = 0` the left side is `0` because the exponent is positive.
* **C2** (`exists_setOf_sign_eq_eq`). A sign cell of `m` polynomials is `{f = 0, g₁ > 0, …, g_m > 0}`.
* **C1** (`exists_pos_between`). `U` open semialgebraic, `B = {f = 0, g_j > 0} ⊆ U` ⇒ a polynomial `q` with
  `B ⊆ {q > 0, g_j > 0} ⊆ U`: L1 on `T := Uᶜ ∩ ⋂_j {g_j ≥ 0}` with `g := ∏ g_j`, and
  `q := g^{2(M+1)} − C f² ((1 + N)(1 + g²))^{M+1}`.
* **L2** (`exists_eq_iUnion_iInter_pos`). An open semialgebraic set is `⋃_{i} ⋂_{j} {Q_ij > 0}`: sign normal form
  (`TauCeti.IsSemialgebraic.exists_eq_setOf_sign_eval`), C2 and C1 on each cell contained in `U`.
* **L3a** (`compl_iUnion_iInter_pos`), **L3** (`exists_eq_iUnion_iInter_nonneg`). Complement and distributivity,
  indexing choice functions by `finFunctionFinEquiv : (Fin I → Fin J) ≃ Fin (J ^ I)`.

Corrections that the research made to the orchestrator's sketch in `PLAN.md` §4.4 (all adopted):

1. **Exponent.** With the exponent `M` returned by the growth lemma the inequality is false when `M = 0` at points
   where `f = g = 0` (`0 ^ 0 = 1`); example `T = {0}`, `f = g = X`. The exponent must be `M + 1`.
2. **Squares instead of absolute values**, so that `E` and `q` are polynomial with no case distinction (the sketch's
   `B'` contained `(1 + |g|)`, which is not a polynomial).
3. The restriction `1 ≤ t` and the monotonicity argument for `t ≤ t₀` are unnecessary (`t ≥ t₀` by construction).
4. The constant is placed on the right-hand side (`C ≥ 0`), since the growth lemma gives `c ≥ 0`, not `c > 0`.

Facts that are false as carelessly stated (R1 §3.6, verified by the auditor): the unweighted inequality on an
unbounded closed set; the inequality with exponent `0`; L1 without closedness of `T`; C1 without openness of `U`;
"the closure of a basic open set is the relaxed set" (`{x²(x − 1) > 0}`).

## 4. Units of Phase 3b

| unit | file | content | depends on |
|---|---|---|---|
| P3-a | `Semialgebraic/Finiteness/Lojasiewicz.lean` | F0, F1, F2, F3, L1 | `Growth/Main.lean` |
| P3-b | `Semialgebraic/Finiteness/Cells.lean` | C2, L3a | Mathlib only |
| P3-c | `Semialgebraic/Finiteness/Main.lean`, `Semialgebraic/Interface/Finiteness.lean`, `SemialgebraicCheck/A2.lean` | C1, L2, L3, interface theorem, shape check | P3-a, P3-b |

Briefs: `notes/briefs/P3-a-lojasiewicz.md`, `P3-b-cells.md`, `P3-c-finiteness.md`. P3-a and P3-b run in parallel,
P3-c after both. Each is audited by a Sonnet auditor (`notes/briefs/audit-lean.md`).

## 5. The weaker statement FT′

FT′: every closed semialgebraic `K ⊆ ℝ^ι` is `{x | ∃ z ∈ [0, 1/2]^k, R(x, z) = 0}` for a polynomial `R`.

* FT ⇒ FT′ by the gadget `0 ≤ p ↔ ∃ z ∈ [0, ½], p = (p² + 1) z` (HardnessBilevel `gad.G6`/`gad.G7`).
* FT′ suffices for Theorem 2.15: its core lemma consumes the closed epigraph only through such a
  bounded-quantifier zero-set description, and the lower level has no convexity requirement.
* FT′ does not suffice for Theorem 2.20 on the `t220.core` route: the lower-level objective must be convex in the
  lower variable, which needs a decomposition of `{f ≤ p_i}` into *basic closed* pieces. On that route the hypothesis
  is equivalent to the full theorem (for `D` closed semialgebraic, apply it to the indicator of `Dᶜ`). Whether some
  other proof of Theorem 2.20 could use FT′ is open.
* FT′ is not materially cheaper on the chosen route: it needs F0–L2 unchanged, saves L3a (about 15 lines) and costs
  a gadget lemma. It is therefore not a separate target.

## 6. Audits

* **R1: SOUND.** Every lemma was re-derived independently before reading the report's proof, tested on concrete and
  degenerate examples, the 45 Lean names were resolved at the pins, and the scratch prototype of the whole chain
  compiles with axioms `[propext, Classical.choice, Quot.sound]` and the target statement as its last theorem. The
  corrections concern wording only: (1) the report under-describes what a grep for "Łojasiewicz" finds in TauCeti
  (TauCeti has Łojasiewicz-type statements in Morse theory and triangulation lemmas, but no Łojasiewicz inequality
  for semialgebraic sets, no finiteness theorem, no basic sets — conclusion unchanged); (2) an example in the FT′
  section used the wrong lift (conclusion unchanged); (3) two overstatements about `PLAN.md` §4.4, covered by the
  list of corrections in §3 above.
* **R2: SOUND AFTER CORRECTIONS.** No mathematical error. Lemma T, the closure formula (Theorem C), the necessity
  counterexamples, the monic form, the transport along polynomial automorphisms and the induction were re-derived
  independently; the counterexamples were checked by hand and by exact rational arithmetic; the inventory of TauCeti
  (no closure or frontier control of CAD cells, no finiteness theorem, no semialgebraic Łojasiewicz inequality, no
  real spectrum, no strict dimension drop for frontiers) was confirmed by grep, and the circularity of the
  real-spectrum route was confirmed in Schweighofer's source. Scratch prototypes of Lemma T (95 lines) and of the
  monic form through Mathlib's `varChange` (12 lines) compile. Corrections: (1) R2's comparison with route 1 was
  written before R1 finished and is out of date — its "primary route" becomes the fallback; (2) the change of
  coordinates is needed for Theorem C as formulated, not shown to be needed by every Thom-type route; (3) the effort
  is more likely 1100–1600 lines than 900–1400 (no unit XL). The auditor's own recommendation is route 1, with
  route 2 as documented fallback (budget about 1300 lines).

Both audits therefore support the recommendation of §1.

## 6a. Outcome of Phase 3b

Route 1 was implemented as planned (units P3-a, P3-b, P3-c, each audited ACCEPT): 523 lines of Lean in
`Semialgebraic/Finiteness/` and `Semialgebraic/Interface/Finiteness.lean`. The interface theorem
`Semialgebraic.Interface.exists_eq_iUnion_iInter_nonneg` depends on `[propext, Classical.choice, Quot.sound]` only,
and `SemialgebraicCheck/A2.lean` inhabits the verbatim copy of `HasFinitenessTheorem` with no glue.

## 7. Risk assessment

| risk | likelihood | impact | mitigation |
|---|---|---|---|
| mathematical error in the chosen route | very low | high | two independent derivations (R1, auditor), a compiling prototype; the Lean kernel is the final check |
| the interface theorem drifts from the class field | low | high | `SemialgebraicCheck/A2.lean` inhabits a verbatim copy of the class with no glue; the auditor compares symbol by symbol |
| set-builder / `simp` friction at this Mathlib pin (`Set.mem_setOf_eq` deprecated, `IsClosed.inter` not unifying with `{x | _ ∧ _}`) | medium | low | patterns recorded in R1 §4.4 and in the Phase 2 reports |
| growth of `J ^ I` in the closed form | certain | none | the statement only asks for existence |
| TauCeti changes upstream | medium | low | TauCeti is pinned; the route uses five stable TauCeti lemmas |
| the constants are not effective | certain | none | not required by HardnessBilevel |

## 8. Not verified

* Bochnak–Coste–Roy, Basu–Pollack–Roy and Coste's notes could not be fetched; statements attributed to them are from
  memory and no proof depends on them. Schweighofer's notes (arXiv 2205.04211) were read by R1 and by the auditor.
* The textbook form of route 1 and the repaired route 2 were derived on paper only; their Lean sizes are estimates.
* "Cheapest" is a judgement, not a theorem.
