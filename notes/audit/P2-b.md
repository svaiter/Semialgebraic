# Audit of unit P2-b (`Semialgebraic.Growth.IsLUB`, plan id G3)

**Verdict: ACCEPT**

## 1. Build
`lake build Semialgebraic.Growth.IsLUB` succeeds (7696 jobs). Re-elaborating the file with `lake env lean` gives no
errors and no warnings (no deprecations).

## 2. Forbidden tokens
grep for `sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|opaque|set_option|instance`: no hits.
No `set_option`. No new `def`/`class`/`structure`/notation. Imports: the two TauCeti modules only.

## 3. Axioms (scratch `/tmp/audit-p2b/A.lean`)
All seven public declarations depend on exactly `[propext, Classical.choice, Quot.sound]`:
isSemialgebraic_setOf_isLUB, isSemialgebraic_setOf_isLUB_fin_two, isSemialgebraic_setOf_exists_real,
isSemialgebraic_setOf_forall_real, isSemialgebraic_setOf_le_coord, isSemialgebraic_setOf_lt_coord,
isLUB_iff_forall_lt_exists.

## 4. Faithfulness
Both required statements in the file are textually identical to the brief (and to PLAN G3: `E`, `σ` arbitrary
`Type*`, `Sum.elim (z ∘ Sum.inl) (fun _ => u) ∈ E`, value at `z (Sum.inr ())`; plane form with `![u, z 1] ∈ E`,
value `z 0`). Decisive test: `example : <statement verbatim> := fun hE => <theorem> hE` elaborates for both
G3 statements, and for the two optional quantifier helpers. No hypotheses added, no strengthening, no deviation.
Universe: `σ : Type u_1` (as `Type*`).

## 5. No definitional cheating / non-vacuity
No new definitions. Hypotheses are just `IsSemialgebraic E`, satisfiable. Sanity instance: `σ = Unit`,
`E = {(p, u) | 0 ≤ u ∧ u ≤ p²}` (sa); the fibre over `p` is `[0, p²]`, the set is `{(p, s) | s = p²}`, nonempty and sa.
Plane form: `E = {(u, t) | u ≤ t}`, set `{z | z 0 = z 1}`.

## 6. Interface theorem
Not applicable.

## 7. Proof hygiene (non-blocking)
Proofs are short, commented, use `simp only`. Fibre-coordinate pullbacks are repeated twice (hE₁/hE₂) but fine.
Elaboration time ~3 s. No `Classical` opened. No issues.

## Required fixes
none
