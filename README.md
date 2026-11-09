# Semialgebraic

A Lean 4 companion library to [TauCeti](https://github.com/TauCetiProject/TauCeti)'s real algebraic geometry.
Its purpose is to prove, over `ℝ` and in TauCeti's vocabulary (`TauCeti.IsSemialgebraic`), the three facts that
[`HardnessBilevelProgramming`](https://github.com/svaiter/HardnessBilevelProgramming) takes as hypotheses:

| id | fact | interface theorem (namespace `Semialgebraic.Interface`) | status |
|---|---|---|---|
| A1 | Tarski–Seidenberg, projection form | `image_comp_inl` (`Semialgebraic/Interface/Projection.lean`) | done (from TauCeti's CAD) |
| A2 | finiteness theorem for closed semialgebraic sets | `exists_eq_iUnion_iInter_nonneg` (`Semialgebraic/Interface/Finiteness.lean`) | done |
| A3 | polynomial growth of locally bounded semialgebraic functions | `growth` (`Semialgebraic/Interface/Growth.lean`) | done |

The plan and its status are in `PLAN.md`.

## Pins

Lean `leanprover/lean4:v4.36.0-rc2`, TauCeti `2c9b12be`, Mathlib `1b1ccf4b` (the commit of TauCeti's manifest).

## Building

```bash
scripts/setup.sh      # once: Mathlib oleans, and the mappings of TauCeti's olean cache
. scripts/env.sh      # in every shell: lets Lake fetch TauCeti modules instead of compiling them
lake build
scripts/check.sh      # build + forbidden-token scan + #print axioms of the interface theorems
```
