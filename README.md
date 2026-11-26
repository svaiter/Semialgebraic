# Semialgebraic

Semialgebraic is a Lean 4 library for real semialgebraic geometry. It formalizes the
finiteness theorem for open and closed semialgebraic sets, a weighted Łojasiewicz
inequality, and polynomial growth bounds. The statements use
`TauCeti.IsSemialgebraic` from [TauCeti](https://github.com/TauCetiProject/TauCeti).

## Main results

| Result | Statement | Lean theorem |
| --- | --- | --- |
| Finiteness theorem | Every open semialgebraic subset of a finite-dimensional real coordinate space is a finite union of sets defined by finitely many strict polynomial inequalities. For closed semialgebraic sets, the inequalities are weak. | [`Semialgebraic.exists_eq_iUnion_iInter_pos` and `Semialgebraic.exists_eq_iUnion_iInter_nonneg`](Semialgebraic/Finiteness/Main.lean) |
| Weighted Łojasiewicz inequality | On a closed semialgebraic set, if the zero set of a polynomial `f` is contained in that of `g`, an even power of `g` is bounded by `f²` times a polynomial weight. | [`Semialgebraic.exists_lojasiewicz`](Semialgebraic/Finiteness/Lojasiewicz.lean) |
| Polynomial growth | A real-valued function with a semialgebraic graph that is bounded on bounded sets admits a global bound of the form `abs (f x) ≤ B + (1 + ∑ i, x i ^ 2) ^ M` for some real `B` and natural `M`. | [`Semialgebraic.exists_polynomial_growth`](Semialgebraic/Growth/Main.lean) |
| Fibrewise least upper bounds | The graph of the least upper bound of a semialgebraic family of real sets is semialgebraic where the least upper bound exists. For a single real parameter, its magnitude grows at most polynomially as the parameter tends to positive infinity. | [`Semialgebraic.isSemialgebraic_setOf_isLUB`](Semialgebraic/Growth/IsLUB.lean) and [`Semialgebraic.exists_growth_isLUB`](Semialgebraic/Growth/Main.lean) |

The finiteness proof first derives the weighted Łojasiewicz inequality using
polynomial growth of fibrewise least upper bounds. It then uses that inequality
to enlarge each sign cell inside an open semialgebraic set to a set defined by
strict polynomial inequalities. The closed case follows by taking complements.

## Using the library

Import the main module to access the results.

```lean
import Semialgebraic

#check Semialgebraic.exists_eq_iUnion_iInter_nonneg
#check Semialgebraic.exists_lojasiewicz
#check Semialgebraic.exists_polynomial_growth
```

- [`Semialgebraic/Finiteness/`](Semialgebraic/Finiteness) contains the open and closed finiteness theorems, the Łojasiewicz inequality, and the sign-cell lemmas.
- [`Semialgebraic/Growth/`](Semialgebraic/Growth) contains the growth bounds and the semialgebraicity of fibrewise least upper bounds.
- [`Semialgebraic/Interface/`](Semialgebraic/Interface) provides the projection, closed finiteness, and growth theorems in the form used by [HardnessBilevelProgramming](https://github.com/svaiter/HardnessBilevelProgramming). The projection theorem comes from TauCeti’s cylindrical algebraic decomposition. [`SemialgebraicCheck/`](SemialgebraicCheck) checks these interfaces against copies of the downstream assumption classes.

## Building and checking

From the repository root, with Bash, Git, and Lean’s toolchain manager
[Elan](https://github.com/leanprover/elan) installed, run:

```bash
bash scripts/setup.sh
bash scripts/check.sh
```

Setup fetches the Mathlib cache and the mappings for TauCeti’s build cache.
The check script builds the library and the interface checks, scans for proof
placeholders and other forbidden declarations, and verifies that the three
interface theorems depend only on `propext`, `Classical.choice`, and `Quot.sound`.

For a library-only build, run `bash -c 'source scripts/env.sh && lake build'`
from the repository root after setup.

The checked-in toolchain and dependency files pin Lean to `v4.36.0-rc2`,
TauCeti to `2c9b12be`, and Mathlib to `1b1ccf4b`.

## Proof notes

The [finiteness report](notes/finiteness-report.md) explains the choice of proof
and compares the approaches considered. The [project plan](PLAN.md) records the
development history.
