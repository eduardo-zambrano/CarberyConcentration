/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Carbery Concentration Inequalities - Version A Formalization

This library provides a Lean 4 formalization of key results from:
"Dependence-Aware Concentration Inequalities: A Multivariate Extension via
Carbery's Inequality" (Version A - continuous distributions)

## Approach

This formalization works with **finite state spaces** to provide rigorous
verification of the paper's core mathematical claims. While the paper treats
continuous distributions with Lebesgue measure, the fundamental algebraic
structure of Carbery's inequality and the concentration bounds are the same
in the finite setting. This follows Terry Tao's pedagogical approach.

## Correspondence with Version A Paper

The finite formalization verifies the following results from the paper:

| Paper Result | Lean Theorem | Notes |
|--------------|--------------|-------|
| Theorem 2.1 (Carbery) | `carberyInequality` | Axiomatized |
| Definition 2.2 (Q_n) | `carberyFunctional` | Adapted to finite sums |
| Lemma 2.5 (Independence) | `carberyFunctional_of_independent` | All marginals power 2 |
| Theorem 3.1 (Markov) | `multivariate_markov` | Proved |
| Theorem 3.2 (Chebyshev) | `multivariate_chebyshev` | Proved |
| Theorem 3.4 (General moment) | `general_moment_bound` | Proved |
| Theorem 3.5 (MGF) | `mgf_inequality` | Proved |
| Theorem 4.1 (Permutation) | `permutation_bound_uniform` | Proved |

## Key Mathematical Insight

Under **independence**, the Carbery functional simplifies to:
  Q_n^{n+1}(p) = ∏_{i=1}^n ‖p_i‖_{L^2}^2

where all marginals appear with power 2 (not 3 for interior marginals as
incorrectly claimed in some earlier versions). This is verified in
`carberyFunctional_of_independent`.

## Files

- `Basic.lean`: Core definitions, Carbery inequality (axiom), independence structure
- `ConcentrationInequalities.lean`: Markov, Chebyshev, general moment bounds
- `MGF.lean`: MGF inequality and Chernoff-type bounds
- `Permutation.lean`: Variable reordering and optimization

## Note on Continuous Results

The Gaussian closed-form expressions (Section 5 of the paper) involving
determinants of tridiagonal matrices do not have direct finite analogs.
These results apply specifically to the continuous Gaussian case with
Lebesgue measure.

## References

* Carbery, A. (2004). A multilinear generalisation of the Cauchy-Schwarz inequality.
  Proceedings of the AMS, 132(11), 3141-3152.

* Zambrano, E. (2025). Dependence-Aware Concentration Inequalities:
  A Multivariate Extension via Carbery's Inequality. (Working paper)
-/

import CarberyVersionA.Basic
import CarberyVersionA.ConcentrationInequalities
import CarberyVersionA.MGF
import CarberyVersionA.Permutation
