# Lean Formalization: Carbery Concentration Inequalities (Version A)

This directory contains a Lean 4 formalization that verifies key mathematical claims from the paper:

**"Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality"**
by Eduardo Zambrano (Version A - continuous distributions)

## Approach

While Version A of the paper works with continuous distributions and Lebesgue measure, this formalization uses **finite state spaces** to provide rigorous verification. The fundamental algebraic structure of Carbery's inequality and the concentration bounds are identical in both settings.

This follows Terry Tao's pedagogical approach: prove results in finite settings first, where measure-theoretic technicalities disappear.

## Correspondence with Paper

| Paper Result | Lean Theorem | Status |
|--------------|--------------|--------|
| Theorem 2.1 (Carbery's Inequality) | `carberyInequality` | Axiomatized |
| Definition 2.2 (Q_n functional) | `carberyFunctional` | Defined |
| Lemma 2.5 (Independence structure) | `carberyFunctional_of_independent` | Proved |
| Theorem 3.1 (Markov) | `multivariate_markov` | Proved |
| Theorem 3.2 (Chebyshev) | `multivariate_chebyshev` | Proved |
| Theorem 3.4 (General moment) | `general_moment_bound` | Proved |
| Theorem 3.5 (MGF) | `mgf_inequality` | Proved |
| Theorem 4.1 (Permutation bound) | `permutation_bound_uniform` | Proved |

### Results NOT formalized (continuous-only):

- Section 5 (Gaussian distributions): The closed-form expressions for Gaussian Q_n involving determinants of tridiagonal matrices are specific to the continuous setting with Lebesgue measure.

## Building

```bash
# Install dependencies
lake update

# Build the project
lake build
```

Requires Lean 4 and Mathlib v4.24.0 or compatible.

## File Structure

```
CarberyVersionA/
├── CarberyVersionA.lean      # Main import file with documentation
├── CarberyVersionA/
│   ├── Basic.lean            # Core definitions, Carbery axiom
│   ├── ConcentrationInequalities.lean  # Markov, Chebyshev bounds
│   ├── MGF.lean              # MGF inequality
│   └── Permutation.lean      # Variable reordering optimization
├── lakefile.toml             # Lean Lake build configuration
└── lean-toolchain            # Lean version specification
```

## Key Mathematical Insight

The formalization verifies that under **independence**, the Carbery functional simplifies to:

$$Q_n^{n+1}(p) = \prod_{i=1}^{n} \|p_i\|_{L^2}^2$$

where **all marginals appear with power 2** (not power 3 for interior marginals as incorrectly stated in some earlier drafts). This is formalized in `carberyFunctional_of_independent`.

## References

- Carbery, A. (2004). *A multilinear generalisation of the Cauchy-Schwarz inequality.* Proceedings of the AMS, 132(11), 3141-3152.
- Zambrano, E. (2025). *Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality.* Working paper.
