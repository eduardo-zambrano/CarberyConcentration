# Lean Formalization: Carbery Concentration Inequalities

This repository contains a Lean 4 formalization that verifies key mathematical claims from the paper:

**"Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality"**
by Eduardo Zambrano

## Key Mathematical Insight: Carbery's Inequality (Expectation Form)

The central result adapted from Carbery's multilinear generalization of the Cauchy-Schwarz inequality is:

**Theorem (Carbery's Inequality, Expectation Form).** Let $\mathbf{X} = (X_1, \ldots, X_n)$ have joint density $p$ with marginal densities $p_1, \ldots, p_n$. For nonnegative measurable functions $g_i: \mathbb{R} \to \mathbb{R}_+$,

$$\mathbb{E}\left[\prod_{i=1}^n g_i(X_i) \cdot p_i(X_i)^{1/(n+1)}\right] \leq Q_n(p) \prod_{i=1}^n \left(\mathbb{E}\left[g_i(X_i)^{n+1}\right]\right)^{1/(n+1)}$$

where $Q_n(p)$ is the **dependence functional** encoding the joint distribution through consecutive bivariate marginals:

$$Q_n^{n+1}(p) = \int p_1(s_1) \prod_{j=1}^{n-1} p_{j,j+1}(s_j, s_{j+1}) \, p_n(s_n) \, ds_1 \cdots ds_n$$

**Intuition.** The inequality relates expected products of functions to products of individual expectations, with the dependence functional $Q_n(p)$ capturing the "cost" of dependence. The density factors $p_i(X_i)^{1/(n+1)}$ arise from a measure-change transformation that converts Lebesgue-measure norms (in the original Carbery inequality) to probability-measure expectations. When $n=1$, this reduces to the classical Cauchy-Schwarz inequality. For independent variables, $Q_n$ factors into a product of $L^2$ norms of the marginals, each appearing with power 2. For dependent variables, the consecutive bivariate marginals $p_{j,j+1}$ encode the pairwise dependence structure, making the bound naturally suited for Markov chains and sequences with local dependence.

## Formalization Approach

While the paper treats continuous distributions with Lebesgue measure, this formalization uses **finite state spaces** to provide rigorous verification. The fundamental algebraic structure of Carbery's inequality and the derived concentration bounds are identical in both settings, with integrals replaced by finite sums.

## Correspondence with Paper

| Paper Result | Lean Theorem | Status |
|--------------|--------------|--------|
| Theorem 2.1 (Carbery's Inequality) | `carberyInequality` | Axiomatized |
| Definition 2.2 ($Q_n$ functional) | `carberyFunctional` | Defined |
| Lemma 2.5 (Independence structure) | `carberyFunctional_of_independent` | Proved |
| Theorem 3.1 (Markov) | `multivariate_markov` | Proved |
| Theorem 3.2 (Chebyshev) | `multivariate_chebyshev` | Proved |
| Theorem 3.4 (General moment) | `general_moment_bound` | Proved |
| Theorem 3.5 (MGF) | `mgf_inequality` | Proved |
| Proposition 4.1 (Structural properties) | `carberyFunctionalPow_marginal_sufficiency` | Proved |
| Proposition 4.2 (Markov chain) | `carberyFunctionalPow_markov_chain_structure` | Proved |
| Proposition 6.1 (Permutation bound) | `permutation_bound_uniform` | Proved |

### Results NOT formalized (continuous-only):

- Section 5 (Gaussian distributions): The closed-form expressions for Gaussian $Q_n$ involving determinants of tridiagonal matrices are specific to the continuous setting with Lebesgue measure.

## Independence Structure

The formalization verifies that under **independence**, the Carbery functional simplifies to:

$$Q_n^{n+1}(p) = \prod_{i=1}^{n} \|p_i\|_{L^2}^2$$

where **all marginals appear with power 2**. This is formalized in `carberyFunctional_of_independent`.

## Building

```bash
# Install dependencies
lake update

# Download Mathlib cache (faster than building from source)
lake exe cache get

# Build the project
lake build
```

Requires Lean 4 and Mathlib v4.24.0 or compatible.

## File Structure

```
CarberyConcentration/
├── CarberyVersionA.lean      # Main import file with documentation
├── CarberyVersionA/
│   ├── Basic.lean            # Core definitions, Carbery axiom, independence
│   ├── ConcentrationInequalities.lean  # Markov, Chebyshev bounds
│   ├── MGF.lean              # MGF inequality
│   └── Permutation.lean      # Variable reordering optimization
├── lakefile.toml             # Lean Lake build configuration
└── lean-toolchain            # Lean version specification
```

## References

- Carbery, A. (2004). *A multilinear generalisation of the Cauchy-Schwarz inequality.* Proceedings of the AMS, 132(11), 3141-3152.
- Tao, T. (2023). *A generalized Cauchy-Schwarz inequality via the Gibbs variational formula.* [Blog post](https://terrytao.wordpress.com/2023/12/10/a-generalized-cauchy-schwarz-inequality-via-the-gibbs-variational-formula/).
- Zambrano, E. (2026). *Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality.* Working paper.
