# Lean Formalization: Carbery Concentration Inequalities

This repository contains a Lean 4 formalization that verifies key mathematical claims from the paper:

**"Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality"**
by Eduardo Zambrano

All proofs compile with **zero `sorry`** (unverified steps), except for Carbery's inequality itself, which is axiomatized as an established result.

## Point of Departure: Carbery's Inequality (Expectation Form)

All the results of the paper stem from an adaptation of Carbery's multilinear generalization of the Cauchy-Schwarz inequality:

**Theorem (Carbery's Inequality, Expectation Form).** Let $\mathbf{X} = (X_1, \ldots, X_n)$ have joint density $p$ with marginal densities $p_1, \ldots, p_n$. For nonnegative measurable functions $g_i: \mathbb{R} \to \mathbb{R}_+$,

$$\mathbb{E}\left[\prod_{i=1}^n g_i(X_i) \cdot p_i(X_i)^{1/(n+1)}\right] \leq Q_n(p) \prod_{i=1}^n \left(\mathbb{E}\left[g_i(X_i)^{n+1}\right]\right)^{1/(n+1)}$$

where $Q_n(p)$ is the **dependence functional** encoding the joint distribution through consecutive bivariate marginals:

$$Q_n^{n+1}(p) = \int p_1(s_1) \prod_{j=1}^{n-1} p_{j,j+1}(s_j, s_{j+1}) \, p_n(s_n) \, ds_1 \cdots ds_n$$

**Intuition.** The inequality relates expected products of functions to products of individual expectations, with the dependence functional $Q_n(p)$ capturing the "cost" of dependence. The density factors $p_i(X_i)^{1/(n+1)}$ arise from a measure-change transformation that converts Lebesgue-measure norms (in the original Carbery inequality) to probability-measure expectations. When $n=1$, this reduces to the classical Cauchy-Schwarz inequality. For independent variables, $Q_n$ factors into a product of $L^2$ norms of the marginals, each appearing with power 2. For dependent variables, the consecutive bivariate marginals $p_{j,j+1}$ encode the pairwise dependence structure, making the bound naturally suited for Markov chains and sequences with local dependence.

## Formalization Approach

While the paper treats continuous distributions with Lebesgue measure, this formalization uses **finite state spaces** to provide rigorous verification. The fundamental algebraic structure of Carbery's inequality and the derived concentration bounds are identical in both settings, with integrals replaced by finite sums.

The tensorization theorem (Proposition 4.1(ii)) is proved for **homogeneous state spaces** where all coordinates share the same finite type. This avoids dependent-type complications while capturing the full algebraic content of the result. The heterogeneous generalization (different state spaces at each coordinate) is left as future work.

## Correspondence with Paper

| Paper Result | Lean Theorem | Status |
|--------------|--------------|--------|
| Carbery's Inequality (Lebesgue form) | `carberyInequality` | Axiomatized |
| $Q_n$ functional definition | `carberyFunctional`, `carberyFunctionalPow` | Defined |
| Independence structure lemma | `carberyFunctional_of_independent` | Proved |
| Marginal sufficiency | `carberyFunctionalPow_marginal_sufficiency` | Proved |
| Tensorization (general) | `carberyFunctionalPow_tensorization` | Proved |
| Tensorization (univariate case) | `tensorization_univariate` | Proved |
| Markov chain structure | `carberyFunctionalPow_markov_chain_structure` | Proved |
| Multivariate Markov inequality | `multivariate_markov` | Proved |
| Multivariate Chebyshev inequality | `multivariate_chebyshev` | Proved |
| General concentration inequality | `general_moment_bound` | Proved |
| MGF inequality | `mgf_inequality` | Proved |
| Permutation bound | `permutation_bound_uniform` | Proved |

### Key auxiliary lemmas for tensorization:

| Lemma | Lean Name | Purpose |
|-------|-----------|---------|
| Product PMF construction | `JointPMF.independentProduct` | Independent product of joint PMFs |
| Sum splitting | `sum_fin_add_equiv` | $\sum_{z \in \text{Fin}(m+k)} = \sum_x \sum_y$ |
| Product splitting | `Fin.prod_split_three` | Split $\prod_{j=0}^{m+k-2}$ at boundary $j = m-1$ |
| Left boundary marginal | `independentProduct_marginal_left` | $p_Z$ marginal at $0$ equals $p_X$ marginal |
| Right boundary marginal | `independentProduct_marginal_right` | $p_Z$ marginal at $m+k-1$ equals $p_Y$ marginal |
| Boundary factorization | `independentProduct_bivariate_boundary` | $p_{Z_m, Z_{m+1}} = p_{X_m} \cdot p_{Y_1}$ |
| X-block bivariates | `independentProduct_bivariate_left` | Internal X-block bivariates match $p_X$ |
| Y-block bivariates | `independentProduct_bivariate_right` | Internal Y-block bivariates match $p_Y$ |

### Results NOT formalized (continuous-only):

- Section 5 (Gaussian distributions): The closed-form expressions for Gaussian $Q_n$ involving determinants of tridiagonal matrices are specific to the continuous setting with Lebesgue measure.
- The density correction mechanism (Definition 2.6, Lemma 2.7) that bridges Lebesgue norms to probabilistic expectations.

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
│   ├── Basic.lean            # Core definitions, Carbery axiom, independence,
│   │                         #   tensorization, structural properties
│   ├── ConcentrationInequalities.lean  # Markov, Chebyshev bounds
│   ├── MGF.lean              # MGF inequality
│   ├── NumericalExample.lean # Numerical verification examples
│   └── Permutation.lean      # Variable reordering optimization
├── lakefile.toml             # Lean Lake build configuration
└── lean-toolchain            # Lean version specification
```

## References

- Carbery, A. (2004). *A multilinear generalisation of the Cauchy-Schwarz inequality.* Proceedings of the AMS, 132(11), 3141-3152.
- Tao, T. (2023). *A generalized Cauchy-Schwarz inequality via the Gibbs variational formula.* [Blog post](https://terrytao.wordpress.com/2023/12/10/a-generalized-cauchy-schwarz-inequality-via-the-gibbs-variational-formula/).
- Zambrano, E. (2026). *Dependence-Aware Concentration Inequalities: A Multivariate Extension via Carbery's Inequality.* Working paper.
