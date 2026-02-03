/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Numerical Illustration (Section 6.1)

This file formalizes the numerical example from Section 6.1 of the paper,
demonstrating the Carbery bound for n = 3 binary random variables under
three dependence structures: independence, Markov chain, and perfect dependence.

## Setup

- n = 3 binary random variables X₁, X₂, X₃ ∈ {0, 1}
- Common marginal P(Xᵢ = 1) = 4/5 = 0.8
- Threshold aᵢ = 1

For binary variables with threshold 1:
- ‖xᵢ‖_{ℓ⁴} = (0⁴ + 1⁴)^{1/4} = 1
- So the bound simplifies to: P(X₁ = 1, X₂ = 1, X₃ = 1) ≤ Q₃(p)

## Results

| Dependence | True Prob | Q₃⁴(p) | Q₃(p) | Ratio |
|------------|-----------|--------|-------|-------|
| Independence | 64/125 = 0.512 | 4913/15625 | ≈0.749 | 1.46 |
| Markov (ρ=0.5) | 81/125 = 0.648 | 5597/15625 | ≈0.774 | 1.19 |
| Perfect | 4/5 = 0.800 | 257/625 | ≈0.801 | 1.001 |

## References

* [Zambrano, E., Dependence-Aware Concentration Inequalities, 2026]
-/

import CarberyVersionA.Basic

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

/-!
## Binary State Space

We use Bool as the binary state space {0, 1}.
-/

/-- The trivariate binary state space. -/
abbrev BinaryTrivariate := Fin 3 → Bool

/-!
## Rational Number Verification

We verify the key calculations using rationals, which have decidable equality.
-/

/-- True probability under independence: (4/5)³ = 64/125 -/
theorem true_prob_independent_rat : (4 / 5 : ℚ) ^ 3 = 64 / 125 := by norm_num

/-- True probability under Markov: (4/5)(9/10)(9/10) = 81/125 -/
theorem true_prob_markov_rat : (4 / 5 : ℚ) * (9 / 10) * (9 / 10) = 81 / 125 := by norm_num

/-- True probability under perfect dependence: 4/5 -/
theorem true_prob_perfect_rat : (4 / 5 : ℚ) = 4 / 5 := rfl

/-- Q₃⁴(p) under independence: ((4/5)² + (1/5)²)³ = (17/25)³ = 4913/15625 -/
theorem carbery_pow4_independent_rat :
    (((4 / 5 : ℚ) ^ 2 + (1 / 5) ^ 2)) ^ 3 = 4913 / 15625 := by norm_num

/-- Intermediate: (4/5)² + (1/5)² = 17/25 -/
theorem sum_sq_marginals : (4 / 5 : ℚ) ^ 2 + (1 / 5) ^ 2 = 17 / 25 := by norm_num

/-- Q₃⁴(p) under Markov: computed term by term = 5597/15625

Term-by-term calculation:
- (0,0,0): (1/5)(3/25)(3/25)(1/5) = 9/15625
- (0,0,1): (1/5)(3/25)(2/25)(4/5) = 24/15625
- (0,1,0): (1/5)(2/25)(2/25)(1/5) = 4/15625
- (0,1,1): (1/5)(2/25)(18/25)(4/5) = 144/15625
- (1,0,0): (4/5)(2/25)(3/25)(1/5) = 24/15625
- (1,0,1): (4/5)(2/25)(2/25)(4/5) = 64/15625
- (1,1,0): (4/5)(18/25)(2/25)(1/5) = 144/15625
- (1,1,1): (4/5)(18/25)(18/25)(4/5) = 5184/15625
Sum = 5597/15625
-/
theorem carbery_pow4_markov_rat :
    (9 + 24 + 4 + 144 + 24 + 64 + 144 + 5184 : ℚ) / 15625 = 5597 / 15625 := by norm_num

/-- Verify individual Markov terms -/
theorem markov_term_000 : (1/5 : ℚ) * (3/25) * (3/25) * (1/5) = 9/15625 := by norm_num
theorem markov_term_001 : (1/5 : ℚ) * (3/25) * (2/25) * (4/5) = 24/15625 := by norm_num
theorem markov_term_010 : (1/5 : ℚ) * (2/25) * (2/25) * (1/5) = 4/15625 := by norm_num
theorem markov_term_011 : (1/5 : ℚ) * (2/25) * (18/25) * (4/5) = 144/15625 := by norm_num
theorem markov_term_100 : (4/5 : ℚ) * (2/25) * (3/25) * (1/5) = 24/15625 := by norm_num
theorem markov_term_101 : (4/5 : ℚ) * (2/25) * (2/25) * (4/5) = 64/15625 := by norm_num
theorem markov_term_110 : (4/5 : ℚ) * (18/25) * (2/25) * (1/5) = 144/15625 := by norm_num
theorem markov_term_111 : (4/5 : ℚ) * (18/25) * (18/25) * (4/5) = 5184/15625 := by norm_num

/-- Verify bivariate marginals for Markov chain -/
theorem markov_bivariate_11 : (4/5 : ℚ) * (9/10) = 18/25 := by norm_num
theorem markov_bivariate_10 : (4/5 : ℚ) * (1/10) = 2/25 := by norm_num
theorem markov_bivariate_01 : (1/5 : ℚ) * (2/5) = 2/25 := by norm_num
theorem markov_bivariate_00 : (1/5 : ℚ) * (3/5) = 3/25 := by norm_num

/-- Q₃⁴(p) under perfect dependence: (1/5)⁴ + (4/5)⁴ = 257/625 -/
theorem carbery_pow4_perfect_rat :
    (1 / 5 : ℚ) ^ 4 + (4 / 5) ^ 4 = 257 / 625 := by norm_num

/-!
## Bound Validity

The bound is valid if (True Prob)⁴ ≤ Q₃⁴(p).
-/

/-- Independence: (64/125)⁴ ≤ 4913/15625 -/
theorem bound_valid_independent_rat :
    (64 / 125 : ℚ) ^ 4 ≤ 4913 / 15625 := by
  -- (64/125)⁴ = 16777216/244140625
  -- 4913/15625 = 76765625/244140625
  -- 16777216 < 76765625 ✓
  norm_num

/-- Markov: (81/125)⁴ ≤ 5597/15625 -/
theorem bound_valid_markov_rat :
    (81 / 125 : ℚ) ^ 4 ≤ 5597 / 15625 := by
  -- (81/125)⁴ = 43046721/244140625
  -- 5597/15625 = 87453125/244140625
  -- 43046721 < 87453125 ✓
  norm_num

/-- Perfect: (4/5)⁴ ≤ 257/625 -/
theorem bound_valid_perfect_rat :
    (4 / 5 : ℚ) ^ 4 ≤ 257 / 625 := by
  -- (4/5)⁴ = 256/625 ≤ 257/625 ✓
  norm_num

/-!
## Ordering Properties

Key qualitative result: Q₃⁴ increases with positive dependence.
-/

/-- Q₃⁴ increases: independence < Markov < perfect -/
theorem carbery_pow4_ordering_rat :
    (4913 : ℚ) / 15625 < 5597 / 15625 ∧
    (5597 : ℚ) / 15625 < 257 / 625 := by
  constructor
  · norm_num
  · -- 5597/15625 < 257/625 = 6425/15625
    norm_num

/-- True probabilities increase: independence < Markov < perfect -/
theorem true_prob_ordering_rat :
    (64 : ℚ) / 125 < 81 / 125 ∧
    (81 : ℚ) / 125 < 4 / 5 := by
  constructor <;> norm_num

/-!
## Ratio Computations

The ratio Bound/TrueProb decreases as dependence increases.
-/

-- Q₃(p) = Q₃⁴(p)^{1/4}, so Ratio⁴ = Q₃⁴(p) / TrueProb⁴

/-- Independence ratio⁴ = (4913/15625) / (64/125)⁴ -/
theorem ratio_pow4_independent :
    (4913 / 15625 : ℚ) / ((64 / 125) ^ 4) = 4913 * 244140625 / (15625 * 16777216) := by
  norm_num

/-- Markov ratio⁴ -/
theorem ratio_pow4_markov :
    (5597 / 15625 : ℚ) / ((81 / 125) ^ 4) = 5597 * 244140625 / (15625 * 43046721) := by
  norm_num

/-- Perfect ratio⁴ = (257/625) / (256/625) = 257/256 ≈ 1.004 -/
theorem ratio_pow4_perfect :
    (257 / 625 : ℚ) / ((4 / 5) ^ 4) = 257 / 256 := by norm_num

/-- The perfect dependence ratio is very close to 1 -/
theorem ratio_perfect_close_to_one :
    (257 : ℚ) / 256 - 1 = 1 / 256 := by norm_num

/-!
## Decimal Approximations

For reference, here are the decimal values from the paper.
-/

/-- 64/125 = 0.512 exactly -/
theorem decimal_true_independent : (64 : ℚ) / 125 = 512 / 1000 := by norm_num

/-- 81/125 = 0.648 exactly -/
theorem decimal_true_markov : (81 : ℚ) / 125 = 648 / 1000 := by norm_num

/-- 4/5 = 0.8 exactly -/
theorem decimal_true_perfect : (4 : ℚ) / 5 = 8 / 10 := by norm_num

/-- 4913/15625 = 0.314432 exactly -/
theorem decimal_Q4_independent : (4913 : ℚ) / 15625 = 314432 / 1000000 := by norm_num

/-- 5597/15625 = 0.358208 exactly -/
theorem decimal_Q4_markov : (5597 : ℚ) / 15625 = 358208 / 1000000 := by norm_num

/-- 257/625 = 0.4112 exactly -/
theorem decimal_Q4_perfect : (257 : ℚ) / 625 = 4112 / 10000 := by norm_num

end
