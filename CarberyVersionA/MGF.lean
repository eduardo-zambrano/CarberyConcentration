/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# MGF-Type Inequality (Finite State Spaces)

This file contains the moment generating function (MGF) type inequality
derived from Carbery's inequality, specialized to finite state spaces.

## Main results (Paper Contribution - Zambrano 2026)

* `mgf_inequality_counting`: MGF-type bound (Theorem 3.5)

## Important Note on Measure Choice

**Carbery's inequality uses COUNTING MEASURE norms, not marginal-weighted norms.**

This means:
- The MGF bounds use "counting measure MGF": `∑_s exp(t·g(s))` (unweighted)
- This is DIFFERENT from the standard probabilistic MGF: `E[exp(tX)] = ∑_s μ(s)·exp(t·g(s))`

## References

* [Zambrano, E., Dependence-Aware Concentration Inequalities, 2026]
* [Carbery, A., A multilinear generalisation of the Cauchy-Schwarz inequality, 2004]
-/

import CarberyVersionA.ConcentrationInequalities

open scoped ENNReal NNReal BigOperators
open Finset Real

noncomputable section

variable {n : ℕ} {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-!
## Moment Generating Functions

For finite state spaces, MGFs are always well-defined finite sums.
-/

/-- The COUNTING MEASURE MGF: sum over all states without marginal weights.
    This is what Carbery's inequality provides bounds for.

    mgfCounting(t) = ∑_s exp(t · g(s))

    **Important**: This is NOT the same as the probabilistic MGF E[exp(tX)]. -/
def mgfCounting (g : α → ℝ) (t : ℝ) [Fintype α] : ℝ≥0∞ :=
  ∑ s : α, ENNReal.ofReal (Real.exp (t * g s))

/-- The joint MGF: E[exp(∑ᵢ tᵢ · gᵢ(Xᵢ))]. -/
def JointPMF.jointMgf (p : JointPMF Ω) (g : ∀ i, Ω i → ℝ) (t : Fin n → ℝ) : ℝ≥0∞ :=
  ∑ x : ∀ i, Ω i, p.prob x * ENNReal.ofReal (Real.exp (∑ i, t i * g i (x i)))

/-!
## MGF-Type Inequality

**Theorem 3.5** (Zambrano 2026): Carbery's inequality provides bounds using COUNTING MEASURE norms.

For t₁,...,tₙ ≥ 0:
  E[exp(∑ᵢ tᵢ gᵢ(Xᵢ))] ≤ Qₙ(p) · ∏ᵢ (∑_s exp((n+1)tᵢ gᵢ(s)))^{1/(n+1)}

Note: The RHS uses COUNTING MEASURE sums, not marginal-weighted MGFs.
-/

/-- **MGF-Type Inequality** (Theorem 3.5) for finite spaces.

    For t₁,...,tₙ ≥ 0 and real-valued functions gᵢ:
    E[exp(∑ᵢ tᵢ gᵢ(Xᵢ))] ≤ Qₙ(p) · ∏ᵢ (mgfCounting(gᵢ, (n+1)tᵢ))^{1/(n+1)}

    where mgfCounting(g,t) = ∑_s exp(t·g(s)) is the COUNTING MEASURE MGF.

    **Important**: This is NOT a bound using the probabilistic MGF E[exp(tX)].

    **Paper contribution**: Theorem 3.5. -/
theorem mgf_inequality_counting (hn : n ≥ 1) (p : JointPMF Ω)
    (g : ∀ i, Ω i → ℝ) (t : Fin n → ℝ) (ht : ∀ i, t i ≥ 0) :
    p.jointMgf g t ≤
    carberyFunctional hn p *
    ∏ i : Fin n, (mgfCounting (g i) ((n + 1 : ℕ) * t i)) ^ (1 / (n + 1 : ℝ)) := by
  -- Step 1: Rewrite jointMgf in the form needed for Carbery's inequality
  simp only [JointPMF.jointMgf, mgfCounting]
  -- exp(∑ᵢ tᵢ gᵢ(xᵢ)) = ∏ᵢ exp(tᵢ gᵢ(xᵢ))
  have exp_sum : ∀ x : ∀ i, Ω i,
      Real.exp (∑ i, t i * g i (x i)) = ∏ i, Real.exp (t i * g i (x i)) := by
    intro x
    rw [Real.exp_sum]
  simp_rw [exp_sum]
  -- Convert ofReal of product to product of ofReal
  have ofReal_prod : ∀ x : ∀ i, Ω i,
      ENNReal.ofReal (∏ i, Real.exp (t i * g i (x i))) =
      ∏ i, ENNReal.ofReal (Real.exp (t i * g i (x i))) := by
    intro x
    rw [ENNReal.ofReal_prod_of_nonneg]
    intro i _
    exact le_of_lt (Real.exp_pos _)
  simp_rw [ofReal_prod]
  -- Step 2: Apply Carbery's inequality with f_i(s) = ofReal(exp(t_i g_i(s)))
  have carb := carberyInequality hn p (fun i s => ENNReal.ofReal (Real.exp (t i * g i s)))
  -- Step 3: Show the L^{n+1} counting measure norms equal mgfCounting
  have norm_eq : ∀ i : Fin n,
      lpNormFinite (n + 1 : ℝ) (fun s => ENNReal.ofReal (Real.exp (t i * g i s))) =
      (∑ s : Ω i, ENNReal.ofReal (Real.exp (↑(n + 1) * t i * g i s))) ^
      (1 / (n + 1 : ℝ)) := by
    intro i
    simp only [lpNormFinite]
    congr 1
    apply Finset.sum_congr rfl
    intro s _
    -- Need: ofReal(exp(t_i g_i s))^(n+1) = ofReal(exp((n+1) t_i g_i s))
    rw [ENNReal.ofReal_rpow_of_nonneg (le_of_lt (Real.exp_pos _)) (by linarith : (0 : ℝ) ≤ ↑n + 1)]
    congr 1
    rw [← Real.exp_mul]
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  -- Step 4: Combine using Carbery's inequality
  calc ∑ x, p.prob x * ∏ i, ENNReal.ofReal (Real.exp (t i * g i (x i)))
      ≤ carberyFunctional hn p * ∏ i, lpNormFinite (n + 1 : ℝ)
          (fun s => ENNReal.ofReal (Real.exp (t i * g i s))) := carb
    _ = carberyFunctional hn p * ∏ i,
          (∑ s : Ω i, ENNReal.ofReal (Real.exp (↑(n + 1) * t i * g i s))) ^
          (1 / (n + 1 : ℝ)) := by
        congr 1
        apply Finset.prod_congr rfl
        intro i _
        exact norm_eq i

end
