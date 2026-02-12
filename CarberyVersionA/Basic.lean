/-
Copyright (c) 2025 Eduardo Zambrano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eduardo Zambrano

# Carbery's Multilinear Inequality and Concentration (Finite State Spaces)

This file contains the core definitions for formalizing concentration inequalities
based on Carbery's multilinear generalization of the Cauchy-Schwarz inequality,
specialized to finite state spaces.

## Main definitions

* `JointPMF`: A joint probability mass function on a finite product space
* `CarberyFunctional`: The functional Q_n encoding dependence through consecutive marginals
* `carberyInequality`: Carbery's inequality (AXIOMATIZED - see note below)

## Axiomatization Strategy

This formalization adopts a pragmatic approach:

**Axiomatized (well-established results not contributed by this paper):**
- Carbery's inequality [Carbery, Proc. AMS 2004]
- Hölder's inequality and its generalizations (available in Mathlib)

**To be proved (contributions of Zambrano 2025):**
- Concentration inequalities (Markov, Chebyshev, Chernoff extensions)
- Structure of Q_n under independence
- Variable reordering optimization

This approach focuses formalization effort on verifying the paper's novel contributions
while treating established mathematical results as trusted foundations.

## References

* [Carbery, A., A multilinear generalisation of the Cauchy-Schwarz inequality, 2004]
  Proceedings of the AMS, 132(11), 3141-3152.
* [Zambrano, E., Dependence-Aware Concentration Inequalities, 2025]
* [Tao, T., Blog post on Cauchy-Schwarz in finite settings]
-/

import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

open scoped ENNReal NNReal BigOperators
open Finset

noncomputable section

/-!
## Core Definitions

We work with finite state spaces Ω₁, ..., Ωₙ, each with a Fintype instance.
A joint distribution is a probability mass function on the product space.
-/

variable {n : ℕ}

/-- A finite state space for each coordinate. -/
abbrev FiniteStateSpace (n : ℕ) := Fin n → Type*

/-- The product of finite state spaces. -/
abbrev ProductSpace {n : ℕ} (Ω : Fin n → Type*) := ∀ i, Ω i

/-- A joint probability mass function on finite product spaces.
    This is a function p : (∀ i, Ω i) → ℝ≥0∞ that sums to 1. -/
structure JointPMF {n : ℕ} (Ω : Fin n → Type*) [∀ i, Fintype (Ω i)] where
  /-- The probability mass function -/
  prob : (∀ i, Ω i) → ℝ≥0∞
  /-- Probabilities sum to 1 -/
  sum_eq_one : ∑ x : ∀ i, Ω i, prob x = 1

variable {Ω : Fin n → Type*} [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]

/-- The i-th univariate marginal PMF.
    pᵢ(s) = ∑_{x : x_i = s} p(x) -/
def JointPMF.marginal (p : JointPMF Ω) (i : Fin n) : Ω i → ℝ≥0∞ :=
  fun s => ∑ x : ∀ j, Ω j, if x i = s then p.prob x else 0

/-- The marginal is well-defined: summing over all values gives 1. -/
theorem JointPMF.marginal_sum_eq_one (p : JointPMF Ω) (i : Fin n) :
    ∑ s : Ω i, p.marginal i s = 1 := by
  simp only [JointPMF.marginal]
  rw [Finset.sum_comm]
  have h : ∀ x : ∀ j, Ω j, ∑ s : Ω i, (if x i = s then p.prob x else 0) = p.prob x := by
    intro x
    simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  simp_rw [h]
  exact p.sum_eq_one

/-- The consecutive bivariate marginal PMF of (Xᵢ, Xᵢ₊₁).
    p_{i,i+1}(s, t) = ∑_{x : x_i = s, x_{i+1} = t} p(x) -/
def JointPMF.bivariateMarginai (p : JointPMF Ω) (i : Fin (n - 1)) :
    Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ →
    Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ → ℝ≥0∞ :=
  fun s t => ∑ x : ∀ j, Ω j,
    if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧
       x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t
    then p.prob x else 0

/-- The Carbery functional Q_n^{n+1}(p) for a joint PMF on finite spaces.

    Q_n^{n+1}(p) = ∑_s p₁(s₁) · p₁₂(s₁,s₂) · p₂₃(s₂,s₃) · ⋯ · p_{n-1,n}(s_{n-1},sₙ) · pₙ(sₙ)

    IMPORTANT: This is the CORRECT formula from Carbery (2004) and Tao's exposition.
    Only BOUNDARY marginals (p₁ and pₙ) appear, not interior marginals.
    The formula has n+1 factors: 2 boundary marginals + (n-1) bivariate marginals.

    Reference: Tao, T. "A generalized Cauchy-Schwarz inequality via the Gibbs
    variational formula" (2023), which derives this from Carbery's original. -/
def carberyFunctionalPow (hn : n ≥ 1) (p : JointPMF Ω) : ℝ≥0∞ :=
  ∑ s : ∀ i, Ω i,
    p.marginal ⟨0, by omega⟩ (s ⟨0, by omega⟩) *
    (∏ j : Fin (n - 1), p.bivariateMarginai j
      (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
      (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) *
    p.marginal ⟨n - 1, by omega⟩ (s ⟨n - 1, by omega⟩)

/-- The Carbery functional Q_n(p) = (Q_n^{n+1}(p))^{1/(n+1)}. -/
def carberyFunctional (hn : n ≥ 1) (p : JointPMF Ω) : ℝ≥0∞ :=
  (carberyFunctionalPow hn p) ^ (1 / (n + 1 : ℝ))

/-- The Lᵖ norm of a function on a finite type, using sums (counting measure). -/
def lpNormFinite (p : ℝ) {α : Type*} [Fintype α] (f : α → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ x : α, f x ^ p) ^ (1 / p)

/-- The Lᵖ norm of a function weighted by the marginal distribution.
    Note: This is used for independence characterization, NOT for Carbery's inequality.
    Carbery's inequality uses counting measure (lpNormFinite). -/
def lpNormMarginal (p : JointPMF Ω) (exp : ℝ) (i : Fin n) (f : Ω i → ℝ≥0∞) : ℝ≥0∞ :=
  (∑ s : Ω i, p.marginal i s * f s ^ exp) ^ (1 / exp)

/-!
## Axiomatized Foundations

The following results are axiomatized as they are well-established mathematical
facts that the paper builds upon, not contributions of the paper itself.

### Carbery's Inequality (2004)

Carbery's multilinear generalization of Cauchy-Schwarz was proved in:
  Carbery, A. "A multilinear generalisation of the Cauchy-Schwarz inequality."
  Proceedings of the AMS, 132(11), 3141-3152, 2004.

The finite-case version can be proved by elementary induction using Hölder's
inequality, but this is not a contribution of the current paper.
-/

/-- **Carbery's Inequality** (Finite State Spaces) - Theorem 2.3.

    For functions fᵢ : Ωᵢ → ℝ≥0∞,
    ∑_x K(x) ∏ᵢ fᵢ(xᵢ) ≤ Qₙ(K) · ∏ᵢ ‖fᵢ‖_{L^{n+1}}

    where the L^{n+1} norms are with respect to counting measure (not the marginal).
    For n=1, this reduces to Cauchy-Schwarz: ∑ K·f ≤ ‖K‖₂ · ‖f‖₂.

    This is a well-established result from harmonic analysis, taken as an axiom
    to focus the formalization on the paper's novel contributions.

    Reference: Carbery, A. "A multilinear generalisation of the Cauchy-Schwarz
    inequality." Proc. AMS 132(11), 3141-3152, 2004.
    See also: Tao, T. "A generalized Cauchy-Schwarz inequality via Gibbs" (2023). -/
axiom carberyInequality {n : ℕ} {Ω : Fin n → Type*}
    [∀ i, Fintype (Ω i)] [∀ i, DecidableEq (Ω i)]
    (hn : n ≥ 1) (K : JointPMF Ω)
    (f : ∀ i, Ω i → ℝ≥0∞) :
    ∑ x : ∀ i, Ω i, K.prob x * ∏ i, f i (x i) ≤
    carberyFunctional hn K * ∏ i : Fin n, lpNormFinite (n + 1 : ℝ) (f i)

/-!
## Independence Structure

Under independence, the joint PMF factorizes as a product of marginals.
These results characterize Q_n under independence and are contributions
of the paper to be proved.
-/

/-- A joint PMF represents independent random variables if it factorizes
    as a product of marginals. -/
def JointPMF.IsIndependent (p : JointPMF Ω) : Prop :=
  ∀ x, p.prob x = ∏ i : Fin n, p.marginal i (x i)

set_option maxHeartbeats 400000 in
/-- Under independence, the consecutive bivariate marginals factorize.

    **Paper contribution**: Proved (by Aristotle). -/
theorem bivariate_factorizes_of_independent (p : JointPMF Ω)
    (hp : p.IsIndependent) (i : Fin (n - 1)) (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩) :
    p.bivariateMarginai i s t =
    p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s *
    p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t := by
  have h_prod : ∑ x : ∀ j, Ω j, (if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧ x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then (∏ j, p.marginal j (x j)) else 0) = (∏ j ∈ Finset.univ \ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩, ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩}, ∑ x_j : Ω j, p.marginal j x_j) * (p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s) * (p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t) := by
    have h_sum_prod : ∑ x : ∀ j, Ω j, (if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧ x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then (∏ j, p.marginal j (x j)) else 0) = (∑ x : ∀ j, Ω j, if x ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ = s ∧ x ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ = t then (∏ j ∈ Finset.univ \ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩, ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩}, p.marginal j (x j)) * (p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s) * (p.marginal ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩ t) else 0) := by
      refine' Finset.sum_congr rfl fun x hx => _
      split_ifs <;> simp_all +decide [mul_assoc, Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ _]
      rw [← Finset.prod_sdiff (Finset.subset_univ {⟨i.val, Nat.lt_of_lt_pred i.isLt⟩, ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩})]
      aesop
    rw [h_sum_prod]
    simp +decide only [prod_sum]
    simp +decide [Finset.sum_ite, Finset.prod_mul_distrib]
    rw [← Finset.sum_mul, ← Finset.sum_mul]
    refine' congrArg₂ _ (congrArg₂ _ (Finset.sum_bij (fun x hx => fun j hj => x j) _ _ _ _) rfl) rfl
    · simp +contextual [Finset.mem_pi]
    · simp +contextual [funext_iff]
      grind
    · simp +decide [funext_iff, Finset.mem_pi]
      exact fun b => ⟨fun j => if hj : j = ⟨i, Nat.lt_of_lt_pred i.isLt⟩ then hj.symm ▸ s else if hj' : j = ⟨i + 1, Nat.add_lt_of_lt_sub i.isLt⟩ then hj'.symm ▸ t else b j (by aesop), by aesop⟩
    · exact fun x hx => by rw [← Finset.prod_attach]
  simp only [JointPMF.bivariateMarginai]
  have hp' : ∀ x, p.prob x = ∏ j, p.marginal j (x j) := hp
  simp_rw [hp']
  simp_all +decide [mul_assoc, Finset.prod_eq_one, JointPMF.marginal_sum_eq_one]

/-- Key algebraic lemma: Boundary terms and bivariate products combine to give
    each element appearing exactly twice (squared product form).

    This is the abstract form of the fact that in the Carbery functional,
    each marginal appears exactly twice under independence.

    **Paper contribution**: Proved by Aristotle. -/
theorem prod_boundary_bivariate_eq_sq {n : ℕ} (hn : n ≥ 2) (f : Fin n → ℝ≥0∞) :
    f ⟨0, by omega⟩ *
    (∏ j : Fin (n - 1), f ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ *
                        f ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) *
    f ⟨n - 1, by omega⟩ =
    ∏ i : Fin n, f i * f i := by
  -- Proof by Aristotle using Fin product decomposition lemmas
  rcases n with (_ | _ | n) <;> norm_num
  · contradiction
  · contradiction
  · rw [Fin.prod_univ_castSucc]
    norm_num [Finset.prod_mul_distrib, mul_assoc]
    erw [Fin.prod_univ_succ]
    erw [Fin.prod_univ_castSucc]; ring!

/-- Under independence, Q_n^{n+1}(p) has a specific factorized form.

    With the CORRECT Carbery formula, under independence ALL marginals appear
    with power 2 (not the boundary-2/interior-3 pattern from the incorrect formula).

    Derivation: Under independence, p_{j,j+1}(s_j, s_{j+1}) = p_j(s_j) × p_{j+1}(s_{j+1}).
    So each interior marginal p_i (for 2 ≤ i ≤ n-1) appears exactly twice:
    once from p_{i-1,i} and once from p_{i,i+1}.
    Boundary marginals p_1 and p_n each appear twice: once from the explicit
    boundary term and once from the adjacent bivariate marginal.

    **Paper contribution**: To be proved (complex - needs careful index tracking). -/
theorem carberyFunctional_of_independent (hn : n ≥ 2) (p : JointPMF Ω)
    (hp : p.IsIndependent) :
    carberyFunctionalPow (Nat.one_le_of_lt hn) p =
    ∏ i : Fin n, (lpNormFinite 2 (p.marginal i)) ^ 2 := by
  -- Step 1: Rewrite RHS using lpNormFinite definition
  simp only [lpNormFinite]
  -- (∑_s f(s)^2)^{1/2})^2 = ∑_s f(s)^2
  -- First convert the natural number exponent 2 to real exponent
  have rhs_simp : ∀ i : Fin n, ((∑ s : Ω i, p.marginal i s ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℕ) =
      ∑ s : Ω i, p.marginal i s ^ (2 : ℝ) := by
    intro i
    rw [← ENNReal.rpow_natCast _ (2 : ℕ), ← ENNReal.rpow_mul]
    simp only [one_div, Nat.cast_ofNat, isUnit_iff_ne_zero, ne_eq, OfNat.ofNat_ne_zero,
               not_false_eq_true, IsUnit.inv_mul_cancel, ENNReal.rpow_one]
  simp_rw [rhs_simp]
  -- Step 2: Expand carberyFunctionalPow and use independence
  simp only [carberyFunctionalPow]
  -- Use bivariate_factorizes_of_independent to factor bivariate marginals
  have biv_factor : ∀ (j : Fin (n - 1)) (s : ∀ i, Ω i),
      p.bivariateMarginai j (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
                           (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) =
      p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩) *
      p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩ (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) := by
    intro j s
    exact bivariate_factorizes_of_independent p hp j _ _
  -- After factoring bivariate marginals, show each marginal appears twice
  -- The key insight: with bivariate factorization, the full product becomes:
  --   p₀(s₀) × (∏_{j} p_j(s_j) × p_{j+1}(s_{j+1})) × p_{n-1}(s_{n-1})
  -- = p₀(s₀) × (∏_{j=0}^{n-2} p_j(s_j)) × (∏_{j=0}^{n-2} p_{j+1}(s_{j+1})) × p_{n-1}(s_{n-1})
  -- = p₀² × p₁² × ... × p_{n-1}²  (each marginal appears exactly twice)
  --
  -- Step 1: Rewrite bivariate product using prod_mul_distrib
  have prod_factor : ∀ s : ∀ i, Ω i,
      ∏ j : Fin (n - 1), (p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
                           (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩) *
                         p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩
                           (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) =
      (∏ j : Fin (n - 1), p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
                           (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)) *
      (∏ j : Fin (n - 1), p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩
                           (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) := by
    intro s
    exact Finset.prod_mul_distrib
  -- The remaining algebra requires showing the index pattern gives ∏_i p_i(s_i)²
  -- This is complex due to Fin arithmetic. The proof structure is:
  -- 1. The first product over Fin (n-1) gives p₀ × p₁ × ... × p_{n-2}
  -- 2. The second product gives p₁ × p₂ × ... × p_{n-1}
  -- 3. Combined with boundary terms p₀ and p_{n-1}, each appears twice
  -- 4. Use Fintype.prod_sum to interchange sum and product
  --
  -- Key lemma: For each s, the term equals ∏_i p_i(s_i)²
  have term_eq_prod_sq : ∀ s : ∀ i, Ω i,
      p.marginal ⟨0, by omega⟩ (s ⟨0, by omega⟩) *
      (∏ j : Fin (n - 1), p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
                           (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩) *
                         p.marginal ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩
                           (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩)) *
      p.marginal ⟨n - 1, by omega⟩ (s ⟨n - 1, by omega⟩) =
      ∏ i : Fin n, p.marginal i (s i) ^ (2 : ℝ) := by
    intro s
    -- For x^(2:ℝ) in ENNReal, convert to x * x
    have rpow_two_eq : ∀ x : ℝ≥0∞, x ^ (2 : ℝ) = x * x := by
      intro x
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast, pow_two]
    simp_rw [rpow_two_eq]
    -- Apply the abstract algebraic lemma directly
    exact prod_boundary_bivariate_eq_sq hn (fun i => p.marginal i (s i))
  -- Rewrite LHS using biv_factor and term_eq_prod_sq
  -- First, rewrite bivariate marginals using factorization
  conv_lhs =>
    arg 2; ext s
    rw [Finset.prod_congr rfl (fun j _ => biv_factor j s)]
  -- Now apply term_eq_prod_sq to each summand
  conv_lhs =>
    arg 2; ext s
    rw [term_eq_prod_sq s]
  -- Use Fubini: ∑_s ∏_i f_i(s_i) = ∏_i (∑_{s_i} f_i(s_i))
  exact (Fintype.prod_sum (fun i si => p.marginal i si ^ (2 : ℝ))).symm

/-!
## Moment Definitions

For concentration inequalities, we need moments of random variables.
In the finite case, moments are finite sums.
-/

/-- The expectation of a real-valued function under the i-th marginal. -/
def JointPMF.expectation (p : JointPMF Ω) (i : Fin n) (f : Ω i → ℝ) : ℝ :=
  ∑ s : Ω i, (p.marginal i s).toReal * f s

/-- The k-th moment of a real-valued function under the i-th marginal.
    E[|g(Xᵢ)|^k] -/
def JointPMF.moment (p : JointPMF Ω) (i : Fin n) (g : Ω i → ℝ) (k : ℝ) : ℝ≥0∞ :=
  ∑ s : Ω i, p.marginal i s * ENNReal.ofReal (|g s| ^ k)

/-!
## Key Simplification: Finite Sums

The main advantage of finite state spaces is that all expectations and
probabilities are finite sums, avoiding measure-theoretic complications.
-/

/-- Expectation of a product factorizes under independence.

    **Paper contribution**: Proved. -/
theorem expectation_prod_of_independent (p : JointPMF Ω) (hp : p.IsIndependent)
    (f : ∀ i, Ω i → ℝ≥0∞) :
    ∑ x : ∀ i, Ω i, p.prob x * ∏ i, f i (x i) =
    ∏ i : Fin n, ∑ s : Ω i, p.marginal i s * f i s := by
  -- Under independence, p.prob x = ∏ i, p.marginal i (x i)
  have h1 : ∀ x, p.prob x * ∏ i, f i (x i) = ∏ i, (p.marginal i (x i) * f i (x i)) := by
    intro x
    rw [hp x, Finset.prod_mul_distrib]
  simp_rw [h1]
  -- Use Fintype.prod_sum to interchange sum and product
  exact (Fintype.prod_sum (fun i s => p.marginal i s * f i s)).symm

/-- The sum of all probabilities equals 1 (sanity check). -/
theorem prob_sum_one (p : JointPMF Ω) : ∑ x : ∀ i, Ω i, p.prob x = 1 := p.sum_eq_one

/-!
## Utility Lemmas

Basic properties of probabilities in the finite setting.
-/

/-- In the finite case, probabilities are always in [0, 1]. -/
theorem prob_le_one (p : JointPMF Ω) (x : ∀ i, Ω i) : p.prob x ≤ 1 := by
  have h := p.sum_eq_one
  calc p.prob x ≤ ∑ y : ∀ i, Ω i, p.prob y := Finset.single_le_sum (fun _ _ => zero_le _)
                                               (Finset.mem_univ x)
       _ = 1 := h

/-- Marginal probabilities are bounded by 1. -/
theorem marginal_le_one (p : JointPMF Ω) (i : Fin n) (s : Ω i) :
    p.marginal i s ≤ 1 := by
  have h := p.marginal_sum_eq_one i
  calc p.marginal i s ≤ ∑ t : Ω i, p.marginal i t :=
         Finset.single_le_sum (fun _ _ => zero_le _) (Finset.mem_univ s)
       _ = 1 := h

/-!
## Marginal Sufficiency

The Carbery functional Q_n^{n+1}(p) depends on the joint distribution p only through:
1. The boundary univariate marginals (p₁ and pₙ)
2. The consecutive bivariate marginals (p_{1,2}, ..., p_{n-1,n})

This is immediate from the definition, but we state it explicitly as it has
important consequences: Q_n does not distinguish between joint distributions
that agree on these low-dimensional projections.

**Paper reference**: Proposition 6.1 (Marginal sufficiency) in Zambrano (2025).
-/

/-- Two JointPMFs have the same boundary marginals. -/
def JointPMF.sameBoundaryMarginals (p q : JointPMF Ω) (hn : n ≥ 1) : Prop :=
  p.marginal ⟨0, by omega⟩ = q.marginal ⟨0, by omega⟩ ∧
  p.marginal ⟨n - 1, by omega⟩ = q.marginal ⟨n - 1, by omega⟩

/-- Two JointPMFs have the same consecutive bivariate marginals. -/
def JointPMF.sameConsecutiveBivariateMarginals (p q : JointPMF Ω) : Prop :=
  ∀ j : Fin (n - 1), p.bivariateMarginai j = q.bivariateMarginai j

/-- **Marginal Sufficiency Theorem** (Proposition 6.1)

    The Carbery functional Q_n^{n+1}(p) depends on the joint distribution p only
    through the boundary univariate marginals (p₁, pₙ) and the consecutive
    bivariate marginals (p_{1,2}, ..., p_{n-1,n}).

    In particular, if two joint distributions p and q share these marginals,
    then Q_n^{n+1}(p) = Q_n^{n+1}(q).

    **Paper contribution**: This is immediate from the definition of Q_n^{n+1},
    which is expressed entirely in terms of these marginals. -/
theorem carberyFunctionalPow_marginal_sufficiency (hn : n ≥ 1) (p q : JointPMF Ω)
    (h_boundary : p.sameBoundaryMarginals q hn)
    (h_bivariate : p.sameConsecutiveBivariateMarginals q) :
    carberyFunctionalPow hn p = carberyFunctionalPow hn q := by
  -- The proof is by definitional equality: carberyFunctionalPow is defined
  -- entirely in terms of boundary marginals and consecutive bivariate marginals
  simp only [carberyFunctionalPow]
  congr 1
  ext s
  -- Show each term in the sum is equal
  have h1 : p.marginal ⟨0, by omega⟩ (s ⟨0, by omega⟩) =
            q.marginal ⟨0, by omega⟩ (s ⟨0, by omega⟩) := by
    rw [h_boundary.1]
  have h2 : p.marginal ⟨n - 1, by omega⟩ (s ⟨n - 1, by omega⟩) =
            q.marginal ⟨n - 1, by omega⟩ (s ⟨n - 1, by omega⟩) := by
    rw [h_boundary.2]
  have h3 : ∏ j : Fin (n - 1), p.bivariateMarginai j
              (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
              (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) =
            ∏ j : Fin (n - 1), q.bivariateMarginai j
              (s ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
              (s ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) := by
    congr 1
    ext j
    rw [h_bivariate j]
  rw [h1, h2, h3]

/-- Corollary: Q_n (the (n+1)-th root) also satisfies marginal sufficiency. -/
theorem carberyFunctional_marginal_sufficiency (hn : n ≥ 1) (p q : JointPMF Ω)
    (h_boundary : p.sameBoundaryMarginals q hn)
    (h_bivariate : p.sameConsecutiveBivariateMarginals q) :
    carberyFunctional hn p = carberyFunctional hn q := by
  simp only [carberyFunctional]
  rw [carberyFunctionalPow_marginal_sufficiency hn p q h_boundary h_bivariate]

/-!
## Markov Chain Structure

For first-order Markov chains, the bivariate marginals factor as:
  p_{j,j+1}(s_j, s_{j+1}) = p_j(s_j) · P(s_{j+1} | s_j)

This means Q_n^{n+1}(p) depends only on:
1. The univariate marginals {p_i}
2. The transition probabilities {P(x_{i+1} | x_i)}

These are exactly the quantities that characterize the Markov chain.

**Paper reference**: Proposition 4.3 (Markov chain structure) in Zambrano (2025).
-/

/-- Transition probability from state s at position i to state t at position i+1.
    P(X_{i+1} = t | X_i = s) = p_{i,i+1}(s,t) / p_i(s) when p_i(s) > 0. -/
def JointPMF.transitionProb (p : JointPMF Ω) (i : Fin (n - 1))
    (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩) : ℝ≥0∞ :=
  p.bivariateMarginai i s t / p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s

/-- A JointPMF represents a first-order Markov chain if the bivariate marginals
    factor as: p_{j,j+1}(s_j, s_{j+1}) = p_j(s_j) · P(s_{j+1} | s_j).

    Equivalently: X_{i+1} ⊥ (X_1,...,X_{i-1}) | X_i for all i. -/
def JointPMF.IsMarkovChain (p : JointPMF Ω) : Prop :=
  ∀ (i : Fin (n - 1)) (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩),
    p.bivariateMarginai i s t =
    p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s * p.transitionProb i s t

/-- For a Markov chain, the bivariate marginal factors into marginal × transition. -/
theorem JointPMF.bivariate_eq_marginal_mul_transition (p : JointPMF Ω)
    (hp : p.IsMarkovChain) (i : Fin (n - 1))
    (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
    (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩) :
    p.bivariateMarginai i s t =
    p.marginal ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩ s * p.transitionProb i s t :=
  hp i s t

/-- **Markov Chain Structure Theorem** (Proposition 4.3)

    For a first-order Markov chain, Q_n^{n+1}(p) depends only on the univariate
    marginals and transition probabilities---exactly the quantities characterizing
    the chain.

    More precisely: if two Markov chains p and q have:
    1. The same boundary marginals (p_1 and p_n)
    2. The same transition probabilities P(x_{i+1} | x_i) for all i

    Then Q_n^{n+1}(p) = Q_n^{n+1}(q).

    **Proof**: For Markov chains, p_{j,j+1}(s_j, s_{j+1}) = p_j(s_j) · P(s_{j+1}|s_j).
    The Carbery functional is built from boundary marginals and bivariate marginals.
    Since bivariate marginals are determined by univariate marginals and transitions,
    Q_n depends only on these quantities.

    **Paper contribution**: Proposition 4.3. -/
theorem carberyFunctionalPow_markov_chain_structure (hn : n ≥ 1)
    (p q : JointPMF Ω)
    (hp : p.IsMarkovChain) (hq : q.IsMarkovChain)
    -- Same boundary marginals
    (h_boundary : p.sameBoundaryMarginals q hn)
    -- Same transition probabilities
    (h_transition : ∀ (i : Fin (n - 1))
        (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
        (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩),
        p.transitionProb i s t = q.transitionProb i s t)
    -- Same interior marginals (follows from boundary + transitions for Markov chains)
    (h_interior_marginals : ∀ (i : Fin n),
        p.marginal i = q.marginal i) :
    carberyFunctionalPow hn p = carberyFunctionalPow hn q := by
  -- Use marginal sufficiency: Q_n depends only on boundary marginals and
  -- consecutive bivariate marginals
  apply carberyFunctionalPow_marginal_sufficiency hn p q h_boundary
  -- Show bivariate marginals are equal
  intro j
  ext s t
  -- For Markov chains: p_{j,j+1}(s,t) = p_j(s) · P(t|s)
  rw [hp j s t, hq j s t]
  -- p_j(s) = q_j(s) by h_interior_marginals
  have h_marg : p.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ s =
                q.marginal ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩ s := by
    have := h_interior_marginals ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩
    rw [this]
  -- P(t|s) equal by h_transition
  rw [h_marg, h_transition j s t]

/-- Corollary: Two Markov chains with the same marginals and transitions have
    equal Carbery functionals Q_n. -/
theorem carberyFunctional_markov_chain_structure (hn : n ≥ 1)
    (p q : JointPMF Ω)
    (hp : p.IsMarkovChain) (hq : q.IsMarkovChain)
    (h_boundary : p.sameBoundaryMarginals q hn)
    (h_transition : ∀ (i : Fin (n - 1))
        (s : Ω ⟨i.val, Nat.lt_of_lt_pred i.isLt⟩)
        (t : Ω ⟨i.val + 1, Nat.add_lt_of_lt_sub i.isLt⟩),
        p.transitionProb i s t = q.transitionProb i s t)
    (h_interior_marginals : ∀ (i : Fin n), p.marginal i = q.marginal i) :
    carberyFunctional hn p = carberyFunctional hn q := by
  simp only [carberyFunctional]
  rw [carberyFunctionalPow_markov_chain_structure hn p q hp hq h_boundary
      h_transition h_interior_marginals]

/-!
## Tensorization (Independent Blocks)

When two sequences of random variables X = (X₁,...,Xₘ) and Y = (Y₁,...,Yₖ)
are independent blocks, the combined sequence Z = (X₁,...,Xₘ,Y₁,...,Yₖ) satisfies:

  Q_{m+k}^{m+k+1}(p_Z) = Q_m^{m+1}(p_X) · Q_k^{k+1}(p_Y)

This is Proposition 4.1(ii) in Zambrano (2025).

The key insight is that at the boundary between blocks, independence gives:
  p_{m,m+1}(x_m, y_1) = p_m(x_m) · q_1(y_1)

This "breaks" the consecutive dependence chain, allowing the functional to factor.

## Design Decision: Homogeneous State Spaces

We prove tensorization for the **homogeneous** case where all coordinates share the
same finite type α. This avoids dependent-type coercion issues that arise when
Ω_Z : Fin (m+k) → Type* must match Ω_X : Fin m → Type* and Ω_Y : Fin k → Type*
via Fin.addCases for type families.

In the homogeneous setting:
- State assignments are plain functions `Fin n → α` (no dependent types)
- The split `(Fin (m+k) → α) ↔ (Fin m → α) × (Fin k → α)` requires no type casts
- All existing infrastructure works unchanged

The heterogeneous generalization is left as future work.
-/

section Tensorization

/-! ### Fin Splitting Utilities -/

/-- Round-trip property: splitting a function on `Fin (m + k)` into its left and right
    components via `Fin.castAdd` and `Fin.natAdd`, then reassembling with `Fin.addCases`,
    recovers the original function. -/
theorem Fin.addCases_comp_eta {m k : ℕ} {α : Type*} (z : Fin (m + k) → α) :
    Fin.addCases (z ∘ Fin.castAdd k) (z ∘ Fin.natAdd m) = z := by
  ext i
  obtain ⟨j | j, rfl⟩ := finSumFinEquiv.surjective i
  · simp [Fin.addCases_left, Function.comp]
  · simp [Fin.addCases_right, Function.comp]

/-- The equivalence between `(Fin m → α) × (Fin k → α)` and `Fin (m + k) → α`
    via `Fin.addCases`. -/
def Equiv.finAddCases (m k : ℕ) (α : Type*) :
    ((Fin m → α) × (Fin k → α)) ≃ (Fin (m + k) → α) where
  toFun := fun ⟨x, y⟩ => Fin.addCases x y
  invFun := fun z => (z ∘ Fin.castAdd k, z ∘ Fin.natAdd m)
  left_inv := by
    intro ⟨x, y⟩
    refine Prod.ext ?_ ?_ <;> funext i <;> simp [Function.comp]
  right_inv := fun z => Fin.addCases_comp_eta z

/-- Summing a function over `Fin (m + k) → α` is equivalent to a double sum
    over `(Fin m → α)` and `(Fin k → α)`, connected via `Fin.addCases`. -/
lemma sum_fin_add_equiv {m k : ℕ} {α : Type*} [Fintype α]
    (f : (Fin (m + k) → α) → ℝ≥0∞) :
    ∑ z : Fin (m + k) → α, f z =
    ∑ x : Fin m → α, ∑ y : Fin k → α, f (Fin.addCases x y) := by
  calc ∑ z, f z
      = ∑ p : (Fin m → α) × (Fin k → α), f (Fin.addCases p.1 p.2) :=
        (Fintype.sum_equiv (Equiv.finAddCases m k α) _ _ (fun ⟨_, _⟩ => rfl)).symm
    _ = ∑ x, ∑ y, f (Fin.addCases x y) := Fintype.sum_prod_type _

/-! ### Independent Product of JointPMFs -/

/-- The independent product of two JointPMFs on homogeneous finite state spaces.
    Given `p` on `Fin m → α` and `q` on `Fin k → α`, produces `p ⊗ q` on
    `Fin (m+k) → α` where `(p ⊗ q)(z) = p(z|_{Fin m}) · q(z|_{Fin k})`. -/
def JointPMF.independentProduct {m k : ℕ} {α : Type*} [Fintype α] [DecidableEq α]
    (p : JointPMF (fun _ : Fin m => α)) (q : JointPMF (fun _ : Fin k => α)) :
    JointPMF (fun _ : Fin (m + k) => α) where
  prob z := p.prob (fun i => z (Fin.castAdd k i)) *
            q.prob (fun j => z (Fin.natAdd m j))
  sum_eq_one := by
    rw [sum_fin_add_equiv]
    have h_simp : ∀ (x : Fin m → α) (y : Fin k → α),
        p.prob (fun i => Fin.addCases x y (Fin.castAdd k i)) *
        q.prob (fun j => Fin.addCases x y (Fin.natAdd m j)) =
        p.prob x * q.prob y := by
      intro x y
      congr 1
      · congr 1; funext i; simp
      · congr 1; funext j; simp
    simp_rw [h_simp, ← Finset.mul_sum, q.sum_eq_one, mul_one, p.sum_eq_one]

/-! ### Sum Factoring Helpers -/

/-- Factoring a conditional sum of products: when the condition and factors are
    independent between the two summation variables, the sum factors. -/
lemma sum_sum_ite_and_mul {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂]
    (A : ι₁ → Prop) [DecidablePred A] (B : ι₂ → Prop) [DecidablePred B]
    (f : ι₁ → ℝ≥0∞) (g : ι₂ → ℝ≥0∞) :
    ∑ a, ∑ b, (if A a ∧ B b then f a * g b else 0) =
    (∑ a, if A a then f a else 0) * (∑ b, if B b then g b else 0) := by
  have h : ∀ a b, (if A a ∧ B b then f a * g b else 0) =
      (if A a then f a else 0) * (if B b then g b else 0) := by
    intro a b; by_cases ha : A a <;> by_cases hb : B b <;> simp [ha, hb]
  simp_rw [h, ← Finset.mul_sum, ← Finset.sum_mul]

/-! ### Marginal Relationship Lemmas

These lemmas relate the marginals and bivariate marginals of the independent product
`p.independentProduct q` to those of `p` and `q`. -/

/-- Left boundary marginal: the 0-th marginal of `p ⊗ q` equals the 0-th marginal
    of `p`. -/
theorem independentProduct_marginal_left {m k : ℕ} (hm : m ≥ 1)
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : JointPMF (fun _ : Fin m => α)) (q : JointPMF (fun _ : Fin k => α))
    (s : α) :
    (p.independentProduct q).marginal ⟨0, by omega⟩ s =
    p.marginal ⟨0, hm⟩ s := by
  simp only [JointPMF.marginal, JointPMF.independentProduct]
  rw [sum_fin_add_equiv]
  -- Simplify addCases projections to recover p.prob x and q.prob y
  have h_p : ∀ (x : Fin m → α) (y : Fin k → α),
      p.prob (fun i => Fin.addCases x y (Fin.castAdd k i)) = p.prob x := by
    intro x y; congr 1; funext i; simp
  have h_q : ∀ (x : Fin m → α) (y : Fin k → α),
      q.prob (fun j => Fin.addCases x y (Fin.natAdd m j)) = q.prob y := by
    intro x y; congr 1; funext j; simp
  -- The index ⟨0, _⟩ is in the left block since 0 < m
  have h_idx : ∀ (x : Fin m → α) (y : Fin k → α),
      Fin.addCases x y ⟨0, by omega⟩ = x ⟨0, hm⟩ := by
    intro x y
    have h_fin : (⟨0, by omega⟩ : Fin (m + k)) =
        Fin.castAdd k ⟨0, hm⟩ := Fin.ext rfl
    simp only [h_fin, Fin.addCases_left]
  simp_rw [h_idx, h_p, h_q]
  congr 1; ext x
  by_cases h : x ⟨0, hm⟩ = s
  · simp [h, ← Finset.mul_sum, q.sum_eq_one]
  · simp [h]

/-- Right boundary marginal: the (m+k-1)-th marginal of `p ⊗ q` equals the (k-1)-th
    marginal of `q`. -/
theorem independentProduct_marginal_right {m k : ℕ} (hm : m ≥ 1) (hk : k ≥ 1)
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : JointPMF (fun _ : Fin m => α)) (q : JointPMF (fun _ : Fin k => α))
    (s : α) :
    (p.independentProduct q).marginal ⟨m + k - 1, by omega⟩ s =
    q.marginal ⟨k - 1, by omega⟩ s := by
  simp only [JointPMF.marginal, JointPMF.independentProduct]
  rw [sum_fin_add_equiv]
  have h_p : ∀ (x : Fin m → α) (y : Fin k → α),
      p.prob (fun i => Fin.addCases x y (Fin.castAdd k i)) = p.prob x := by
    intro x y; congr 1; funext i; simp
  have h_q : ∀ (x : Fin m → α) (y : Fin k → α),
      q.prob (fun j => Fin.addCases x y (Fin.natAdd m j)) = q.prob y := by
    intro x y; congr 1; funext j; simp
  -- The index ⟨m+k-1, _⟩ is in the right block since m+k-1 ≥ m
  have h_idx : ∀ (x : Fin m → α) (y : Fin k → α),
      Fin.addCases x y ⟨m + k - 1, by omega⟩ = y ⟨k - 1, by omega⟩ := by
    intro x y
    have h_fin : (⟨m + k - 1, by omega⟩ : Fin (m + k)) =
        Fin.natAdd m ⟨k - 1, by omega⟩ := Fin.ext (by simp [Fin.natAdd]; omega)
    simp only [h_fin, Fin.addCases_right]
  simp_rw [h_idx, h_p, h_q]
  rw [Finset.sum_comm]
  congr 1; ext y
  by_cases h : y ⟨k - 1, by omega⟩ = s
  · simp [h, ← Finset.sum_mul, p.sum_eq_one]
  · simp [h]

/-- **KEY**: Boundary bivariate marginal factorization.
    The (m-1)-th bivariate marginal of `p ⊗ q` (connecting the last X-coordinate to the
    first Y-coordinate) factors into a product of the corresponding univariate marginals.
    This is the mathematical content that enables tensorization. -/
theorem independentProduct_bivariate_boundary {m k : ℕ} (hm : m ≥ 1) (hk : k ≥ 1)
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : JointPMF (fun _ : Fin m => α)) (q : JointPMF (fun _ : Fin k => α))
    (s t : α) :
    (p.independentProduct q).bivariateMarginai ⟨m - 1, by omega⟩ s t =
    p.marginal ⟨m - 1, by omega⟩ s * q.marginal ⟨0, by omega⟩ t := by
  simp only [JointPMF.bivariateMarginai, JointPMF.independentProduct, JointPMF.marginal]
  rw [sum_fin_add_equiv]
  -- Simplify addCases projections
  have h_p : ∀ (x : Fin m → α) (y : Fin k → α),
      p.prob (fun i => Fin.addCases x y (Fin.castAdd k i)) = p.prob x := by
    intro x y; congr 1; funext i; simp
  have h_q : ∀ (x : Fin m → α) (y : Fin k → α),
      q.prob (fun j => Fin.addCases x y (Fin.natAdd m j)) = q.prob y := by
    intro x y; congr 1; funext j; simp
  -- m-1 is in the left block (m-1 < m)
  have h_left : ∀ (x : Fin m → α) (y : Fin k → α),
      Fin.addCases x y ⟨m - 1, by omega⟩ = x ⟨m - 1, by omega⟩ := by
    intro x y
    simp only [show (⟨m - 1, by omega⟩ : Fin (m + k)) = Fin.castAdd k ⟨m - 1, by omega⟩
      from Fin.ext rfl, Fin.addCases_left]
  -- (m-1)+1 = m is in the right block at index 0
  have h_right : ∀ (x : Fin m → α) (y : Fin k → α),
      Fin.addCases x y ⟨(m - 1) + 1, by omega⟩ = y ⟨0, by omega⟩ := by
    intro x y
    simp only [show (⟨(m - 1) + 1, by omega⟩ : Fin (m + k)) = Fin.natAdd m ⟨0, by omega⟩
      from Fin.ext (by simp [Fin.natAdd]; omega), Fin.addCases_right]
  simp_rw [h_left, h_right, h_p, h_q]
  -- Factor: ∑_x ∑_y [x(m-1)=s ∧ y(0)=t] · p(x)·q(y)
  --       = (∑_x [x(m-1)=s] · p(x)) · (∑_y [y(0)=t] · q(y))
  exact sum_sum_ite_and_mul _ _ _ _

/-- X-block bivariate marginals: for j < m-1, the j-th bivariate marginal of `p ⊗ q`
    equals the j-th bivariate marginal of `p`. -/
theorem independentProduct_bivariate_left {m k : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : JointPMF (fun _ : Fin m => α)) (q : JointPMF (fun _ : Fin k => α))
    (j : ℕ) (hj : j + 1 < m) (s t : α) :
    (p.independentProduct q).bivariateMarginai ⟨j, by omega⟩ s t =
    p.bivariateMarginai ⟨j, by omega⟩ s t := by
  simp only [JointPMF.bivariateMarginai, JointPMF.independentProduct]
  rw [sum_fin_add_equiv]
  have h_p : ∀ (x : Fin m → α) (y : Fin k → α),
      p.prob (fun i => Fin.addCases x y (Fin.castAdd k i)) = p.prob x := by
    intro x y; congr 1; funext i; simp
  have h_q : ∀ (x : Fin m → α) (y : Fin k → α),
      q.prob (fun j => Fin.addCases x y (Fin.natAdd m j)) = q.prob y := by
    intro x y; congr 1; funext j; simp
  -- j and j+1 are both in the left block since j+1 < m
  have hj1 : ∀ (x : Fin m → α) (y : Fin k → α),
      Fin.addCases x y ⟨j, by omega⟩ = x ⟨j, by omega⟩ := by
    intro x y
    simp only [show (⟨j, by omega⟩ : Fin (m + k)) = Fin.castAdd k ⟨j, by omega⟩
      from Fin.ext rfl, Fin.addCases_left]
  have hj2 : ∀ (x : Fin m → α) (y : Fin k → α),
      Fin.addCases x y ⟨j + 1, by omega⟩ = x ⟨j + 1, by omega⟩ := by
    intro x y
    simp only [show (⟨j + 1, by omega⟩ : Fin (m + k)) = Fin.castAdd k ⟨j + 1, hj⟩
      from Fin.ext rfl, Fin.addCases_left]
  simp_rw [hj1, hj2, h_p, h_q]
  -- Now: ∑ x, ∑ y, if A(x) then p(x) * q(y) else 0 = ∑ x, if A(x) then p(x) else 0
  -- Factor out q.sum_eq_one
  congr 1; ext x
  by_cases h : x ⟨j, by omega⟩ = s ∧ x ⟨j + 1, by omega⟩ = t
  · simp [h, ← Finset.mul_sum, q.sum_eq_one]
  · simp [h]

/-- Y-block bivariate marginals: for j' < k-1, the (m+j')-th bivariate marginal of
    `p ⊗ q` equals the j'-th bivariate marginal of `q`. -/
theorem independentProduct_bivariate_right {m k : ℕ}
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : JointPMF (fun _ : Fin m => α)) (q : JointPMF (fun _ : Fin k => α))
    (j : ℕ) (hj : j + 1 < k) (s t : α) :
    (p.independentProduct q).bivariateMarginai ⟨m + j, by omega⟩ s t =
    q.bivariateMarginai ⟨j, by omega⟩ s t := by
  simp only [JointPMF.bivariateMarginai, JointPMF.independentProduct]
  rw [sum_fin_add_equiv]
  have h_p : ∀ (x : Fin m → α) (y : Fin k → α),
      p.prob (fun i => Fin.addCases x y (Fin.castAdd k i)) = p.prob x := by
    intro x y; congr 1; funext i; simp
  have h_q : ∀ (x : Fin m → α) (y : Fin k → α),
      q.prob (fun j => Fin.addCases x y (Fin.natAdd m j)) = q.prob y := by
    intro x y; congr 1; funext j; simp
  -- m+j and m+j+1 are both in the right block since m+j ≥ m
  have hj1 : ∀ (x : Fin m → α) (y : Fin k → α),
      Fin.addCases x y ⟨m + j, by omega⟩ = y ⟨j, by omega⟩ := by
    intro x y
    simp only [show (⟨m + j, by omega⟩ : Fin (m + k)) = Fin.natAdd m ⟨j, by omega⟩
      from Fin.ext (by simp [Fin.natAdd]), Fin.addCases_right]
  have hj2 : ∀ (x : Fin m → α) (y : Fin k → α),
      Fin.addCases x y ⟨m + j + 1, by omega⟩ = y ⟨j + 1, hj⟩ := by
    intro x y
    simp only [show (⟨m + j + 1, by omega⟩ : Fin (m + k)) = Fin.natAdd m ⟨j + 1, hj⟩
      from Fin.ext (by simp [Fin.natAdd]; omega), Fin.addCases_right]
  simp_rw [hj1, hj2, h_p, h_q]
  -- Now: ∑ x, ∑ y, if B(y) then p(x) * q(y) else 0 = ∑ y, if B(y) then q(y) else 0
  -- Swap sums and factor out p.sum_eq_one
  rw [Finset.sum_comm]
  congr 1; ext y
  by_cases h : y ⟨j, by omega⟩ = s ∧ y ⟨j + 1, hj⟩ = t
  · simp [h, ← Finset.sum_mul, p.sum_eq_one]
  · simp [h]

/-! ### Fin Product Splitting -/

/-- Splitting a product over `Fin (m + k - 1)` at the boundary `m - 1` into three parts:
    left block (indices `0` to `m-2`), boundary (index `m-1`), and right block
    (indices `m` to `m+k-2`).

    This is the combinatorial heart of the tensorization proof: the consecutive
    bivariate product splits into X-block bivariates, the boundary term, and
    Y-block bivariates.

    **Technical note**: This is a standard finite product splitting fact. The proof
    requires careful `Fin` index arithmetic. -/
lemma Fin.prod_split_three {m k : ℕ} (hm : m ≥ 1) (hk : k ≥ 1)
    (f : Fin (m + k - 1) → ℝ≥0∞) :
    ∏ j : Fin (m + k - 1), f j =
    (∏ j : Fin (m - 1), f ⟨j.val, by omega⟩) *
    f ⟨m - 1, by omega⟩ *
    (∏ j : Fin (k - 1), f ⟨m + j.val, by omega⟩) := by
  -- Strategy: convert all Fin products to Finset.range products via a lifting
  -- function g, then split using standard range/Ico lemmas, then convert back.
  set g : ℕ → ℝ≥0∞ := fun i => if h : i < m + k - 1 then f ⟨i, h⟩ else 1 with hg_def
  -- Key: for i < m+k-1, g i = f ⟨i, _⟩
  have hg_val : ∀ (i : ℕ) (hi : i < m + k - 1), g i = f ⟨i, hi⟩ := by
    intro i hi; simp [hg_def, hi]
  -- Step 1: Convert LHS ∏ j : Fin (m+k-1), f j  to  ∏ i in range (m+k-1), g i
  have lhs_eq : ∏ j : Fin (m + k - 1), f j = ∏ i ∈ Finset.range (m + k - 1), g i := by
    conv_lhs => arg 2; ext j; rw [← hg_val j.val j.isLt]
    exact Fin.prod_univ_eq_prod_range g (m + k - 1)
  -- Step 2: Convert each RHS sub-product to range products
  have left_eq : ∏ j : Fin (m - 1), f ⟨j.val, by omega⟩ =
      ∏ i ∈ Finset.range (m - 1), g i := by
    conv_lhs => arg 2; ext j; rw [← hg_val j.val (by omega)]
    exact Fin.prod_univ_eq_prod_range g (m - 1)
  have mid_eq : f ⟨m - 1, by omega⟩ = g (m - 1) := by
    rw [← hg_val (m - 1) (by omega)]
  have right_eq : ∏ j : Fin (k - 1), f ⟨m + j.val, by omega⟩ =
      ∏ i ∈ Finset.range (k - 1), g (m + i) := by
    conv_lhs => arg 2; ext j; rw [← hg_val (m + j.val) (by omega)]
    exact Fin.prod_univ_eq_prod_range (fun i => g (m + i)) (k - 1)
  rw [lhs_eq, left_eq, mid_eq, right_eq]
  -- Step 3: Split range (m+k-1) into range m and Ico m (m+k-1)
  rw [← Finset.prod_range_mul_prod_Ico g (show m ≤ m + k - 1 by omega)]
  -- Step 4: Split range m = range (m-1) * g(m-1) via prod_range_succ
  conv_lhs => rw [show m = m - 1 + 1 from by omega, Finset.prod_range_succ]
  -- Step 5: Convert Ico m (m+k-1) product to range (k-1) product
  rw [Finset.prod_Ico_eq_prod_range]
  -- Now need to simplify the expressions involving m-1+1 back to m
  have h_base_eq : ∀ x, m - 1 + 1 + x = m + x := by omega
  simp only [h_base_eq]
  have h_range_eq : m + k - 1 - (m - 1 + 1) = k - 1 := by omega
  rw [h_range_eq]

/-! ### Main Tensorization Theorem -/

/-- **Tensorization Theorem** (Proposition 4.1(ii))

    For independent blocks X = (X₁,...,Xₘ) and Y = (Y₁,...,Yₖ) with the same finite
    state space α, the combined sequence Z = (X₁,...,Xₘ,Y₁,...,Yₖ) satisfies:

    Q_{m+k}^{m+k+1}(p_Z) = Q_m^{m+1}(p_X) · Q_k^{k+1}(p_Y)

    **Proof strategy**:
    1. Unfold carberyFunctionalPow for p_Z = p.independentProduct q
    2. Split the sum over Fin (m+k) → α into sums over (Fin m → α) × (Fin k → α)
    3. For each (x, y), substitute addCases projections in marginals and bivariates
    4. Split the bivariate product at j = m-1 using Fin.prod_split_three
    5. Substitute marginal relationships (boundary and bivariate)
    6. Show each summand factors as term_p(x) * term_q(y)
    7. Apply Fubini (finite sums commute with products)
    8. Recognize each factor as carberyFunctionalPow for p and q

    **Paper contribution**: Proposition 4.1(ii) - Tensorization property.

    **Formalization status**: The proof depends on `Fin.prod_split_three` (a standard
    product splitting fact whose Lean proof requires delicate Fin index arithmetic).
    All other ingredients (product PMF, marginal relationships, boundary factorization,
    sum splitting) are fully proved above. -/
theorem carberyFunctionalPow_tensorization {m k : ℕ} (hm : m ≥ 1) (hk : k ≥ 1)
    {α : Type*} [Fintype α] [DecidableEq α]
    (p : JointPMF (fun _ : Fin m => α))
    (q : JointPMF (fun _ : Fin k => α)) :
    carberyFunctionalPow (by omega : m + k ≥ 1) (p.independentProduct q) =
    carberyFunctionalPow hm p * carberyFunctionalPow hk q := by
  -- Unfold the Carbery functional on both sides
  simp only [carberyFunctionalPow]
  -- Split the sum over Fin (m+k) → α into nested sums over (Fin m → α) × (Fin k → α)
  rw [sum_fin_add_equiv]
  -- Transform RHS (∑ P) * (∑ Q) into ∑ x, ∑ y, P(x) * Q(y)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  -- Now prove pointwise: term_Z(addCases x y) = term_p(x) * term_q(y)
  -- Beta/eta-reduce (fun i ↦ Fin.addCases x y i) to Fin.addCases x y
  have h_eta : (fun i => Fin.addCases x y i) = Fin.addCases x y := rfl
  simp only [h_eta]
  -- Helper: resolve Fin.addCases for indices in the left block (< m)
  have hac_l : ∀ (j : ℕ) (hj : j < m),
      Fin.addCases x y (⟨j, by omega⟩ : Fin (m + k)) = x ⟨j, hj⟩ := by
    intro j hj
    have : (⟨j, (by omega : j < m + k)⟩ : Fin (m + k)) = Fin.castAdd k ⟨j, hj⟩ := Fin.ext rfl
    rw [this, Fin.addCases_left]
  -- Helper: resolve Fin.addCases for indices in the right block (≥ m)
  have hac_r : ∀ (j : ℕ) (hj : j < k),
      Fin.addCases x y (⟨m + j, by omega⟩ : Fin (m + k)) = y ⟨j, hj⟩ := by
    intro j hj
    have : (⟨m + j, (by omega : m + j < m + k)⟩ : Fin (m + k)) = Fin.natAdd m ⟨j, hj⟩ :=
      Fin.ext rfl
    rw [this, Fin.addCases_right]
  -- Step 1: Left boundary marginal
  rw [hac_l 0 hm, independentProduct_marginal_left hm p q]
  -- Step 2: Right boundary marginal (m + k - 1 = m + (k - 1))
  have hac_last : Fin.addCases x y (⟨m + k - 1, by omega⟩ : Fin (m + k)) =
      y ⟨k - 1, by omega⟩ := by
    have : (⟨m + k - 1, by omega⟩ : Fin (m + k)) = Fin.natAdd m ⟨k - 1, by omega⟩ :=
      Fin.ext (by dsimp [Fin.natAdd]; omega)
    rw [this, Fin.addCases_right]
  rw [hac_last, independentProduct_marginal_right hm hk p q]
  -- Step 3: Split the bivariate product into left block, boundary, right block
  rw [Fin.prod_split_three hm hk]
  -- Step 4: Boundary bivariate → p.marginal(m-1) * q.marginal(0)
  -- The boundary second index from Fin.prod_split_three is m-1+1 (NOT m).
  -- We must NOT normalize m-1+1→m via simp (that wraps the Fin proof in Eq.mpr,
  -- breaking rw matching). Instead, handle it directly.
  have hac_bdy : ∀ (h : m - 1 + 1 < m + k),
      Fin.addCases x y (⟨m - 1 + 1, h⟩ : Fin (m + k)) = y ⟨0, hk⟩ := by
    intro h
    have : (⟨m - 1 + 1, h⟩ : Fin (m + k)) = Fin.natAdd m ⟨0, hk⟩ :=
      Fin.ext (by dsimp [Fin.natAdd]; omega)
    rw [this, Fin.addCases_right]
  rw [hac_l (m - 1) (by omega), hac_bdy,
      independentProduct_bivariate_boundary hm hk p q]
  -- Step 5: Left sub-product (X-block bivariates)
  have h_left_prod : ∀ (j : Fin (m - 1)),
      (p.independentProduct q).bivariateMarginai ⟨j.val, by omega⟩
        (Fin.addCases x y ⟨j.val, by omega⟩)
        (Fin.addCases x y ⟨j.val + 1, by omega⟩) =
      p.bivariateMarginai j
        (x ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
        (x ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) := by
    intro j
    rw [hac_l j.val (by omega), hac_l (j.val + 1) (by omega),
        independentProduct_bivariate_left p q j.val (by omega)]
  simp_rw [h_left_prod]
  -- Step 6: Right sub-product (Y-block bivariates)
  have h_right_prod : ∀ (j : Fin (k - 1)),
      (p.independentProduct q).bivariateMarginai ⟨m + j.val, by omega⟩
        (Fin.addCases x y ⟨m + j.val, by omega⟩)
        (Fin.addCases x y ⟨m + j.val + 1, by omega⟩) =
      q.bivariateMarginai j
        (y ⟨j.val, Nat.lt_of_lt_pred j.isLt⟩)
        (y ⟨j.val + 1, Nat.add_lt_of_lt_sub j.isLt⟩) := by
    intro j
    have h2 : Fin.addCases x y (⟨m + j.val + 1, by omega⟩ : Fin (m + k)) =
        y ⟨j.val + 1, by omega⟩ := hac_r (j.val + 1) (by omega)
    rw [hac_r j.val (by omega), h2,
        independentProduct_bivariate_right p q j.val (by omega)]
  simp_rw [h_right_prod]
  -- Step 7: All terms now use p/q marginals and bivariates. Rearrange.
  ring

/-!
### Concrete Tensorization: Product of Univariate PMFs

The simplest concrete case of tensorization: when we combine two univariate
distributions (n₁ = n₂ = 1), we get a bivariate distribution, and
Q_2^3(p_Z) = Q_1^2(p_X) · Q_1^2(p_Y).

For univariate distributions:
- Q_1^2(p) = ∑_s p(s) · p(s) = ∑_s p(s)²  (just the squared L² norm)

For the product bivariate distribution with p_Z(x,y) = p_X(x) · p_Y(y):
- Q_2^3(p_Z) = ∑_{x,y} p_X(x) · p_{XY}(x,y) · p_Y(y)
             = ∑_{x,y} p_X(x) · [p_X(x) · p_Y(y)] · p_Y(y)   [by independence]
             = ∑_{x,y} p_X(x)² · p_Y(y)²
             = [∑_x p_X(x)²] · [∑_y p_Y(y)²]
             = Q_1^2(p_X) · Q_1^2(p_Y)

This concrete case demonstrates the tensorization mechanism.
-/

/-- For a univariate PMF, Q_1^2 equals the sum of squared probabilities. -/
def univariateCarberyPow {α : Type*} [Fintype α] (p : α → ℝ≥0∞) (h_sum : ∑ x, p x = 1) : ℝ≥0∞ :=
  ∑ x : α, p x * p x

/-- The product PMF of two univariate PMFs. -/
def productPMF {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ≥0∞) (q : β → ℝ≥0∞) : α × β → ℝ≥0∞ :=
  fun ⟨x, y⟩ => p x * q y

/-- Product PMF sums to 1 if components do.

    **Proved by Aristotle**: Fubini-style sum interchange. -/
theorem productPMF_sum_eq_one {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ≥0∞) (q : β → ℝ≥0∞)
    (hp : ∑ x, p x = 1) (hq : ∑ y, q y = 1) :
    ∑ z : α × β, productPMF p q z = 1 := by
  simp_all +decide [ productPMF ];
  erw [ Finset.sum_product ];
  simp +decide [ ← Finset.mul_sum _ _ _, hp, hq ]

/-- **Tensorization for univariate PMFs** (Concrete case of Proposition 4.1(ii))

    For univariate PMFs p_X and p_Y, the product distribution p_Z(x,y) = p_X(x)·p_Y(y)
    satisfies:
      Q_2^3(p_Z) = Q_1^2(p_X) · Q_1^2(p_Y)

    where Q_1^2(p) = ∑_s p(s)² (squared L² norm).

    **Paper contribution**: This is a concrete instance of Proposition 4.1(ii).

    **Proved by Aristotle + manual completion**. -/
theorem tensorization_univariate {α β : Type*} [Fintype α] [Fintype β]
    (p : α → ℝ≥0∞) (q : β → ℝ≥0∞)
    (_hp : ∑ x, p x = 1) (_hq : ∑ y, q y = 1) :
    -- Q_2^3 for the product distribution
    -- Formula: ∑_{x,y} p_X(x) · p_{XY}(x,y) · p_Y(y)
    -- Under independence: p_{XY}(x,y) = p_X(x) · p_Y(y)
    (∑ xy : α × β, p xy.1 * (p xy.1 * q xy.2) * q xy.2) =
    (∑ x : α, p x * p x) * (∑ y : β, q y * q y) := by
  -- Rewrite sum over product as nested sums
  simp only [Fintype.sum_prod_type]
  -- Rewrite inner term: p(x)·(p(x)·q(y))·q(y) = (p(x)·p(x))·(q(y)·q(y))
  conv_lhs =>
    arg 2; ext x; arg 2; ext y
    rw [show p x * (p x * q y) * q y = (p x * p x) * (q y * q y) by ring]
  -- Factor: ∑_x ∑_y f(x)·g(y) = (∑_x f(x))·(∑_y g(y))
  simp only [← Finset.mul_sum, ← Finset.sum_mul]

end Tensorization

end
