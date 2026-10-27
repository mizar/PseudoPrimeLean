/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.WeightedSobolevPointEvaluation
public import PseudoPrime.Analysis.ExponentialMeanSquareBounds

/-! # Point bounds for actual finite exponential sums -/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- A purely imaginary exponential has unit norm for all real frequency and displacement.
Evaluate the real part of its exponent to bound finite sums. -/
theorem norm_phase (γ v : ℝ) : ‖Complex.exp (Complex.I * γ * v)‖ = 1 := by
  rw [Complex.norm_exp]
  simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero, Real.exp_zero]

/-- Every finite exponential sum is uniformly bounded by the sum of its coefficient norms.
Apply the triangle inequality and the unit norm of each phase for boundary decay. -/
theorem norm_exponentialSum_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) (v : ℝ) :
    ‖exponentialSum s γ a v‖ ≤ ∑ j ∈ s, ‖a j‖ := by
  calc
    _ ≤ ∑ j ∈ s, ‖a j * Complex.exp (Complex.I * γ j * v)‖ := norm_sum_le s _
    _ = _ := Finset.sum_congr rfl (fun j hj ↦ by rw [norm_mul, norm_phase, mul_one])

/-- The real-displacement derivative of a phase is its frequency times I times the phase.
Differentiate the linear imaginary exponent and regroup the scalar factors. -/
theorem hasDerivAt_phase (γ v : ℝ) :
    HasDerivAt (fun w : ℝ ↦ Complex.exp (Complex.I * γ * w))
      (Complex.I * γ * Complex.exp (Complex.I * γ * v)) v := by
  have h := (((hasDerivAt_id v).ofReal_comp).const_mul (Complex.I * γ)).cexp
  convert h using 1
  · simp only [id_eq]
  · simp only [id_eq, Complex.ofReal_one, mul_one]
    ring

/-- The derivative of a finite exponential sum is the finite sum with coefficients I gamma a.
Differentiate termwise and regroup factors; the derivative is an actual integrable finite sum. -/
theorem hasDerivAt_exponentialSum {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) (v : ℝ) :
    HasDerivAt (exponentialSum s γ a) (exponentialSum s γ (fun j ↦ Complex.I * γ j * a j) v) v := by
  apply
    HasDerivAt.congr_deriv
      (HasDerivAt.fun_sum (fun j hj ↦ (hasDerivAt_phase (γ j) v).const_mul (a j)))
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- For every finite exponential sum, its value at zero is bounded by E plus sqrt(E E').
Supply the proved continuity, boundedness, derivative formula and both energy integrabilities.
No analytic hypotheses are left beyond finite real frequencies and complex coefficients. -/
theorem exponentialSum_norm_zero_sq_le {ι : Type*} (s : Finset ι) (γ : ι → ℝ) (a : ι → ℂ) :
    ‖exponentialSum s γ a 0‖ ^ 2 ≤
      energy (exponentialSum s γ a) +
        Real.sqrt (energy (exponentialSum s γ a)) *
          Real.sqrt (energy (exponentialSum s γ (fun j ↦ Complex.I * γ j * a j))) := by
  exact
    norm_zero_sq_le_energy (continuous_exponentialSum s γ a)
      (continuous_exponentialSum s γ (fun j ↦ Complex.I * γ j * a j))
      (hasDerivAt_exponentialSum s γ a) (integrable_energy_exponentialSum s γ a)
      (integrable_energy_exponentialSum s γ (fun j ↦ Complex.I * γ j * a j))
      (norm_exponentialSum_le s γ a)

end PseudoPrime.Analysis.ExponentialMeanSquare
