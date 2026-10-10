/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.AbelSummation
public import PseudoPrime.Analysis.LogReciprocalKernel
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeSumBounds

/-! Partial summation for the logarithmically weighted Mangoldt sum. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Convert the closed-interval weighted sum to the positive-index Mangoldt sum.
The term at zero vanishes with total division; commuting the factors identifies the weights.
This aligns Abel summation with the cutoff convention of the second-order estimate. -/
private theorem mangoldtLogSum_eq_sum_weight (x : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊x⌋₊, (1 / ((n : ℝ) * Real.log n)) * ArithmeticFunction.vonMangoldt n) =
      ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n) := by
  rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le ⌊x⌋₊)]
  simp only [Nat.cast_zero, zero_mul, div_zero, add_zero]
  apply Finset.sum_congr rfl
  intro n _
  rw [one_div, div_eq_mul_inv, mul_comm]

/-- Replace the derivative weight in the psi integral by its explicit negative kernel.
Every point of `(2, x]` is greater than one, so the derivative formula applies.
This determines the positive sign of the kernel in the partial-summation identity. -/
private theorem integral_deriv_weight_mul_psi (x : ℝ) :
    (∫ t in Set.Ioc 2 x, deriv (fun t : ℝ ↦ 1 / (t * Real.log t)) t * Chebyshev.psi t) =
      -(∫ t in Set.Ioc 2 x, Chebyshev.psi t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2))) := by
  rw [← MeasureTheory.integral_neg]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [(Analysis.hasDerivAt_inv_mul_log ((by norm_num only : (1 : ℝ) < 2).trans ht.1)).deriv,
    neg_mul, mul_comm]

/-- At every real cutoff, the logarithmically weighted Mangoldt sum equals
`psi x / (x * log x)` plus the integral of psi against the reciprocal logarithmic kernel.
Apply Abel summation directly at the real cutoff, using the vanishing coefficients at zero
and one. This is the exact finite-sum interface for extracting the Mertens constant and error. -/
theorem mangoldtLogSum_eq_psi_integral (x : ℝ) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) =
      Chebyshev.psi x / (x * Real.log x) +
        ∫ t in Set.Ioc 2 x, Chebyshev.psi t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  have h :=
    sum_mul_eq_sub_integral_mul₁ (fun n ↦ ArithmeticFunction.vonMangoldt n)
      ArithmeticFunction.map_zero ArithmeticFunction.vonMangoldt_apply_one x
      (fun t ht ↦
        (Analysis.hasDerivAt_inv_mul_log
            ((by norm_num only : (1 : ℝ) < 2).trans_le ht.1)).differentiableAt)
      (Analysis.integrableOn_deriv_inv_mul_log_Icc (by norm_num only : (1 : ℝ) < 2))
  simp only [← Chebyshev.psi_eq_sum_Icc] at h
  rw [mangoldtLogSum_eq_sum_weight x, integral_deriv_weight_mul_psi x, sub_neg_eq_add] at h
  simpa only [div_eq_mul_inv, mul_comm, one_mul] using h

/-- The truncated Mangoldt majorant is exactly the psi integral against the positive kernel.
Subtract the boundary term from the partial-summation identity. This connects the
finite-sum majorant used in L-value bounds to the integral representation. -/
theorem truncatedMangoldtMajorant_eq_psi_integral (x : ℝ) :
    truncatedMangoldtMajorant x =
      ∫ t in Set.Ioc 2 x, Chebyshev.psi t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  rw [truncatedMangoldtMajorant_eq_log_sum_sub_psi, mangoldtLogSum_eq_psi_integral]
  ring

/-- The psi-weighted logarithmic kernel is integrable on every closed interval `[2, x]`.
The kernel is continuous and the Mangoldt partial sum is a finite-step function on this
interval. Use the integrability lemma from Abel summation and identify the partial sum with psi.
This permits splitting its linear main term from the error integral. -/
theorem integrableOn_psi_mul_logReciprocalKernel (x : ℝ) :
    MeasureTheory.IntegrableOn
      (fun t ↦ Chebyshev.psi t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      (Set.Icc 2 x) := by
  have hs : Set.Icc (2 : ℝ) x ⊆ Set.Ioi 1 := fun _ ht ↦
    (by norm_num only : (1 : ℝ) < 2).trans_le ht.1
  have hint :=
    (Analysis.continuousOn_logReciprocalKernel.mono hs).integrableOn_Icc (μ := MeasureTheory.volume)
  have h :=
    integrableOn_mul_sum_Icc (fun n ↦ ArithmeticFunction.vonMangoldt n) (m := 0)
      (by norm_num only : (0 : ℝ) ≤ 2) hint
  simpa only [← Chebyshev.psi_eq_sum_Icc, mul_comm] using h

/-- At a positive cutoff, the psi boundary term splits into `1 / log x` and its error.
Expand the numerator difference and cancel the nonzero cutoff. This isolates the main term
when subtracting `log log x` from the weighted Mangoldt sum. -/
private theorem psi_log_boundary_eq {x : ℝ} (hx : 0 < x) :
    Chebyshev.psi x / (x * Real.log x) =
      1 / Real.log x + (Chebyshev.psi x - x) / (x * Real.log x) := by
  rw [sub_div, div_mul_cancel_left₀ hx.ne', one_div]
  ring

/-- For `x ≥ 2`, subtracting `log log x` isolates the psi error boundary and integral.
Split the integrable psi kernel into its linear main term and remainder. Evaluate the
main integral explicitly and cancel the cutoff's reciprocal logarithm. This exact
identity is the finite-cutoff starting point for the second-order Mertens error. -/
theorem mangoldtLogSum_sub_logLog_eq_psi_error {x : ℝ} (hx : 2 ≤ x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n / ((n : ℝ) * Real.log n)) -
        Real.log (Real.log x) =
      (1 / Real.log 2 - Real.log (Real.log 2)) + (Chebyshev.psi x - x) / (x * Real.log x) +
        ∫ t in Set.Ioc 2 x,
          (Chebyshev.psi t - t) * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)) := by
  have hp := integrableOn_psi_mul_logReciprocalKernel x
  have hmain := Analysis.integral_mul_logReciprocalKernel (by norm_num only : (1 : ℝ) < 2) hx
  have hs : Set.Icc (2 : ℝ) x ⊆ Set.Ioi 1 := fun _ ht ↦
    (by norm_num only : (1 : ℝ) < 2).trans_le ht.1
  have ht :
    MeasureTheory.IntegrableOn (fun t ↦ t * ((Real.log t + 1) / (t ^ 2 * (Real.log t) ^ 2)))
      (Set.Icc 2 x) :=
    (continuousOn_id.mul (Analysis.continuousOn_logReciprocalKernel.mono hs)).integrableOn_Icc (μ :=
      MeasureTheory.volume)
  have hi :=
    MeasureTheory.integral_sub (hp.mono_set Set.Ioc_subset_Icc_self)
      (ht.mono_set Set.Ioc_subset_Icc_self)
  simp only [← sub_mul] at hi
  rw [mangoldtLogSum_eq_psi_integral, hi, hmain]
  have hb :
    Chebyshev.psi x / (x * Real.log x) =
      1 / Real.log x + (Chebyshev.psi x - x) / (x * Real.log x) := by
    rw [sub_div, div_mul_cancel_left₀ ((by norm_num only : (0 : ℝ) < 2).trans_le hx).ne', one_div]
    ring
  rw [hb]
  ring

end PseudoPrime.AnalyticNumberTheory.Arithmetic
