/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularKernel
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Explicit alpha-18 triangular kernel numerical margins

Identify the actual mass and cutoff values and certify a uniform large-index gap.
Finite-conductor zero sums and explicit-formula errors require separate estimates.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The alpha-18 half-point value is less than 300000000. Use the certified
exp(1)<68/25 bound, the eighteenth power, and positivity of exp(-9).
This supplies the pole contribution budget for all large subgroup indices. -/
theorem triangular18_half_value_lt : 4 * (Real.exp 9 - Real.exp (-9)) ^ 2 < (300000000 : ℝ) := by
  have he : Real.exp 1 < (68 / 25 : ℝ) := Real.exp_one_lt_d9.trans (by norm_num only)
  have h18 : Real.exp 1 ^ 18 < (68 / 25 : ℝ) ^ 18 :=
    pow_lt_pow_left₀ he (Real.exp_pos 1).le (by decide)
  have hnum : 4 * (68 / 25 : ℝ) ^ 18 < 300000000 := by norm_num only
  have h9 : Real.exp 9 ^ 2 = Real.exp 1 ^ 18 := by
    rw [pow_two, ← Real.exp_add, show (9 : ℝ) + 9 = 18 by norm_num only]
    simpa only [Nat.cast_ofNat, mul_one] using Real.exp_nat_mul 1 18
  have hpos := Real.exp_pos (-9)
  have hlt : Real.exp (-9) < Real.exp 9 := Real.exp_lt_exp.mpr (by norm_num only)
  have hs : (Real.exp 9 - Real.exp (-9)) ^ 2 < Real.exp 9 ^ 2 := by nlinarith only [hpos, hlt]
  rw [h9] at hs
  nlinarith only [hs, h18, hnum]

/-- For real index h at least 10^9, cutoff mass at least 68 and half-point
value less than 300000000 give normalized denominator greater than 67.7.
Clear the positive denominator and compare the explicit linear budgets.
This is the uniform large-index numerical transfer. -/
theorem triangular18_normalized_denominator_gt {h I κ : ℝ} (hh : 1000000000 ≤ h) (hI : 68 ≤ I)
    (hκ : κ < 300000000) : (677 / 10 : ℝ) < (h * I - κ) / (h - 1) := by
  have hd : 0 < h - 1 := by linarith only [hh]
  apply (lt_div_iff₀ hd).mpr
  have hm : h * 68 ≤ h * I := mul_le_mul_of_nonneg_left hI (le_trans (by norm_num only) hh)
  linarith only [hh, hκ, hm]

/-- Denominator greater than 67.7 leaves a positive coefficient-0.283 gap
above mass 36 plus error 1/100. Compare the exact rational endpoint first.
This is the final squared numerical margin for the alpha-18 branch. -/
theorem triangular18_coefficient_gap {D : ℝ} (hD : (677 / 10 : ℝ) < D) :
    (36 + 1 / 100 : ℝ) ^ 2 < (283 / 1000 : ℝ) * D ^ 2 := by
  have hnum : (36 + 1 / 100 : ℝ) ^ 2 < (283 / 1000 : ℝ) * (677 / 10 : ℝ) ^ 2 := by norm_num only
  nlinarith only [hD, hnum]

/-- The admissible alpha-18 triangular kernel has exact mass 36.
Specialize the imaginary-axis mass identity; this identifies the actual kernel
mass used in the large-index comparison. -/
theorem triangular18_mass :
    (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).mass = 36 := by
  have hm :=
    triangular_mass_of_function (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18))
      (by norm_num only : (0 : ℝ) < 18) rfl
  norm_num only at hm
  exact hm

/-- The alpha-18 triangular profile has truncated weighted integral
68+4*exp(-18). Specialize the proved interval-integral identity.
This identifies the actual cutoff mass, including its lower support endpoint. -/
theorem triangular18_cutoff_integral :
    (∫ u in (0 : ℝ)..1, triangularKernelProfile 18 u / Real.sqrt u) = 68 + 4 * Real.exp (-18) := by
  have hi := integral_triangularKernelProfile (by norm_num only : (0 : ℝ) ≤ 18)
  norm_num only at hi
  exact hi

/-- At s=1/2 the alpha-18 triangular Mellin function has real value
4*(exp(9)-exp(-9))^2. Use the nonsingular exponential formula and real casts.
This connects the analytic half-point term to the numerical budget. -/
theorem triangular18_function_half :
    (Analysis.triangularMellinFunction 18 (1 / 2)).re = 4 * (Real.exp 9 - Real.exp (-9)) ^ 2 := by
  rw [Analysis.triangularMellinFunction_of_ne_zero (by norm_num only : (18 : ℝ) ≠ 0)
      (by norm_num only : (1 / 2 : ℂ) ≠ 0)]
  norm_num only [Complex.ofReal_ofNat]
  rw [← Complex.ofReal_ofNat 9, ← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Complex.ofReal_exp, ←
    Complex.ofReal_sub]
  have hhalf : (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) := by
    simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  rw [hhalf, ← Complex.ofReal_div, ← Complex.ofReal_pow, Complex.ofReal_re]
  ring

/-- For real subgroup index h, normalize the actual alpha-18 cutoff mass and
half-point value by h-1. The definition is used only with h at least 10^9,
where the denominator is positive. It is the large-index comparison denominator. -/
noncomputable def triangular18NormalizedDenominator (h : ℝ) : ℝ :=
  (h * (∫ u in (0 : ℝ)..1, triangularKernelProfile 18 u / Real.sqrt u) -
      ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).function (1 / 2)).re) /
    (h - 1)

/-- For the actual alpha-18 kernel and cutoff profile, every real index
h at least 10^9 has normalized denominator greater than 67.7. Substitute the
proved integral and half-point identities into the uniform numerical transfer.
This removes separate mass and half-point assumptions from the comparison. -/
theorem triangular18_actual_denominator_gt {h : ℝ} (hh : 1000000000 ≤ h) :
    (677 / 10 : ℝ) < triangular18NormalizedDenominator h := by
  change
    (677 / 10 : ℝ) <
      (h * (∫ u in (0 : ℝ)..1, triangularKernelProfile 18 u / Real.sqrt u) -
          (Analysis.triangularMellinFunction 18 (1 / 2)).re) /
        (h - 1)
  rw [triangular18_cutoff_integral, triangular18_function_half]
  have hI : (68 : ℝ) ≤ 68 + 4 * Real.exp (-18) :=
    le_add_of_nonneg_right (mul_nonneg (by norm_num only) (Real.exp_pos _).le)
  exact triangular18_normalized_denominator_gt hh hI triangular18_half_value_lt

/-- For every real index h at least 10^9, the actual alpha-18 kernel mass
plus error 1/100 has square strictly below coefficient 0.283 times the squared
comparison denominator. Substitute the exact mass and proved denominator bound.
This is a numerical margin, not a finite-conductor zero-sum estimate. -/
theorem triangular18_actual_coefficient_gap {h : ℝ} (hh : 1000000000 ≤ h) :
    ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).mass + 1 / 100) ^ 2 <
      (283 / 1000 : ℝ) * (triangular18NormalizedDenominator h) ^ 2 := by
  rw [triangular18_mass]
  exact triangular18_coefficient_gap (triangular18_actual_denominator_gt hh)

/-- The actual alpha-18 mass also allows relative zero-sum error 1/10000
and normalized additive error 1/100 for every real index h at least 10^9.
Compare the exact rational endpoint with the proved denominator bound.
This certifies the alternative relative-error budget without asserting its start. -/
theorem triangular18_actual_relative_error_gap {h : ℝ} (hh : 1000000000 ≤ h) :
    (((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).mass * (1 + 1 / 10000) + 1 / 100) :
          ℝ) ^
        2 <
      (283 / 1000 : ℝ) * (triangular18NormalizedDenominator h) ^ 2 := by
  rw [triangular18_mass]
  have hD := triangular18_actual_denominator_gt hh
  have hnum : (36 * (1 + 1 / 10000) + 1 / 100 : ℝ) ^ 2 < (283 / 1000 : ℝ) * (677 / 10 : ℝ) ^ 2 := by
    norm_num only
  nlinarith only [hD, hnum]

end PseudoPrime.LLS.PaperStatements
