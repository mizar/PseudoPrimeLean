/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularLogarithmicIntegrals
public import PseudoPrime.Analysis.LogarithmicIntegralNumerics

/-! # Numerical alpha-18 integral bounds

The common logarithmic integral is at most twenty-two.
Mellin normalization gives explicit conductor-free remainder constants.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The unnormalized alpha-18 reflected inverse-character integral has norm
at most 6248000000000000 for a nonprincipal inverse. Combine the fixed-decay
bound with the common logarithmic integral at most twenty-two.
This supplies a numerical reflected remainder independent of the modulus. -/
theorem triangular18_reflectedIntegral_norm_le_numeric {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hinv : χ⁻¹ ≠ 1) :
    ‖∫ t : ℝ,
          logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
            Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      (6248000000000000 : ℝ) := by
  have hb := triangular18_reflectedIntegral_norm_le_fixed_decay hinv
  have hJ :=
    mul_le_mul_of_nonneg_left Analysis.logarithmic_inverseSquare_integral_le_twenty_two
      (by norm_num only : (0 : ℝ) ≤ 284 * 1000000000000)
  norm_num only at hb hJ
  simpa only [neg_div] using hb.trans hJ

/-- Every alpha-18 gamma-factor integral has unnormalized norm at most
264000000000000. Combine the logarithmic gamma bound and fixed kernel decay
with the common integral at most twenty-two.
This supplies the numerical gamma remainder for the zero-mass formula. -/
theorem triangular18_gammaIntegral_norm_le_numeric {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖∫ t : ℝ,
          logDeriv χ.gammaFactor (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction 18 (((9 / 16 : ℝ) : ℂ) + Complex.I * t)‖ ≤
      (264000000000000 : ℝ) := by
  have hb := triangular18_gammaIntegral_norm_le_fixed_decay χ
  have hJ :=
    mul_le_mul_of_nonneg_left Analysis.logarithmic_inverseSquare_integral_le_twenty_two
      (by norm_num only : (0 : ℝ) ≤ 12 * 1000000000000)
  norm_num only at hb hJ
  exact hb.trans hJ

/-- If a complex value has norm at most C, Mellin normalization by
1/(2*pi) gives norm at most C/6. Use pi>3 and multiply the two nonnegative
norm bounds. This converts the raw triangular integral budgets. -/
theorem norm_mellinNormalization_mul_le_sixth {z : ℂ} {C : ℝ} (hz : ‖z‖ ≤ C) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * z‖ ≤ C / 6 := by
  have hN : ‖((1 / (2 * Real.pi) : ℝ) : ℂ)‖ ≤ (1 / 6 : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg zero_le_one (mul_nonneg (by norm_num only) Real.pi_pos.le))]
    exact
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 6)
        (by linarith only [Real.pi_gt_three] : (6 : ℝ) ≤ 2 * Real.pi)
  rw [norm_mul]
  have h := mul_le_mul hN hz (norm_nonneg z) (by norm_num only : (0 : ℝ) ≤ 1 / 6)
  simpa only [one_div_mul_eq_div] using h

/-- The normalized alpha-18 reflected integral is at most 1100000000000000
for a nonprincipal inverse character. Apply the raw numerical estimate and
the normalization factor at most one sixth, with a rational safety margin.
This is the left remainder constant in the conductor-free zero formula. -/
theorem triangular18_normalized_reflectedIntegral_norm_le {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hinv : χ⁻¹ ≠ 1) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ⁻¹.completedLFunction (((17 / 16 : ℝ) : ℂ) - Complex.I * t) *
              Analysis.triangularMellinFunction 18 (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))‖ ≤
      (1100000000000000 : ℝ) := by
  have hb :=
    norm_mellinNormalization_mul_le_sixth (triangular18_reflectedIntegral_norm_le_numeric hinv)
  have hnum : (6248000000000000 : ℝ) / 6 ≤ 1100000000000000 := by norm_num only
  exact hb.trans hnum

/-- The normalized alpha-18 gamma integral is at most 50000000000000 for
every character. Apply the raw numerical estimate and the normalization factor
at most one sixth, with a rational safety margin.
This is the gamma remainder constant in the conductor-free zero formula. -/
theorem triangular18_normalized_gammaIntegral_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              Analysis.triangularMellinFunction 18 (((9 / 16 : ℝ) : ℂ) + Complex.I * t))‖ ≤
      (50000000000000 : ℝ) := by
  have hb := norm_mellinNormalization_mul_le_sixth (triangular18_gammaIntegral_norm_le_numeric χ)
  have hnum : (264000000000000 : ℝ) / 6 ≤ 50000000000000 := by norm_num only
  exact hb.trans hnum

/-- For any positive triangular parameter, function F and real scale x,
the designated weighted residue at -1/2 is zero. The regularized entire kernel
has factor s+1/2, which vanishes there. No character or GRH hypothesis is needed.
This removes the pole term from the triangular absolute zero-mass formula. -/
theorem triangular_weightedResidue_pole_eq_zero {a : ℝ} (ha : 0 < a) (F : ℂ → ℂ) (x : ℝ) :
    MellinKernel.weightedResidue (triangularMellinKernel ha) F x (-1 / 2) = 0 := by
  simp only [MellinKernel.weightedResidue, ite_true]
  change
    -logDeriv F (-1 / 2) *
        (((-1 / 2 : ℂ) + 1 / 2) * Analysis.triangularMellinFunction a (-1 / 2) *
          (x : ℂ) ^ (-1 / 2 : ℂ)) =
      0
  rw [show (-1 / 2 : ℂ) + 1 / 2 = 0 by ring, zero_mul, zero_mul, mul_zero]

end PseudoPrime.LLS.PaperStatements
