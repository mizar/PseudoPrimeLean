/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteZeroMass
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorCentralBounds

/-! # Uniform alpha-18 triangular archimedean remainder

Shift the gamma integral to the imaginary axis and certify an explicit constant
independent of the positive scale. This avoids growth from the original right line.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- On Re s=1/2, every character gamma logarithmic derivative has norm
at most 11+log(4+abs(Im s))/2. Use the logarithmic strip estimate outside
height one and the numerical central estimate inside.
This is compatible with the triangular kernel's quadratic central decay. -/
theorem triangular_gamma_central_log_bound {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : s.re = 1 / 2) : ‖logDeriv χ.gammaFactor s‖ ≤ 11 + Real.log (4 + |s.im|) / 2 := by
  have hlog : 0 ≤ Real.log (4 + |s.im|) := Real.log_nonneg (by linarith only [abs_nonneg s.im])
  by_cases ht : 1 ≤ |s.im|
  · have hsr : |s.re| ≤ 2 := by
      rw [hs]; norm_num only
    have hb := AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_gammaFactor_le_log χ hsr ht
    have hnlog : ‖Complex.log (Real.pi : ℂ)‖ ≤ 3 := by
      rw [← Complex.ofReal_log Real.pi_pos.le, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi))]
      have hp := Real.log_le_sub_one_of_pos Real.pi_pos
      linarith only [hp, Real.pi_lt_four]
    linarith only [hb, hnlog, Real.pi_lt_four,
      AnalyticNumberTheory.Gamma.digammaLogErrorBound_le_eight]
  · have hb :=
      AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_gammaFactor_central_le_linear χ hs
    have ht1 : |s.im| ≤ 1 := (lt_of_not_ge ht).le
    linarith only [hb, ht1, hlog]

/-- The alpha-18 imaginary-axis kernel has norm at most 1300/(1+t^2).
The sinc square is at most 1296, while its product with t^2 is at most four.
Add these two bounds and divide by 1+t^2.
This supplies an explicit central decay constant without compactness input. -/
theorem triangular18_central_decay (t : ℝ) :
    ‖Analysis.triangularMellinFunction 18 (Complex.I * t)‖ ≤ (1300 : ℝ) / (1 + t ^ 2) := by
  have hn : ‖Analysis.triangularMellinFunction 18 (Complex.I * t)‖ ≤ (1296 : ℝ) := by
    rw [Analysis.norm_triangularMellinFunction_imaginary (by norm_num only : (18 : ℝ) ≠ 0)]
    have hs := Real.abs_sinc_le_one (18 * t)
    have ha := sq_abs (Real.sinc (18 * t))
    nlinarith only [hs, ha, abs_nonneg (Real.sinc (18 * t))]
  have ht : ‖Analysis.triangularMellinFunction 18 (Complex.I * t)‖ * t ^ 2 ≤ 4 := by
    by_cases ht0 : t = 0
    · rw [ht0, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero]
      norm_num only
    · have h18 : (18 : ℝ) * t ≠ 0 := mul_ne_zero (by norm_num only) ht0
      have he : (2 * 18 * Real.sinc (18 * t)) * t = 2 * Real.sin (18 * t) := by
        rw [Real.sinc_of_ne_zero h18]
        calc
          _ = 2 * ((Real.sin (18 * t) / (18 * t)) * (18 * t)) := by ring
          _ = _ := by rw [div_mul_cancel₀ _ h18]
      rw [Analysis.norm_triangularMellinFunction_imaginary (by norm_num only : (18 : ℝ) ≠ 0), ←
        mul_pow, he]
      have hs := Real.abs_sin_le_one (18 * t)
      have ha := sq_abs (Real.sin (18 * t))
      nlinarith only [hs, ha, abs_nonneg (Real.sin (18 * t))]
  apply (le_div_iff₀ (by linarith only [sq_nonneg t] : 0 < 1 + t ^ 2)).mpr
  nlinarith only [hn, ht]

/-- For every character and positive scale, the raw central gamma integral
for alpha=18 has norm at most 314600. Its phase has unit norm, the gamma
logarithmic growth coefficient is eleven and central kernel decay is 1300.
Combine these with the common logarithmic integral at most twenty-two.
This is the scale-uniform gamma integral used in the contour remainder. -/
theorem triangular18_central_gammaIntegral_norm_le {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 0 < x) :
    ‖∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            (Analysis.triangularMellinFunction 18 (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))‖ ≤
      (314600 : ℝ) := by
  have hb :
    ‖∫ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            (Analysis.triangularMellinFunction 18 (Complex.I * t) * (x : ℂ) ^ (Complex.I * t))‖ ≤
      (11 * 1300 : ℝ) * (∫ t : ℝ, (Real.log (4 + |t|) + 1) / (1 + t ^ 2)) := by
    apply norm_logWeighted_product_integral_le (by norm_num only : (0 : ℝ) ≤ 11)
    · intro t
      have hr : (Complex.I * (t : ℂ) + 1 / 2).re = (1 / 2 : ℝ) := by
        simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
          Complex.ofReal_im, zero_mul, mul_zero, sub_zero, Complex.div_ofNat_re, Complex.one_re,
          zero_add]
      have hγ := triangular_gamma_central_log_bound χ hr
      simp only [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
        Complex.ofReal_im, one_mul, zero_mul, zero_add, Complex.div_ofNat_im, Complex.one_im,
        zero_div, add_zero] at hγ
      have hL : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
      linarith only [hγ, hL]
    · intro t
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
      simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
      exact triangular18_central_decay t
  have hJ :=
    mul_le_mul_of_nonneg_left Analysis.logarithmic_inverseSquare_integral_le_twenty_two
      (by norm_num only : (0 : ℝ) ≤ 11 * 1300)
  norm_num only at hb hJ
  exact hb.trans hJ

/-- For every character, scale x>=1 and line 0<=b<=5/8, the normalized
alpha-18 gamma integral has norm at most 55000. Shift to the central line
using the proved contour identity and normalize the explicit raw bound.
This removes the right-line growth factor from the triangular explicit remainder. -/
theorem triangular18_gammaIntegral_norm_le_uniform {q : ℕ} (χ : DirichletCharacter ℂ q) {b x : ℝ}
    (hb : 0 ≤ b) (hbK : b ≤ 5 / 8) (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              (K.function ((b : ℂ) + Complex.I * t) * (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))‖ ≤
      (55000 : ℝ) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hb' : b ≤ 1 / 2 + K.delta := by
    change b ≤ (1 / 2 + 1 / 8 : ℝ)
    linarith only [hbK]
  have he :=
    MellinKernel.gammaIntegral_eq_central K χ hb hb' (by linarith only [hbK] : b ≤ 3 / 2) hx
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * _‖ ≤ _
  rw [he]
  have hraw := triangular18_central_gammaIntegral_norm_le χ (zero_lt_one.trans_le hx)
  have hn := norm_mellinNormalization_mul_le_sixth hraw
  have hnum : (314600 : ℝ) / 6 ≤ 55000 := by norm_num only
  exact hn.trans hnum

end PseudoPrime.LLS.PaperStatements
