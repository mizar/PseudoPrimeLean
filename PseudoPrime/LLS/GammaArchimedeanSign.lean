/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaSpecifiedBaseSeries
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Nonpositive Gamma archimedean contribution at scales at least two -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At either exact parity base and scale at least two, the signed real scalar
archimedean series is nonpositive. Special digamma values reduce the full upper
bound to elementary logarithmic constants, and the initial integral is
nonnegative. This is the scalar sign gate for the actual Gamma integral. -/
theorem gamma_scalar_archimedean_series_nonpos_of_exact_parity {b x : ℝ}
    (hb : b = 1 / 4 ∨ b = 3 / 4) (hx : 2 ≤ x) :
    ((-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2) * (Real.sqrt x⁻¹ * Real.exp (-x⁻¹)) +
        (1 / 2 : ℝ) *
          (∑' n : ℕ,
            (Real.sqrt x⁻¹ * Real.exp (-x⁻¹) / (b + n) -
              ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (b + n) x r)) ≤
      0 := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx
  have hz0 : 0 ≤ x⁻¹ := (inv_pos.mpr hx0).le
  have hz : x⁻¹ ≤ (1 / 2 : ℝ) := by
    simpa only [one_div] using inv_le_inv₀ hx0 (by norm_num only : (0 : ℝ) < 2) |>.mpr hx
  have hl0 : 0 ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hl1 : Real.log 2 ≤ 1 := by linarith only [Real.log_two_lt_d9]
  have hlhalf : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith only [Real.log_two_gt_d9]
  have hbase :=
    gamma_real_baseline_le_neg_three_quarters (by norm_num only : (0 : ℝ) < 1) (le_refl (1 : ℝ))
  norm_num only [Complex.ofReal_one, Complex.digamma_one, Complex.neg_re,
    Complex.ofReal_re] at hbase
  have heven : (Complex.digamma (1 : ℂ) - Complex.digamma (1 / 2 : ℂ)).re = 2 * Real.log 2 := by
    have h :=
      tsum_real_reciprocal_difference (by norm_num only : (0 : ℝ) < 1)
        (by norm_num only : (0 : ℝ) < 1 / 2)
    norm_num only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat] at h
    rw [← h, tsum_even_gamma_reciprocal_error]
  have hhalf :
    (Complex.digamma (1 / 2 : ℂ)).re = -Real.eulerMascheroniConstant - 2 * Real.log 2 := by
    rw [Complex.sub_re, Complex.digamma_one, Complex.neg_re, Complex.ofReal_re] at heven
    linarith only [heven]
  have hthreehalf :
    (Complex.digamma (3 / 2 : ℂ)).re = 2 - Real.eulerMascheroniConstant - 2 * Real.log 2 := by
    have h := re_digamma_real_add_one (by norm_num only : (0 : ℝ) < 1 / 2)
    norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, hhalf] at h
    linarith only [h]
  have hK : 0 ≤ Real.sqrt x⁻¹ * Real.exp (-x⁻¹) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.exp_pos _).le
  rcases hb with rfl | rfl
  · have h := gamma_scalar_archimedean_series_le (by norm_num only : (0 : ℝ) < 1 / 4) hx0
    norm_num only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.digamma_one, Complex.neg_re, Complex.ofReal_re, Complex.sub_re, hhalf] at h
    have hc : (-Real.log Real.pi - Real.eulerMascheroniConstant) / 2 + x⁻¹ * Real.log 2 ≤ 0 := by
      have hm := mul_le_mul_of_nonneg_right hz hl0
      nlinarith only [hbase, hm, hl1]
    have hi : 0 ≤ ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (1 / 4) x r :=
      MeasureTheory.integral_nonneg (fun r ↦ gammaResolventScalarDensity_nonneg _ x r)
    have hm := mul_nonpos_of_nonneg_of_nonpos hK hc
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
    nlinarith only [h, hi, hm]
  · have h := gamma_scalar_archimedean_series_le (by norm_num only : (0 : ℝ) < 3 / 4) hx0
    norm_num only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat,
      Complex.digamma_one, Complex.neg_re, Complex.ofReal_re, Complex.sub_re, hthreehalf] at h
    have hc :
      (-Real.log Real.pi - Real.eulerMascheroniConstant) / 2 + (1 - Real.log 2) * (1 + x⁻¹) ≤
        0 := by
      have hA : 1 - Real.log 2 ≤ (1 / 2 : ℝ) := by linarith only [hlhalf]
      have hB : 1 + x⁻¹ ≤ (3 / 2 : ℝ) := by linarith only [hz]
      have hm :=
        mul_le_mul hA hB (by linarith only [hz0] : (0 : ℝ) ≤ 1 + x⁻¹)
          (by norm_num only : (0 : ℝ) ≤ 1 / 2)
      nlinarith only [hbase, hm]
    have hi : 0 ≤ ∫ r : ℝ in Set.Ioi 0, gammaResolventScalarDensity (3 / 4) x r :=
      MeasureTheory.integral_nonneg (fun r ↦ gammaResolventScalarDensity_nonneg _ x r)
    have hm := mul_nonpos_of_nonneg_of_nonpos hK hc
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
    nlinarith only [h, hi, hm]

/-- For every complex Dirichlet character and every real scale at least two,
the normalized actual central Gamma archimedean integral has nonpositive real
part. Exact parity, the certified scalar inversion and the signed series bound
prove the claim without GRH. This removes a positive archimedean cost from
subsequent one-sided explicit-formula estimates. -/
theorem gamma_central_archimedean_integral_re_nonpos {q : ℕ} (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 2 ≤ x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * gammaCentralMellinWeight x t)).re ≤
      0 := by
  obtain ⟨b, hb, h⟩ := gamma_central_archimedean_integral_re_eq_scalar_exact_parity χ
  rw [h x (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)]
  exact gamma_scalar_archimedean_series_nonpos_of_exact_parity hb hx

/-- At scale at least two, the actual Gamma integral on any admissible right
line has nonpositive real part. The proved contour-independence identity
transfers the central sign result to the line used by the completed explicit
formula, so no positive archimedean allowance is needed in a real upper bound. -/
theorem gamma_right_integral_re_nonpos {q : ℕ} (χ : DirichletCharacter ℂ q) {b x : ℝ} (hb : 0 ≤ b)
    (hbK : b ≤ 1 / 2 + gammaMellinKernel.delta) (hb2 : b ≤ 3 / 2) (hx : 2 ≤ x) :
    (((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            logDeriv χ.gammaFactor (((b : ℂ) + Complex.I * t) + 1 / 2) *
              (gammaMellinKernel.function ((b : ℂ) + Complex.I * t) *
                (x : ℂ) ^ ((b : ℂ) + Complex.I * t)))).re ≤
      0 := by
  rw [MellinKernel.gammaIntegral_eq_central gammaMellinKernel χ hb hbK hb2
      (le_trans (by norm_num only : (1 : ℝ) ≤ 2) hx)]
  exact gamma_central_archimedean_integral_re_nonpos χ hx

end PseudoPrime.LLS.PaperStatements
