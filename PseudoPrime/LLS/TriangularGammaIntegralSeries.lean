/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSignedGammaBounds
public import PseudoPrime.LLS.TriangularDigammaIntegralExchange

/-! # Complex Gamma-factor parity and central triangular integral series -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- For every Dirichlet character, choose the positive Gamma argument one quarter
or three quarters and express its central logarithmic derivative through complex digamma.
Split character parity and exclude poles using positive real parts. This supplies the
complex identity needed for the signed integral series, before taking real parts. -/
theorem gamma_central_eq_complex_digamma {q : ℕ} (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ t : ℝ,
          logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) =
            (-Complex.log Real.pi + Complex.digamma ((b : ℂ) + Complex.I * (t / 2))) / 2 := by
  rcases χ.even_or_odd with hχ | hχ
  · refine ⟨1 / 4, le_refl _, by norm_num only, ?_⟩
    intro t
    have hz : (Complex.I * (t : ℂ) + 1 / 2) / 2 = ((1 / 4 : ℝ) : ℂ) + Complex.I * (t / 2) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
      ring
    have hp : 0 < ((Complex.I * (t : ℂ) + 1 / 2) / 2).re := by
      simp only [complex_div_two_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      norm_num only [Complex.one_re]
    have he :=
      logDeriv_gammaFactor_eq_of_even_of_half_ne_neg_nat hχ
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)
    rw [he, hz]
    ring
  · refine ⟨3 / 4, by norm_num only, by norm_num only, ?_⟩
    intro t
    have hz :
      ((Complex.I * (t : ℂ) + 1 / 2) + 1) / 2 = ((3 / 4 : ℝ) : ℂ) + Complex.I * (t / 2) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
      ring
    have hp : 0 < (((Complex.I * (t : ℂ) + 1 / 2) + 1) / 2).re := by
      simp only [complex_div_two_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero]
      norm_num only [Complex.one_re]
    have he :=
      logDeriv_gammaFactor_eq_of_odd_of_half_ne_neg_nat hχ
        (fun n ↦ AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n)
    rw [he, hz]
    ring

/-- For every character, one Gamma base between one quarter and one gives the
central triangular Gamma integral as its real-axis baseline times the triangular profile
plus the convergent vertical reciprocal-difference integral series. The triangular parameter
and scale may be any positive reals. Split integrable terms and use the proved digamma
series-integral exchange. No GRH is needed. This preserves signs for subsequent pole inversion. -/
theorem triangular_central_gammaIntegral_eq_vertical_resolvent_series {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ∃ b : ℝ,
      1 / 4 ≤ b ∧
        b ≤ 1 ∧
        ∀ (a x : ℝ),
          0 < a →
            0 < x →
            ((1 / (2 * Real.pi) : ℝ) : ℂ) *
                (∫ t : ℝ,
                  logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                    (Analysis.triangularMellinFunction a (Complex.I * t) *
                      (x : ℂ) ^ (Complex.I * t))) =
              ((-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2) *
                  (triangularKernelProfile a x : ℂ) +
                (((1 / (2 * Real.pi) : ℝ) : ℂ) / 2) *
                  (∑' n : ℕ,
                    ∫ t : ℝ,
                      (1 / ((b + n : ℝ) : ℂ) - 1 / (((b + n : ℝ) : ℂ) + Complex.I * (t / 2))) *
                        Analysis.triangularMellinFunction a (Complex.I * t) *
                        (x : ℂ) ^ (Complex.I * t)) := by
  obtain ⟨b, hb, hb1, hp⟩ := gamma_central_eq_complex_digamma χ
  refine ⟨b, hb, hb1, ?_⟩
  intro a x ha hx
  let K := triangularMellinKernel ha
  let W := fun t : ℝ ↦
    Analysis.triangularMellinFunction a (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)
  let B := (-Complex.log Real.pi + Complex.digamma (b : ℂ)) / 2
  let D := fun t : ℝ ↦
    (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) * W t
  have hW : MeasureTheory.Integrable W := by
    have h :=
      MellinKernel.integrable_inverse_in_strip K (c := 0) (u := x⁻¹)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < 0; norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) (inv_pos.mpr hx)
    simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_inv, Complex.cpow_neg,
      Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] at h
    exact h
  have hG :=
    MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := x) (by norm_num only)
      (by
        change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) hx
  simp only [Complex.ofReal_zero, zero_add, mul_assoc] at hG
  have he (t : ℝ) :
    logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t = B * W t + (1 / 2 : ℂ) * D t := by
    rw [hp]
    dsimp only [B, D]
    ring
  have hD : MeasureTheory.Integrable D :=
    ((hG.sub (hW.const_mul B)).const_mul (2 : ℂ)).congr
      (MeasureTheory.ae_of_all _
        (fun t ↦ by
          change 2 * (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t - B * W t) = D t
          rw [he]
          ring))
  have hm :=
    inverseMellin_triangular ha (c := 0) (u := x⁻¹) (by norm_num only [abs_zero]) (inv_pos.mpr hx)
  unfold inverseMellin at hm
  simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_inv, Complex.cpow_neg,
    Complex.inv_cpow_ofReal_nonneg hx.le, inv_inv] at hm
  unfold triangularKernelProfile at hm
  rw [Real.log_inv, abs_neg] at hm
  change ((1 / (2 * Real.pi) : ℝ) : ℂ) * (∫ t : ℝ, W t) = (triangularKernelProfile a x : ℂ) at hm
  have hseries :=
    integral_triangular_digamma_vertical_sub_eq_tsum ha
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 4) hb) hx
  have hd :
    (fun t : ℝ ↦ D t) =
      (fun t : ℝ ↦
        (Complex.digamma ((b : ℂ) + Complex.I * (t / 2)) - Complex.digamma (b : ℂ)) *
          Analysis.triangularMellinFunction a (Complex.I * t) *
          (x : ℂ) ^ (Complex.I * t)) := by
    funext t
    dsimp only [D, W]
    ring
  rw [← hd] at hseries
  change
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ, logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) * W t) =
      _
  rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ he),
    MeasureTheory.integral_add (hW.const_mul B) (hD.const_mul (1 / 2 : ℂ)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, hseries]
  rw [← hm]
  dsimp only [B]
  ring

end PseudoPrime.LLS.PaperStatements
