/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleFourier
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleEvenBaseline

/-! # Signed central gamma integral for the section 76 triangle -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At positive width and positive real shift the integrated vertical digamma
difference equals the sum of its exact exponentially corrected pole moments. -/
theorem triangle_vertical_series {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∫ t : ℝ,
        (1 / 2 : ℝ) *
          ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
          ‖Analysis.triangularMellinFunction a (Complex.I * t)‖) =
      ∑' n : ℕ, Real.pi / (2 * (b + n) ^ 2) * (1 - Real.exp (-(4 * a * (b + n)))) := by
  let F := fun n : ℕ ↦ fun t : ℝ ↦
    (1 / 2 : ℝ) * ((t / 2) ^ 2 / ((b + n) * ((b + n) ^ 2 + (t / 2) ^ 2))) *
      ‖Analysis.triangularMellinFunction a (Complex.I * t)‖
  have hp (n : ℕ) : 0 < b + n := add_pos_of_pos_of_nonneg hb (Nat.cast_nonneg n)
  have hF0 (n : ℕ) (t : ℝ) : 0 ≤ F n t := by
    exact
      mul_nonneg
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)
          (div_nonneg (sq_nonneg _)
            (mul_nonneg (hp n).le (add_nonneg (sq_nonneg _) (sq_nonneg _)))))
        (norm_nonneg _)
  have hf (n : ℕ) : MeasureTheory.Integrable (F n) :=
    (Analysis.triangular_digamma_integrable_and_bound ha.ne' (hp n)).1
  have hbound (n : ℕ) : (∫ t : ℝ, F n t) ≤ Real.pi * ((b + n) ^ 2)⁻¹ :=
    (Analysis.triangular_digamma_integrable_and_bound ha.ne' (hp n)).2
  have heNorm (n : ℕ) : (∫ t : ℝ, ‖F n t‖) = ∫ t : ℝ, F n t :=
    MeasureTheory.integral_congr_ae
      (Filter.Eventually.of_forall (fun t ↦ Real.norm_of_nonneg (hF0 n t)))
  have hs := (Analysis.summable_shifted_inverse_squares hb).mul_left Real.pi
  have hsNorm : Summable (fun n : ℕ ↦ ∫ t : ℝ, ‖F n t‖) :=
    hs.of_nonneg_of_le (fun n ↦ MeasureTheory.integral_nonneg (fun t ↦ norm_nonneg _))
      (fun n ↦ by
        rw [heNorm]; exact hbound n)
  have he := MeasureTheory.integral_tsum_of_summable_integral_norm hf hsNorm
  have hpoint (t : ℝ) :
    (∑' n : ℕ, F n t) =
      (1 / 2 : ℝ) *
        ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
        ‖Analysis.triangularMellinFunction a (Complex.I * t)‖ := by
    dsimp only [F]
    rw [tsum_mul_right, tsum_mul_left, ←
      AnalyticNumberTheory.Gamma.digamma_vertical_re_sub_eq_tsum hb]
    simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint)] at he
  rw [← he]
  exact tsum_congr (fun n => triangle_digamma_pole_exact ha (hp n))

/-- At the even shift and width 5/4 the raw vertical correction is twice pi
times the origin series for half-width 5/2. -/
theorem triangle_even_vertical_series :
    (∫ t : ℝ,
        (1 / 2 : ℝ) *
          ((Complex.digamma (1 / 4 + Complex.I * (t / 2))).re - (Complex.digamma (1 / 4)).re) *
          ‖Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)‖) =
      (2 * Real.pi) * ∑' n : ℕ, triangleOriginTerm n := by
  have h := triangle_vertical_series (a := 5 / 4) (b := 1 / 4) (by norm_num only) (by norm_num only)
  push_cast at h
  rw [h, ← tsum_mul_left]
  apply tsum_congr
  intro n
  unfold triangleOriginTerm
  rw [show (4 * (5 / 4 : ℝ) * (1 / 4 + n)) = (2 * n + 1 / 2) * (5 / 2) by ring]
  have hden : (2 * (n : ℝ) + 1 / 2) ^ 2 = 4 * (1 / 4 + n) ^ 2 := by ring
  rw [hden]
  field_simp
  ring

/-- Adding the normalized vertical correction to the real central baseline
of an even character recovers the section 76 origin gamma constant exactly. -/
theorem triangle_even_vertical_gamma {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.Even) :
    2 * (logDeriv χ.gammaFactor (1 / 2)).re +
        (4 / 5) *
          ((∫ t : ℝ,
              (1 / 2 : ℝ) *
                ((Complex.digamma (1 / 4 + Complex.I * (t / 2))).re -
                  (Complex.digamma (1 / 4)).re) *
                ‖Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)‖) /
            (2 * Real.pi)) =
      triangleOriginGamma := by
  rw [triangle_even_baseline hχ, triangle_even_vertical_series, triangleOriginGamma,
    mul_div_cancel_left₀ _ (by positivity : (2 * Real.pi) ≠ 0)]

/-- The normalized signed vertical integral of the actual even gamma factor
at width 5/4 equals the certified origin gamma constant of section 76. -/
theorem triangle_even_gamma_integral {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.Even) :
    (4 / 5) *
        ((∫ t : ℝ,
            (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re) /
          (2 * Real.pi)) =
      triangleOriginGamma := by
  let b : ℝ := 1 / 4
  have he (t : ℝ) :
    (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2)).re =
      (-Real.log Real.pi + (Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re) / 2 := by
    have hz : ((Complex.I * (t : ℂ) + 1 / 2) / 2) = (b : ℂ) + Complex.I * (t / 2) := by
      dsimp only [b]; push_cast; ring
    have hp : 0 < ((Complex.I * (t : ℂ) + 1 / 2) / 2).re := by
      rw [hz]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.div_ofNat_im, Complex.ofReal_im, zero_div, zero_mul, mul_zero, sub_zero, add_zero]
      norm_num only [b]
    rw [AnalyticNumberTheory.DirichletLFunction.gammaLogDeriv_even_eq_digamma hχ
        (fun n => AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos hp n),
      hz, ← Complex.ofReal_log Real.pi_pos.le]
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.neg_re, Complex.ofReal_re]
    ring
  let w := fun t : ℝ ↦ ‖Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)‖
  let B := (-Real.log Real.pi + (Complex.digamma (b : ℂ)).re) / 2
  let C := fun t : ℝ ↦
    (1 / 2 : ℝ) *
      ((Complex.digamma ((b : ℂ) + Complex.I * (t / 2))).re - (Complex.digamma (b : ℂ)).re) *
      w t
  let K := LLS.PaperStatements.triangularMellinKernel (by norm_num only : (0 : ℝ) < (5 / 4))
  have hw : MeasureTheory.Integrable w := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_line_in_strip K (c := 0)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < 0; norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only)
    simp only [Complex.ofReal_zero, zero_add] at h
    exact h.norm
  have hid (t : ℝ) :
    (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
          Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re =
      B * w t + C t := by
    rw [Analysis.triangularMellinFunction_imaginary (by norm_num only : ((5 / 4) : ℝ) ≠ 0)]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    rw [he]
    dsimp only [B, C, w]
    rw [Analysis.norm_triangularMellinFunction_imaginary (by norm_num only : ((5 / 4) : ℝ) ≠ 0)]
    ring
  have hr :
    MeasureTheory.Integrable
      (fun t : ℝ =>
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re) := by
    have h :=
      LLS.PaperStatements.MellinKernel.integrable_gammaFactor_power_line K χ (c := 0) (x := 1)
        (by norm_num only)
        (by
          change (0 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) zero_lt_one
    simp only [Complex.ofReal_zero, zero_add, Complex.ofReal_one, Complex.one_cpow, mul_one] at h
    exact Complex.reCLM.integrable_comp h
  have hc : MeasureTheory.Integrable C := by
    have h := hr.sub (hw.const_mul B)
    convert h using 1
    funext t
    change
      C t =
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
              Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re -
          B * w t
    rw [hid]
    ring
  have hm : (∫ t : ℝ, w t) / (2 * Real.pi) = 5 / 2 := by
    have h :=
      LLS.PaperStatements.triangular_mass_of_function K (by norm_num only : (0 : ℝ) < (5 / 4)) rfl
    norm_num only at h
    exact h
  have hi :
    (∫ t : ℝ,
        (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
            Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re) =
      B * (∫ t : ℝ, w t) + ∫ t : ℝ, C t := by
    rw [MeasureTheory.integral_congr_ae (MeasureTheory.ae_of_all _ hid),
      MeasureTheory.integral_add (hw.const_mul B) hc, MeasureTheory.integral_const_mul]
  have hB := he 0
  simp only [Complex.ofReal_zero, mul_zero, zero_add, zero_div, add_zero] at hB
  rw [hi, add_div, mul_div_assoc, hm, ← triangle_even_vertical_gamma hχ]
  simp only [C, b, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  change (logDeriv χ.gammaFactor (1 / 2)).re = B at hB
  rw [hB]
  ring

/-- The origin prime correction exceeds 28/5 with the gamma term expressed
directly as the signed vertical integral of any even character. -/
theorem triangle_even_origin_saving {q : ℕ} {χ : DirichletCharacter ℂ q} (hχ : χ.Even) :
    28 / 5 <
      2 *
          (∑ m ∈ Finset.Ioc 0 ⌊Real.exp (5 / 2)⌋₊,
            ArithmeticFunction.vonMangoldt m / Real.sqrt m * (1 - Real.log m / (5 / 2))) -
        (4 / 5) *
          ((∫ t : ℝ,
              (logDeriv χ.gammaFactor (Complex.I * t + 1 / 2) *
                  Analysis.triangularMellinFunction (5 / 4) (Complex.I * t)).re) /
            (2 * Real.pi)) := by
  rw [triangle_even_gamma_integral hχ]
  exact triangle_origin_correction

end PseudoPrime.PrimeTestBounds.MillerRabin
