/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaPhase570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaConvolutionSplit

/-! # Dilation and signed pole comparison for the section 31 Gamma density -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rescaling the argument by 17/18 converts the section 31 density to the
previous sixth-pole density, including its zero extension on negative inputs. -/
theorem density_rescale_570 (v : ℝ) : gammaDensity570 v = quarterGammaDensity (17 / 18 * v) := by
  unfold gammaDensity570 quarterGammaDensity
  simp only [mul_nonneg_iff_of_pos_left (by norm_num only : (0 : ℝ) < 17 / 18)]
  split_ifs
  · rw [show -(27 / 25 : ℝ) * (17 / 18 * v) = -(51 / 50 : ℝ) * v by ring]
    ring
  · rfl

/-- Dilating the positive half-line gives the exact section 31 convolution
in terms of the previous density with reciprocal scaling of the pole parameter. -/
theorem convolution_rescale_570 (z c : ℝ) :
    (∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-c * |v - z|)) =
      18 / 17 * quarterGammaConvolution (17 / 18 * z) (18 / 17 * c) := by
  let f := fun u : ℝ ↦ quarterGammaDensity u * Real.exp (-(18 / 17 * c) * |u - 17 / 18 * z|)
  have h := MeasureTheory.integral_comp_mul_left_Ioi f 0 (by norm_num only : (0 : ℝ) < 17 / 18)
  have he (v : ℝ) : gammaDensity570 v * Real.exp (-c * |v - z|) = f (17 / 18 * v) := by
    dsimp only [f]
    rw [density_rescale_570, ← mul_sub, abs_mul, abs_of_pos (by norm_num only : (0 : ℝ) < 17 / 18)]
    congr 2
    ring
  simp only [he]
  simpa only [mul_zero, smul_eq_mul, show ((17 / 18 : ℝ)⁻¹) = 18 / 17 by norm_num only,
    quarterGammaConvolution, f] using h

/-- At shifted scale at least thirteen, every pole of height at least 5/2
dominates the density after normalization. Dilation transfers the signed comparison. -/
theorem convolution_ge_density_570 {z c : ℝ} (hz : 13 ≤ z) (hc : 5 / 2 ≤ c) :
    2 / c * gammaDensity570 z ≤
      ∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-c * |v - z|) := by
  rw [convolution_rescale_570, density_rescale_570]
  have h :=
    quarter_gamma_convolution_ge_density (z := 17 / 18 * z) (c := 18 / 17 * c)
      (by linarith only [hz]) (by linarith only [hc])
  have hs := mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ 18 / 17)
  convert hs using 1
  ring

/-- For a positive pole rate, the real phase resolvent is the real part of the
complex resolvent integral. The reciprocal denominator is bounded by `1 / c²`. -/
theorem phase_resolvent_570 (y : ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ t : ℝ, gammaPhase570 y t / (c ^ 2 + t ^ 2)) =
      (∫ t : ℝ,
          (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)).re := by
  have hden (t : ℝ) : 0 < c ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos hc) (sq_nonneg t)
  have hcont : Continuous (fun t : ℝ ↦ (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp
      ((continuous_const.add (continuous_id.pow 2)).inv₀ (fun t ↦ (hden t).ne'))
  have hi := (gamma_phase_integrable_570 y).2.2
  have hm := hi.mul_bdd (c := (c ^ 2)⁻¹) hcont.aestronglyMeasurable
  have hb : ∀ᵐ t : ℝ, ‖(((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)‖ ≤ (c ^ 2)⁻¹ := by
    apply Filter.Eventually.of_forall
    intro t
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (hden t).le)]
    exact inv_anti₀ (sq_pos_of_pos hc) (le_add_of_nonneg_right (sq_nonneg t))
  have hr := Complex.reCLM.integral_comp_comm (hm hb)
  change
    (∫ t : ℝ,
        (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)).re) =
      _ at hr
  have he :
    (∫ t : ℝ, gammaPhase570 y t / (c ^ 2 + t ^ 2)) =
      ∫ t : ℝ,
        (quarterKernel570.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y) *
            (((c ^ 2 + t ^ 2)⁻¹ : ℝ) : ℂ)).re := by
    apply MeasureTheory.integral_congr_ae
    apply Filter.Eventually.of_forall
    intro t
    simp only [gammaPhase570, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero, div_eq_mul_inv]
  rw [he, hr]
  simp only [one_div]
  rfl

/-- The normalized phase mass equals the shifted Gamma density. This is the
zero-pole Fourier inversion used to compare each correction with its resolvent. -/
theorem phase_mass_eq_density_570 (y : ℝ) :
    (1 / (2 * Real.pi)) * (∫ t : ℝ, gammaPhase570 y t) = gammaDensity570 (y + 14 / 5) := by
  have hr := Complex.reCLM.integral_comp_comm (gamma_phase_integrable_570 y).2.2
  change
    (∫ t : ℝ, gammaPhase570 y t) =
      (∫ t : ℝ,
          quarterKernel570.function (Complex.I * t) *
            Complex.exp (Complex.I * (t : ℂ) * y)).re at hr
  rw [hr]
  have h := congrArg Complex.re (kernel_fourier_eq_570 y)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at h
  have he : (14 / 5 : ℝ) - (y + 14 / 5) = -y := by ring
  rw [← he, profile_shift_570] at h
  exact h

/-- For every tail pole above 5/2 and shifted logarithmic scale above thirteen,
the phase mass is bounded by its normalized resolvent. This compares the two
terms of each digamma correction before summing over poles. -/
theorem phase_mass_le_resolvent_570 {y c : ℝ} (hy : 13 ≤ y + 14 / 5) (hc : 5 / 2 ≤ c) :
    (∫ t : ℝ, gammaPhase570 y t) ≤ c ^ 2 * ∫ t : ℝ, gammaPhase570 y t / (c ^ 2 + t ^ 2) := by
  have hc0 : 0 < c := by linarith only [hc]
  have h := congrArg Complex.re (pole_density_positive_570 y hc0)
  simp only [← Complex.ofReal_mul, integral_complex_ofReal, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero] at h
  rw [← phase_resolvent_570 y hc0] at h
  have hd := mul_le_mul_of_nonneg_left (convolution_ge_density_570 hy hc) (half_pos hc0).le
  have he : c / 2 * (2 / c) = 1 := by field_simp
  rw [← mul_assoc, he, one_mul, ← phase_mass_eq_density_570] at hd
  have hpi : 0 < 1 / (2 * Real.pi) := by positivity
  apply (mul_le_mul_iff_right₀ hpi).mp
  linarith only [h, hd]

/-- Convert endpoint bounds for the two exponentials and the fifth tail polynomial
into a lower bound for the first resolvent convolution at any nonnegative shift. -/
private theorem convolution_lower_of_endpoints {z A B P D : ℝ} (hz : 0 ≤ z)
    (ha : A ≤ Real.exp (-(9 / 17 : ℝ) * (17 / 18 * z)))
    (hb : Real.exp (-(27 / 25 : ℝ) * (17 / 18 * z)) ≤ B)
    (hp : Analysis.logPowerTailPoly (27 / 25 - 9 / 17) 5 (17 / 18 * z) ≤ P) (hP : 0 ≤ P)
    (hD : D < 18 / 17 * ((27 / 25 : ℝ) ^ 5 / 120) * (A * (120 / (27 / 25 - 9 / 17) ^ 6) - B * P)) :
    D < ∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-(1 / 2) * |v - z|) := by
  let u := (17 / 18 : ℝ) * z
  have h0 : 0 ≤ u := mul_nonneg (by norm_num only) hz
  have hpos :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only : (0 : ℝ) < 9 / 17 + 27 / 25) h0 5
  have hm :=
    (mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right hb hP)
  have hn := mul_nonneg (Real.exp_pos (-(27 / 25 : ℝ) * u)).le hpos
  rw [convolution_rescale_570, show (18 / 17 : ℝ) * (1 / 2) = 9 / 17 by norm_num only,
    quarter_gamma_convolution_expansion h0 (by norm_num only) (by norm_num only),
    quarter_gamma_tail_poly_zero (by norm_num only)]
  dsimp only [u] at hn
  linarith only [hD, ha, hm, hn]

/-- For shifted logarithms between 14.12 and 14.16 the first resolvent
convolution exceeds 0.033. The positive endpoint term dominates the negative
fifth tail polynomial, bounded at the right endpoint by monotonicity. -/
theorem first_convolution_lower_584 {z : ℝ} (hl : 1412 / 100 ≤ z) (hu : z ≤ 1416 / 100) :
    33 / 1000 < ∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-(1 / 2) * |v - z|) := by
  let u := (17 / 18 : ℝ) * z
  have h0 : 0 ≤ u := by
    dsimp only [u]; linarith only [hl]
  have h1 : u ≤ (17 / 18 : ℝ) * (1416 / 100) := by
    dsimp only [u]; linarith only [hu]
  have hp :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 27 / 25 - 9 / 17) h0 h1 5
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1200) (j := 10) (n := 24) (lo := 708 / 100)
        (hi := 8) (by decide +kernel)).1
  have hlog' :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1750000) (j := 21) (n := 24) (lo := 14) (hi :=
        1439 / 100) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog hlog'
  have he :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 1200)).mp
      (show 9 / 17 * u ≤ Real.log 1200 by
        dsimp only [u]; linarith only [hu, hlog])
  have he' :=
    (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 1750000)).mp
      (show Real.log 1750000 ≤ 27 / 25 * u by
        dsimp only [u]; linarith only [hl, hlog'])
  have ha := one_div_le_one_div_of_le (Real.exp_pos _) he
  have hb := one_div_le_one_div_of_le (by norm_num only) he'
  rw [one_div (Real.exp _), ← Real.exp_neg, ← neg_mul] at ha hb
  apply
    convolution_lower_of_endpoints (by linarith only [hl]) ha hb
      (hp.trans
        (show _ ≤ (1750000 : ℝ) by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]))
      (by norm_num only) (by norm_num only)

/-- For shifted logarithms between 14.12 and 14.22 the first resolvent
convolution exceeds 0.031. The positive endpoint term dominates the negative
fifth tail polynomial, bounded at the right endpoint by monotonicity. -/
theorem first_convolution_lower_600 {z : ℝ} (hl : 1412 / 100 ≤ z) (hu : z ≤ 1422 / 100) :
    31 / 1000 < ∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-(1 / 2) * |v - z|) := by
  let u := (17 / 18 : ℝ) * z
  have h0 : 0 ≤ u := by
    dsimp only [u]; linarith only [hl]
  have h1 : u ≤ (17 / 18 : ℝ) * (1422 / 100) := by
    dsimp only [u]; linarith only [hu]
  have hp :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 27 / 25 - 9 / 17) h0 h1 5
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1250) (j := 10) (n := 24) (lo := 711 / 100)
        (hi := 8) (by decide +kernel)).1
  have hlog' :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1750000) (j := 21) (n := 24) (lo := 14) (hi :=
        1439 / 100) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog hlog'
  have he :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 1250)).mp
      (show 9 / 17 * u ≤ Real.log 1250 by
        dsimp only [u]; linarith only [hu, hlog])
  have he' :=
    (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 1750000)).mp
      (show Real.log 1750000 ≤ 27 / 25 * u by
        dsimp only [u]; linarith only [hl, hlog'])
  have ha := one_div_le_one_div_of_le (Real.exp_pos _) he
  have hb := one_div_le_one_div_of_le (by norm_num only) he'
  rw [one_div (Real.exp _), ← Real.exp_neg, ← neg_mul] at ha hb
  apply
    convolution_lower_of_endpoints (by linarith only [hl]) ha hb
      (hp.trans
        (show _ ≤ (1800000 : ℝ) by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]))
      (by norm_num only) (by norm_num only)

/-- The section 99 shifted logarithms admit a common first-convolution
lower bound. Retaining both signs of the split tail improves the coarse bound. -/
theorem first_convolution_sharp_600 {z : ℝ} (hl : 14.15 ≤ z) (hu : z ≤ 14.21) :
    0.03434 < ∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-(1 / 2) * |v - z|) := by
  let u : ℝ := 17 / 18 * z
  have h₀ : 0 ≤ u := by
    dsimp only [u]; linarith only [hl]
  have h₁ : 17 / 18 * 14.15 ≤ u := by
    dsimp only [u]; linarith only [hl]
  have h₂ : u ≤ 17 / 18 * 14.21 := by
    dsimp only [u]; linarith only [hu]
  have hp :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 27 / 25 - 9 / 17) h₀ h₂ 5
  have hq :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 9 / 17 + 27 / 25)
      (by norm_num only) h₁ 5
  have hA :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1220) (j := 10) (n := 24) (lo := 7106 / 1000)
        (hi := 8) (by decide +kernel)).1
  have hB :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1820000) (j := 21) (n := 24) (lo := 14) (hi :=
        1442 / 100) (by decide +kernel)).2
  have hD :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1980000) (j := 21) (n := 24) (lo := 14496 / 1000)
        (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hA hB hD
  have he :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 1220)).mp
      (show 9 / 17 * u ≤ Real.log 1220 by linarith only [h₂, hA])
  have hf :=
    (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 1820000)).mp
      (show Real.log 1820000 ≤ 27 / 25 * u by linarith only [h₁, hB])
  have hg :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 1980000)).mp
      (show 27 / 25 * u ≤ Real.log 1980000 by linarith only [h₂, hD])
  have ha := one_div_le_one_div_of_le (Real.exp_pos _) he
  have hb := one_div_le_one_div_of_le (by norm_num only) hf
  have hd := one_div_le_one_div_of_le (Real.exp_pos _) hg
  rw [one_div (Real.exp _), ← Real.exp_neg, ← neg_mul] at ha hb hd
  have hm :=
    mul_le_mul hb
      (hp.trans
        (show _ ≤ (1800000 : ℝ) by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]))
      (Analysis.log_power_tail_poly_nonneg (by norm_num only) h₀ 5) (by norm_num only)
  have hn :=
    mul_le_mul hd
      ((show (300000 : ℝ) ≤ _ by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]).trans
        hq)
      (by norm_num only) (Real.exp_pos _).le
  rw [convolution_rescale_570, show (18 / 17 : ℝ) * (1 / 2) = 9 / 17 by norm_num only,
    quarter_gamma_convolution_expansion h₀ (by norm_num only) (by norm_num only),
    quarter_gamma_tail_poly_zero (by norm_num only)]
  dsimp only [u] at ha hm hn
  linarith only [ha, hm, hn]

/-- Both section 99 radius ranges share a first Gamma recovery exceeding 0.03434. -/
theorem section99_first_gamma {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) :
    0.03434 <
      ∫ v in Set.Ioi (0 : ℝ),
        gammaDensity570 v * Real.exp (-(1 / 2) * |v - (Real.log (r ^ 2) + 14 / 5)|) := by
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 20) (lo := 227 / 40) (hi :=
        6) (by decide +kernel)).1
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 20) (lo := 5) (hi :=
        1141 / 200) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h₁ h₂
  apply first_convolution_sharp_600
  · rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h₁, Real.log_le_log (by norm_num only) hl]
  · rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h₂, Real.log_le_log (by linarith only [hl]) hu]

/-- On the upper section 99 row, bound the two exponential endpoints
and both signed fifth moments of the full first Gamma convolution. -/
theorem first_convolution_upper_row {z : ℝ} (hl : 14.20088 ≤ z) (hu : z ≤ 14.20757) :
    0.0364 < ∫ v in Set.Ioi (0 : ℝ), gammaDensity570 v * Real.exp (-(1 / 2) * |v - z|) := by
  let u : ℝ := 17 / 18 * z
  have h₀ : 0 ≤ u := by
    dsimp only [u]; linarith only [hl]
  have h₁ : 17 / 18 * 14.20088 ≤ u := by
    dsimp only [u]; linarith only [hl]
  have h₂ : u ≤ 17 / 18 * 14.20757 := by
    dsimp only [u]; linarith only [hu]
  have hp :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 27 / 25 - 9 / 17) h₀ h₂ 5
  have hq :=
    Analysis.log_power_tail_poly_mono (by norm_num only : (0 : ℝ) < 9 / 17 + 27 / 25)
      (by norm_num only) h₁ 5
  have hA :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1217) (j := 10) (n := 24) (lo := 7.1041) (hi :=
        8) (by decide +kernel)).1
  have hB :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1953000) (j := 21) (n := 24) (lo := 14) (hi :=
        14.48488) (by decide +kernel)).2
  have hD :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1966500) (j := 21) (n := 24) (lo := 14.49176)
        (hi := 15) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hA hB hD
  have he :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 1217)).mp
      (show 9 / 17 * u ≤ Real.log 1217 by linarith only [h₂, hA])
  have hf :=
    (Real.log_le_iff_le_exp (by norm_num only : (0 : ℝ) < 1953000)).mp
      (show Real.log 1953000 ≤ 27 / 25 * u by linarith only [h₁, hB])
  have hg :=
    (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 1966500)).mp
      (show 27 / 25 * u ≤ Real.log 1966500 by linarith only [h₂, hD])
  have ha := one_div_le_one_div_of_le (Real.exp_pos _) he
  have hb := one_div_le_one_div_of_le (by norm_num only) hf
  have hd := one_div_le_one_div_of_le (Real.exp_pos _) hg
  rw [one_div (Real.exp _), ← Real.exp_neg, ← neg_mul] at ha hb hd
  have hP :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only : (0 : ℝ) < 27 / 25 - 9 / 17) h₀ 5
  have hQ :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only : (0 : ℝ) < 9 / 17 + 27 / 25)
      (show 0 ≤ 17 / 18 * (14.20088 : ℝ) by norm_num only) 5
  have hm := mul_le_mul hb hp hP (by norm_num only)
  have hn := mul_le_mul hd hq hQ (Real.exp_pos _).le
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat] at hm hn
  rw [convolution_rescale_570, show (18 / 17 : ℝ) * (1 / 2) = 9 / 17 by norm_num only,
    quarter_gamma_convolution_expansion h₀ (by norm_num only) (by norm_num only),
    quarter_gamma_tail_poly_zero (by norm_num only)]
  dsimp only [u] at ha hm hn ⊢
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]
  linarith only [ha, hm, hn]

/-- The full first Gamma convolution exceeds 0.0364 throughout the
upper radius interval from 299 through 300. -/
theorem section99_first_gamma_upper {r : ℝ} (hl : 299 ≤ r) (hu : r ≤ 300) :
    0.0364 <
      ∫ v in Set.Ioi (0 : ℝ),
        gammaDensity570 v * Real.exp (-(1 / 2) * |v - (Real.log (r ^ 2) + 14 / 5)|) := by
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 299) (j := 8) (n := 24) (lo := 5.70044) (hi := 6)
        (by decide +kernel)).1
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 24) (lo := 5) (hi :=
        5.703785) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h₁ h₂
  apply first_convolution_upper_row
  · rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h₁, Real.log_le_log (by norm_num only) hl]
  · rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h₂, Real.log_le_log (by linarith only [hl]) hu]

end PseudoPrime.PrimeTestBounds.MillerRabin
