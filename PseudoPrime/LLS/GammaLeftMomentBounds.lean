/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaLeftIntegralBounds
public import PseudoPrime.Analysis.GammaLeftMoments
public import PseudoPrime.Analysis.QuadraticGammaSmoothedNumerics

/-! # Sharp Gamma left-integral moment bounds

Three-region moment envelopes control the actual completed integral.
The fixed scale and conductor gate yield the numerical left error two.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal data, the left integrand at -9/16 is bounded
by x^(-9/16) times the zeroth and first Gamma envelopes, with coefficient log(q)+283.
Reflect the completed derivative and retain each moment separately. -/
theorem gamma_left_integrand_bound_moments {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖-logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))‖ ≤
      x ^ (-9 / 16 : ℝ) *
        ((Real.log q + 283) * Analysis.gammaLeftZeroEnvelope t +
          Analysis.gammaLeftFirstEnvelope t) := by
  let s : ℂ := ((-9 / 16 : ℝ) : ℂ) + Complex.I * t
  have hs : (s + 1 / 2).re = (-1 / 16 : ℝ) := by
    norm_num only [s, Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      add_zero]
  have hi : (s + 1 / 2).im = t := by
    simp only [s, Complex.add_im, Complex.ofReal_im, Complex.div_ofNat_im, Complex.one_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, one_mul, zero_mul, zero_div,
      zero_add, add_zero]
  have he : s + 1 / 2 = ((-1 / 16 : ℝ) : ℂ) + Complex.I * t := by
    dsimp only [s]
    simp only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hlog : 0 ≤ Real.log q := Real.log_nonneg hq1
  have hnlog : ‖Complex.log (q : ℂ)‖ = Real.log q := by
    rw [← Complex.natCast_log, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog]
  have hd :=
    AnalyticNumberTheory.DirichletLFunction.norm_logDeriv_completed_neg_one_sixteenth_le hp hne hinv
      t
  rw [hnlog, ← he] at hd
  have h0 := Analysis.norm_Gamma_neg_one_sixteenth_le_zeroEnvelope hs
  have h1 := Analysis.norm_Gamma_neg_one_sixteenth_mul_height_le_firstEnvelope hs
  rw [hi] at h0 h1
  have hC : 0 ≤ Real.log q + 283 := by linarith only [hlog]
  have hB := add_le_add (mul_le_mul_of_nonneg_left h0 hC) h1
  have hdg := mul_le_mul_of_nonneg_right hd (norm_nonneg (Complex.Gamma (s + 1 / 2)))
  have hb :
    ‖logDeriv χ.completedLFunction (s + 1 / 2)‖ * ‖Complex.Gamma (s + 1 / 2)‖ ≤
      (Real.log q + 283) * Analysis.gammaLeftZeroEnvelope t +
        Analysis.gammaLeftFirstEnvelope t := by
    nlinarith only [hB, hdg]
  change
    ‖-logDeriv χ.completedLFunction (s + 1 / 2) * (Complex.Gamma (s + 1 / 2) * (x : ℂ) ^ s)‖ ≤ _
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hsr : s.re = (-9 / 16 : ℝ) := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [hsr, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx.le (-9 / 16))).trans_eq (mul_comm _ _)

/-- For nonnegative coefficient C, the normalized integral of C times the
zeroth envelope plus the first envelope is bounded by (16/5)C+5/3.
Linearity and the two certified moment bounds supply the left-error budget. -/
theorem gamma_left_envelope_normalized_le {C : ℝ} (hC : 0 ≤ C) :
    (1 / (2 * Real.pi)) *
        (∫ t : ℝ, C * Analysis.gammaLeftZeroEnvelope t + Analysis.gammaLeftFirstEnvelope t) ≤
      (16 / 5) * C + 5 / 3 := by
  rw [MeasureTheory.integral_add (Analysis.gammaLeftZeroEnvelope_integrable.const_mul C)
      Analysis.gammaLeftFirstEnvelope_integrable,
    MeasureTheory.integral_const_mul]
  calc
    _ =
        C * ((1 / (2 * Real.pi)) * (∫ t : ℝ, Analysis.gammaLeftZeroEnvelope t)) +
          ((1 / (2 * Real.pi)) * (∫ t : ℝ, Analysis.gammaLeftFirstEnvelope t)) :=
      by ring
    _ ≤ C * (16 / 5) + 5 / 3 :=
      add_le_add (mul_le_mul_of_nonneg_left Analysis.gammaLeftZeroEnvelope_normalized_le hC)
        Analysis.gammaLeftFirstEnvelope_normalized_le
    _ = _ := by ring

/-- For positive scale and primitive nonprincipal data, the normalized left
integral is bounded by x^(-9/16)((16/5)(log(q)+283)+5/3).
Integrate the two moment envelopes and keep the full real-power decay.
This replaces the coarse constant 10000 in the smoothed quadratic comparison. -/
theorem norm_gamma_left_integral_le_moments {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log q + 283) + 5 / 3) := by
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
      (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
        (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hfi : MeasureTheory.Integrable F :=
    MellinKernel.integrable_completed_left_line gammaMellinKernel hp hne hinv
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) hx
  let C := Real.log q + 283
  let E := fun t : ℝ ↦
    x ^ (-9 / 16 : ℝ) * (C * Analysis.gammaLeftZeroEnvelope t + Analysis.gammaLeftFirstEnvelope t)
  have hgi : MeasureTheory.Integrable E :=
    ((Analysis.gammaLeftZeroEnvelope_integrable.const_mul C).add
          Analysis.gammaLeftFirstEnvelope_integrable).const_mul
      _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith only [Real.log_nonneg hq1]
  have hb :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hgi
        (fun t ↦ gamma_left_integrand_bound_moments hp hne hinv hx t))
  have hnorm := gamma_left_envelope_normalized_le hC
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  change ‖((1 / (2 * Real.pi) : ℝ) : ℂ) * ∫ t : ℝ, F t‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (div_nonneg zero_le_one hpi.le)]
  have hmul := mul_le_mul_of_nonneg_left hb (div_nonneg zero_le_one hpi.le)
  dsimp only [E] at hmul
  rw [MeasureTheory.integral_const_mul] at hmul
  calc
    _ ≤
        (1 / (2 * Real.pi)) *
          (x ^ (-9 / 16 : ℝ) *
            (∫ t : ℝ, C * Analysis.gammaLeftZeroEnvelope t + Analysis.gammaLeftFirstEnvelope t)) :=
      hmul
    _ =
        x ^ (-9 / 16 : ℝ) *
          ((1 / (2 * Real.pi)) *
            (∫ t : ℝ, C * Analysis.gammaLeftZeroEnvelope t + Analysis.gammaLeftFirstEnvelope t)) :=
      by ring
    _ ≤ x ^ (-9 / 16 : ℝ) * ((16 / 5) * C + 5 / 3) :=
      mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg hx.le _)

/-- For x≥3¹⁶, x^(-9/16) is at most 1/(3sqrt(x)). Separate the exponent into
-1/16 and -1/2 and compare the former factor using the scale lower bound.
This retains the extra decay needed for the left integral. -/
theorem rpow_neg_nine_sixteenths_le_div_three_sqrt {x : ℝ} (hx : (3 : ℝ) ^ 16 ≤ x) :
    x ^ (-9 / 16 : ℝ) ≤ 1 / (3 * Real.sqrt x) := by
  have hxpos : 0 < x := (pow_pos (by norm_num only : (0 : ℝ) < 3) 16).trans_le hx
  have hsmall :=
    Real.rpow_le_rpow_of_nonpos (pow_pos (by norm_num only : (0 : ℝ) < 3) 16) hx
      (by norm_num only : (-1 / 16 : ℝ) ≤ 0)
  have hthree : ((3 : ℝ) ^ 16) ^ (-1 / 16 : ℝ) = 1 / 3 := by
    rw [← Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 3)]
    norm_num only [Real.rpow_neg_one]
  have hhalf : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [neg_div, Real.rpow_neg hxpos.le, ← Real.sqrt_eq_rpow, one_div]
  rw [hthree] at hsmall
  calc
    _ = x ^ (-1 / 16 : ℝ) * x ^ (-1 / 2 : ℝ) := by
      rw [← Real.rpow_add hxpos]
      norm_num only
    _ ≤ (1 / 3) * (1 / Real.sqrt x) := by
      rw [hhalf]
      exact mul_le_mul_of_nonneg_right hsmall (div_nonneg zero_le_one (Real.sqrt_nonneg x))
    _ = _ := by ring

/-- For L≥46000, x≥3¹⁶, sqrt(x)≥9L/16 and 0≤Q≤L+2, the left moment
budget x^(-9/16)((16/5)(Q+283)+5/3) is at most two.
Combine the extra decay with the square-root scale and rational arithmetic. -/
theorem gamma_left_moment_error_le_two {L x Q : ℝ} (hL : 46000 ≤ L) (hx : (3 : ℝ) ^ 16 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hQ0 : 0 ≤ Q) (hQ : Q ≤ L + 2) :
    x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Q + 283) + 5 / 3) ≤ 2 := by
  have hs : 0 < Real.sqrt x := by linarith only [hroot, hL]
  have hC : 0 ≤ (16 / 5 : ℝ) * (Q + 283) + 5 / 3 := by linarith only [hQ0]
  have hm := mul_le_mul_of_nonneg_right (rpow_neg_nine_sixteenths_le_div_three_sqrt hx) hC
  apply hm.trans
  rw [one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs)]
  nlinarith only [hroot, hL, hQ]

/-- For primitive nonprincipal data with log(q)≤L+2, the normalized left
integral is at most two when the stated large-input scale conditions hold.
Apply the moment integral bound and its explicit scalar budget. -/
theorem norm_gamma_left_integral_le_two_of_moments {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {L x : ℝ} (hL : 46000 ≤ L)
    (hx : (3 : ℝ) ^ 16 ≤ x) (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hq : Real.log q ≤ L + 2) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      2 := by
  have hxpos : 0 < x := (pow_pos (by norm_num only : (0 : ℝ) < 3) 16).trans_le hx
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  exact
    (norm_gamma_left_integral_le_moments hp hne hinv hxpos).trans
      (gamma_left_moment_error_le_two hL hx hroot (Real.log_nonneg hq1) hq)

/-- At L≥46000, the fixed scale (32/99)L² is at least 3¹⁶.
The endpoint square comparison verifies the extra-decay gate. -/
theorem ramp_scale_ge_three_sixteenth {L : ℝ} (hL : 46000 ≤ L) :
    (3 : ℝ) ^ 16 ≤ (32 / 99 : ℝ) * L ^ 2 := by
  have hsq : (46000 : ℝ) ^ 2 ≤ L ^ 2 := by nlinarith only [hL, sq_nonneg (L - 46000)]
  norm_num only
  nlinarith only [hsq]

/-- For primitive nonprincipal data, L≥46000 and log(q)≤L+2, the fixed-scale
left integral has norm at most two. Apply the general moment estimate at
x=(32/99)L²; this is the smoothed quadratic witness formula's left-error contract. -/
theorem norm_gamma_left_integral_le_two_at_ramp_scale {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {L : ℝ}
    (hL : 46000 ≤ L) (hq : Real.log q ≤ L + 2) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (((32 / 99 : ℝ) * L ^ 2) : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      2 := by
  have h :=
    norm_gamma_left_integral_le_two_of_moments (χ := χ) (L := L) (x := (32 / 99 : ℝ) * L ^ 2) hp hne
      hinv hL (ramp_scale_ge_three_sixteenth hL)
      (Analysis.ramp_scale_sqrt_lower (by linarith only [hL])) hq
  simpa only [Complex.ofReal_mul, Complex.ofReal_pow] using h

end PseudoPrime.LLS.PaperStatements
