/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaRefinedLeftMomentBounds
public import PseudoPrime.Analysis.GammaRefinedMomentConstants

/-! # Sharp refined moments in the actual Gamma left integral

The reflected constant twenty-eight is combined with moments three halves and one.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Input: primitive nonprincipal data, positive scale, and any real height.
Claim: the actual left-line integrand uses the refined zeroth and first envelopes.
Proof: reflect the completed derivative and keep the two Gamma moments separately.
Role: pointwise majorant for the sharp left-integral bound. -/
theorem gamma_left_integrand_bound_sharp_moments {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    ‖-logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))‖ ≤
      x ^ (-9 / 16 : ℝ) *
        ((Real.log q + 28) * Analysis.gammaRefinedZeroEnvelope t +
          Analysis.gammaRefinedFirstEnvelope t) := by
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
  have hd := norm_logDeriv_completed_neg_one_sixteenth_le_refined hp hne hinv t
  rw [hnlog, ← he] at hd
  have h0 : ‖Complex.Gamma (s + 1 / 2)‖ ≤ Analysis.gammaRefinedZeroEnvelope (s + 1 / 2).im :=
    Analysis.norm_Gamma_le_gammaRefinedZeroEnvelope hs
  have h1 :
    ‖Complex.Gamma (s + 1 / 2)‖ * |(s + 1 / 2).im| ≤
      Analysis.gammaRefinedFirstEnvelope (s + 1 / 2).im :=
    Analysis.norm_Gamma_mul_height_le_gammaRefinedFirstEnvelope hs
  rw [hi] at h0 h1
  have hC : 0 ≤ Real.log q + 28 := by linarith only [hlog]
  have hB := add_le_add (mul_le_mul_of_nonneg_left h0 hC) h1
  have hdg := mul_le_mul_of_nonneg_right hd (norm_nonneg (Complex.Gamma (s + 1 / 2)))
  have hb :
    ‖logDeriv χ.completedLFunction (s + 1 / 2)‖ * ‖Complex.Gamma (s + 1 / 2)‖ ≤
      (Real.log q + 28) * Analysis.gammaRefinedZeroEnvelope t +
        Analysis.gammaRefinedFirstEnvelope t := by
    nlinarith only [hB, hdg]
  change
    ‖-logDeriv χ.completedLFunction (s + 1 / 2) * (Complex.Gamma (s + 1 / 2) * (x : ℂ) ^ s)‖ ≤ _
  rw [norm_mul, norm_neg, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
  have hsr : s.re = (-9 / 16 : ℝ) := by
    simp only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  rw [hsr, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx.le (-9 / 16))).trans_eq (mul_comm _ _)

/-- Input: a nonnegative real coefficient C.
Claim: the normalized integral of C times the zeroth envelope plus the first is at most 3C/2+1.
Proof: integral linearity and the two certified normalized moment bounds.
Role: combine conductor and height costs without losing the sharp moment constants. -/
theorem gamma_sharp_left_envelope_normalized_le {C : ℝ} (hC : 0 ≤ C) :
    (1 / (2 * Real.pi)) *
        (∫ t : ℝ, C * Analysis.gammaRefinedZeroEnvelope t + Analysis.gammaRefinedFirstEnvelope t) ≤
      (3 / 2) * C + 1 := by
  rw [MeasureTheory.integral_add (Analysis.gammaRefinedZeroEnvelope_integrable.const_mul C)
      Analysis.gammaRefinedFirstEnvelope_integrable,
    MeasureTheory.integral_const_mul]
  calc
    _ =
        C * ((1 / (2 * Real.pi)) * (∫ t : ℝ, Analysis.gammaRefinedZeroEnvelope t)) +
          ((1 / (2 * Real.pi)) * (∫ t : ℝ, Analysis.gammaRefinedFirstEnvelope t)) :=
      by ring
    _ ≤ C * (3 / 2) + 1 :=
      add_le_add (mul_le_mul_of_nonneg_left Analysis.gammaRefinedZeroEnvelope_normalized_le hC)
        Analysis.gammaRefinedFirstEnvelope_normalized_le
    _ = _ := by ring

/-- Input: primitive nonprincipal data with nonprincipal inverse and positive scale.
Claim: the actual left integral is at most x^(-9/16) times (3(log q+28)/2+1).
Proof: integrate the sharp pointwise envelopes and normalize their certified moments.
Role: the left error required by the subunit witness comparison. -/
theorem norm_gamma_left_integral_le_sharp_moments {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
          (∫ t : ℝ,
            -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
              (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
                (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))‖ ≤
      x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Real.log q + 28) + 1) := by
  let F := fun t : ℝ ↦
    -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
      (gammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
        (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hfi : MeasureTheory.Integrable F :=
    MellinKernel.integrable_completed_left_line gammaMellinKernel hp hne hinv
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by norm_num only) (by norm_num only) hx
  let C := Real.log q + 28
  let E := fun t : ℝ ↦
    x ^ (-9 / 16 : ℝ) *
      (C * Analysis.gammaRefinedZeroEnvelope t + Analysis.gammaRefinedFirstEnvelope t)
  have hgi : MeasureTheory.Integrable E :=
    ((Analysis.gammaRefinedZeroEnvelope_integrable.const_mul C).add
          Analysis.gammaRefinedFirstEnvelope_integrable).const_mul
      _
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hC : 0 ≤ C := by
    dsimp only [C]
    linarith only [Real.log_nonneg hq1]
  have hb :=
    (MeasureTheory.norm_integral_le_integral_norm F).trans
      (MeasureTheory.integral_mono hfi.norm hgi
        (fun t ↦ gamma_left_integrand_bound_sharp_moments hp hne hinv hx t))
  have hnorm := gamma_sharp_left_envelope_normalized_le hC
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
            (∫ t : ℝ,
              C * Analysis.gammaRefinedZeroEnvelope t + Analysis.gammaRefinedFirstEnvelope t)) :=
      hmul
    _ =
        x ^ (-9 / 16 : ℝ) *
          ((1 / (2 * Real.pi)) *
            (∫ t : ℝ,
              C * Analysis.gammaRefinedZeroEnvelope t + Analysis.gammaRefinedFirstEnvelope t)) :=
      by ring
    _ ≤ x ^ (-9 / 16 : ℝ) * ((3 / 2) * C + 1) :=
      mul_le_mul_of_nonneg_left hnorm (Real.rpow_nonneg hx.le _)

end PseudoPrime.LLS.PaperStatements
