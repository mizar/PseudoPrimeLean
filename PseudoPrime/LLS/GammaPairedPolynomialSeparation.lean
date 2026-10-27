/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaPrincipalCapComparison
public import PseudoPrime.LLS.GammaSignedVariationPrincipalBounds
public import PseudoPrime.LLS.GammaNonOneRefinedNumerics
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Paired separation with retained logarithmic errors and an arbitrary prefix -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Input: x >= 1, a root upper bound R, an endpoint logarithm bound u and a
nonnegative coefficient of R. Claim: the displayed positive polynomial implies
strict paired-ramp separation with arbitrary retained prefix C. Clear the
positive root denominator and retain logarithmic terms. Role: avoid rounding
all error terms to constants separately at each new entrance. -/
theorem gamma_paired_scalar_lt_gap {L x C R u : ℝ} (hx : 1 ≤ x) (hroot : Real.sqrt x ≤ R)
    (hlog : Real.log ((101 / 40 : ℝ) * x) ≤ u)
    (hcoef : 0 ≤ (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600)
    (hpoly :
      0 <
        ((83125234337 / 100000000000 : ℝ) - 231 / 24700) * x -
          ((11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + 328051 / 197600) * R -
          (38017647 / 988000 : ℝ) * u -
          (7 / 6 : ℝ) * L -
          14082763 / 197600) :
    (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + ((7 / 6 : ℝ) * L + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) <
      2 *
          ((∫ t in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight t) * Real.sqrt x -
            gammaRampPairedErrorNumerator x / Real.sqrt x) -
        gammaSignedVariationPrincipalCap x := by
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hsq := Real.sq_sqrt hx0.le
  have hc := mul_le_mul_of_nonneg_left hroot hcoef
  have hxlog := (Real.log_le_log hx0 (show x ≤ (101 / 40 : ℝ) * x by linarith only [hx])).trans hlog
  have hrlog :=
    (Real.log_le_log (mul_pos hx0 (by norm_num only : (0 : ℝ) < 99 / 40))
          (show x * (99 / 40) ≤ (101 / 40 : ℝ) * x by linarith only [hx])).trans
      hlog
  have hm := mul_le_mul_of_nonneg_right Analysis.gamma_ramp_mass_lower hx0.le
  have hd :=
    PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx)
  simp only [one_mul] at hd
  have he := mul_le_mul_of_nonneg_left hd (by norm_num only : (0 : ℝ) ≤ 43)
  have hclear :
    ((11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C) * Real.sqrt x + ((7 / 6 : ℝ) * L + 47) <
      (2 * (∫ t in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight t) - 1) * x -
        2 * gammaRampPairedErrorNumerator x -
        (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800) := by
    unfold gammaRampPairedErrorNumerator rampSmoothedIncrementError rampExtendedSmoothedError
    nlinarith only [hpoly, hc, hxlog, hrlog, hlog, hm]
  have hdiv := (div_lt_div_iff_of_pos_right hs).mpr hclear
  have heq :
    (((11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C) * Real.sqrt x + ((7 / 6 : ℝ) * L + 47)) /
        Real.sqrt x =
      (11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * C + ((7 / 6 : ℝ) * L + 47) / Real.sqrt x := by
    rw [add_div, mul_div_cancel_right₀ _ hs.ne']
  rw [heq] at hdiv
  have hcancel : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff hs.ne').mpr
    nlinarith only [hsq]
  have heq2 :
    ((2 * (∫ t in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight t) - 1) * x -
          2 * gammaRampPairedErrorNumerator x -
          (Real.sqrt x / 20 + (5517 / 4000 : ℝ) * Real.log x + 2469 / 800)) /
        Real.sqrt x =
      2 *
          ((∫ t in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight t) * Real.sqrt x -
            gammaRampPairedErrorNumerator x / Real.sqrt x) -
        gammaSignedVariationPrincipalCap x := by
    dsimp only [gammaSignedVariationPrincipalCap]
    rw [sub_div, sub_div, mul_div_assoc, hcancel]
    ring
  rw [heq2] at hdiv
  have heq3 :
    ((7 / 6 : ℝ) * L + 47) / Real.sqrt x =
      ((7 / 6 : ℝ) * L + 4) / Real.sqrt x + 43 / Real.sqrt x := by
    rw [← add_div]
    congr 1
    ring
  rw [heq3] at hdiv
  rw [mul_one_div] at he
  linarith only [hdiv, he]

end PseudoPrime.LLS

namespace PseudoPrime.LLS

/-- Input: L >= 205. Claim: a rational root cap, tangent logarithm cap and
positive polynomial hold for x=(2/5)L^2 and prefix lower bound 203/50.
Use a short log certificate at 205 and a quadratic in L-205. Role: specialize
the generic comparison on the whole half-line without finite interval cells. -/
theorem gamma_paired_polynomial_profile_of_log_ge_205 {L : ℝ} (hL : 205 ≤ L) :
    Real.sqrt ((2 / 5 : ℝ) * L ^ 2) ≤ (31623 / 50000 : ℝ) * L ∧
      Real.log ((101 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2)) ≤ (2 / 205 : ℝ) * L + 43281 / 5000 ∧
      0 <
        ((83125234337 / 100000000000 : ℝ) - 231 / 24700) * ((2 / 5 : ℝ) * L ^ 2) -
          ((11783423 / 25000000 : ℝ) * L + 541 / 50 - 2 * (203 / 50) + 328051 / 197600) *
            ((31623 / 50000 : ℝ) * L) -
          (38017647 / 988000 : ℝ) * ((2 / 205 : ℝ) * L + 43281 / 5000) -
          (7 / 6 : ℝ) * L -
          14082763 / 197600 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hroot : Real.sqrt ((2 / 5 : ℝ) * L ^ 2) ≤ (31623 / 50000 : ℝ) * L := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨by linarith only [hL], by nlinarith only [sq_nonneg L]⟩
  have hc : Analysis.rationalLogIntervalCheck 205 8 16 5 (53231 / 10000) = true := by decide +kernel
  have hl := (Analysis.rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hl
  have ht := Analysis.log_le_log_add_sub_div (by norm_num only : (0 : ℝ) < 205) hL0
  have hlogL : Real.log L ≤ (L - 205) / 205 + 53231 / 10000 := by linarith only [hl, ht]
  have hlog :
    Real.log ((101 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2)) ≤ (2 / 205 : ℝ) * L + 43281 / 5000 := by
    rw [show (101 / 40 : ℝ) * ((2 / 5 : ℝ) * L ^ 2) = (101 / 100 : ℝ) * L ^ 2 by ring,
      Real.log_mul (by norm_num only) (sq_pos_of_pos hL0).ne', Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    have hr := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 101 / 100)
    linarith only [hlogL, hr]
  refine ⟨hroot, hlog, ?_⟩
  nlinarith only [hL, sq_nonneg (L - 205)]

end PseudoPrime.LLS
