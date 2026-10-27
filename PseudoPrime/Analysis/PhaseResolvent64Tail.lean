/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteResolventPolynomial
public import PseudoPrime.Analysis.PhaseResolventCandidate64
public import PseudoPrime.Analysis.GammaResolventTail

/-! # A certified unbounded spectral tail for the rounded phase candidate -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: the real shift v=t^2-256.
Output: the exact cleared numerator of (1+t^2)*R(t)-1/40000 for the rounded candidate.
All eleven coefficients are positive. Role: certify the whole tail using a degree-ten polynomial. -/
noncomputable def phase64TailPolynomial (v : ℝ) : ℝ :=
  (11665965954239211842788100875141 / 781250000 : ℝ) +
    (6205703817371312095531459837513 / 15625000000 : ℝ) * v ^ 1 +
    (350116631596903029385520475507 / 62500000000 : ℝ) * v ^ 2 +
    (14772905314355231209782045847 / 250000000000 : ℝ) * v ^ 3 +
    (1193204422210774797719291 / 2500000000 : ℝ) * v ^ 4 +
    (5444401504605345470001 / 2000000000 : ℝ) * v ^ 5 +
    (1284600048168751383989 / 125000000000 : ℝ) * v ^ 6 +
    (6069281306120503313 / 250000000000 : ℝ) * v ^ 7 +
    (1020583404701739 / 31250000000 : ℝ) * v ^ 8 +
    (984514455679 / 50000000000 : ℝ) * v ^ 9 +
    (1174879 / 1000000000 : ℝ) * v ^ 10

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: any real shift v.
Claim: the recursive candidate numerator produces the displayed exact shifted polynomial.
Proof: normalize rational list constants and check a polynomial ring identity.
Role: check externally computed coefficients inside Lean. -/
theorem phase64_shifted_polynomial_identity (v : ℝ) :
    (257 + v) * finiteResolventNumerator phaseResolvent64Coefficients (256 + v) -
        (1 / 40000 : ℝ) * finiteResolventDenominator phaseResolvent64Coefficients (256 + v) =
      phase64TailPolynomial v := by
  norm_num only [finiteResolventNumerator, finiteResolventDenominator, phaseResolvent64Coefficients,
    phase64TailPolynomial]
  ring

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a nonnegative shift.
Claim: the exact shifted polynomial is strictly positive.
Proof: the constant is positive and every other monomial is nonnegative.
Role: supply the polynomial premise for the unbounded tail. -/
theorem phase64_tail_polynomial_pos {v : ℝ} (hv : 0 ≤ v) : 0 < phase64TailPolynomial v := by
  dsimp only [phase64TailPolynomial]
  repeat' apply add_pos_of_pos_of_nonneg
  · norm_num only
  all_goals exact mul_nonneg (by norm_num only) (pow_nonneg hv _)

/-- Input: an ordinate with square at least 256.
Claim: the candidate resolvent scaled by 1+t^2 exceeds 1/40000.
Proof: substitute the nonnegative shift in the exact positive polynomial.
Role: compare the rational tail with the certified Gamma decay. -/
theorem phase64_scaled_gt_of_sq_ge_256 {t : ℝ} (ht : 256 ≤ t ^ 2) :
    (1 / 40000 : ℝ) < (1 + t ^ 2) * finiteSignedResolvent phaseResolvent64Coefficients t := by
  have hv : 0 ≤ t ^ 2 - 256 := sub_nonneg.mpr ht
  have he := phase64_shifted_polynomial_identity (t ^ 2 - 256)
  have hs : (256 : ℝ) + (t ^ 2 - 256) = t ^ 2 := by ring
  have hr : (257 : ℝ) + (t ^ 2 - 256) = 1 + t ^ 2 := by ring
  rw [hs, hr] at he
  exact
    finiteResolvent_scaled_gt phaseResolvent64Coefficients
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 256) ht)
      (he.symm ▸ phase64_tail_polynomial_pos hv)

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: a complex value, a positive real scale and a real ordinate.
Claim: the negative real phase-modulated value is at most the norm of the value.
Proof: a purely imaginary power of a positive real base has norm one.
Role: transfer norm tail bounds to signed phase bounds uniformly in scale. -/
theorem neg_re_mul_imaginary_power_le_norm (z : ℂ) {x : ℝ} (hx : 0 < x) (t : ℝ) :
    -(z * (x : ℂ) ^ (Complex.I * t)).re ≤ ‖z‖ := by
  have hn : ‖z * (x : ℂ) ^ (Complex.I * t)‖ = ‖z‖ := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hx]
    norm_num only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.rpow_zero, mul_one]
  exact (neg_le_abs _).trans ((Complex.abs_re_le_norm _).trans_eq hn)

/-- Input: any ordinate with absolute value at least sixteen.
Claim: the rounded candidate resolvent strictly exceeds the Gamma norm on the half line.
Proof: compare the existing exponential Gamma bound with the new rational polynomial bound.
Role: discharge the whole spectral tail independently of the scale. -/
theorem phase64_norm_Gamma_lt_of_abs_ge_sixteen {t : ℝ} (ht : 16 ≤ |t|) :
    ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)‖ <
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  have hs : (256 : ℝ) ≤ t ^ 2 := by nlinarith only [ht, sq_abs t]
  have h :=
    (scaled_Gamma_half_add_I_lt_of_abs_ge_sixteen ht).trans (phase64_scaled_gt_of_sq_ge_256 hs)
  exact (mul_lt_mul_iff_right₀ (by nlinarith only [sq_nonneg t] : 0 < 1 + t ^ 2)).mp h

/-- Input: a positive real scale and an ordinate of absolute value at least sixteen.
Claim: the rounded candidate dominates the negative real Gamma phase.
Proof: discard the phase only on the tail and use strict norm domination.
Role: remove the unbounded-frequency premise from candidate certification. -/
theorem phase64_signed_phase_le_of_abs_ge_sixteen {x t : ℝ} (hx : 0 < x) (ht : 16 ≤ |t|) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  exact
    (neg_re_mul_imaginary_power_le_norm _ hx t).trans
      (phase64_norm_Gamma_lt_of_abs_ge_sixteen ht).le

/-- Input: a positive scale and a signed Gamma phase majorant on absolute ordinates at most sixteen.
Claim: the same majorant holds at every real ordinate.
Proof: combine the supplied compact comparison with the proved rational tail.
Role: reduce the remaining spectral obligation to a compact interval. -/
theorem phase64_signed_phase_le_of_compact {x : ℝ} (hx : 0 < x)
    (hc :
      ∀ t : ℝ,
        |t| ≤ 16 →
          -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
            finiteSignedResolvent phaseResolvent64Coefficients t)
    (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  by_cases ht : |t| ≤ 16
  · exact hc t ht
  · exact phase64_signed_phase_le_of_abs_ge_sixteen hx (le_of_not_ge ht)

end PseudoPrime.Analysis
