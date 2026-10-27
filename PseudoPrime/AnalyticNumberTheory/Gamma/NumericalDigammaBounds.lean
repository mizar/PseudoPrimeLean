/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.UniformDigamma
public import PseudoPrime.Analysis.EulerMascheroniBounds
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.Real.Pi.Bounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Numerical bounds for the uniform digamma error

The inverse-square majorant has a Basel-sum value and an explicit bound of eight.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The uniform digamma error majorant equals four times the Basel sum π²/6.
Shift away its zero term and factor out four. This identifies the previously
unspecified summable error with an explicit constant. -/
theorem digammaLogErrorBound_eq_pi_sq : digammaLogErrorBound = 4 * (Real.pi ^ 2 / 6) := by
  have he := hasSum_zeta_two.summable.tsum_eq_zero_add
  rw [hasSum_zeta_two.tsum_eq] at he
  norm_num only [Nat.cast_zero, zero_pow (by decide : (2 : ℕ) ≠ 0), div_zero, zero_add] at he
  have hshift : (∑' n : ℕ, (1 : ℝ) / ((n : ℝ) + 1) ^ 2) = Real.pi ^ 2 / 6 := by
    simpa only [Nat.cast_add, Nat.cast_one] using he.symm
  unfold digammaLogErrorBound
  calc
    (∑' n : ℕ, (4 : ℝ) / ((n : ℝ) + 1) ^ 2) = ∑' n : ℕ, 4 * (1 / ((n : ℝ) + 1) ^ 2) :=
      tsum_congr (fun n ↦ (mul_one_div _ _).symm)
    _ = 4 * (Real.pi ^ 2 / 6) := by rw [tsum_mul_left, hshift]

/-- The uniform digamma error majorant is at most eight. Use the Basel identity
and the certified upper bound for π. This supplies a concrete archimedean constant
for the signed Poisson comparison. -/
theorem digammaLogErrorBound_le_eight : digammaLogErrorBound ≤ 8 := by
  rw [digammaLogErrorBound_eq_pi_sq]
  nlinarith only [Real.pi_lt_d2, Real.pi_pos]

/-- On Re s ≥ 1/2, the norm of digamma minus the principal logarithm is at most
eight. Compose the uniform analytic estimate with its explicit numerical bound.
This keeps all shifts in the Gamma resolvent comparison under one constant. -/
theorem norm_digamma_sub_log_le_eight {s : ℂ} (hs : 1 / 2 ≤ s.re) :
    ‖Complex.digamma s - Complex.log s‖ ≤ 8 := by
  exact (norm_digamma_sub_log_le hs).trans digammaLogErrorBound_le_eight

/-- Bound the logarithmic normalization in the completed Gamma factor by two.
Use positivity of log π and comparison with log 4. -/
private theorem abs_log_pi_le_two : |Real.log Real.pi| ≤ 2 := by
  have hn := Real.log_nonneg (Real.pi_gt_three.le.trans' (show (1 : ℝ) ≤ 3 by norm_num only))
  have hm := Real.log_le_log Real.pi_pos Real.pi_lt_four.le
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow] at hm
  norm_num only at hm
  rw [abs_of_nonneg hn]
  have h2 := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num only)
  linarith only [hm, h2]

/-- On Re s ≥ 1/2 with |log norm s| ≤ 2, the real archimedean correction
(digamma s - log π)/2 has absolute value at most six. Combine the explicit
uniform digamma error eight with the two logarithmic bounds. This is the
per-node archimedean allowance in the Gamma resolvent certificate. -/
theorem abs_re_digamma_sub_log_pi_div_two_le_six {s : ℂ} (hs : 1 / 2 ≤ s.re)
    (hlog : |Real.log ‖s‖| ≤ 2) : |((Complex.digamma s).re - Real.log Real.pi) / 2| ≤ 6 := by
  have he := (abs_re_digamma_sub_log_norm_le hs).trans digammaLogErrorBound_le_eight
  have ht := abs_sub_le (Complex.digamma s).re (Real.log ‖s‖) (Real.log Real.pi)
  have hc := abs_sub (Real.log ‖s‖) (Real.log Real.pi)
  rw [abs_div, abs_of_pos (show (0 : ℝ) < 2 by norm_num only)]
  linarith only [he, ht, hc, hlog, abs_log_pi_le_two]

/-- The logarithm is bounded in absolute value by two on [1/2,17/4].
Use monotonicity for the lower endpoint and the tangent bound at two for the upper bound. -/
private theorem abs_log_le_two_of_mem {r : ℝ} (hr : 1 / 2 ≤ r) (hu : r ≤ 17 / 4) :
    |Real.log r| ≤ 2 := by
  have hp : 0 < r := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hr
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 2) hr
  rw [Real.log_div (by norm_num only : (1 : ℝ) ≠ 0) (by norm_num only : (2 : ℝ) ≠ 0), Real.log_one,
    zero_sub] at hlo
  have hhi := Real.log_le_sub_one_of_pos (div_pos hp (by norm_num only : (0 : ℝ) < 2))
  rw [Real.log_div hp.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at hhi
  apply abs_le.mpr
  constructor <;> linarith only [hlo, hhi, hu, Real.log_two_lt_d9]

/-- For every real Gamma argument in [1/2,17/4], the archimedean correction has
absolute value at most six. Certify the logarithm bound on this entire interval
and apply the uniform digamma estimate. This covers all resolvent nodes and both parities. -/
theorem abs_real_digamma_sub_log_pi_div_two_le_six {r : ℝ} (hr : 1 / 2 ≤ r) (hu : r ≤ 17 / 4) :
    |((Complex.digamma (r : ℂ)).re - Real.log Real.pi) / 2| ≤ 6 := by
  have hlog := abs_log_le_two_of_mem hr hu
  have hp : 0 ≤ r := (by norm_num only : (0 : ℝ) ≤ 1 / 2).trans hr
  apply abs_re_digamma_sub_log_pi_div_two_le_six
  · exact hr
  · simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp] using hlog

/-- Digamma's real part is monotone on the positive real axis. Subtract the
convergent reciprocal series and compare each positive reciprocal. This allows
archimedean corrections to be controlled by explicit endpoint values. -/
theorem re_digamma_mono_of_pos {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (Complex.digamma (a : ℂ)).re ≤ (Complex.digamma (b : ℂ)).re := by
  have hb := ha.trans_le hab
  have h := digamma_sub_eq_resolventSeries (s := (b : ℂ)) (t := (a : ℂ)) hb ha
  have hs := summable_resolventDifference (s := (a : ℂ)) (t := (b : ℂ)) ha.le hb.le
  have hr := congrArg Complex.re h
  rw [Complex.sub_re, Complex.re_tsum hs] at hr
  have hn : 0 ≤ ∑' n : ℕ, (1 / ((a : ℂ) + n) - 1 / ((b : ℂ) + n)).re := by
    apply tsum_nonneg
    intro n
    have ha' : 0 < a + n := add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n)
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_add, ← Complex.ofReal_one,
      ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re]
    exact sub_nonneg.mpr (one_div_le_one_div_of_le ha' (add_le_add_left hab _))
  linarith only [hr, hn]

/-- The logarithmic normalization log π is at most 6/5. Apply the logarithm's
tangent bound at three and the numerical upper bounds for π and log three. -/
private theorem log_pi_le_six_fifths : Real.log Real.pi ≤ 6 / 5 := by
  have h := Real.log_le_sub_one_of_pos (div_pos Real.pi_pos (by norm_num only : (0 : ℝ) < 3))
  rw [Real.log_div Real.pi_pos.ne' (by norm_num only : (3 : ℝ) ≠ 0)] at h
  linarith only [h, Real.pi_lt_d2, Real.log_three_lt_d9]

/-- On [1/2,17/4], the real archimedean correction (digamma(r)-log π)/2 has
absolute value at most 8/5. Monotonicity bounds digamma between its values at
one half and five; their exact formulas and Euler's constant bounds close the
comparison. This sharpens the per-node Gamma allowance in the resolvent sum. -/
theorem abs_real_digamma_sub_log_pi_div_two_le_eight_fifths {r : ℝ} (hr : 1 / 2 ≤ r)
    (hu : r ≤ 17 / 4) : |((Complex.digamma (r : ℂ)).re - Real.log Real.pi) / 2| ≤ 8 / 5 := by
  have hlo := re_digamma_mono_of_pos (by norm_num only : (0 : ℝ) < 1 / 2) hr
  have hhi :=
    re_digamma_mono_of_pos (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hr)
      (hu.trans (by norm_num only : (17 / 4 : ℝ) ≤ 5))
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hlo hhi
  rw [Complex.digamma_one_half] at hlo
  have hval := Complex.digamma_nat_add_one 4
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hval
  rw [hval] at hhi
  norm_num only [Complex.sub_re, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.ofReal_re,
    Complex.log_re, Complex.norm_ofNat, ← Complex.ofReal_ofNat, Complex.ofReal_im,
    Complex.div_ofNat_re, harmonic, Finset.sum_range_succ, Finset.sum_range_zero] at hlo hhi
  change
    -2 * Real.log 2 - -(0 : ℝ) * (Complex.log 2).im - Real.eulerMascheroniConstant ≤
      (Complex.digamma (r : ℂ)).re at hlo
  change (Complex.digamma (r : ℂ)).re ≤ 25 / 12 - Real.eulerMascheroniConstant at hhi
  norm_num only at hlo
  apply abs_le.mpr
  constructor
  · linarith only [hlo, Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths,
      Real.log_two_lt_d9, log_pi_le_six_fifths]
  · have he := Real.one_half_lt_eulerMascheroniConstant
    have hp := Real.log_nonneg (Real.pi_gt_three.le.trans' (by norm_num only : (1 : ℝ) ≤ 3))
    linarith only [hhi, he, hp]

end PseudoPrime.AnalyticNumberTheory.Gamma
