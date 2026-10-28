/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonNumericalBounds

/-! # Sharper real archimedean corrections away from the first Gamma argument

Digamma monotonicity improves the correction to 9/10 when the argument is at least one.
The parity-dependent Dirichlet Gamma factors preserve the same bound for sigma at least two.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The logarithmic normalization log(pi) is at most 6/5.
 Apply the tangent bound at three and the certified pi and log(3) bounds.
 This supplies the lower endpoint of the real Gamma correction. -/
theorem real_log_pi_le_six_fifths : Real.log Real.pi ≤ 6 / 5 := by
  have h := Real.log_le_sub_one_of_pos (div_pos Real.pi_pos (by norm_num only : (0 : ℝ) < 3))
  rw [Real.log_div Real.pi_pos.ne' (by norm_num only : (3 : ℝ) ≠ 0)] at h
  linarith only [h, Real.pi_lt_d2, Real.log_three_lt_d9]

/-- For real argument 1≤r≤17/4, the archimedean digamma correction has absolute value
 at most 9/10. Use monotonicity and exact values at one and five, with Euler constant bounds.
 This sharpens the allowance for later resolvent nodes. -/
theorem abs_real_digamma_sub_log_pi_div_two_le_nine_tenths {r : ℝ} (hr : 1 ≤ r) (hu : r ≤ 17 / 4) :
    |((Complex.digamma (r : ℂ)).re - Real.log Real.pi) / 2| ≤ 9 / 10 := by
  have hlo := re_digamma_mono_of_pos (by norm_num only : (0 : ℝ) < 1) hr
  have hhi :=
    re_digamma_mono_of_pos (zero_lt_one.trans_le hr)
      (hu.trans (by norm_num only : (17 / 4 : ℝ) ≤ 5))
  norm_num only [Complex.ofReal_one, Complex.ofReal_ofNat] at hlo hhi
  have hvlo := Complex.digamma_nat_add_one 0
  have hvhi := Complex.digamma_nat_add_one 4
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat, harmonic, Finset.sum_range_succ,
    Finset.sum_range_zero, Complex.sub_re, Complex.ofReal_re, Complex.neg_re] at hvlo hvhi
  rw [hvlo] at hlo
  rw [hvhi] at hhi
  norm_num only [Complex.sub_re, Complex.zero_re, Complex.ofReal_re, Complex.div_ofNat_re,
    ← Complex.ofReal_ofNat] at hlo hhi
  change (Complex.digamma (r : ℂ)).re ≤ 25 / 12 - Real.eulerMascheroniConstant at hhi
  apply abs_le.mpr
  constructor
  · linarith only [hlo, Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths,
      real_log_pi_le_six_fifths]
  · have he := Real.one_half_lt_eulerMascheroniConstant
    have hp := Real.log_nonneg (Real.pi_gt_three.le.trans' (by norm_num only : (1 : ℝ) ≤ 3))
    linarith only [hhi, he, hp]

end PseudoPrime.AnalyticNumberTheory.Gamma
