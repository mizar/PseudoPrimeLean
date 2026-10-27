/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.NumericalDigammaBounds

/-! # Finite-prefix lower bounds for the real digamma function

Positive reciprocal differences give explicit rational lower bounds.
These bound real Gamma-factor corrections at individual resolvent nodes.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For 0<a≤r and any natural prefix length m, the sum of the first m reciprocal
 differences is at most Re(digamma(r)-digamma(a)). Use the convergent resolvent series,
 nonnegative real summands and finite-sum comparison with the infinite sum.
 This gives explicit lower bounds without numerical differentiation. -/
theorem real_digamma_difference_ge_prefix {a r : ℝ} (ha : 0 < a) (har : a ≤ r) (m : ℕ) :
    (∑ k ∈ Finset.range m, (1 / (a + k) - 1 / (r + k))) ≤
      (Complex.digamma (r : ℂ)).re - (Complex.digamma (a : ℂ)).re := by
  have hr := ha.trans_le har
  have h := digamma_sub_eq_resolventSeries (s := (r : ℂ)) (t := (a : ℂ)) hr ha
  have hs := summable_resolventDifference (s := (a : ℂ)) (t := (r : ℂ)) ha.le hr.le
  have he (k : ℕ) : (1 / ((a : ℂ) + k) - 1 / ((r : ℂ) + k)).re = 1 / (a + k) - 1 / (r + k) := by
    simp only [← Complex.ofReal_natCast, ← Complex.ofReal_add, ← Complex.ofReal_one,
      ← Complex.ofReal_div, ← Complex.ofReal_sub, Complex.ofReal_re]
  have hn (k : ℕ) : 0 ≤ (1 / ((a : ℂ) + k) - 1 / ((r : ℂ) + k)).re := by
    rw [he]
    exact
      sub_nonneg.mpr
        (one_div_le_one_div_of_le (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg k))
          (add_le_add_left har k))
  have hsum := Summable.sum_le_tsum (Finset.range m) (fun k _ ↦ hn k) (Complex.reCLM.summable hs)
  have hre := congrArg Complex.re h
  rw [Complex.sub_re, Complex.re_tsum hs] at hre
  calc
    _ = ∑ k ∈ Finset.range m, (1 / ((a : ℂ) + k) - 1 / ((r : ℂ) + k)).re :=
      Finset.sum_congr rfl (fun k _ ↦ (he k).symm)
    _ ≤ ∑' k : ℕ, (1 / ((a : ℂ) + k) - 1 / ((r : ℂ) + k)).re := hsum
    _ = _ := hre.symm

/-- The logarithmic normalization is at most 6/5. Use the logarithm tangent bound
 at three and the certified pi and log-three bounds. This is the lower Gamma endpoint cost. -/
private theorem prefix_log_pi_le_six_fifths : Real.log Real.pi ≤ 6 / 5 := by
  have h := Real.log_le_sub_one_of_pos (div_pos Real.pi_pos (by norm_num only : (0 : ℝ) < 3))
  rw [Real.log_div Real.pi_pos.ne' (by norm_num only : (3 : ℝ) ≠ 0)] at h
  linarith only [h, Real.pi_lt_d2, Real.log_three_lt_d9]

/-- The normalization log(pi) is at least one. Compare pi with exp(1)
 using the certified numerical constants. This supplies the upper Gamma endpoint cost. -/
theorem real_log_pi_ge_one : (1 : ℝ) ≤ Real.log Real.pi := by
  apply (Real.le_log_iff_exp_le Real.pi_pos).mpr
  have he := Real.exp_one_lt_d9.le
  have hp := Real.pi_gt_three
  linarith only [he, hp]

/-- For 1/2≤R≤r≤17/4 and any prefix length m, the real Gamma correction is bounded
 by the stated maximum of 3/10 and an explicit reciprocal-prefix expression.
 Use the lower digamma prefix from one half and the exact upper value at five.
 This supplies rational, parity-uniform per-node Gamma allowances. -/
theorem real_archimedean_correction_bound_of_prefix {R r : ℝ} (hR : 1 / 2 ≤ R) (hRr : R ≤ r)
    (hu : r ≤ 17 / 4) (m : ℕ) :
    |((Complex.digamma (r : ℂ)).re - Real.log Real.pi) / 2| ≤
      max (3 / 10 : ℝ)
        ((159 / 50 - ∑ k ∈ Finset.range m, (1 / ((1 / 2 : ℝ) + k) - 1 / (R + k))) / 2) := by
  have hR0 : 0 < R := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hR
  have hr0 := hR0.trans_le hRr
  have hp := real_digamma_difference_ge_prefix (by norm_num only : (0 : ℝ) < 1 / 2) hR m
  have hlo := re_digamma_mono_of_pos hR0 hRr
  have hhi := re_digamma_mono_of_pos hr0 (hu.trans (by norm_num only : (17 / 4 : ℝ) ≤ 5))
  have hhalf :
    (Complex.digamma ((1 / 2 : ℝ) : ℂ)).re = -2 * Real.log 2 - Real.eulerMascheroniConstant := by
    rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.digamma_one_half]
    norm_num only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.log_re,
      Complex.norm_ofNat, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    change
      -2 * Real.log 2 - -(0 : ℝ) * (Complex.log 2).im - Real.eulerMascheroniConstant =
        -2 * Real.log 2 - Real.eulerMascheroniConstant
    simp only [neg_zero, zero_mul, sub_zero]
  rw [hhalf] at hp
  have hv := Complex.digamma_nat_add_one 4
  norm_num only [Nat.reduceAdd, Nat.cast_ofNat] at hv
  norm_num only [Complex.ofReal_ofNat] at hhi
  rw [hv] at hhi
  norm_num only [Complex.sub_re, Complex.div_ofNat_re, Complex.ofReal_re, harmonic,
    Finset.sum_range_succ, Finset.sum_range_zero] at hhi
  change (Complex.digamma (r : ℂ)).re ≤ 25 / 12 - Real.eulerMascheroniConstant at hhi
  have hc0 :=
    le_max_left (3 / 10 : ℝ)
      ((159 / 50 - ∑ k ∈ Finset.range m, (1 / ((1 / 2 : ℝ) + k) - 1 / (R + k))) / 2)
  have hcp :=
    le_max_right (3 / 10 : ℝ)
      ((159 / 50 - ∑ k ∈ Finset.range m, (1 / ((1 / 2 : ℝ) + k) - 1 / (R + k))) / 2)
  apply abs_le.mpr
  constructor
  · have h2 : Real.log (2 : ℝ) ≤ 7 / 10 := Real.log_two_lt_d9.le.trans (by norm_num only)
    linarith only [hp, hlo, h2, Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths,
      prefix_log_pi_le_six_fifths, hcp]
  · linarith only [hhi, Real.one_half_lt_eulerMascheroniConstant, real_log_pi_ge_one, hc0]

end PseudoPrime.AnalyticNumberTheory.Gamma
