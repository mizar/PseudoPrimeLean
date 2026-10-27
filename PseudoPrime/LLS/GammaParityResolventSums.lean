/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaResolventRationalBounds
public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries

/-! # Cancellation-preserving reciprocal sums for the Gamma parity tails -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For two positive real bases, the reciprocal differences form a summable
real series. Transfer the proved complex resolvent summability through the
continuous real-part map; neither reciprocal series is separated. -/
theorem summable_real_reciprocal_difference {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Summable (fun n : ℕ ↦ 1 / (b + n) - 1 / (a + n)) := by
  have h :=
    AnalyticNumberTheory.Gamma.summable_resolventDifference (s := (b : ℂ)) (t := (a : ℂ))
      (by simpa only [Complex.ofReal_re] using hb.le)
      (by simpa only [Complex.ofReal_re] using ha.le)
  apply Complex.summable_ofReal.mp
  simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
    Complex.ofReal_natCast] using h

/-- The sum of the real reciprocal differences is the real part of the digamma
difference for positive bases. The proof maps the convergent complex series,
keeping each reciprocal difference intact throughout the calculation. -/
theorem tsum_real_reciprocal_difference {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    (∑' n : ℕ, (1 / (b + n) - 1 / (a + n))) =
      (Complex.digamma (a : ℂ) - Complex.digamma (b : ℂ)).re := by
  have h :=
    AnalyticNumberTheory.Gamma.digamma_sub_eq_resolventSeries (s := (a : ℂ)) (t := (b : ℂ))
      (by simpa only [Complex.ofReal_re] using ha) (by simpa only [Complex.ofReal_re] using hb)
  have hs := (summable_real_reciprocal_difference ha hb)
  have hC : Summable (fun n : ℕ ↦ ((1 / (b + n) - 1 / (a + n) : ℝ) : ℂ)) :=
    Complex.summable_ofReal.mpr hs
  have he :
    (∑' n : ℕ, ((1 / (b + n) - 1 / (a + n) : ℝ) : ℂ)) =
      Complex.digamma (a : ℂ) - Complex.digamma (b : ℂ) := by
    simpa only [Complex.ofReal_sub, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
      Complex.ofReal_natCast] using h.symm
  have hr := congrArg Complex.re he
  rw [Complex.re_tsum hC] at hr
  simpa only [Complex.ofReal_re] using hr

/-- The even-parity tail error has sum 2 log 2. Evaluate the digamma difference
at one and one half; the Euler constants cancel before taking real parts.
This is the exact coefficient of the reciprocal-scale error in the even tail. -/
theorem tsum_even_gamma_reciprocal_error :
    (∑' n : ℕ, (1 / (1 / 2 + (n : ℝ)) - 1 / (1 + (n : ℝ)))) = 2 * Real.log 2 := by
  rw [tsum_real_reciprocal_difference (by norm_num only : (0 : ℝ) < 1)
      (by norm_num only : (0 : ℝ) < 1 / 2)]
  norm_num only [Complex.ofReal_one, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.digamma_one,
    Complex.digamma_one_half, Complex.sub_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, Complex.log_ofReal_re, show (2 : ℂ).re = (2 : ℝ) from rfl,
    show (2 : ℂ).im = (0 : ℝ) from rfl, Complex.neg_im, zero_mul, mul_zero, sub_zero,
    abs_of_pos (by norm_num only : (0 : ℝ) < 2)]
  have hl : (Complex.log 2).re = Real.log 2 := by
    have h := congrArg Complex.re (Complex.ofReal_log (by norm_num only : (0 : ℝ) ≤ 2))
    norm_num only [Complex.ofReal_re, Complex.ofReal_ofNat] at h
    exact h.symm
  rw [hl]
  ring

/-- The odd-parity tail error has sum 2(1-log 2). The digamma recurrence
at one half reduces the sum to the even-parity special values. This supplies
the exact error coefficient without splitting either divergent reciprocal sum. -/
theorem tsum_odd_gamma_reciprocal_error :
    (∑' n : ℕ, (1 / (1 + (n : ℝ)) - 1 / (3 / 2 + (n : ℝ)))) = 2 * (1 - Real.log 2) := by
  rw [tsum_real_reciprocal_difference (by norm_num only : (0 : ℝ) < 3 / 2)
      (by norm_num only : (0 : ℝ) < 1)]
  have hp : ∀ m : ℕ, (1 / 2 : ℂ) ≠ -(m : ℂ) :=
    AnalyticNumberTheory.Gamma.not_neg_nat_of_re_pos
      (by norm_num only [Complex.div_ofNat_re, Complex.one_re])
  have hG := Complex.digamma_apply_add_one (1 / 2 : ℂ) hp
  have hEq : ((3 / 2 : ℝ) : ℂ) = (1 / 2 : ℂ) + 1 := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
  rw [hEq, hG]
  norm_num only [Complex.ofReal_one, Complex.digamma_one, Complex.digamma_one_half, Complex.sub_re,
    Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.neg_im, zero_mul, mul_zero, sub_zero, show (2 : ℂ).re = (2 : ℝ) from rfl,
    show (2 : ℂ).im = (0 : ℝ) from rfl, Complex.div_re, Complex.normSq_ofNat, Complex.one_re,
    Complex.one_im, zero_div, add_zero]
  have hl : (Complex.log 2).re = Real.log 2 := by
    have h := congrArg Complex.re (Complex.ofReal_log (by norm_num only : (0 : ℝ) ≤ 2))
    norm_num only [Complex.ofReal_re, Complex.ofReal_ofNat] at h
    exact h.symm
  rw [hl]
  ring

end PseudoPrime.LLS.PaperStatements
