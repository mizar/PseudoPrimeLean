/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.DigammaPrefixBounds

/-! # Positive vertical corrections to the real digamma value -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For positive a, the real reciprocal difference equals the positive rational
correction t^2/(a*(a^2+t^2)). Clear denominators with their proved nonzero values.
This is the algebraic identity behind the vertical digamma series. -/
theorem vertical_resolvent_rational_identity {a t : ℝ} (ha : 0 < a) :
    1 / a - a / (a ^ 2 + t ^ 2) = t ^ 2 / (a * (a ^ 2 + t ^ 2)) := by
  have hb : 0 < a ^ 2 + t ^ 2 := add_pos_of_pos_of_nonneg (sq_pos_of_pos ha) (sq_nonneg t)
  apply (eq_div_iff (mul_pos ha hb).ne').mpr
  calc
    _ = ((1 / a) * a) * (a ^ 2 + t ^ 2) - ((a / (a ^ 2 + t ^ 2)) * (a ^ 2 + t ^ 2)) * a := by ring
    _ = t ^ 2 := by
      rw [div_mul_cancel₀ 1 ha.ne', div_mul_cancel₀ a hb.ne']
      ring

/-- For positive a and real height t, the real part of the reciprocal difference
is t^2/(a*(a^2+t^2)). Compute the complex inverse via its norm square.
This keeps the real-axis digamma value separate from the positive correction. -/
theorem vertical_resolvent_re {a t : ℝ} (ha : 0 < a) :
    (1 / (a : ℂ) - 1 / ((a : ℂ) + Complex.I * t)).re = t ^ 2 / (a * (a ^ 2 + t ^ 2)) := by
  have h1 : (1 / (a : ℂ)).re = 1 / a := by
    rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  rw [Complex.sub_re, h1, one_div ((a : ℂ) + Complex.I * t), Complex.inv_re, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im,
    one_mul, zero_add]
  simpa only [pow_two] using vertical_resolvent_rational_identity (t := t) ha

end PseudoPrime.AnalyticNumberTheory.Gamma

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For positive a, real height t and natural n, shift the reciprocal difference
by n and evaluate its real part. The shift stays in the right half-plane.
This is the term identity used in the convergent correction series. -/
theorem vertical_resolvent_re_add_nat {a t : ℝ} (ha : 0 < a) (n : ℕ) :
    (1 / ((a : ℂ) + n) - 1 / (((a : ℂ) + Complex.I * t) + n)).re =
      t ^ 2 / ((a + n) * ((a + n) ^ 2 + t ^ 2)) := by
  have hz : ((a : ℂ) + Complex.I * t) + n = ((a + (n : ℝ) : ℝ) : ℂ) + Complex.I * t := by
    rw [Complex.ofReal_add, Complex.ofReal_natCast]
    ring
  rw [hz, ← Complex.ofReal_natCast, ← Complex.ofReal_add]
  exact vertical_resolvent_re (add_pos_of_pos_of_nonneg ha (Nat.cast_nonneg n))

/-- For positive a and real height t, the real digamma increment along the vertical
line is the sum of positive rational corrections. Apply the convergent Euler
resolvent identity and commute real parts with the series.
This supports signed Gamma-integral estimates without discarding the real baseline. -/
theorem digamma_vertical_re_sub_eq_tsum {a t : ℝ} (ha : 0 < a) :
    (Complex.digamma ((a : ℂ) + Complex.I * t)).re - (Complex.digamma (a : ℂ)).re =
      ∑' n : ℕ, t ^ 2 / ((a + n) * ((a + n) ^ 2 + t ^ 2)) := by
  have hr : 0 < ((a : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using ha
  have hs := summable_resolventDifference (s := (a : ℂ)) (t := (a : ℂ) + Complex.I * t) ha.le hr.le
  have hd := digamma_sub_eq_resolventSeries (s := (a : ℂ) + Complex.I * t) (t := (a : ℂ)) hr ha
  have h := congrArg Complex.re hd
  rw [Complex.sub_re, Complex.re_tsum hs] at h
  exact h.trans (tsum_congr (vertical_resolvent_re_add_nat ha))

/-- For positive a and real height t, the rational vertical digamma corrections
are summable. Transfer convergence from the complex reciprocal difference series.
This supplies convergence for subsequent integration of the positive correction. -/
theorem summable_vertical_digamma_correction {a t : ℝ} (ha : 0 < a) :
    Summable (fun n : ℕ ↦ t ^ 2 / ((a + n) * ((a + n) ^ 2 + t ^ 2))) := by
  have hr : 0 ≤ ((a : ℂ) + Complex.I * t).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero] using ha.le
  have hs := summable_resolventDifference (s := (a : ℂ)) (t := (a : ℂ) + Complex.I * t) ha.le hr
  exact (Complex.reCLM.summable hs).congr (vertical_resolvent_re_add_nat ha)

end PseudoPrime.AnalyticNumberTheory.Gamma

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For positive a, the real digamma value at height t is at least its value
on the real axis. The convergent correction series has nonnegative summands.
This is the sign interface needed before integrating against a positive kernel. -/
theorem digamma_vertical_re_ge_real {a t : ℝ} (ha : 0 < a) :
    (Complex.digamma (a : ℂ)).re ≤ (Complex.digamma ((a : ℂ) + Complex.I * t)).re := by
  apply sub_nonneg.mp
  rw [digamma_vertical_re_sub_eq_tsum ha]
  exact
    tsum_nonneg
      (fun n ↦
        div_nonneg (sq_nonneg t)
          (mul_nonneg (add_nonneg ha.le (Nat.cast_nonneg n))
            (add_nonneg (sq_nonneg _) (sq_nonneg t))))

end PseudoPrime.AnalyticNumberTheory.Gamma
