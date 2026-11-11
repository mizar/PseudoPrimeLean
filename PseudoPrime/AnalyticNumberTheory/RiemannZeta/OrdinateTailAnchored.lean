/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailSplit
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTailError
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics

/-! # Ordinate tails from a finite zero count and an upper anchor -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a positive-height zero-count error at most `log t` on `[a, b]`
and the displayed inverse-square tail bound at `b` imply the standard tail
bound at `a ≥ 1000`. Split the tail and use the finite Abel count estimate. -/
theorem ordinateTail_of_finite_count (hRH : RiemannHypothesis) {a b : ℝ} (ha : 1000 ≤ a)
    (hab : a ≤ b)
    (hQ :
      ∀ t ∈ Set.Icc a b,
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hAnchor :
      ordinateTail b ≤ (1 / Real.pi) * (Real.log b - Real.log (2 * Real.pi) + 1) / b + 1 / b ^ 2) :
    ordinateTail a ≤ Real.log a / (Real.pi * a) := by
  have ha0 : 0 < a := by linarith only [ha]
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hM :
    ContinuousOn (fun t : ℝ ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)
      (Set.Icc a b) := by
    intro t ht
    have ht0 : t ≠ 0 := ne_of_gt (lt_of_lt_of_le ha0 ht.1)
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have hQ2 :
    ∀ t ∈ Set.Icc a b,
      |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
        2 * Real.log t := by
    intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le ha0 ht.1
    have hlog := Real.log_div ht0.ne' hpi.ne'
    have hcount := zeroCount_eq_two_positive hRH ht0.le
    have hterm := hQ t ht
    have heq :
      zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4) =
        2 *
          (positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)) := by
      rw [hcount, hlog]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring
    rw [heq, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
    nlinarith only [hterm]
  have hf :=
    finite_tail_of_log_error (k := 1 / Real.pi) (c := Real.log (2 * Real.pi)) (d := 7 / 4)
      (by linarith only [ha]) hab hM hQ2
  have hs := ordinateTail_split hRH ha0.le hab
  have hpre :
    ordinateTail a ≤
      (1 / Real.pi) * (Real.log a - Real.log (2 * Real.pi) + 1) / a +
        (4 * Real.log a + 1) / a ^ 2 := by
    linarith only [hf, hs, hAnchor]
  apply zero_tail_of_preliminary ha
  rw [Real.log_div ha0.ne' hpi.ne']
  convert hpre using 1
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
