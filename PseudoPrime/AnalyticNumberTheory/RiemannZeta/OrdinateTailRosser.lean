/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTailError
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalPositiveCount
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics

/-! # Ordinate tail from a Rosser-type zero count -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a positive-height zero-count error bounded by `log t` above
`a ≥ 1000` gives the stated inverse-square ordinate-tail bound. Conjugation
reduces the two-sided count to the assumed positive-height estimate. -/
theorem ordinateTail_of_coarse_count (hRH : RiemannHypothesis) {a : ℝ} (ha : 1000 ≤ a)
    (hQ :
      ∀ t ∈ Set.Ici a,
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    ordinateTail a ≤ Real.log a / (Real.pi * a) := by
  apply ordinateTail_of_count hRH ha
  intro t ht
  change a ≤ t at ht
  have ht0 : 0 < t := by linarith only [ha, ht]
  have hc : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  have hterm := hQ t ht
  have hlog := Real.log_div ht0.ne' hc
  have hcount := zeroCount_eq_two_positive hRH ht0.le
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

/-- Under RH and the stated Rosser-type estimate for all positive-height
zero counts above `a ≥ 1000`, bound the two-sided inverse-square ordinate
tail by `log a / (πa)`. Conjugation supplies the factor two and the count
estimate remains an explicit hypothesis. -/
theorem ordinateTail_of_rosser (hRH : RiemannHypothesis) {a : ℝ} (ha : 1000 ≤ a)
    (hQ :
      ∀ t ∈ Set.Ici a,
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    ordinateTail a ≤ Real.log a / (Real.pi * a) := by
  apply ordinateTail_of_coarse_count hRH ha
  intro t ht
  change a ≤ t at ht
  have hbase : 2 * Real.pi * Real.exp 1 ≤ t := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp, ha, ht]
  exact (hQ t ht).trans (rosser_error_le_log hbase)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
