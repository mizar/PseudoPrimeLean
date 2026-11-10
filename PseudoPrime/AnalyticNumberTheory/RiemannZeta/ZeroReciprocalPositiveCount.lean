/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalFromCount
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics

/-! # Reciprocal zero sum from positive-height counting

Connect the standard positive-height count to the two-sided Abel estimate.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a positive-height zero count within `log t` of the stated
main term on `[2πe, b]` implies the reciprocal-height zero-sum bound. Use
conjugation to double the count and apply the two-sided Abel estimate. The
positive-height zero-count estimate remains an explicit hypothesis. -/
theorem reciprocal_of_positive_count (hRH : RiemannHypothesis) {b : ℝ}
    (hb : 2 * Real.pi * Real.exp 1 ≤ b)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) b,
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t) :
    zeroReciprocalSum b ≤ (Real.log (b / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1 := by
  apply zeroReciprocal_of_count_error hRH hb
  intro t ht
  have h0 : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have ht0 : 0 < t := lt_of_lt_of_le h0 ht.1
  have hc : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (by positivity)
  have hlog := Real.log_div ht0.ne' hc
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

/-- Under RH, the stated Rosser-type positive-height count estimate on
`[2πe, b]` implies the reciprocal zero-sum bound. First simplify its error to
`log t`, then apply the positive-height Abel estimate. The Rosser-type estimate
is an explicit hypothesis and is not proved here. -/
theorem reciprocal_of_rosser (hRH : RiemannHypothesis) {b : ℝ} (hb : 2 * Real.pi * Real.exp 1 ≤ b)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) b,
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    zeroReciprocalSum b ≤ (Real.log (b / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1 := by
  apply reciprocal_of_positive_count hRH hb
  intro t ht
  exact (hQ t ht).trans (rosser_error_le_log ht.1)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
