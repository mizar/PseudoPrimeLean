/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTailRosser
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevOrdinateTail

/-! # Chebyshev bound from a Rosser-type zero count -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the stated Rosser-type positive-height zero-count bound,
the explicit Chebyshev error estimate holds for a cutoff `T ≥ 1000`.
The same count hypothesis supplies the low zero sum and the high tail;
the zero-count estimate itself remains an assumption. -/
theorem psi_error_of_rosser (hRH : RiemannHypothesis) {T x h : ℝ} (hT : 1000 ≤ T) (hh : 0 < h)
    (hx : 1 < x - h)
    (hQ :
      ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
        1 / h := by
  have hbase : 2 * Real.pi * Real.exp 1 ≤ T := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp, hT]
  apply psi_error_of_ordinate_tail hRH hbase hh hx
  · exact fun t ht ↦ hQ t ht.1
  · apply ordinateTail_of_rosser hRH hT
    exact fun t ht ↦ hQ t (hbase.trans ht)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
