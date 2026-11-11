/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.OrdinateTail
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevFromZeroCount
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountErrorNumerics

/-! # Chebyshev error from a full ordinate tail

Replace finite-ledger tail assumptions with one summable zero-tail bound.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, a `log t` positive-height zero-count error on the stated interval
and the full ordinate-tail estimate imply the displayed Chebyshev bound. The
full tail controls every finite contour ledger. -/
theorem psi_error_of_coarse_tail (hRH : RiemannHypothesis) {T x h : ℝ}
    (hT : 2 * Real.pi * Real.exp 1 ≤ T) (hh : 0 < h) (hx : 1 < x - h)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) T,
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          Real.log t)
    (hTail : ordinateTail T ≤ Real.log T / (Real.pi * T)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
        1 / h := by
  apply psi_error_of_coarse_count hRH hT hh hx hQ
  intro m
  let S :=
    ((riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
              (unifiedTauRectangleUpper 2 m)).filter
          (fun ρ ↦ ¬ρ.re < 0)).filter
      (fun ρ ↦ ¬|ρ.im| ≤ T)
  have hs :=
    finite_ordinate_tail_le hRH S T
      (fun ρ hρ ↦
        (mem_riemannZetaZerosInAnyRectangle_iff.mp
            (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).1).2)
      (fun ρ hρ ↦ not_lt.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hρ).1).2)
      (fun ρ hρ ↦ lt_of_not_ge (Finset.mem_filter.mp hρ).2)
  exact hs.trans hTail

/-- Under RH, the stated Rosser-type positive zero count and the full
inverse-square ordinate-tail estimate imply the displayed Chebyshev bound.
The full-tail estimate bounds every finite contour ledger. Both numerical
zero-count estimates remain explicit hypotheses. -/
theorem psi_error_of_ordinate_tail (hRH : RiemannHypothesis) {T x h : ℝ}
    (hT : 2 * Real.pi * Real.exp 1 ≤ T) (hh : 0 < h) (hx : 1 < x - h)
    (hQ :
      ∀ t ∈ Set.Icc (2 * Real.pi * Real.exp 1) T,
        |positiveZeroCount t -
              (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
          (137 / 1000 : ℝ) * Real.log t + (443 / 1000 : ℝ) * Real.log (Real.log t) + 397 / 250 +
            1 / (5 * t))
    (hTail : ordinateTail T ≤ Real.log T / (Real.pi * T)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        Real.sqrt (x + h) * ((Real.log (T / (2 * Real.pi))) ^ 2 / (2 * Real.pi) + 1) +
        ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h * (Real.log T / (Real.pi * T)) +
        1 / h := by
  apply psi_error_of_coarse_tail hRH hT hh hx ?_ hTail
  intro t ht
  exact (hQ t ht).trans (rosser_error_le_log ht.1)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
