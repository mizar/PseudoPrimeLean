/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPhaseBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhaseGrid100

/-! # ψ error from a finite grid of low-zero phase bounds -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the low-zero bracket and count hypotheses, phase bounds at
grid nodes control the ψ error when both logarithmic smoothing midpoints
lie in the grid interval. The explicit interpolation error is included. -/
theorem psi_error_phase_grid (hRH : RiemannHypothesis) (g : Fin 29 → ℝ) (hmono : StrictMono g)
    (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {T x h D a B : ℝ} {N : ℕ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo : Real.log ((x - h + x) / 2) ∈ Set.Icc a (a + (N : ℝ) / 250))
    (hhi : Real.log ((x + (x + h)) / 2) ∈ Set.Icc a (a + (N : ℝ) / 250))
    (hnodes : ∀ j : ℕ, j ≤ N → |zeroHeadPhase g (a + (j : ℝ) / 250)| ≤ B) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        (Real.sqrt (x + h) * (B + 3611 / 500000) + 3640 * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24) +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  apply psi_error_phase_brackets hRH g hmono hpos hheight hzero hcount hl hu hT hh hx hD hsqrt htail
  · exact phase100_le_of_grid g (fun i ↦ (hpos i).le) hu hlo hnodes
  · exact phase100_le_of_grid g (fun i ↦ (hpos i).le) hu hhi hnodes

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
