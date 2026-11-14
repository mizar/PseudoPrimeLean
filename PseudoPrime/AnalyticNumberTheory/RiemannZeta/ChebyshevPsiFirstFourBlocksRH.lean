/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstFourBlocks
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPhaseBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiPhaseScaleRH

/-! # ψ error from the first four certified phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH and the explicit height-100 zero hypotheses, the first four
certified phase blocks give this smoothed ψ error whenever both averaging
midpoints have logarithms in [13.81, 14.114]. -/
theorem psi_error_first_four_blocks (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {T x h D : ℝ} (hT : 100 ≤ T) (hh : 0 < h) (hx : 1 < x - h) (hD : 0 ≤ D)
    (hsqrt : Real.sqrt (x + h) ≤ D) (htail : ((x + h) ^ (3 / 2 : ℝ) + x ^ (3 / 2 : ℝ)) / h ≤ D * T)
    (hlo : Real.log ((x - h + x) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (7057 / 500 : ℝ))
    (hhi : Real.log ((x + (x + h)) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (7057 / 500 : ℝ)) :
    |Chebyshev.psi x - x| ≤
      h / 2 + Real.log (2 * Real.pi) +
        (Real.sqrt (x + h) * (51 / 100) + 3640 * (x - h) ^ (-(3 / 2 : ℝ)) * h ^ 2 / 24) +
        D *
          (((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / T +
            1 / (15 * T ^ 2)) +
        1 / h := by
  apply psi_error_phase_brackets hRH g hmono hpos hheight hzero hcount hl hu hT hh hx hD hsqrt htail
  · exact phaseFirstFourBlocks_of_bounds g hl hu hlo
  · exact phaseFirstFourBlocks_of_bounds g hl hu hhi

/-- Under RH and the stated height-100 zero hypotheses, the first four
phase blocks give the normalized ψ error at an admissible relative width.
Both smoothing midpoints must have logarithms in [13.81, 14.114]. -/
theorem psi_error_first_four_blocks_scale (hRH : RiemannHypothesis) (g : Fin 29 → ℝ)
    (hmono : StrictMono g) (hpos : ∀ i, 0 < g i) (hheight : ∀ i, g i ≤ 100)
    (hzero : ∀ i, riemannZeta (((1 / 2 : ℝ) : ℂ) + (g i : ℂ) * Complex.I) = 0)
    (hcount : zeroCount 100 ≤ 58) (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g)
    {x δ : ℝ} (hx : 0 < x) (hd : 0 < δ) (hd2 : δ ≤ 1 / 2) (hleft : 1 < x - x * δ)
    (hcut : 100 ≤ 2 / δ)
    (hlo : Real.log ((x - x * δ + x) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (7057 / 500 : ℝ))
    (hhi : Real.log ((x + (x + x * δ)) / 2) ∈ Set.Icc (1381 / 100 : ℝ) (7057 / 500 : ℝ)) :
    |Chebyshev.psi x - x| / Real.sqrt x ≤
      Real.sqrt x * δ / 2 + Real.log (2 * Real.pi) / Real.sqrt x +
        ((1 + δ / 4) * (51 / 100) + 3640 * δ ^ 2 * (1 - δ) ^ (-(3 / 2 : ℝ)) / 24) +
        (1 + δ) *
          (((Real.log ((2 / δ) / (2 * Real.pi))) ^ 2 + 2 * Real.log ((2 / δ) / (2 * Real.pi)) + 2) /
                (2 * Real.pi) -
              143 / 125 -
              (3 / 8 : ℝ) / (2 / δ) +
            1 / (15 * (2 / δ) ^ 2)) +
        1 / (x * δ * Real.sqrt x) := by
  apply psi_error_phase_scale hRH g hmono hpos hheight hzero hcount hl hu hx hd hd2 hleft hcut
  · exact phaseFirstFourBlocks_of_bounds g hl hu hlo
  · exact phaseFirstFourBlocks_of_bounds g hl hu hhi

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
