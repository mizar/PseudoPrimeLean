/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstTwelveBlocks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirteenthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationThirteenthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourteenthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFourteenthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstSevenBlocks

/-! # Additional certified phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The thirteenth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseThirteenthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7553 / 500 : ℝ) (7615 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7553 / 500 : ℚ) : ℝ)) ((((7553 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7553 / 500) phaseThirteenthBlockLower phaseThirteenthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseThirteenthBlock_walks
      phaseThirteenthBlock_budgets hv'

/-- The fourteenth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseFourteenthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7615 / 500 : ℝ) (7677 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7615 / 500 : ℚ) : ℝ)) ((((7615 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7615 / 500) phaseFourteenthBlockLower phaseFourteenthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseFourteenthBlock_walks
      phaseFourteenthBlock_budgets hv'

/-- The first fourteen phase blocks give the phase bound 51/100 throughout
the stated interval, under the low-zero bracket conditions. -/
theorem phaseFirstFourteenBlocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7677 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases h0 : v ≤ 7553 / 500
  · exact phaseFirstTwelveBlocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 7615 / 500
    · exact phaseThirteenthBlock_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · exact phaseFourteenthBlock_bound g hl hu ⟨le_of_not_ge h1, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
