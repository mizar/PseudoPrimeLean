/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstFourteenBlocks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifteenthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifteenthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixteenthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixteenthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstSevenBlocks

/-! # Additional certified phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The fifteenth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseFifteenthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7677 / 500 : ℝ) (7739 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7677 / 500 : ℚ) : ℝ)) ((((7677 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7677 / 500) phaseFifteenthBlockLower phaseFifteenthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseFifteenthBlock_walks
      phaseFifteenthBlock_budgets hv'

/-- The sixteenth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseSixteenthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7739 / 500 : ℝ) (7801 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7739 / 500 : ℚ) : ℝ)) ((((7739 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7739 / 500) phaseSixteenthBlockLower phaseSixteenthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseSixteenthBlock_walks
      phaseSixteenthBlock_budgets hv'

/-- The first sixteen phase blocks give the phase bound 51/100 throughout
the stated interval, under the low-zero bracket conditions. -/
theorem phaseFirstSixteenBlocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7801 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases h0 : v ≤ 7677 / 500
  · exact phaseFirstFourteenBlocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 7739 / 500
    · exact phaseFifteenthBlock_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · exact phaseSixteenthBlock_bound g hl hu ⟨le_of_not_ge h1, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
