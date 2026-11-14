/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstSixteenBlocks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock017Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock017Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstSevenBlocks

/-! # The first seventeen certified phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The seventeenth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseBlock017Block_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7801 / 500 : ℝ) (7863 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7801 / 500 : ℚ) : ℝ)) ((((7801 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7801 / 500) phaseBlock017BlockLower phaseBlock017BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock017Block_walks
      phaseBlock017Block_budgets hv'

/-- The first seventeen phase blocks give the bound 51/100 throughout
[13.81, 15.726], under the low-zero bracket conditions. -/
theorem phaseFirstSeventeenBlocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7863 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases h : v ≤ 7801 / 500
  · exact phaseFirstSixteenBlocks_of_bounds g hl hu ⟨hv.1, h⟩
  · exact phaseBlock017Block_bound g hl hu ⟨le_of_not_ge h, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
