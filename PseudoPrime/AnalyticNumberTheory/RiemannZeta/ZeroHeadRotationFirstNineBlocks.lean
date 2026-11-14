/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstSevenBlocks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEighthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEighthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationNinthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationNinthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstSevenBlocks

/-! # Additional certified phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The eighth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseEighthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7243 / 500 : ℝ) (7305 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7243 / 500 : ℚ) : ℝ)) ((((7243 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7243 / 500) phaseEighthBlockLower phaseEighthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseEighthBlock_walks
      phaseEighthBlock_budgets hv'

/-- The ninth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseNinthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7305 / 500 : ℝ) (7367 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7305 / 500 : ℚ) : ℝ)) ((((7305 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7305 / 500) phaseNinthBlockLower phaseNinthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseNinthBlock_walks
      phaseNinthBlock_budgets hv'

/-- The first nine phase blocks give the phase bound 51/100 throughout
the stated interval, under the low-zero bracket conditions. -/
theorem phaseFirstNineBlocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7367 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases h0 : v ≤ 7243 / 500
  · exact phaseFirstSevenBlocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 7305 / 500
    · exact phaseEighthBlock_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · exact phaseNinthBlock_bound g hl hu ⟨le_of_not_ge h1, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
