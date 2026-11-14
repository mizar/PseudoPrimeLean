/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstNineBlocks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTenthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTenthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEleventhData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationEleventhBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTwelfthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationTwelfthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstSevenBlocks

/-! # Additional certified phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The tenth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseTenthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7367 / 500 : ℝ) (7429 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7367 / 500 : ℚ) : ℝ)) ((((7367 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7367 / 500) phaseTenthBlockLower phaseTenthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseTenthBlock_walks
      phaseTenthBlock_budgets hv'

/-- The eleventh phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseEleventhBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7429 / 500 : ℝ) (7491 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7429 / 500 : ℚ) : ℝ)) ((((7429 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7429 / 500) phaseEleventhBlockLower phaseEleventhBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseEleventhBlock_walks
      phaseEleventhBlock_budgets hv'

/-- The twelfth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseTwelfthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7491 / 500 : ℝ) (7553 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7491 / 500 : ℚ) : ℝ)) ((((7491 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7491 / 500) phaseTwelfthBlockLower phaseTwelfthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseTwelfthBlock_walks
      phaseTwelfthBlock_budgets hv'

/-- The first twelve phase blocks give the phase bound 51/100 throughout
the stated interval, under the low-zero bracket conditions. -/
theorem phaseFirstTwelveBlocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7553 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases h0 : v ≤ 7367 / 500
  · exact phaseFirstNineBlocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 7429 / 500
    · exact phaseTenthBlock_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · by_cases h2 : v ≤ 7491 / 500
      · exact phaseEleventhBlock_bound g hl hu ⟨le_of_not_ge h1, h2⟩
      · exact phaseTwelfthBlock_bound g hl hu ⟨le_of_not_ge h2, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
