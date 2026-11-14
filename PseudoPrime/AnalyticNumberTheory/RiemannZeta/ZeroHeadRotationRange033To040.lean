/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationRange025To032
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock033Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock033Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock034Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock034Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock035Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock035Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock036Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock036Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock037Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock037Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock038Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock038Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock039Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock039Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock040Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock040Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationRange017To024

/-! # Table-free phase-block interface -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The certified phase block 33 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock033_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8793 / 500 : ℝ) (8855 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8793 / 500 : ℚ) : ℝ)) ((((8793 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8793 / 500) phaseBlock033BlockLower phaseBlock033BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock033Block_walks
      phaseBlock033Block_budgets hv'

/-- The certified phase block 34 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock034_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8855 / 500 : ℝ) (8917 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8855 / 500 : ℚ) : ℝ)) ((((8855 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8855 / 500) phaseBlock034BlockLower phaseBlock034BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock034Block_walks
      phaseBlock034Block_budgets hv'

/-- The certified phase block 35 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock035_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8917 / 500 : ℝ) (8979 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8917 / 500 : ℚ) : ℝ)) ((((8917 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8917 / 500) phaseBlock035BlockLower phaseBlock035BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock035Block_walks
      phaseBlock035Block_budgets hv'

/-- The certified phase block 36 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock036_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8979 / 500 : ℝ) (9041 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8979 / 500 : ℚ) : ℝ)) ((((8979 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8979 / 500) phaseBlock036BlockLower phaseBlock036BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock036Block_walks
      phaseBlock036Block_budgets hv'

/-- The certified phase block 37 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock037_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9041 / 500 : ℝ) (9103 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9041 / 500 : ℚ) : ℝ)) ((((9041 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9041 / 500) phaseBlock037BlockLower phaseBlock037BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock037Block_walks
      phaseBlock037Block_budgets hv'

/-- The certified phase block 38 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock038_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9103 / 500 : ℝ) (9165 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9103 / 500 : ℚ) : ℝ)) ((((9103 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9103 / 500) phaseBlock038BlockLower phaseBlock038BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock038Block_walks
      phaseBlock038Block_budgets hv'

/-- The certified phase block 39 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock039_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9165 / 500 : ℝ) (9227 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9165 / 500 : ℚ) : ℝ)) ((((9165 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9165 / 500) phaseBlock039BlockLower phaseBlock039BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock039Block_walks
      phaseBlock039Block_budgets hv'

/-- The certified phase block 40 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock040_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9227 / 500 : ℝ) (9289 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9227 / 500 : ℚ) : ℝ)) ((((9227 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9227 / 500) phaseBlock040BlockLower phaseBlock040BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock040Block_walks
      phaseBlock040Block_budgets hv'

/-- The certified phase blocks through 40 give the phase bound
61/100 on their combined interval, under the low-zero bracket conditions. -/
theorem phaseFirst040Blocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (9289 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  by_cases h0 : v ≤ 8793 / 500
  · exact phaseFirst032Blocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 8855 / 500
    · exact phaseBlock033_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · by_cases h2 : v ≤ 8917 / 500
      · exact phaseBlock034_bound g hl hu ⟨le_of_not_ge h1, h2⟩
      · by_cases h3 : v ≤ 8979 / 500
        · exact phaseBlock035_bound g hl hu ⟨le_of_not_ge h2, h3⟩
        · by_cases h4 : v ≤ 9041 / 500
          · exact phaseBlock036_bound g hl hu ⟨le_of_not_ge h3, h4⟩
          · by_cases h5 : v ≤ 9103 / 500
            · exact phaseBlock037_bound g hl hu ⟨le_of_not_ge h4, h5⟩
            · by_cases h6 : v ≤ 9165 / 500
              · exact phaseBlock038_bound g hl hu ⟨le_of_not_ge h5, h6⟩
              · by_cases h7 : v ≤ 9227 / 500
                · exact phaseBlock039_bound g hl hu ⟨le_of_not_ge h6, h7⟩
                · exact phaseBlock040_bound g hl hu ⟨le_of_not_ge h7, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
