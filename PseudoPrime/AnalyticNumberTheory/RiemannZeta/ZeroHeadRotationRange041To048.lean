/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationRange033To040
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock041Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock041Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock042Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock042Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock043Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock043Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock044Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock044Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock045Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock045Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock046Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock046Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock047Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock047Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock048Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock048Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationRange017To024

/-! # Table-free phase-block interface -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The certified phase block 41 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock041_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9289 / 500 : ℝ) (9351 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9289 / 500 : ℚ) : ℝ)) ((((9289 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9289 / 500) phaseBlock041BlockLower phaseBlock041BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock041Block_walks
      phaseBlock041Block_budgets hv'

/-- The certified phase block 42 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock042_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9351 / 500 : ℝ) (9413 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9351 / 500 : ℚ) : ℝ)) ((((9351 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9351 / 500) phaseBlock042BlockLower phaseBlock042BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock042Block_walks
      phaseBlock042Block_budgets hv'

/-- The certified phase block 43 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock043_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9413 / 500 : ℝ) (9475 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9413 / 500 : ℚ) : ℝ)) ((((9413 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9413 / 500) phaseBlock043BlockLower phaseBlock043BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock043Block_walks
      phaseBlock043Block_budgets hv'

/-- The certified phase block 44 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock044_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9475 / 500 : ℝ) (9537 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9475 / 500 : ℚ) : ℝ)) ((((9475 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9475 / 500) phaseBlock044BlockLower phaseBlock044BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock044Block_walks
      phaseBlock044Block_budgets hv'

/-- The certified phase block 45 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock045_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9537 / 500 : ℝ) (9599 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9537 / 500 : ℚ) : ℝ)) ((((9537 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9537 / 500) phaseBlock045BlockLower phaseBlock045BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock045Block_walks
      phaseBlock045Block_budgets hv'

/-- The certified phase block 46 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock046_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9599 / 500 : ℝ) (9661 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9599 / 500 : ℚ) : ℝ)) ((((9599 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9599 / 500) phaseBlock046BlockLower phaseBlock046BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock046Block_walks
      phaseBlock046Block_budgets hv'

/-- The certified phase block 47 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock047_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9661 / 500 : ℝ) (9723 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9661 / 500 : ℚ) : ℝ)) ((((9661 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9661 / 500) phaseBlock047BlockLower phaseBlock047BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock047Block_walks
      phaseBlock047Block_budgets hv'

/-- The certified phase block 48 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock048_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9723 / 500 : ℝ) (9785 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9723 / 500 : ℚ) : ℝ)) ((((9723 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9723 / 500) phaseBlock048BlockLower phaseBlock048BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock048Block_walks
      phaseBlock048Block_budgets hv'

/-- The certified phase blocks through 48 give the phase bound
61/100 on their combined interval, under the low-zero bracket conditions. -/
theorem phaseFirst048Blocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (9785 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  by_cases h0 : v ≤ 9289 / 500
  · exact phaseFirst040Blocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 9351 / 500
    · exact phaseBlock041_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · by_cases h2 : v ≤ 9413 / 500
      · exact phaseBlock042_bound g hl hu ⟨le_of_not_ge h1, h2⟩
      · by_cases h3 : v ≤ 9475 / 500
        · exact phaseBlock043_bound g hl hu ⟨le_of_not_ge h2, h3⟩
        · by_cases h4 : v ≤ 9537 / 500
          · exact phaseBlock044_bound g hl hu ⟨le_of_not_ge h3, h4⟩
          · by_cases h5 : v ≤ 9599 / 500
            · exact phaseBlock045_bound g hl hu ⟨le_of_not_ge h4, h5⟩
            · by_cases h6 : v ≤ 9661 / 500
              · exact phaseBlock046_bound g hl hu ⟨le_of_not_ge h5, h6⟩
              · by_cases h7 : v ≤ 9723 / 500
                · exact phaseBlock047_bound g hl hu ⟨le_of_not_ge h6, h7⟩
                · exact phaseBlock048_bound g hl hu ⟨le_of_not_ge h7, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
