/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationRange041To048
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock049Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock049Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock050Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock050Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock051Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock051Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock052Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock052Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationRange017To024

/-! # Table-free phase-block interface -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The certified phase block 49 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock049_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9785 / 500 : ℝ) (9847 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9785 / 500 : ℚ) : ℝ)) ((((9785 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9785 / 500) phaseBlock049BlockLower phaseBlock049BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock049Block_walks
      phaseBlock049Block_budgets hv'

/-- The certified phase block 50 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock050_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9847 / 500 : ℝ) (9909 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9847 / 500 : ℚ) : ℝ)) ((((9847 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9847 / 500) phaseBlock050BlockLower phaseBlock050BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock050Block_walks
      phaseBlock050Block_budgets hv'

/-- The certified phase block 51 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock051_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9909 / 500 : ℝ) (9971 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9909 / 500 : ℚ) : ℝ)) ((((9909 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9909 / 500) phaseBlock051BlockLower phaseBlock051BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock051Block_walks
      phaseBlock051Block_budgets hv'

/-- The certified phase block 52 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock052_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (9971 / 500 : ℝ) (10033 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((9971 / 500 : ℚ) : ℝ)) ((((9971 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (9971 / 500) phaseBlock052BlockLower phaseBlock052BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock052Block_walks
      phaseBlock052Block_budgets hv'

/-- The certified phase blocks through 52 give the phase bound
61/100 on their combined interval, under the low-zero bracket conditions. -/
theorem phaseFirst052Blocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (10033 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  by_cases h0 : v ≤ 9785 / 500
  · exact phaseFirst048Blocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 9847 / 500
    · exact phaseBlock049_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · by_cases h2 : v ≤ 9909 / 500
      · exact phaseBlock050_bound g hl hu ⟨le_of_not_ge h1, h2⟩
      · by_cases h3 : v ≤ 9971 / 500
        · exact phaseBlock051_bound g hl hu ⟨le_of_not_ge h2, h3⟩
        · exact phaseBlock052_bound g hl hu ⟨le_of_not_ge h3, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
