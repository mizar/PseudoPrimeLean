/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationRange017To024
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock025Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock025Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock026Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock026Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock027Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock027Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock028Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock028Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock029Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock029Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock030Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock030Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock031Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock031Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock032Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock032Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationRange017To024

/-! # Table-free phase-block interface -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The certified phase block 25 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock025_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8297 / 500 : ℝ) (8359 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8297 / 500 : ℚ) : ℝ)) ((((8297 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8297 / 500) phaseBlock025BlockLower phaseBlock025BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock025Block_walks
      phaseBlock025Block_budgets hv'

/-- The certified phase block 26 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock026_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8359 / 500 : ℝ) (8421 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8359 / 500 : ℚ) : ℝ)) ((((8359 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8359 / 500) phaseBlock026BlockLower phaseBlock026BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock026Block_walks
      phaseBlock026Block_budgets hv'

/-- The certified phase block 27 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock027_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8421 / 500 : ℝ) (8483 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8421 / 500 : ℚ) : ℝ)) ((((8421 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8421 / 500) phaseBlock027BlockLower phaseBlock027BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock027Block_walks
      phaseBlock027Block_budgets hv'

/-- The certified phase block 28 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock028_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8483 / 500 : ℝ) (8545 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8483 / 500 : ℚ) : ℝ)) ((((8483 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8483 / 500) phaseBlock028BlockLower phaseBlock028BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock028Block_walks
      phaseBlock028Block_budgets hv'

/-- The certified phase block 29 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock029_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8545 / 500 : ℝ) (8607 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8545 / 500 : ℚ) : ℝ)) ((((8545 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8545 / 500) phaseBlock029BlockLower phaseBlock029BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock029Block_walks
      phaseBlock029Block_budgets hv'

/-- The certified phase block 30 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock030_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8607 / 500 : ℝ) (8669 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8607 / 500 : ℚ) : ℝ)) ((((8607 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8607 / 500) phaseBlock030BlockLower phaseBlock030BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock030Block_walks
      phaseBlock030Block_budgets hv'

/-- The certified phase block 31 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock031_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8669 / 500 : ℝ) (8731 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8669 / 500 : ℚ) : ℝ)) ((((8669 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8669 / 500) phaseBlock031BlockLower phaseBlock031BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock031Block_walks
      phaseBlock031Block_budgets hv'

/-- The certified phase block 32 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock032_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8731 / 500 : ℝ) (8793 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8731 / 500 : ℚ) : ℝ)) ((((8731 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8731 / 500) phaseBlock032BlockLower phaseBlock032BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock032Block_walks
      phaseBlock032Block_budgets hv'

/-- The certified phase blocks through 32 give the phase bound
61/100 on their combined interval, under the low-zero bracket conditions. -/
theorem phaseFirst032Blocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (8793 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  by_cases h0 : v ≤ 8297 / 500
  · exact phaseFirst024Blocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 8359 / 500
    · exact phaseBlock025_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · by_cases h2 : v ≤ 8421 / 500
      · exact phaseBlock026_bound g hl hu ⟨le_of_not_ge h1, h2⟩
      · by_cases h3 : v ≤ 8483 / 500
        · exact phaseBlock027_bound g hl hu ⟨le_of_not_ge h2, h3⟩
        · by_cases h4 : v ≤ 8545 / 500
          · exact phaseBlock028_bound g hl hu ⟨le_of_not_ge h3, h4⟩
          · by_cases h5 : v ≤ 8607 / 500
            · exact phaseBlock029_bound g hl hu ⟨le_of_not_ge h4, h5⟩
            · by_cases h6 : v ≤ 8669 / 500
              · exact phaseBlock030_bound g hl hu ⟨le_of_not_ge h5, h6⟩
              · by_cases h7 : v ≤ 8731 / 500
                · exact phaseBlock031_bound g hl hu ⟨le_of_not_ge h6, h7⟩
                · exact phaseBlock032_bound g hl hu ⟨le_of_not_ge h7, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
