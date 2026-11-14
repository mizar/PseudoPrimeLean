/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstTwoBlocks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSecondBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstBlockBound

/-! # Sharper phase bound for the first two blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The first block gives the sharper phase bound 127/250 under the low-zero
bracket conditions, by retaining the exact interpolation budget. -/
theorem phaseFirstBlock_sharp (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (6919 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (127 / 250 : ℝ) := by
  have hg := phase1381_brackets_of_bounds g hl hu
  have hpos : ∀ i, 0 ≤ g i := fun i ↦ (phase1381_lower_pos i).le.trans (hg i).1
  have hV : ∀ j : ℕ, j ≤ 7 → |(((1381 / 100 : ℚ) + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21 := by
    intro j hj
    have hj' : (j : ℝ) ≤ 7 := (Nat.cast_le).2 hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
    have hp : 0 ≤ (1381 / 100 : ℝ) + (j : ℝ) / 250 := by
      exact add_nonneg (by norm_num only) (div_nonneg hj0 (by norm_num only))
    rw [abs_of_nonneg hp]
    linarith only [hj']
  have hgrid : v ∈ Set.Icc (((1381 / 100 : ℚ) : ℝ)) ((((1381 / 100 : ℚ) : ℝ)) + (7 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  have h :=
    phase100_le_of_rotation_walks g (1381 / 100) (1 / 2) phase1381Lower phase1381Upper
      phaseFirstBlockLower phaseFirstBlockUpper 7 hpos hu phase1381_lower_pos
      phase1381_lower_lt_upper hg (by norm_num only) (by norm_num only) hV
      phase1381_samples_in_range phaseFirstBlock_walks phaseFirstBlock_budgets hgrid
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

/-- The second block gives the same sharper phase bound 127/250 under the
low-zero bracket conditions, by retaining the exact interpolation budget. -/
theorem phaseSecondBlock_sharp (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (6919 / 500 : ℝ) (6933 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (127 / 250 : ℝ) := by
  have hg := phase1381_brackets_of_bounds g hl hu
  have hpos : ∀ i, 0 ≤ g i := fun i ↦ (phase1381_lower_pos i).le.trans (hg i).1
  have hV : ∀ j : ℕ, j ≤ 7 → |(((6919 / 500 : ℚ) + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21 := by
    intro j hj
    have hj' : (j : ℝ) ≤ 7 := (Nat.cast_le).2 hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
    have hp : 0 ≤ (6919 / 500 : ℝ) + (j : ℝ) / 250 := by
      exact add_nonneg (by norm_num only) (div_nonneg hj0 (by norm_num only))
    rw [abs_of_nonneg hp]
    linarith only [hj']
  have hgrid : v ∈ Set.Icc (((6919 / 500 : ℚ) : ℝ)) ((((6919 / 500 : ℚ) : ℝ)) + (7 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  have h :=
    phase100_le_of_rotation_walks g (6919 / 500) (1 / 2) phase1381Lower phase1381Upper
      phaseSecondBlockLower phaseSecondBlockUpper 7 hpos hu phase1381_lower_pos
      phase1381_lower_lt_upper hg (by norm_num only) (by norm_num only) hV
      phase1381_samples_in_range phaseSecondBlock_walks phaseSecondBlock_budgets hgrid
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

/-- The two first blocks bound the signed zero head by 127/250 throughout
[13.81, 13.866], under the low-zero bracket conditions. -/
theorem phaseFirstTwoBlocks_sharp (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (6933 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (127 / 250 : ℝ) := by
  by_cases hs : v ≤ 6919 / 500
  · exact phaseFirstBlock_sharp g hl hu ⟨hv.1, hs⟩
  · exact phaseSecondBlock_sharp g hl hu ⟨le_of_not_ge hs, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
