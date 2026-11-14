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
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock018Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock018Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock019Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock019Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock020Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock020Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock021Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock021Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock022Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock022Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock023Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock023Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock024Data
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationBlock024Block
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstSevenBlocks
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstBlockBound

/-! # Table-free phase-block interface -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A successful 3/5 budget gives the uniform bound 61/100. -/
private theorem phase_block_wide_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) (A : ℚ) (lo hi : ℕ → Fin 29 → ℚ)
    (hA : (13 : ℝ) ≤ A ∧ (A : ℝ) ≤ 20)
    (hc :
      ∀ i (k : ℕ),
        k ≤ 4 →
          rotationOrdinateGridCheck A
              (phase1381Lower i + (k : ℚ) * (phase1381Upper i - phase1381Lower i) / 4)
              (fun j ↦ lo j i) (fun j ↦ hi j i) 31 =
            true)
    (hb :
      ∀ j : ℕ,
        j ≤ 31 →
          rationalOrdinateBudgetCheck (3 / 5) 21 phase1381Lower phase1381Upper (lo j) (hi j) = true)
    {v : ℝ} (hv : v ∈ Set.Icc (A : ℝ) ((A : ℝ) + 31 / 250)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hg := phase1381_brackets_of_bounds g hl hu
  have hpos : ∀ i, 0 ≤ g i := fun i ↦ (phase1381_lower_pos i).le.trans (hg i).1
  have hVa : |(A : ℝ)| ≤ 21 := by
    rw [abs_of_nonneg (by linarith only [hA.1])]
    linarith only [hA.2]
  have hV : ∀ j : ℕ, j ≤ 31 → |((A + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21 := by
    intro j hj
    have hj' : (j : ℝ) ≤ 31 := (Nat.cast_le).2 hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
    have hp : 0 ≤ (A : ℝ) + (j : ℝ) / 250 := by
      exact add_nonneg (by linarith only [hA.1]) (div_nonneg hj0 (by norm_num only))
    rw [abs_of_nonneg hp]
    linarith only [hA.2, hj']
  have h :=
    phase100_le_of_rotation_walks g A (3 / 5) phase1381Lower phase1381Upper lo hi 31 hpos hu
      phase1381_lower_pos phase1381_lower_lt_upper hg (by norm_num only) hVa hV
      phase1381_samples_in_range hc hb hv
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

/-- The certified phase block 17 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock017_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
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

/-- The certified phase block 18 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock018_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7863 / 500 : ℝ) (7925 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7863 / 500 : ℚ) : ℝ)) ((((7863 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7863 / 500) phaseBlock018BlockLower phaseBlock018BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock018Block_walks
      phaseBlock018Block_budgets hv'

/-- The certified phase block 19 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock019_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7925 / 500 : ℝ) (7987 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7925 / 500 : ℚ) : ℝ)) ((((7925 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7925 / 500) phaseBlock019BlockLower phaseBlock019BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock019Block_walks
      phaseBlock019Block_budgets hv'

/-- The certified phase block 20 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock020_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7987 / 500 : ℝ) (8049 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7987 / 500 : ℚ) : ℝ)) ((((7987 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (7987 / 500) phaseBlock020BlockLower phaseBlock020BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock020Block_walks
      phaseBlock020Block_budgets hv'

/-- The certified phase block 21 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock021_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8049 / 500 : ℝ) (8111 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8049 / 500 : ℚ) : ℝ)) ((((8049 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8049 / 500) phaseBlock021BlockLower phaseBlock021BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock021Block_walks
      phaseBlock021Block_budgets hv'

/-- The certified phase block 22 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock022_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8111 / 500 : ℝ) (8173 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8111 / 500 : ℚ) : ℝ)) ((((8111 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8111 / 500) phaseBlock022BlockLower phaseBlock022BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock022Block_walks
      phaseBlock022Block_budgets hv'

/-- The certified phase block 23 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock023_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8173 / 500 : ℝ) (8235 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8173 / 500 : ℚ) : ℝ)) ((((8173 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8173 / 500) phaseBlock023BlockLower phaseBlock023BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock023Block_walks
      phaseBlock023Block_budgets hv'

/-- The certified phase block 24 gives its stated bound on
its full logarithmic interval, under the low-zero bracket conditions. -/
private theorem phaseBlock024_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (8235 / 500 : ℝ) (8297 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((8235 / 500 : ℚ) : ℝ)) ((((8235 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_wide_bound g hl hu (8235 / 500) phaseBlock024BlockLower phaseBlock024BlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseBlock024Block_walks
      phaseBlock024Block_budgets hv'

/-- The first 17 blocks give the phase bound 51/100 up to
log height 15.726, under the low-zero bracket conditions. -/
theorem phaseFirst017Blocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7863 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases h : v ≤ 7801 / 500
  · exact phaseFirstSixteenBlocks_of_bounds g hl hu ⟨hv.1, h⟩
  · exact phaseBlock017_bound g hl hu ⟨le_of_not_ge h, hv.2⟩

/-- The first 19 blocks give the phase bound 51/100 up to
log height 15.974, under the low-zero bracket conditions. -/
theorem phaseFirst019Blocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7987 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases h0 : v ≤ 7863 / 500
  · exact phaseFirst017Blocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 7925 / 500
    · exact phaseBlock018_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · exact phaseBlock019_bound g hl hu ⟨le_of_not_ge h1, hv.2⟩

/-- The certified phase blocks through 24 give the phase bound
61/100 on their combined interval, under the low-zero bracket conditions. -/
theorem phaseFirst024Blocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (8297 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (61 / 100 : ℝ) := by
  by_cases h0 : v ≤ 7987 / 500
  · have h := phaseFirst019Blocks_of_bounds g hl hu ⟨hv.1, h0⟩
    linarith only [h]
  · by_cases h1 : v ≤ 8049 / 500
    · exact phaseBlock020_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · by_cases h2 : v ≤ 8111 / 500
      · exact phaseBlock021_bound g hl hu ⟨le_of_not_ge h1, h2⟩
      · by_cases h3 : v ≤ 8173 / 500
        · exact phaseBlock022_bound g hl hu ⟨le_of_not_ge h2, h3⟩
        · by_cases h4 : v ≤ 8235 / 500
          · exact phaseBlock023_bound g hl hu ⟨le_of_not_ge h3, h4⟩
          · exact phaseBlock024_bound g hl hu ⟨le_of_not_ge h4, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
