/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstFourBlocks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFifthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstBlockBound

/-! # Five certified phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The fifth block bounds the signed zero head by 51/100 throughout
[14.114, 14.238] under the stated low-zero bracket conditions. -/
theorem phaseFifthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7057 / 500 : ℝ) (7119 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hg := phase1381_brackets_of_bounds g hl hu
  have hpos : ∀ i, 0 ≤ g i := fun i ↦ (phase1381_lower_pos i).le.trans (hg i).1
  have hV : ∀ j : ℕ, j ≤ 31 → |(((7057 / 500 : ℚ) + (j : ℚ) / 250 : ℚ) : ℝ)| ≤ 21 := by
    intro j hj
    have hj' : (j : ℝ) ≤ 31 := (Nat.cast_le).2 hj
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
    have hp : 0 ≤ (7057 / 500 : ℝ) + (j : ℝ) / 250 := by
      exact add_nonneg (by norm_num only) (div_nonneg hj0 (by norm_num only))
    rw [abs_of_nonneg hp]
    linarith only [hj']
  have hgrid :
    v ∈ Set.Icc (((7057 / 500 : ℚ) : ℝ)) ((((7057 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  have h :=
    phase100_le_of_rotation_walks g (7057 / 500) (1 / 2) phase1381Lower phase1381Upper
      phaseFifthBlockLower phaseFifthBlockUpper 31 hpos hu phase1381_lower_pos
      phase1381_lower_lt_upper hg (by norm_num only) (by norm_num only) hV
      phase1381_samples_in_range phaseFifthBlock_walks phaseFifthBlock_budgets hgrid
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

/-- The low-zero bracket conditions imply the phase bound 51/100 throughout
[13.81, 14.238], by joining the first five certified blocks. -/
theorem phaseFirstFiveBlocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7119 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases hs : v ≤ 7057 / 500
  · exact phaseFirstFourBlocks_of_bounds g hl hu ⟨hv.1, hs⟩
  · exact phaseFifthBlock_bound g hl hu ⟨le_of_not_ge hs, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
