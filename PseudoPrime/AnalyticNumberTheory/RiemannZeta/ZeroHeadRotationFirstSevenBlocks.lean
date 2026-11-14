/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstFiveBlocks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixthData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSixthBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSeventhData
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationSeventhBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstBlockBound

/-! # Two additional certified phase blocks -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A successful 32-node phase block with the stated rational budget gives the
phase bound 51/100, uniformly on its log-height interval. -/
private theorem phase_block_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) (A : ℚ) (lo hi : ℕ → Fin 29 → ℚ)
    (hA : (13 : ℝ) ≤ A ∧ (A : ℝ) ≤ 16)
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
          rationalOrdinateBudgetCheck (1 / 2) 21 phase1381Lower phase1381Upper (lo j) (hi j) = true)
    {v : ℝ} (hv : v ∈ Set.Icc (A : ℝ) ((A : ℝ) + 31 / 250)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
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
    phase100_le_of_rotation_walks g A (1 / 2) phase1381Lower phase1381Upper lo hi 31 hpos hu
      phase1381_lower_pos phase1381_lower_lt_upper hg (by norm_num only) hVa hV
      phase1381_samples_in_range hc hb hv
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  linarith only [h]

/-- The sixth phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseSixthBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7119 / 500 : ℝ) (7181 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7119 / 500 : ℚ) : ℝ)) ((((7119 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7119 / 500) phaseSixthBlockLower phaseSixthBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseSixthBlock_walks
      phaseSixthBlock_budgets hv'

/-- The seventh phase block is bounded by 51/100 on its full interval,
under the low-zero bracket conditions. -/
theorem phaseSeventhBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (7181 / 500 : ℝ) (7243 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  have hv' : v ∈ Set.Icc (((7181 / 500 : ℚ) : ℝ)) ((((7181 / 500 : ℚ) : ℝ)) + (31 : ℝ) / 250) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at ⊢
    norm_num only at hv ⊢
    exact hv
  exact
    phase_block_bound g hl hu (7181 / 500) phaseSeventhBlockLower phaseSeventhBlockUpper
      (by constructor <;> norm_num only [Rat.cast_div, Rat.cast_ofNat]) phaseSeventhBlock_walks
      phaseSeventhBlock_budgets hv'

/-- The first seven phase blocks give the phase bound 51/100 throughout
[13.81, 14.486], under the low-zero bracket conditions. -/
theorem phaseFirstSevenBlocks_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (7243 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
  by_cases h0 : v ≤ 7119 / 500
  · exact phaseFirstFiveBlocks_of_bounds g hl hu ⟨hv.1, h0⟩
  · by_cases h1 : v ≤ 7181 / 500
    · exact phaseSixthBlock_bound g hl hu ⟨le_of_not_ge h0, h1⟩
    · exact phaseSeventhBlock_bound g hl hu ⟨le_of_not_ge h1, hv.2⟩

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
