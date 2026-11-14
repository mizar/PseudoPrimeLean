/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhase
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevPsiRotationGridRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadOrdinate1381
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadRotationFirstBlock
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds

/-! # First block of the two-dimensional phase certificate -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The two internal representations use identical rational endpoints. -/
private theorem phase1381_lower_eq_brackets : ∀ i, phase1381Lower i = lowZero100Lower i := by
  decide +kernel

/-- Existing bracket predicates give the interval used by the finite check. -/
private theorem phase1381_brackets_of_bounds (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) :
    ∀ i, g i ∈ Set.Icc (phase1381Lower i : ℝ) (phase1381Upper i : ℝ) := by
  intro i
  have he := phase1381_lower_eq_brackets i
  have hlow := hl i
  have hupp := hu i
  rw [← he] at hlow hupp
  constructor
  · exact hlow
  · simpa only [phase1381Upper, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hupp

/-- The first eight certified log nodes bound the signed zero head by
51/100 throughout [13.81, 13.838], for every ordinate tuple in the brackets.
The proof includes both ordinate and log-grid interpolation errors. -/
theorem phaseFirstBlock_bound (g : Fin 29 → ℝ) (hl : LowZero100LowerBounds g)
    (hu : LowZero100UpperBounds g) {v : ℝ} (hv : v ∈ Set.Icc (1381 / 100 : ℝ) (6919 / 500 : ℝ)) :
    |zeroHeadPhase g v| ≤ (51 / 100 : ℝ) := by
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

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
