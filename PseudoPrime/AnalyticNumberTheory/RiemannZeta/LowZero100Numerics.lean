/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
public import PseudoPrime.Analysis.RationalReciprocalSum
import Mathlib.Tactic

/-! # Rational lower brackets for the first 29 zero ordinates -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The internally generated lower brackets give a paired reciprocal sum
below `11846/10000` for any ordinates above them. The exact rational check
does not assert that the brackets contain zeros. -/
theorem lowZero100_reciprocal_sharp (g : Fin 29 → ℝ) (hg : LowZero100LowerBounds g) :
    (∑ i, (2 : ℝ) / g i) < (11846 / 10000 : ℝ) := by
  have hp : ∀ i, 0 < lowZero100Lower i := by decide +kernel
  have hc : (∑ i, (2 : ℚ) / lowZero100Lower i) < 11846 / 10000 := by decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    Analysis.reciprocal_sum_lt_of_lower lowZero100Lower g hp hg hc

/-- Any 29 real ordinates satisfying the height-100 lower-bracket predicate
have paired reciprocal sum strictly below `237/200`. The proof kernel-checks
the finite rational reciprocal sum and applies the general comparison lemma. -/
theorem lowZero100_reciprocal_lt (g : Fin 29 → ℝ) (hg : LowZero100LowerBounds g) :
    (∑ i, (2 : ℝ) / g i) < 237 / 200 := by
  have hp : ∀ i, 0 < lowZero100Lower i := by decide +kernel
  have hc : (∑ i, (2 : ℚ) / lowZero100Lower i) < 237 / 200 := by decide +kernel
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    Analysis.reciprocal_sum_lt_of_lower lowZero100Lower g hp hg hc

/-- Any 29 ordinates satisfying the upper-bracket predicate obey the paired
linear bound needed to control the midpoint-rule remainder. The finite
rational bound is checked by the kernel without importing any zero proof. -/
theorem lowZero100_linear_lt (g : Fin 29 → ℝ) (hg : LowZero100UpperBounds g) :
    (∑ i : Fin 29, ((2 : ℝ) * g i + 1)) < 3640 := by
  have hs :
    (∑ i : Fin 29, ((2 : ℝ) * g i + 1)) ≤
      ∑ i : Fin 29, ((2 : ℝ) * ((lowZero100Lower i : ℝ) + 1 / 100) + 1) := by
    apply Finset.sum_le_sum
    intro i hi
    linarith only [hg i]
  have hc : (∑ i : Fin 29, ((2 : ℝ) * ((lowZero100Lower i : ℝ) + 1 / 100) + 1)) < 3640 := by
    have h : ((∑ i : Fin 29, ((2 : ℚ) * (lowZero100Lower i + 1 / 100) + 1) : ℚ) : ℝ) < 3640 := by
      exact_mod_cast
        (show (∑ i : Fin 29, ((2 : ℚ) * (lowZero100Lower i + 1 / 100) + 1)) < 3640 from by
          decide +kernel)
    simpa only [Rat.cast_sum, Rat.cast_add, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat,
      Rat.cast_one] using h
  exact hs.trans_lt hc

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
