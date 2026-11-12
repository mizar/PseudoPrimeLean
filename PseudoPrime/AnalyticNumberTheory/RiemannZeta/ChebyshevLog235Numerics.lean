/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import PseudoPrime.Analysis.PreciseLogTaylorBounds

/-! # Rational logarithm bounds for the 23.5 scale -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A checked rational Taylor enclosure bounds the logarithm of `47/2`.
The two endpoints are used in the initial Lee–Nosal gap calculation. -/
theorem log_47_div_two_bounds :
    (3157000 / 1000000 : ℝ) ≤ Real.log (47 / 2 : ℝ) ∧
      Real.log (47 / 2 : ℝ) ≤ 3157001 / 1000000 := by
  have h :=
    Analysis.preciseLogCheck_sound (N := (47 / 2 : ℚ)) (j := 5) (n := 32) (lo := 3157000 / 1000000)
      (hi := 3157001 / 1000000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  constructor
  · linarith only [h.1]
  · linarith only [h.2]

/-- A checked rational Taylor enclosure bounds the logarithm of `235/12`.
This is the logarithmic width at the initial scale `L = 47/2`. -/
theorem log_235_div_twelve_bounds :
    (2974678 / 1000000 : ℝ) ≤ Real.log (235 / 12 : ℝ) ∧
      Real.log (235 / 12 : ℝ) ≤ 2974679 / 1000000 := by
  have h :=
    Analysis.preciseLogCheck_sound (N := (235 / 12 : ℚ)) (j := 5) (n := 32) (lo :=
      2974678 / 1000000) (hi := 2974679 / 1000000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  constructor
  · linarith only [h.1]
  · linarith only [h.2]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
