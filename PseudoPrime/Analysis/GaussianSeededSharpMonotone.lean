/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSeededSharpComparison

/-! # Monotonicity of the sharp seeded candidates and their selected minimum -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Each sharp seeded raw root is monotone on the whole real scale.
Apply the quadratic-root monotonicity theorem to its positive affine conductor term. -/
theorem gaussianSeededSharp_raw_mono (f : Bool) : Monotone (gaussianSeededSharpRawRoot f) := by
  intro a b hab
  change
    gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
        (gaussianMRRefinedConductor * a + gaussianSeededSharpConstant f) ≤
      gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
        (gaussianMRRefinedConductor * b + gaussianSeededSharpConstant f)
  exact
    gaussianBudgetRoot_mono gaussianMRRefined_coefficients.1
      (add_le_add
        (mul_le_mul_of_nonneg_left hab
          (by norm_num only [gaussianMRRefinedConductor] : (0 : ℝ) ≤ gaussianMRRefinedConductor))
        (le_refl (gaussianSeededSharpConstant f)))

/-- Clipping a monotone raw root at a fixed floor preserves monotonicity. -/
theorem gaussianSeededSharp_root_mono (f : Bool) : Monotone (gaussianSeededSharpRoot f) := by
  intro a b hab
  exact max_le_max (le_refl _) (gaussianSeededSharp_raw_mono f hab)

/-- Each clipped sharp seeded cutoff is monotone for all real scales.
Square its positive root twice and multiply by the positive scale factor. -/
theorem gaussianSeededSharp_bound_mono (f : Bool) : Monotone (gaussianSeededSharpBound f) := by
  intro a b hab
  have h2 :=
    (sq_le_sq₀ (gaussianSeededSharp_root_pos f a).le (gaussianSeededSharp_root_pos f b).le).mpr
      (gaussianSeededSharp_root_mono f hab)
  have h4 := (sq_le_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_le_mul_of_nonneg_left h4 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Below scale 63, the selected seeded function equals its 35000 floor.
The exact first switch lies above 240, independently of analytic assumptions. -/
theorem gaussianSeededSharp_eq_floor {L : ℝ} (hL : L < 63) : gaussianSeededSharp L = 35000 := by
  have hs : L ≤ gaussianSeededSharpSwitch false 35000 := by
    linarith only [hL, gaussianSeededSharp_switch35_bounds.1]
  simp only [gaussianSeededSharp, gaussianSeededSharpSelected, ite_eq_left hs]

/-- The selected sharp seeded function is at least 35000 for every real input.
Resolve the low constant piece or use both certified clipped-profile floors. -/
theorem gaussianSeededSharp_floor (L : ℝ) : (35000 : ℝ) ≤ gaussianSeededSharp L := by
  by_cases hL : L < 63
  · rw [gaussianSeededSharp_eq_floor hL]
  · rw [gaussianSeededSharp_eq_min (le_of_not_gt hL)]
    apply le_min
    · simpa only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, Nat.cast_ofNat] using
        gaussianSeededSharp_cutoff_le false L
    · have h := gaussianSeededSharp_cutoff_le true L
      norm_num only [gaussianSeededSharpCutoff, ite_true, Nat.cast_ofNat] at h
      linarith only [h]

/-- The selected sharp seeded function is monotone on the whole real scale.
Above 63 use the profile minimum; below 63 combine the constant piece and global floor. -/
theorem gaussianSeededSharp_mono : Monotone gaussianSeededSharp := by
  intro a b hab
  by_cases ha : 63 ≤ a
  · rw [gaussianSeededSharp_eq_min ha, gaussianSeededSharp_eq_min (ha.trans hab)]
    exact
      min_le_min (gaussianSeededSharp_bound_mono false hab)
        (gaussianSeededSharp_bound_mono true hab)
  · rw [gaussianSeededSharp_eq_floor (lt_of_not_ge ha)]
    exact gaussianSeededSharp_floor b

end PseudoPrime.Analysis
