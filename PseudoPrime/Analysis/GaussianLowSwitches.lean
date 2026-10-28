/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianLowProfiles

/-! # Rational Gaussian floor switches -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The rational logarithmic scale at which the raw root reaches the floor u. -/
noncomputable def gaussianLowSwitch (u D : ℝ) : ℝ :=
  (gaussianMRRefinedD * u ^ 2 - gaussianMRRefinedBeta * u - D) / gaussianMRRefinedConductor

/-- For nonnegative L and residual, a floor at least nine exceeds the raw root
exactly up to its rational switch. The quadratic budget gives both implications. -/
theorem gaussianLow_raw_le_iff {u D L : ℝ} (hu : 9 ≤ u) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
          (gaussianMRRefinedConductor * L + D) ≤
        u ↔
      L ≤ gaussianLowSwitch u D := by
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hb : gaussianMRRefinedBeta < 9 * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * u := by
    have hm := mul_le_mul_of_nonneg_left hu gaussianMRRefined_coefficients.1.le
    linarith only [hb, hm]
  have hC := add_nonneg (mul_nonneg hc.le hL) hD
  rw [gaussianLowSwitch, le_div_iff₀ hc]
  constructor
  · intro hroot
    have hG :=
      gaussianBudget_of_root_le gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2 hC
        hcoef hroot
    nlinarith only [hG]
  · intro hbudget
    apply
      gaussianBudgetRoot_le_of_budget gaussianMRRefined_coefficients.1
        gaussianMRRefined_coefficients.2 hC hcoef
    nlinarith only [hbudget]

/-- For nonnegative L and residual, the raw root exceeds the floor exactly
after its rational switch. Factor the quadratic difference using its positive factor. -/
theorem gaussianLow_raw_ge_iff {u D L : ℝ} (hu : 9 ≤ u) (hD : 0 ≤ D) (hL : 0 ≤ L) :
    u ≤
        gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
          (gaussianMRRefinedConductor * L + D) ↔
      gaussianLowSwitch u D ≤ L := by
  have hc : 0 < gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hb : gaussianMRRefinedBeta < 9 * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * u := by
    have hm := mul_le_mul_of_nonneg_left hu gaussianMRRefined_coefficients.1.le
    linarith only [hb, hm]
  have hC := add_nonneg (mul_nonneg hc.le hL) hD
  let t :=
    gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta (gaussianMRRefinedConductor * L + D)
  have ht : 0 < t :=
    gaussianBudgetRoot_pos gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2
  have he :
    gaussianMRRefinedD * t ^ 2 = gaussianMRRefinedBeta * t + (gaussianMRRefinedConductor * L + D) :=
    gaussianBudgetRoot_equation gaussianMRRefined_coefficients.1 hC
  have hm : 0 < gaussianMRRefinedD * (t + u) - gaussianMRRefinedBeta := by
    have hp := mul_pos gaussianMRRefined_coefficients.1 ht
    linarith only [hcoef, hp]
  rw [gaussianLowSwitch, div_le_iff₀ hc]
  constructor
  · intro hut
    have hp := mul_nonneg (sub_nonneg.mpr hut) hm.le
    nlinarith only [he, hp]
  · intro hbudget
    by_contra hnot
    have hp := mul_pos (sub_pos.mpr (lt_of_not_ge hnot)) hm
    nlinarith only [he, hp, hbudget]

/-- The Gaussian family is monotone on all real scales, as a minimum of monotone profiles. -/
theorem gaussianLowFamily_mono : Monotone gaussianLowFamily := by
  intro L K hLK
  exact
    min_le_min (GaussianLowProfile.low.bound_mono hLK)
      (min_le_min (GaussianLowProfile.middle.bound_mono hLK)
        (GaussianLowProfile.upper.bound_mono hLK))

/-- Ordered positive profile roots yield ordered cutoffs by squaring twice. -/
theorem gaussianLow_bound_le {f g : GaussianLowProfile} {L : ℝ} (h : f.root L ≤ g.root L) :
    f.bound L ≤ g.bound L := by
  have hsq := (sq_le_sq₀ (f.root_pos L).le (g.root_pos L).le).mpr h
  have hsq2 := (sq_le_sq₀ (sq_nonneg (f.root L)) (sq_nonneg (g.root L))).mpr hsq
  exact mul_le_mul_of_nonneg_left hsq2 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- If the first raw root remains below the second floor, its floored root
is smaller whenever the floors are ordered. -/
theorem gaussianLow_roots_before {u v D E L : ℝ} (huv : u ≤ v)
    (hraw :
      gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
          (gaussianMRRefinedConductor * L + D) ≤
        v) :
    gaussianLowRoot u D L ≤ gaussianLowRoot v E L := by
  exact max_le (huv.trans (le_max_left _ _)) (hraw.trans (le_max_left _ _))

/-- After the second floor lies below the first raw root, the smaller
residual profile has the smaller floored root. -/
theorem gaussianLow_roots_after {u v D E L : ℝ} (hD : E ≤ D)
    (hraw :
      v ≤
        gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
          (gaussianMRRefinedConductor * L + D)) :
    gaussianLowRoot v E L ≤ gaussianLowRoot u D L := by
  apply max_le (hraw.trans (le_max_right _ _))
  apply le_trans (gaussianBudgetRoot_mono gaussianMRRefined_coefficients.1 _) (le_max_right _ _)
  linarith only [hD]

/-- Before the low-to-middle switch, the low profile dominates the middle profile. -/
theorem gaussianLow_low_middle_before {L : ℝ} (hL : 0 ≤ L)
    (h : L ≤ gaussianLowSwitch (19 / 2) (93 / 10)) :
    GaussianLowProfile.low.bound L ≤ GaussianLowProfile.middle.bound L := by
  apply gaussianLow_bound_le
  change gaussianLowRoot (91 / 10) (93 / 10) L ≤ gaussianLowRoot (19 / 2) (163 / 20) L
  apply gaussianLow_roots_before (by norm_num only)
  exact
    (gaussianLow_raw_le_iff (by norm_num only : (9 : ℝ) ≤ 19 / 2)
          (by norm_num only : (0 : ℝ) ≤ 93 / 10) hL).mpr
      h

/-- After the low-to-middle switch, the middle profile dominates the low profile. -/
theorem gaussianLow_middle_low_after {L : ℝ} (hL : 0 ≤ L)
    (h : gaussianLowSwitch (19 / 2) (93 / 10) ≤ L) :
    GaussianLowProfile.middle.bound L ≤ GaussianLowProfile.low.bound L := by
  apply gaussianLow_bound_le
  change gaussianLowRoot (19 / 2) (163 / 20) L ≤ gaussianLowRoot (91 / 10) (93 / 10) L
  apply gaussianLow_roots_after (by norm_num only)
  exact
    (gaussianLow_raw_ge_iff (by norm_num only : (9 : ℝ) ≤ 19 / 2)
          (by norm_num only : (0 : ℝ) ≤ 93 / 10) hL).mpr
      h

/-- Before the middle-to-upper switch, the middle profile dominates the upper profile. -/
theorem gaussianLow_middle_upper_before {L : ℝ} (hL : 0 ≤ L)
    (h : L ≤ gaussianLowSwitch (49 / 5) (163 / 20)) :
    GaussianLowProfile.middle.bound L ≤ GaussianLowProfile.upper.bound L := by
  apply gaussianLow_bound_le
  change gaussianLowRoot (19 / 2) (163 / 20) L ≤ gaussianLowRoot (49 / 5) (813 / 100) L
  apply gaussianLow_roots_before (by norm_num only)
  exact
    (gaussianLow_raw_le_iff (by norm_num only : (9 : ℝ) ≤ 49 / 5)
          (by norm_num only : (0 : ℝ) ≤ 163 / 20) hL).mpr
      h

/-- After the middle-to-upper switch, the upper profile dominates the middle profile. -/
theorem gaussianLow_upper_middle_after {L : ℝ} (hL : 0 ≤ L)
    (h : gaussianLowSwitch (49 / 5) (163 / 20) ≤ L) :
    GaussianLowProfile.upper.bound L ≤ GaussianLowProfile.middle.bound L := by
  apply gaussianLow_bound_le
  change gaussianLowRoot (49 / 5) (813 / 100) L ≤ gaussianLowRoot (19 / 2) (163 / 20) L
  apply gaussianLow_roots_after (by norm_num only)
  exact
    (gaussianLow_raw_ge_iff (by norm_num only : (9 : ℝ) ≤ 49 / 5)
          (by norm_num only : (0 : ℝ) ≤ 163 / 20) hL).mpr
      h

/-- On nonnegative scales, two rational switches select the winning profile.
No numerical root search or analytic hypothesis enters this identity. -/
theorem gaussianLowFamily_selection {L : ℝ} (hL : 0 ≤ L) :
    gaussianLowFamily L =
      if L ≤ gaussianLowSwitch (19 / 2) (93 / 10) then GaussianLowProfile.low.bound L
      else
        if L ≤ gaussianLowSwitch (49 / 5) (163 / 20) then GaussianLowProfile.middle.bound L
        else GaussianLowProfile.upper.bound L := by
  have horder : gaussianLowSwitch (19 / 2) (93 / 10) ≤ gaussianLowSwitch (49 / 5) (163 / 20) := by
    norm_num only [gaussianLowSwitch, gaussianMRRefinedD, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsIndex,
      gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor]
  by_cases hfirst : L ≤ gaussianLowSwitch (19 / 2) (93 / 10)
  · rw [ite_eq_left hfirst]
    exact
      min_eq_left
        (le_min (gaussianLow_low_middle_before hL hfirst)
          ((gaussianLow_low_middle_before hL hfirst).trans
            (gaussianLow_middle_upper_before hL (hfirst.trans horder))))
  · rw [ite_eq_right hfirst]
    have hm := gaussianLow_middle_low_after hL (le_of_not_ge hfirst)
    by_cases hsecond : L ≤ gaussianLowSwitch (49 / 5) (163 / 20)
    · rw [ite_eq_left hsecond]
      change min _ (min _ _) = _
      rw [min_eq_left (gaussianLow_middle_upper_before hL hsecond), min_eq_right hm]
    · rw [ite_eq_right hsecond]
      have hu := gaussianLow_upper_middle_after hL (le_of_not_ge hsecond)
      change min _ (min _ _) = _
      rw [min_eq_right hu, min_eq_right (hu.trans hm)]

/-- Each profile changes from its floor to its raw root at its rational switch.
Together with family selection this gives all five floor and profile boundaries. -/
theorem gaussianLowProfile_floor_selection (f : GaussianLowProfile) {L : ℝ} (hL : 0 ≤ L) :
    f.root L =
      if L ≤ gaussianLowSwitch f.floor f.residual then f.floor
      else
        gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
          (gaussianMRRefinedConductor * L + f.residual) := by
  have hu : (9 : ℝ) ≤ f.floor := by
    have h := f.signs.1; linarith only [h]
  have hiff := gaussianLow_raw_le_iff hu f.signs.2.le hL
  by_cases h : L ≤ gaussianLowSwitch f.floor f.residual
  · rw [ite_eq_left h]
    exact max_eq_left (hiff.mpr h)
  · rw [ite_eq_right h]
    exact max_eq_right (le_of_not_ge (fun hr => h (hiff.mp hr)))

end PseudoPrime.Analysis
