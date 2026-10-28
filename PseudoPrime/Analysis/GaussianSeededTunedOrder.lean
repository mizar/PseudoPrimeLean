/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSeededTuned
public import PseudoPrime.Analysis.GaussianSeededSharpMonotone

/-! # Tuned seeded Gaussian monotonicity and strict sharp comparison -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The two-profile tuned numerical minimum retains both unchanged prefix floors. -/
noncomputable def gaussianSeededTunedFamily (L : ℝ) : ℝ :=
  min (gaussianSeededTunedBound false L) (gaussianSeededTunedBound true L)

/-- The raw tuned cutoff is the positive quadratic root raised to the fourth power,
scaled by six fifths, before the prefix floor is imposed. -/
noncomputable def gaussianSeededTunedRawBound (f : Bool) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * (gaussianSeededTunedRawRoot f L ^ 2) ^ 2

/-- Each tuned raw cutoff has its own exact displacement from the sharp profile. -/
theorem seededTuned_rawBound_shift (f : Bool) (L : ℝ) :
    gaussianSeededTunedRawBound f L =
      gaussianSeededSharpRawBound f (L - gaussianSeededTunedShift f) := by
  simp only [gaussianSeededTunedRawBound, gaussianSeededSharpRawBound,
    gaussianSeededTuned_raw_shift]

/-- The tuned cutoff is exactly the maximum of its prefix floor and raw cutoff. -/
theorem seededTuned_eq_max (f : Bool) (L : ℝ) :
    gaussianSeededTunedBound f L =
      max (gaussianSeededSharpCutoff f : ℝ) (gaussianSeededTunedRawBound f L) := by
  rw [gaussianSeededTuned_bound_shift, gaussianSeededSharp_eq_max, seededTuned_rawBound_shift]

/-- Both positive profile displacements are less than one unit of logarithmic scale. -/
theorem seededTuned_shift_bounds (f : Bool) :
    0 < gaussianSeededTunedShift f ∧ gaussianSeededTunedShift f < 1 := by
  cases f <;>
    norm_num only [gaussianSeededTunedShift, Bool.false_eq_true, ite_false, ite_true, and_self]

/-- Each tuned clipped cutoff is monotone on the entire real scale,
as a translation of the corresponding sharp clipped cutoff. -/
theorem seededTuned_bound_mono (f : Bool) : Monotone (gaussianSeededTunedBound f) := by
  intro a b hab
  rw [gaussianSeededTuned_bound_shift, gaussianSeededTuned_bound_shift]
  exact gaussianSeededSharp_bound_mono f (sub_le_sub_right hab _)

/-- The minimum of the two tuned monotone cutoffs is globally monotone. -/
theorem seededTunedFamily_mono : Monotone gaussianSeededTunedFamily := by
  intro a b hab
  exact min_le_min (seededTuned_bound_mono false hab) (seededTuned_bound_mono true hab)

/-- Each tuned profile is globally no larger than its sharp counterpart. -/
theorem seededTuned_le_sharp (f : Bool) (L : ℝ) :
    gaussianSeededTunedBound f L ≤ gaussianSeededSharpBound f L := by
  rw [gaussianSeededTuned_bound_shift]
  exact gaussianSeededSharp_bound_mono f (sub_le_self L (seededTuned_shift_bounds f).1.le)

/-- The tuned minimum is no larger than the current selected seeded candidate
throughout its analytic entrance range. -/
theorem seededTunedFamily_le_sharp {L : ℝ} (hL : 63 ≤ L) :
    gaussianSeededTunedFamily L ≤ gaussianSeededSharp L := by
  rw [gaussianSeededSharp_eq_min hL]
  exact min_le_min (seededTuned_le_sharp false L) (seededTuned_le_sharp true L)

/-- At nonnegative scale each tuned raw curve is strictly smaller than its sharp raw curve.
The positive decrease of the residual makes the quadratic-root comparison strict. -/
theorem seededTuned_raw_lt_sharp (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianSeededTunedRawBound f L < gaussianSeededSharpRawBound f L := by
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hD : 0 ≤ gaussianSeededTunedConstant f := by
    cases f <;> norm_num only [gaussianSeededTunedConstant, Bool.false_eq_true, ite_false, ite_true]
  have hlt : gaussianSeededTunedConstant f < gaussianSeededSharpConstant f := by
    cases f <;>
      norm_num only [gaussianSeededTunedConstant, gaussianSeededSharpConstant, Bool.false_eq_true,
        ite_false, ite_true]
  have hroot :=
    gaussianBudgetRoot_strictMono (b := gaussianMRRefinedBeta) gaussianMRRefined_coefficients.1
      (add_nonneg (mul_nonneg hc hL) hD)
      (add_lt_add_of_le_of_lt (le_refl (gaussianMRRefinedConductor * L)) hlt)
  change gaussianSeededTunedRawRoot f L < gaussianSeededSharpRawRoot f L at hroot
  have h2 :=
    (sq_lt_sq₀ (gaussianSeededTuned_raw_pos f L).le (gaussianSeededSharp_raw_pos f L).le).mpr hroot
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- A sharp raw curve lies above its own prefix floor after its exact switch. -/
theorem seededSharp_raw_gt_floor (f : Bool) {L : ℝ} (hL : 0 ≤ L)
    (hS : gaussianSeededSharpSwitch f (gaussianSeededSharpCutoff f : ℝ) < L) :
    (gaussianSeededSharpCutoff f : ℝ) < gaussianSeededSharpRawBound f L := by
  have hN : (35000 : ℝ) ≤ (gaussianSeededSharpCutoff f : ℝ) := by
    cases f <;>
      norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, ite_true,
        Nat.cast_ofNat]
  exact
    lt_of_not_ge
      (fun h ↦ (not_le.mpr hS) ((gaussianSeededSharp_raw_bound_compare (f := f) hL hN).1.mp h))

/-- Once a sharp profile leaves its floor, its tuned counterpart is strictly smaller. -/
theorem seededTuned_lt_sharp (f : Bool) {L : ℝ} (hL : 0 ≤ L)
    (hfloor : (gaussianSeededSharpCutoff f : ℝ) < gaussianSeededSharpRawBound f L) :
    gaussianSeededTunedBound f L < gaussianSeededSharpBound f L := by
  rw [seededTuned_eq_max, gaussianSeededSharp_eq_max]
  exact (max_lt hfloor (seededTuned_raw_lt_sharp f hL)).trans_le (le_max_right _ _)

/-- The tuned family strictly improves the current seeded selection after its last switch. -/
theorem seededTunedFamily_strict_last {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianSeededSharpSwitch true 50000 < L) :
    gaussianSeededTunedFamily L < gaussianSeededSharp L := by
  have hf := seededSharp_raw_gt_floor true (by linarith only [hL]) hS
  have hn := seededTuned_lt_sharp true (by linarith only [hL]) hf
  rw [gaussianSeededSharp_eq_max, max_eq_right hf.le] at hn
  have hs :=
    (min_le_right (gaussianSeededTunedBound false L) (gaussianSeededTunedBound true L)).trans_lt hn
  have h35 : ¬L ≤ gaussianSeededSharpSwitch false 35000 := by
    linarith only [gaussianSeededSharp_switch_order.1, gaussianSeededSharp_switch_order.2, hS]
  have h50 : ¬L < gaussianSeededSharpSwitch false 50000 := by
    linarith only [gaussianSeededSharp_switch_order.2, hS]
  simpa only [gaussianSeededTunedFamily, gaussianSeededSharp, gaussianSeededSharpSelected,
    ite_eq_right h35, ite_eq_right h50, ite_eq_right (not_le.mpr hS)] using hs

/-- The first strict band includes the beginning of the sharp 50000 plateau.
Use the false profile before the old switch, then its shifted raw cutoff below 50000. -/
theorem seededTunedFamily_strict_first {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianSeededSharpSwitch false 35000 < L)
    (hU : L < gaussianSeededSharpSwitch false 50000 + gaussianSeededTunedShift false) :
    gaussianSeededTunedFamily L < gaussianSeededSharp L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  by_cases hOld : L < gaussianSeededSharpSwitch false 50000
  · have hf := seededSharp_raw_gt_floor false h0 hS
    have hn := seededTuned_lt_sharp false h0 hf
    rw [gaussianSeededSharp_eq_max, max_eq_right hf.le] at hn
    have hs :=
      (min_le_left (gaussianSeededTunedBound false L) (gaussianSeededTunedBound true L)).trans_lt hn
    simpa only [gaussianSeededTunedFamily, gaussianSeededSharp, gaussianSeededSharpSelected,
      ite_eq_right (not_le.mpr hS), ite_eq_left hOld] using hs
  · have hshift : 0 ≤ L - gaussianSeededTunedShift false := by
      linarith only [hL, (seededTuned_shift_bounds false).2]
    have hNew : L - gaussianSeededTunedShift false < gaussianSeededSharpSwitch false 50000 := by
      linarith only [hU]
    have hraw : gaussianSeededTunedRawBound false L < (50000 : ℝ) := by
      rw [seededTuned_rawBound_shift]
      exact
        lt_of_not_ge
          (fun h ↦
            (not_le.mpr hNew)
              ((gaussianSeededSharp_raw_bound_compare (f := false) hshift
                    (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mp
                h))
    have hnew : gaussianSeededTunedBound false L < (50000 : ℝ) := by
      rw [seededTuned_eq_max]
      exact
        max_lt
          (by
            norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false,
              Nat.cast_ofNat])
          hraw
    have holdRaw : (50000 : ℝ) ≤ gaussianSeededSharpRawBound false L :=
      (gaussianSeededSharp_raw_bound_compare (f := false) h0
            (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
        (le_of_not_gt hOld)
    have hold35 : (50000 : ℝ) ≤ gaussianSeededSharpBound false L := by
      rw [gaussianSeededSharp_eq_max]
      exact holdRaw.trans (le_max_right _ _)
    have hold50 : (50000 : ℝ) ≤ gaussianSeededSharpBound true L := by
      simpa only [gaussianSeededSharpCutoff, ite_true, Nat.cast_ofNat] using
        gaussianSeededSharp_cutoff_le true L
    rw [gaussianSeededSharp_eq_min hL]
    exact ((min_le_left _ _).trans_lt hnew).trans_le (le_min hold35 hold50)

/-- The tuned two-profile minimum is globally at least 35000,
since neither certified prefix floor is smaller. -/
theorem seededTunedFamily_floor (L : ℝ) : (35000 : ℝ) ≤ gaussianSeededTunedFamily L := by
  have h0 := gaussianSeededTuned_cutoff_le false L
  have h1 := gaussianSeededTuned_cutoff_le true L
  norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, ite_true,
    Nat.cast_ofNat] at h0 h1
  exact le_min h0 ((by norm_num only : (35000 : ℝ) ≤ 50000).trans h1)

/-- Above scale 63 the family retains the common quadratic lower bound
used to compare both seeded profiles with high-range triangular candidates. -/
theorem seededTunedFamily_lower {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianSeededTunedFamily L := by
  exact
    lt_min (gaussianSeededTuned_bound_lower (f := false) hL)
      (gaussianSeededTuned_bound_lower (f := true) hL)

end PseudoPrime.Analysis
