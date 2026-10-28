/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSeededTunedOrder

/-! # Exact four-piece selection for tuned seeded profiles -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The exact tuned switch for floor N is the current profile switch plus its own shift. -/
noncomputable def gaussianSeededTunedSwitch (f : Bool) (N : ℝ) : ℝ :=
  gaussianSeededSharpSwitch f N + gaussianSeededTunedShift f

/-- The tuned raw curve has its profile-specific exact floor comparison at every L>=63. -/
theorem seededTuned_raw_compare {f : Bool} {L N : ℝ} (hL : 63 ≤ L) (hN : 35000 ≤ N) :
    (gaussianSeededTunedRawBound f L ≤ N ↔ L ≤ gaussianSeededTunedSwitch f N) ∧
      (N ≤ gaussianSeededTunedRawBound f L ↔ gaussianSeededTunedSwitch f N ≤ L) := by
  have h0 : 0 ≤ L - gaussianSeededTunedShift f := by
    linarith only [hL, (seededTuned_shift_bounds f).2]
  rw [seededTuned_rawBound_shift]
  have h := gaussianSeededSharp_raw_bound_compare (f := f) h0 hN
  constructor
  · rw [h.1]
    dsimp only [gaussianSeededTunedSwitch]
    constructor <;> intro hs <;> linarith only [hs]
  · rw [h.2]
    dsimp only [gaussianSeededTunedSwitch]
    constructor <;> intro hs <;> linarith only [hs]

/-- The smaller true-profile residual gives a strictly smaller raw curve at nonnegative scale. -/
theorem seededTuned_raw_profiles_lt {L : ℝ} (hL : 0 ≤ L) :
    gaussianSeededTunedRawBound true L < gaussianSeededTunedRawBound false L := by
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hD : 0 ≤ gaussianSeededTunedConstant true := by
    norm_num only [gaussianSeededTunedConstant, Bool.false_eq_true, ite_false, ite_true]
  have hlt : gaussianSeededTunedConstant true < gaussianSeededTunedConstant false := by
    norm_num only [gaussianSeededTunedConstant, gaussianSeededTunedConstant, Bool.false_eq_true,
      ite_false, ite_true]
  have hroot :=
    gaussianBudgetRoot_strictMono (b := gaussianMRRefinedBeta) gaussianMRRefined_coefficients.1
      (add_nonneg (mul_nonneg hc hL) hD)
      (add_lt_add_of_le_of_lt (le_refl (gaussianMRRefinedConductor * L)) hlt)
  change gaussianSeededTunedRawRoot true L < gaussianSeededTunedRawRoot false L at hroot
  have h2 :=
    (sq_lt_sq₀ (gaussianSeededTuned_raw_pos true L).le (gaussianSeededTuned_raw_pos false L).le).mpr
      hroot
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- The tuned numerical selection has four pieces: floor35000, raw35,
floor50000 and raw50. Each switch retains its own profile displacement. -/
noncomputable def gaussianSeededTunedSelected (L : ℝ) : ℝ :=
  if L ≤ gaussianSeededTunedSwitch false 35000 then 35000
  else
    if L < gaussianSeededTunedSwitch false 50000 then gaussianSeededTunedRawBound false L
    else
      if L ≤ gaussianSeededTunedSwitch true 50000 then 50000 else gaussianSeededTunedRawBound true L

/-- Above the analytic entrance, the two-profile actual minimum equals the exact
four-piece selection. Use the raw floor comparisons and strict residual ordering. -/
theorem seededTunedFamily_eq_selected {L : ℝ} (hL : 63 ≤ L) :
    gaussianSeededTunedFamily L = gaussianSeededTunedSelected L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hprof := (seededTuned_raw_profiles_lt h0).le
  rw [gaussianSeededTunedFamily, seededTuned_eq_max false L, seededTuned_eq_max true L]
  norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, ite_true, Nat.cast_ofNat]
  by_cases h35 : L ≤ gaussianSeededTunedSwitch false 35000
  · have ha :=
      (seededTuned_raw_compare (f := false) hL (by norm_num only : (35000 : ℝ) ≤ 35000)).1.mpr h35
    have hb : gaussianSeededTunedRawBound true L ≤ (50000 : ℝ) := by linarith only [hprof, ha]
    simp only [gaussianSeededTunedSelected, ite_eq_left h35, max_eq_left ha, max_eq_left hb,
      min_eq_left (by norm_num only : (35000 : ℝ) ≤ 50000)]
  · have ha :=
      (seededTuned_raw_compare (f := false) hL (by norm_num only : (35000 : ℝ) ≤ 35000)).2.mpr
        (le_of_not_ge h35)
    by_cases h50 : L < gaussianSeededTunedSwitch false 50000
    · have hb :=
        (seededTuned_raw_compare (f := false) hL (by norm_num only : (35000 : ℝ) ≤ 50000)).1.mpr
          h50.le
      have hc : gaussianSeededTunedRawBound true L ≤ (50000 : ℝ) := hprof.trans hb
      simp only [gaussianSeededTunedSelected, ite_eq_right h35, ite_eq_left h50, max_eq_right ha,
        max_eq_left hc, min_eq_left hb]
    · have hb :=
        (seededTuned_raw_compare (f := false) hL (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
          (le_of_not_gt h50)
      by_cases hlast : L ≤ gaussianSeededTunedSwitch true 50000
      · have hc :=
          (seededTuned_raw_compare (f := true) hL (by norm_num only : (35000 : ℝ) ≤ 50000)).1.mpr
            hlast
        simp only [gaussianSeededTunedSelected, ite_eq_right h35, ite_eq_right h50,
          ite_eq_left hlast, max_eq_right ha, max_eq_left hc, min_eq_right hb]
      · have hc :=
          (seededTuned_raw_compare (f := true) hL (by norm_num only : (35000 : ℝ) ≤ 50000)).2.mpr
            (le_of_not_ge hlast)
        simp only [gaussianSeededTunedSelected, ite_eq_right h35, ite_eq_right h50,
          ite_eq_right hlast, max_eq_right ha, max_eq_right hc, min_eq_right hprof]

/-- The three tuned boundaries retain strict order because the last profile has the larger shift. -/
theorem seededTuned_switch_order :
    gaussianSeededTunedSwitch false 35000 < gaussianSeededTunedSwitch false 50000 ∧
      gaussianSeededTunedSwitch false 50000 < gaussianSeededTunedSwitch true 50000 := by
  have hd : gaussianSeededTunedShift false < gaussianSeededTunedShift true := by
    norm_num only [gaussianSeededTunedShift, Bool.false_eq_true, ite_false, ite_true]
  exact
    ⟨add_lt_add_of_lt_of_le gaussianSeededSharp_switch_order.1 (le_refl _),
      add_lt_add gaussianSeededSharp_switch_order.2 hd⟩

/-- At each switched floor above the analytic entrance, the neighboring raw formula
equals the constant floor, so the adjacent interval values coincide. -/
theorem seededTuned_raw_at_switch {f : Bool} {N : ℝ} (hN : 35000 ≤ N)
    (hS : 63 ≤ gaussianSeededTunedSwitch f N) :
    gaussianSeededTunedRawBound f (gaussianSeededTunedSwitch f N) = N := by
  have h := seededTuned_raw_compare (f := f) hS hN
  exact le_antisymm (h.1.mpr le_rfl) (h.2.mpr le_rfl)

end PseudoPrime.Analysis
