/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.NextTunedBase
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSeededSurplus

/-! # Strict surplus comparisons with the complete tuned envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At nonnegative logarithmic scales, either surplus raw curve is strictly below its tuned curve.
The mass, width and conductor agree, while the residual is strictly smaller. -/
theorem seededSurplus_raw_lt_tuned (f : Bool) {L : ℝ} (hL : 0 ≤ L) :
    gaussianSeededSurplusRawBound f L < gaussianSeededTunedRawBound f L := by
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hD : 0 ≤ gaussianSeededSurplusConstant f := by
    cases f <;>
      norm_num only [gaussianSeededSurplusConstant, Bool.false_eq_true, ite_false, ite_true]
  have hlt : gaussianSeededSurplusConstant f < gaussianSeededTunedConstant f := by
    cases f <;>
      norm_num only [gaussianSeededSurplusConstant, gaussianSeededTunedConstant, Bool.false_eq_true,
        ite_false, ite_true]
  have hr :=
    Analysis.gaussianBudgetRoot_strictMono (b := gaussianMRRefinedBeta)
      gaussianMRRefined_coefficients.1 (add_nonneg (mul_nonneg hc hL) hD)
      (add_lt_add_of_le_of_lt (le_refl (gaussianMRRefinedConductor * L)) hlt)
  change gaussianSeededSurplusRawRoot f L < gaussianSeededTunedRawRoot f L at hr
  have h2 :=
    (sq_lt_sq₀ (gaussianSeededSurplus_raw_pos f L).le (gaussianSeededTuned_raw_pos f L).le).mpr hr
  have h4 := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr h2
  exact mul_lt_mul_of_pos_left h4 (by norm_num only : (0 : ℝ) < 6 / 5)

/-- Beyond a tuned profile's exact floor switch,
its raw curve strictly exceeds that prefix floor. -/
theorem seededTuned_raw_gt_cutoff (f : Bool) {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianSeededTunedSwitch f (gaussianSeededSharpCutoff f : ℝ) < L) :
    (gaussianSeededSharpCutoff f : ℝ) < gaussianSeededTunedRawBound f L := by
  have hN : (35000 : ℝ) ≤ (gaussianSeededSharpCutoff f : ℝ) := by
    cases f <;>
      norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, ite_true,
        Nat.cast_ofNat]
  exact lt_of_not_ge fun h ↦ not_le_of_gt hS ((seededTuned_raw_compare hL hN).1.mp h)

/-- Beyond the current floor switch, the entire surplus clipped cutoff is strictly below the
current tuned raw curve. Both branches of its maximum satisfy the strict comparison. -/
theorem seededSurplus_lt_raw (f : Bool) {L : ℝ} (hL : 63 ≤ L)
    (hS : gaussianSeededTunedSwitch f (gaussianSeededSharpCutoff f : ℝ) < L) :
    gaussianSeededSurplusBound f L < gaussianSeededTunedRawBound f L := by
  rw [seededSurplus_eq_max]
  exact
    max_lt (seededTuned_raw_gt_cutoff f hL hS)
      (seededSurplus_raw_lt_tuned f (by linarith only [hL]))

/-- Throughout [245,255], the surplus 35000 profile strictly improves the full tuned selection.
Use its exact raw-35000 normal form rather than comparing only the seeded families. -/
theorem seededSurplus35_lt_tuned {n : ℕ} (hN : 3000 ≤ n) (hL : 245 ≤ Real.log n)
    (hU : Real.log n ≤ 255) :
    gaussianSeededSurplusBound false (Real.log n) < tunedSelectedEnvelope n := by
  rw [tunedSelected_eq_raw35 hN hL hU]
  apply seededSurplus_lt_raw false (by linarith only [hL])
  norm_num only [gaussianSeededSharpCutoff, Bool.false_eq_true, ite_false, Nat.cast_ofNat]
  dsimp only [gaussianSeededTunedSwitch]
  linarith only [hL, gaussianSeededSharp_switch35_bounds.2, (seededTuned_shift_bounds false).2]

/-- From scale 300 to the first high entrance, the surplus 50000 profile strictly improves the
full tuned selection. This includes the initial comparison band [300,310]. -/
theorem seededSurplus50_lt_tuned {n : ℕ} (hN : 3000 ≤ n) (hL : 300 ≤ Real.log n)
    (hU : Real.log n < 30000000000) :
    gaussianSeededSurplusBound true (Real.log n) < tunedSelectedEnvelope n := by
  rw [tunedSelected_eq_raw50 hN hL hU]
  apply seededSurplus_lt_raw true (by linarith only [hL])
  norm_num only [gaussianSeededSharpCutoff, ite_true, Nat.cast_ofNat]
  dsimp only [gaussianSeededTunedSwitch]
  linarith only [hL, (gaussianSeededSharp_switch50_bounds true).2,
    (seededTuned_shift_bounds true).2]

end PseudoPrime.PrimeTestBounds.MillerRabin
