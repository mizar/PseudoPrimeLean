/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusShape

/-! # Certified global surplus coefficient thresholds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational root bound certifies a strict normalized global upper bound at one scale. -/
theorem jointSurplus_endpoint_cert {rho R T B c : ℝ} (hrho : 0 ≤ rho) (hR : 0 ≤ R) (hT : 0 < T)
    (hroot : (28794111 / 12500000 : ℝ) < (10971611 / 5000000 : ℝ) * B)
    (hbudget :
      (20115621 / 25000000 : ℝ) * T + R + (28794111 / 12500000 : ℝ) * B ≤
        (10971611 / 5000000 : ℝ) * B ^ 2)
    (hcert : (21 / 10 : ℝ) * (max rho (B ^ 2)) ^ 2 < c * T ^ 2)
    (hbranch : jointSurplusGlobal T ≤ jointSurplusCutoff rho R T) :
    jointSurplusGlobal T / T ^ 2 < c := by
  have hC : 0 ≤ (20115621 / 25000000 : ℝ) * T + R :=
    add_nonneg (mul_nonneg (by norm_num only) hT.le) hR
  have hrootB : jointSurplusRoot R T ≤ B :=
    Analysis.gaussianBudgetRoot_le_of_budget (by norm_num only) (by norm_num only) hC hroot hbudget
  have hroot0 : 0 ≤ jointSurplusRoot R T :=
    (Analysis.gaussianBudgetRoot_pos (by norm_num only) (by norm_num only)).le
  have hsq := pow_le_pow_left₀ hroot0 hrootB 2
  have hrad : jointSurplusRadius rho R T ≤ max rho (B ^ 2) := max_le_max le_rfl hsq
  have hrad0 : 0 ≤ jointSurplusRadius rho R T := hrho.trans (le_max_left _ _)
  have hradsq := pow_le_pow_left₀ hrad0 hrad 2
  have hcut : jointSurplusCutoff rho R T < c * T ^ 2 := by
    unfold jointSurplusCutoff
    have hh := mul_le_mul_of_nonneg_left hradsq (by norm_num only : (0 : ℝ) ≤ 21 / 10)
    exact hh.trans_lt hcert
  have ht2 : 0 < T ^ 2 := sq_pos_of_pos hT
  exact (div_lt_iff₀ ht2).2 (hbranch.trans_lt hcut)

/-- Transfer a strict normalized endpoint bound to every larger scale. -/
theorem jointSurplus_threshold {T c L : ℝ} (hT : 0 < T) (hL : T ≤ L)
    (hcert : jointSurplusGlobal T / T ^ 2 < c) : jointSurplusGlobal L < c * L ^ 2 := by
  have hLp : 0 < L := hT.trans_le hL
  have h := jointSurplusGlobal_ratio_anti hT hL
  exact (div_lt_iff₀ (sq_pos_of_pos hLp)).1 (h.trans_lt hcert)

/-- The global comparison is strictly below the stated coefficient from scale 283. -/
theorem jointSurplus_lt_fourNinths {L : ℝ} (hL : 283 ≤ L) :
    jointSurplusGlobal L < (4 / 9 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 283) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 130) (R := 30) (B := 57 / 5) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_left _ _)

/-- The global comparison is strictly below the stated coefficient from scale 290. -/
theorem jointSurplus_lt_sevenSixteenths {L : ℝ} (hL : 290 ≤ L) :
    jointSurplusGlobal L < (7 / 16 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 290) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 130) (R := 30) (B := 23 / 2) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_left _ _)

/-- The global comparison is strictly below the stated coefficient from scale 300. -/
theorem jointSurplus_lt_0432 {L : ℝ} (hL : 300 ≤ L) :
    jointSurplusGlobal L < (54 / 125 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 300) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 130) (R := 30) (B := 583 / 50) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_left _ _)

/-- The global comparison is strictly below the stated coefficient from scale 330. -/
theorem jointSurplus_lt_042 {L : ℝ} (hL : 330 ≤ L) :
    jointSurplusGlobal L < (21 / 50 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 330) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 130) (R := 30) (B := 12143 / 1000) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_left _ _)

/-- The global comparison is strictly below the stated coefficient from scale 400. -/
theorem jointSurplus_lt_0397 {L : ℝ} (hL : 400 ≤ L) :
    jointSurplusGlobal L < (397 / 1000 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 400) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 155) (R := 29) (B := 13181 / 1000) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The global comparison is strictly below the stated coefficient from scale 1000. -/
theorem jointSurplus_lt_0338 {L : ℝ} (hL : 1000 ≤ L) :
    jointSurplusGlobal L < (169 / 500 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 1000) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 155) (R := 29) (B := 2503 / 125) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The global comparison is strictly below the stated coefficient from scale 4000. -/
theorem jointSurplus_lt_0304 {L : ℝ} (hL : 4000 ≤ L) :
    jointSurplusGlobal L < (38 / 125 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 4000) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 155) (R := 29) (B := 39) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The global comparison is strictly below the stated coefficient from scale 6500. -/
theorem jointSurplus_lt_03 {L : ℝ} (hL : 6500 ≤ L) :
    jointSurplusGlobal L < (3 / 10 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 6500) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 155) (R := 29) (B := 12371 / 250) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_right _ _)

/-- The global comparison is strictly below the stated coefficient from scale 25000. -/
theorem jointSurplus_lt_029 {L : ℝ} (hL : 25000 ≤ L) :
    jointSurplusGlobal L < (29 / 100 : ℝ) * L ^ 2 := by
  apply jointSurplus_threshold (T := 25000) (by norm_num only) hL
  apply
    jointSurplus_endpoint_cert (rho := 155) (R := 29) (B := 96341 / 1000) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only [max_def, ite_false, ite_true])
  exact (min_le_right _ _).trans (min_le_right _ _)

end PseudoPrime.PrimeTestBounds.MillerRabin
