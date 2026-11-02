/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCumulativeBounds

/-! # Rational Gaussian history caps and recovery scales

The root tests and entrance constants are selected for this MR cumulative application.
They are isolated from the Mathlib-only recurrence core and from pointwise selection APIs.
All comparisons use the current actual Gaussian base, exact rational arithmetic and the
existing finite profile list. No natural-input enumeration or prefix data is added.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A strict rational root budget above the fixed floor bounds the surplus cutoff strictly.
For nonnegative L, use the quadratic-root upper theorem and equation to exclude equality,
then square the positive root comparison twice. This supports the two finite root tests. -/
theorem gaussianSurplus_lt_of_budget {L r : ℝ} (hL : 0 ≤ L) (hr : 91 / 10 < r)
    (hb :
      gaussianMRRefinedConductor * L + 38 / 5 + gaussianMRRefinedBeta * r <
        gaussianMRRefinedD * r ^ 2) :
    gaussianSurplusBound L < (6 / 5 : ℝ) * (r ^ 2) ^ 2 := by
  have hC : 0 ≤ gaussianMRRefinedConductor * L + 38 / 5 := by
    norm_num only [gaussianMRRefinedConductor]
    linarith only [hL]
  have hcoef0 : gaussianMRRefinedBeta < gaussianMRRefinedD * (91 / 10) := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
  have hcoef := hcoef0.trans (mul_lt_mul_of_pos_left hr gaussianMRRefined_coefficients.1)
  have hraw_le :=
    Analysis.gaussianBudgetRoot_le_of_budget gaussianMRRefined_coefficients.1
      gaussianMRRefined_coefficients.2 hC hcoef hb.le
  have hraw :
    Analysis.gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
        (gaussianMRRefinedConductor * L + 38 / 5) <
      r := by
    apply lt_of_le_of_ne hraw_le
    intro heq
    have he :=
      Analysis.gaussianBudgetRoot_equation (b := gaussianMRRefinedBeta)
        gaussianMRRefined_coefficients.1 hC
    rw [heq] at he
    linarith only [he, hb]
  have hroot : gaussianSurplusRoot L < r := max_lt hr hraw
  have hr0 : 0 ≤ r := (by norm_num only : (0 : ℝ) ≤ 91 / 10).trans hr.le
  have hs := (sq_lt_sq₀ (gaussianSurplus_root_pos L).le hr0).mpr hroot
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
  exact mul_lt_mul_of_pos_left hs' (by norm_num only : (0 : ℝ) < 6 / 5)

/-- For nonnegative scales through 101, the current Gaussian cutoff is below 8419.
The rational root 9.14 satisfies a strict budget at the upper endpoint; apply its fourth power. -/
theorem gaussianSurplus_cap101 {L : ℝ} (hL : 0 ≤ L) (hU : L ≤ 101) :
    gaussianSurplusBound L < (8419 : ℝ) := by
  have hb :
    gaussianMRRefinedConductor * L + 38 / 5 + gaussianMRRefinedBeta * (457 / 50) <
      gaussianMRRefinedD * (457 / 50 : ℝ) ^ 2 := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedConductor, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
    linarith only [hU]
  exact
    (gaussianSurplus_lt_of_budget hL (by norm_num only : (91 / 10 : ℝ) < 457 / 50) hb).trans_le
      (by norm_num only)

/-- Every old square-base history is at least the square capped at the first possible entrance.
Each profile entrance is at least thirty billion; induction propagates that retained floor.
This identifies the previous cumulative expression exactly on the small comparison interval. -/
theorem historyEnvelope_ge_entry (fs : List TriangularProfile) (L : ℝ) :
    min (L ^ 2) ((30000000000 : ℝ) ^ 2) ≤ historyEnvelope fs L := by
  induction fs generalizing L with
  | nil => exact min_le_left _ _
  | cons f fs ih =>
    apply le_min (ih L)
    have hT : (30000000000 : ℝ) ^ 2 ≤ f.T ^ 2 :=
      (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 30000000000)
            ((by norm_num only : (0 : ℝ) ≤ 30000000000).trans f.entry)).mpr
        f.entry
    have hcap := ih f.T
    rw [min_eq_right hT] at hcap
    exact ((min_le_right _ _).trans hcap).trans (le_max_left _ _)

/-- Whenever the squared scale is below the first entrance squared, the old history is the square.
Combine its universal upper bound with the retained entrance lower bound. -/
theorem historyEnvelope_eq_sq_small (fs : List TriangularProfile) {L : ℝ}
    (hL : L ^ 2 ≤ (30000000000 : ℝ) ^ 2) : historyEnvelope fs L = L ^ 2 := by
  apply le_antisymm (historyEnvelope_le_sq fs L)
  have hb := historyEnvelope_ge_entry fs L
  rw [min_eq_left hL] at hb
  exact hb

/-- At every natural endpoint, the Gaussian cumulative expression is below its common-scale base.
Project through the left minima; this exposes the low-scale improvement directly. -/
theorem gaussianCumulative_le_base (N : ℕ) :
    gaussianCumulativeEnvelope N ≤ gaussianHistoryBase (Real.log N) := by
  exact
    baseHistory_le_base TriangularProfile.T TriangularProfile.C gaussianHistoryBase historyProfiles
      (Real.log N)

/-- On the closed log band from 100 to 101, the new cumulative value beats the entire old history.
The old expression equals log squared, while the Gaussian base is below 8419.
This is a comparison of full cumulative expressions and requires no GRH assumption. -/
theorem gaussianCumulative_lt_history {N : ℕ} (hL : 100 ≤ Real.log N) (hU : Real.log N ≤ 101) :
    gaussianCumulativeEnvelope N < historyCumulativeEnvelope N := by
  have h0 : 0 ≤ Real.log N := by linarith only [hL]
  have h63 : (63 : ℝ) ≤ Real.log N := by linarith only [hL]
  have hs : Real.log N ^ 2 ≤ (30000000000 : ℝ) ^ 2 :=
    (sq_le_sq₀ h0 (by norm_num only : (0 : ℝ) ≤ 30000000000)).mpr (hU.trans (by norm_num only))
  change gaussianCumulativeEnvelope N < historyEnvelope historyProfiles (Real.log N)
  rw [historyEnvelope_eq_sq_small historyProfiles hs]
  have hb :=
    (gaussianCumulative_le_base N).trans
      (min_le_right (Real.log N ^ 2) (gaussianSurplusBound (max 63 (Real.log N))))
  rw [max_eq_right h63] at hb
  exact
    hb.trans_lt
      (lt_trans (gaussianSurplus_cap101 h0 hU)
        (by nlinarith only [hL, sq_nonneg (Real.log N - 100)]))

/-- At the first triangular entrance, the Gaussian base is below 59/125 of the entrance square.
The integer root cap 137150 gives a strict rational budget and fourth-power certificate.
This reduces the retained cost for the first profile without new finite input checks. -/
theorem gaussianBase_first_cap :
    gaussianHistoryBase 30000000000 < (59 / 125 : ℝ) * (30000000000 : ℝ) ^ 2 := by
  have hb :
    gaussianMRRefinedConductor * 30000000000 + 38 / 5 + gaussianMRRefinedBeta * 137150 <
      gaussianMRRefinedD * (137150 : ℝ) ^ 2 := by
    norm_num only [gaussianMRRefinedD, gaussianMRRefinedConductor, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussian6FifthsIndex, gaussian6FifthsEndpoint]
  have hu :=
    gaussianSurplus_lt_of_budget (by norm_num only : (0 : ℝ) ≤ 30000000000)
      (by norm_num only : (91 / 10 : ℝ) < 137150) hb
  have hg : gaussianHistoryBase 30000000000 ≤ gaussianSurplusBound 30000000000 := by
    exact
      (min_le_right _ _).trans_eq (congrArg gaussianSurplusBound (max_eq_right (by norm_num only)))
  exact hg.trans_lt (hu.trans_le (by norm_num only))

/-- At the second entrance, the first-profile Gaussian history is exactly .4603 times scale squared.
The certified first cap is smaller, and the Gaussian quadratic lower bound keeps the base
above this value. This replaces the older .5625 history coefficient. -/
theorem gaussianHistory_second_entry :
    baseHistory TriangularProfile.T TriangularProfile.C gaussianHistoryBase [triangularP04603]
        40000000000 =
      (4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2 := by
  change
    min (gaussianHistoryBase 40000000000)
        (max (gaussianHistoryBase 30000000000) ((4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2)) =
      _
  have hfirst : gaussianHistoryBase 30000000000 ≤ (4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2 :=
    gaussianBase_first_cap.le.trans (by norm_num only)
  rw [max_eq_right hfirst]
  apply min_eq_right
  change
    (4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2 ≤
      min ((40000000000 : ℝ) ^ 2) (gaussianSurplusBound (max 63 40000000000))
  rw [max_eq_right (by norm_num only : (63 : ℝ) ≤ 40000000000)]
  exact
    le_min (by norm_num only)
      ((by norm_num only :
            (4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2 ≤
              (15 / 32 : ℝ) * (40000000000 : ℝ) ^ 2).trans
        (gaussianSurplus_bound_lower (by norm_num only : (0 : ℝ) ≤ 40000000000)).le)

/-- Appending earlier profiles retains their history as an upper bound on the full expression.
Induct through the newer prefix and project its left minima. This transfers recovery caps. -/
theorem triangularHistory_le_append (B : ℝ → ℝ) (xs ys : List TriangularProfile) (L : ℝ) :
    baseHistory TriangularProfile.T TriangularProfile.C B (xs ++ ys) L ≤
      baseHistory TriangularProfile.T TriangularProfile.C B ys L := by
  induction xs with
  | nil => exact le_rfl
  | cons f xs ih => exact (min_le_left _ _).trans ih

/-- The full Gaussian cumulative expression recovers .4603 when its first rational history cap fits.
Select the first profile and project the other seven left minima before using the cap. -/
theorem gaussian_first_recovered {N : ℕ}
    (hr : (59 / 125 : ℝ) * (30000000000 : ℝ) ^ 2 ≤ (4603 / 10000 : ℝ) * Real.log N ^ 2) :
    gaussianCumulativeEnvelope N ≤ (4603 / 10000 : ℝ) * Real.log N ^ 2 := by
  have hs :
    baseHistory TriangularProfile.T TriangularProfile.C gaussianHistoryBase [triangularP04603]
        (Real.log N) ≤
      (4603 / 10000 : ℝ) * Real.log N ^ 2 :=
    (min_le_right _ _).trans (max_le (gaussianBase_first_cap.le.trans hr) le_rfl)
  exact
    (triangularHistory_le_append gaussianHistoryBase
          [triangularP02823622, triangularP028289, triangularP028399, triangularP02891,
            triangularP02992, triangularP03315, triangularP04145]
          [triangularP04603] (Real.log N)).trans
      hs

/-- The full Gaussian cumulative expression recovers .4145 when its second history cap fits.
Select the second profile, use the exact first-profile entrance history and project newer minima. -/
theorem gaussian_second_recovered {N : ℕ}
    (hr : (4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2 ≤ (4145 / 10000 : ℝ) * Real.log N ^ 2) :
    gaussianCumulativeEnvelope N ≤ (4145 / 10000 : ℝ) * Real.log N ^ 2 := by
  have hs :
    baseHistory TriangularProfile.T TriangularProfile.C gaussianHistoryBase
        [triangularP04145, triangularP04603] (Real.log N) ≤
      (4145 / 10000 : ℝ) * Real.log N ^ 2 :=
    (min_le_right _ _).trans (max_le (gaussianHistory_second_entry.le.trans hr) le_rfl)
  exact
    (triangularHistory_le_append gaussianHistoryBase
          [triangularP02823622, triangularP028289, triangularP028399, triangularP02891,
            triangularP02992, triangularP03315]
          [triangularP04145, triangularP04603] (Real.log N)).trans
      hs

/-- The two integer recovery scales satisfy both new caps and precede both old recovery thresholds.
Check the four rational square comparisons exactly; no approximate square roots are used. -/
theorem gaussian_recovery_certificates :
    (59 / 125 : ℝ) * (30000000000 : ℝ) ^ 2 ≤ (4603 / 10000 : ℝ) * (30378881000 : ℝ) ^ 2 ∧
      (4603 / 10000 : ℝ) * (40000000000 : ℝ) ^ 2 ≤ (4145 / 10000 : ℝ) * (42152002600 : ℝ) ^ 2 ∧
      (30378881000 : ℝ) ^ 2 < (30000000000 : ℝ) ^ 2 / (4603 / 10000) ∧
      (42152002600 : ℝ) ^ 2 < (30000000000 : ℝ) ^ 2 / (4145 / 10000) := by
  norm_num only [and_self]

/-- From log endpoint 30378881000, the full cumulative envelope is at most .4603 log squared.
Square the positive scale comparison and apply the first rational recovery certificate. -/
theorem gaussian_first_recovery_scale {N : ℕ} (hL : 30378881000 ≤ Real.log N) :
    gaussianCumulativeEnvelope N ≤ (4603 / 10000 : ℝ) * Real.log N ^ 2 := by
  apply gaussian_first_recovered
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 30378881000)
          ((by norm_num only : (0 : ℝ) ≤ 30378881000).trans hL)).mpr
      hL
  exact
    gaussian_recovery_certificates.1.trans
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 4603 / 10000))

/-- From log endpoint 42152002600, the full cumulative envelope is at most .4145 log squared.
Square the positive scale comparison and apply the second rational recovery certificate. -/
theorem gaussian_second_recovery_scale {N : ℕ} (hL : 42152002600 ≤ Real.log N) :
    gaussianCumulativeEnvelope N ≤ (4145 / 10000 : ℝ) * Real.log N ^ 2 := by
  apply gaussian_second_recovered
  have hs :=
    (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 42152002600)
          ((by norm_num only : (0 : ℝ) ≤ 42152002600).trans hL)).mpr
      hL
  exact
    gaussian_recovery_certificates.2.1.trans
      (mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 4145 / 10000))

end PseudoPrime.PrimeTestBounds.MillerRabin
