/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvCheck

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvCheck
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvLocal
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapCurvAffine
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapTaylor
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapEval
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapExp
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteCells

/-! # Kernel-checked curvature caps for the finite K186 cells -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An upper curvature bound throughout a closed dyadic comparison interval. -/
private def CheckedCurvature (a b : ℕ) (C : ℚ) : Prop :=
  ∀ x ∈ Set.Icc ((a : ℝ) / 32) ((b : ℝ) / 32),
    gaussianMidResidualCurv k186GapSlope (4 * (301 / 20000 + 1 / 6000)) k186GapRates k186GapProfiles
        x ≤
      (C : ℝ)

/-- Use adjacent curvature intervals without introducing a new residual endpoint. -/
private theorem checked_split {a m b : ℕ} {C : ℚ} (hl : CheckedCurvature a m C)
    (hr : CheckedCurvature m b C) : CheckedCurvature a b C := by
  intro x hx
  by_cases h : x ≤ (m : ℝ) / 32
  · exact hl x ⟨hx.1, h⟩
  · exact hr x ⟨le_of_not_ge h, hx.2⟩

/-- Transfer a closed curvature certificate to the corresponding residual cell. -/
private theorem checked_to_cell (i : Fin 20) {a b : ℕ} {C : ℚ}
    (ha : (k186FiniteCell i).left = (a : ℚ) / 32) (hb : (k186FiniteCell i).right = (b : ℚ) / 32)
    (hC : (k186FiniteCell i).upperCurvature = C) (h : CheckedCurvature a b C) {x : ℝ}
    (hx : x ∈ Set.Ioo ((k186FiniteCell i).left : ℝ) (k186FiniteCell i).right) :
    gaussianMidResidualCurv k186GapSlope (4 * (301 / 20000 + 1 / 6000)) k186GapRates k186GapProfiles
        x ≤
      ((k186FiniteCell i).upperCurvature : ℝ) := by
  rw [ha, hb] at hx
  simp only [Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat] at hx
  rw [hC]
  exact h x ⟨hx.1.le, hx.2.le⟩

/-- Check the signed curvature over dyadic indices 960 to 1022. -/
private theorem checked_0_0 : CheckedCurvature 960 1022 (1628336647 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1022 to 1084. -/
private theorem checked_0_1 : CheckedCurvature 1022 1084 (1628336647 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1084 to 1146. -/
private theorem checked_1_0 : CheckedCurvature 1084 1146 (16557975141 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1146 to 1208. -/
private theorem checked_2_0 : CheckedCurvature 1146 1208 (100125413 / 10000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1208 to 1239. -/
private theorem checked_3_0 : CheckedCurvature 1208 1239 (282709021 / 125000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1239 to 1270. -/
private theorem checked_4_0 : CheckedCurvature 1239 1270 (6025901189 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1270 to 1301. -/
private theorem checked_5_0 : CheckedCurvature 1270 1301 (2362679123 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1301 to 1332. -/
private theorem checked_5_1 : CheckedCurvature 1301 1332 (2362679123 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1332 to 1363. -/
private theorem checked_6_0 : CheckedCurvature 1332 1363 (6869715957 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1363 to 1394. -/
private theorem checked_7_0 : CheckedCurvature 1363 1394 (13544019257 / 500000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1394 to 1425. -/
private theorem checked_8_0 : CheckedCurvature 1394 1425 (24384585687 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1425 to 1456. -/
private theorem checked_9_0 : CheckedCurvature 1425 1456 (4702122591 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1456 to 1487. -/
private theorem checked_10_0 : CheckedCurvature 1456 1487 (2382220037 / 250000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1487 to 1518. -/
private theorem checked_10_1 : CheckedCurvature 1487 1518 (2382220037 / 250000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1518 to 1549. -/
private theorem checked_11_0 : CheckedCurvature 1518 1549 (37933781607 / 500000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1549 to 1580. -/
private theorem checked_12_0 : CheckedCurvature 1549 1580 (36153811909 / 200000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1580 to 1611. -/
private theorem checked_13_0 : CheckedCurvature 1580 1611 (199864072313 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1611 to 1642. -/
private theorem checked_14_0 : CheckedCurvature 1611 1642 (2081560211 / 15625000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1642 to 1704. -/
private theorem checked_15_0 : CheckedCurvature 1642 1704 (146655101471 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1704 to 1766. -/
private theorem checked_16_0 : CheckedCurvature 1704 1766 (54137772713 / 125000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1766 to 1828. -/
private theorem checked_17_0 : CheckedCurvature 1766 1828 (1694727035807 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1828 to 1890. -/
private theorem checked_18_0 : CheckedCurvature 1828 1890 (3621261921333 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- Check the signed curvature over dyadic indices 1890 to 1952. -/
private theorem checked_19_0 : CheckedCurvature 1890 1952 (7095934361887 / 1000000000) := by
  intro x hx
  exact
    k186_curv_le_of_compare (by decide) (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (by decide +kernel) hx

/-- The finite residual has the checked curvature on each of the twenty cells. -/
theorem k186_gap_curv_checked (i : Fin 20) {x : ℝ}
    (hx : x ∈ Set.Ioo ((k186FiniteCell i).left : ℝ) (k186FiniteCell i).right) :
    gaussianMidResidualCurv k186GapSlope (4 * (301 / 20000 + 1 / 6000)) k186GapRates k186GapProfiles
        x ≤
      ((k186FiniteCell i).upperCurvature : ℝ) := by
  fin_cases i
  · exact
      checked_to_cell 0 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (checked_split checked_0_0 checked_0_1) hx
  · exact
      checked_to_cell 1 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_1_0 hx
  · exact
      checked_to_cell 2 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_2_0 hx
  · exact
      checked_to_cell 3 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_3_0 hx
  · exact
      checked_to_cell 4 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_4_0 hx
  · exact
      checked_to_cell 5 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (checked_split checked_5_0 checked_5_1) hx
  · exact
      checked_to_cell 6 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_6_0 hx
  · exact
      checked_to_cell 7 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_7_0 hx
  · exact
      checked_to_cell 8 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_8_0 hx
  · exact
      checked_to_cell 9 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_9_0 hx
  · exact
      checked_to_cell 10 (by decide +kernel) (by decide +kernel) (by decide +kernel)
        (checked_split checked_10_0 checked_10_1) hx
  · exact
      checked_to_cell 11 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_11_0 hx
  · exact
      checked_to_cell 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_12_0 hx
  · exact
      checked_to_cell 13 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_13_0 hx
  · exact
      checked_to_cell 14 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_14_0 hx
  · exact
      checked_to_cell 15 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_15_0 hx
  · exact
      checked_to_cell 16 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_16_0 hx
  · exact
      checked_to_cell 17 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_17_0 hx
  · exact
      checked_to_cell 18 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_18_0 hx
  · exact
      checked_to_cell 19 (by decide +kernel) (by decide +kernel) (by decide +kernel) checked_19_0 hx

end PseudoPrime.PrimeTestBounds.MillerRabin
