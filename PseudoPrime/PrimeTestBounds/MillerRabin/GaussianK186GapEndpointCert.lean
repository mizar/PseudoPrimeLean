/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapEndpoint

import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapEval
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapExp
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186FiniteCells
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186GapEndpoint

/-! # Shared endpoint certificates for the twenty K186 cells -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The dyadic endpoint indices and lower estimates in increasing order. -/
private def endpoints : Fin 21 → ℕ × ℚ :=
  ![(960, 1300658689 / 200000000), (1084, 8475235193 / 1000000000), (1146, 8147793981 / 1000000000),
    (1208, 7822676527 / 1000000000), (1239, 7457300537 / 1000000000),
    (1270, 7290545341 / 1000000000), (1332, 7983205669 / 1000000000),
    (1363, 7582737401 / 1000000000), (1394, 8057347463 / 1000000000), (1425, 746451793 / 62500000),
    (1456, 9377930133 / 500000000), (1518, 26287913833 / 1000000000),
    (1549, 31140692547 / 1000000000), (1580, 13516450501 / 250000000),
    (1611, 22427070563 / 200000000), (1642, 43508906053 / 200000000),
    (1704, 612320798507 / 1000000000), (1766, 1495212496081 / 1000000000),
    (1828, 1899335159301 / 500000000), (1890, 1250632389111 / 125000000),
    (1952, 26475625976097 / 1000000000)]

/-- Certify the lower residual value at endpoint 0. -/
private theorem endpoint_0 :
    ((endpoints 0).2 : ℝ) ≤ k186FiniteGap (((endpoints 0).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 1. -/
private theorem endpoint_1 :
    ((endpoints 1).2 : ℝ) ≤ k186FiniteGap (((endpoints 1).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 2. -/
private theorem endpoint_2 :
    ((endpoints 2).2 : ℝ) ≤ k186FiniteGap (((endpoints 2).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 3. -/
private theorem endpoint_3 :
    ((endpoints 3).2 : ℝ) ≤ k186FiniteGap (((endpoints 3).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 4. -/
private theorem endpoint_4 :
    ((endpoints 4).2 : ℝ) ≤ k186FiniteGap (((endpoints 4).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 5. -/
private theorem endpoint_5 :
    ((endpoints 5).2 : ℝ) ≤ k186FiniteGap (((endpoints 5).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 6. -/
private theorem endpoint_6 :
    ((endpoints 6).2 : ℝ) ≤ k186FiniteGap (((endpoints 6).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 7. -/
private theorem endpoint_7 :
    ((endpoints 7).2 : ℝ) ≤ k186FiniteGap (((endpoints 7).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 8. -/
private theorem endpoint_8 :
    ((endpoints 8).2 : ℝ) ≤ k186FiniteGap (((endpoints 8).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 9. -/
private theorem endpoint_9 :
    ((endpoints 9).2 : ℝ) ≤ k186FiniteGap (((endpoints 9).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 10. -/
private theorem endpoint_10 :
    ((endpoints 10).2 : ℝ) ≤ k186FiniteGap (((endpoints 10).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 11. -/
private theorem endpoint_11 :
    ((endpoints 11).2 : ℝ) ≤ k186FiniteGap (((endpoints 11).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 12. -/
private theorem endpoint_12 :
    ((endpoints 12).2 : ℝ) ≤ k186FiniteGap (((endpoints 12).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 13. -/
private theorem endpoint_13 :
    ((endpoints 13).2 : ℝ) ≤ k186FiniteGap (((endpoints 13).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 14. -/
private theorem endpoint_14 :
    ((endpoints 14).2 : ℝ) ≤ k186FiniteGap (((endpoints 14).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 15. -/
private theorem endpoint_15 :
    ((endpoints 15).2 : ℝ) ≤ k186FiniteGap (((endpoints 15).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 16. -/
private theorem endpoint_16 :
    ((endpoints 16).2 : ℝ) ≤ k186FiniteGap (((endpoints 16).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 17. -/
private theorem endpoint_17 :
    ((endpoints 17).2 : ℝ) ≤ k186FiniteGap (((endpoints 17).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 18. -/
private theorem endpoint_18 :
    ((endpoints 18).2 : ℝ) ≤ k186FiniteGap (((endpoints 18).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 19. -/
private theorem endpoint_19 :
    ((endpoints 19).2 : ℝ) ≤ k186FiniteGap (((endpoints 19).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- Certify the lower residual value at endpoint 20. -/
private theorem endpoint_20 :
    ((endpoints 20).2 : ℝ) ≤ k186FiniteGap (((endpoints 20).1 : ℝ) / 32) := by
  exact
    k186_gap_lower_of_compare _ (k186_gap_exp_lower_pos _) (k186_gap_exp_lower_pos _)
      (k186_gap_exp_lower_pos _) (by decide +kernel)

/-- The checked estimates, indexed by the distinct endpoints. -/
private theorem endpoint_lower (i : Fin 21) :
    ((endpoints i).2 : ℝ) ≤ k186FiniteGap (((endpoints i).1 : ℝ) / 32) := by
  fin_cases i
  · exact endpoint_0
  · exact endpoint_1
  · exact endpoint_2
  · exact endpoint_3
  · exact endpoint_4
  · exact endpoint_5
  · exact endpoint_6
  · exact endpoint_7
  · exact endpoint_8
  · exact endpoint_9
  · exact endpoint_10
  · exact endpoint_11
  · exact endpoint_12
  · exact endpoint_13
  · exact endpoint_14
  · exact endpoint_15
  · exact endpoint_16
  · exact endpoint_17
  · exact endpoint_18
  · exact endpoint_19
  · exact endpoint_20

/-- Each left endpoint uses the corresponding entry of the shared certificate. -/
theorem k186_gap_left_checked (i : Fin 20) :
    ((k186FiniteCell i).lowerLeft : ℝ) ≤ k186FiniteGap (k186FiniteCell i).left := by
  have he :
    (k186FiniteCell i).left = ((endpoints i.castSucc).1 : ℚ) / 32 ∧
      (k186FiniteCell i).lowerLeft = (endpoints i.castSucc).2 := by
    fin_cases i <;> decide +kernel
  rw [he.1, he.2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  exact endpoint_lower i.castSucc

/-- Each right endpoint uses the next entry of the shared certificate. -/
theorem k186_gap_right_checked (i : Fin 20) :
    ((k186FiniteCell i).lowerRight : ℝ) ≤ k186FiniteGap (k186FiniteCell i).right := by
  have he :
    (k186FiniteCell i).right = ((endpoints i.succ).1 : ℚ) / 32 ∧
      (k186FiniteCell i).lowerRight = (endpoints i.succ).2 := by
    fin_cases i <;> decide +kernel
  rw [he.1, he.2, Rat.cast_div, Rat.cast_natCast, Rat.cast_ofNat]
  exact endpoint_lower i.succ

end PseudoPrime.PrimeTestBounds.MillerRabin
