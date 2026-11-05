/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularJointSharp

/-! # Interior numerical cells for the joint triangular gap -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A rational cell margin implies the normalized joint interior gap throughout its
interval. Use the root and fourth-root bounds and the logarithmic endpoint signs. -/
theorem joint_margin_of_cell {x L T v y0 y1 : ℝ} (hT : 280 ≤ T) (hL : T ≤ L)
    (hylo : y0 ≤ Real.log x) (hyhi : Real.log x ≤ y1) (hy1 : y1 ≤ 36)
    (hroot : (5313 / 10000 : ℝ) * L ≤ Real.sqrt x) (hq0 : 0 ≤ x ^ (1 / 4 : ℝ))
    (hquarter : x ^ (1 / 4 : ℝ) ≤ (83 / 100 : ℝ) * L / v)
    (hcell :
      856 <
        ((220 - 4 * y1 - 3 / 10000) * (5313 / 10000) - (72 - y1) -
            (1064 / 5 - (19 / 5 : ℝ) * y0 + 13 / 10000000) * (83 / 100) / v) *
          T) :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + (72 - Real.log x) * L +
        856 <
      (220 - 4 * Real.log x) * Real.sqrt x -
        (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ) := by
  have hLp : 0 ≤ L := by linarith only [hT, hL]
  have hA : 0 ≤ (220 - 4 * Real.log x - 3 / 10000 : ℝ) := by linarith only [hyhi, hy1]
  have hB : 0 ≤ (1064 / 5 - (19 / 5 : ℝ) * y0 + 13 / 10000000 : ℝ) := by
    linarith only [hylo, hyhi, hy1]
  have hr := mul_le_mul_of_nonneg_left hroot hA
  have hq := mul_le_mul_of_nonneg_left hquarter hB
  have hyq :=
    mul_le_mul_of_nonneg_right
      (show
        (1064 / 5 - (19 / 5 : ℝ) * Real.log x + 13 / 10000000 : ℝ) ≤
          1064 / 5 - (19 / 5 : ℝ) * y0 + 13 / 10000000
        by linarith only [hylo])
      hq0
  have hyl :=
    mul_le_mul_of_nonneg_right
      (show ((1 - 4 * (5313 / 10000 : ℝ)) * y1) ≤ ((1 - 4 * (5313 / 10000 : ℝ)) * Real.log x) by
        nlinarith only [hyhi])
      hLp
  let d :=
    (220 - 4 * y1 - 3 / 10000) * (5313 / 10000) - (72 - y1) -
      (1064 / 5 - (19 / 5 : ℝ) * y0 + 13 / 10000000) * (83 / 100) / v
  have hd : 0 < d := by
    have ht : 0 ≤ T := by linarith only [hT]
    by_contra hn
    have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) ht
    change 856 < d * T at hcell
    linarith only [hcell, h]
  have ht := mul_le_mul_of_nonneg_left hL hd.le
  have hm : 856 < d * L := hcell.trans_le ht
  dsimp only [d] at hm
  simp only [div_eq_mul_inv] at hq hm
  nlinarith only [hr, hq, hyq, hyl, hm]

/-- A normalized joint margin implies the full large-index interior gap. The two
inverse-scale terms and the principal cost are absorbed into the index budget. -/
theorem joint_gap_of_margin {x L h : ℝ} (hx : 1 < x) (hu : x ≤ Real.exp 36) (hL : 0 ≤ L)
    (hh : 1000000000000 ≤ h)
    (hmargin :
      (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) +
          (72 - Real.log x) * L +
          856 <
        (220 - 4 * Real.log x) * Real.sqrt x -
          (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ)) :
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((72 - Real.log x) * L) <
      h *
        ((220 - 4 * Real.log x) * Real.sqrt x -
          (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ) -
          855) := by
  have hhp : 0 < h := by linarith only [hh]
  have hlog := Real.log_le_log (zero_lt_one.trans hx) hu
  rw [Real.log_exp] at hlog
  have hinv : x⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans hx)).2 hx.le
  have hinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hx).le
  have hsInv : Real.sqrt x⁻¹ ≤ 1 := Real.sqrt_le_one.mpr hinv
  have hrInv : (x⁻¹) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hinv0 hinv (by norm_num only)
  have hS : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hQ : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hpc : 0 ≤ (72 - Real.log x) * L := mul_nonneg (by linarith only [hlog]) hL
  have hidx := mul_le_mul_of_nonneg_right (by linarith only [] : h - 1 ≤ h) hpc
  have hpr := mul_le_mul_of_nonneg_right hh hS
  have hpq := mul_le_mul_of_nonneg_right hh hQ
  have hcost :
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((72 - Real.log x) * L) ≤
      h *
        ((3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) +
          (72 - Real.log x) * L +
          1) := by
    nlinarith only [hidx, hpr, hpq, hsInv, hrInv, hh]
  have hg :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + (72 - Real.log x) * L +
        1 <
      (220 - 4 * Real.log x) * Real.sqrt x -
        (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ) -
        855 := by
    linarith only [hmargin]
  exact hcost.trans_lt (mul_lt_mul_of_pos_left hg hhp)

end PseudoPrime.LLS.PaperStatements
