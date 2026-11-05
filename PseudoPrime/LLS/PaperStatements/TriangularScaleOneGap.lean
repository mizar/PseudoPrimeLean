/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneBounds

/-! # Numerical reduction of the interior scale-one gap -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At a large subgroup index and within triangular support, a normalized strict margin
implies the complete scale-one credited gap. Bound both inverse-scale terms and the pole
cost explicitly before restoring the positive exponential contribution. -/
theorem scaleOne_interior_gap_of_margin {x L h : ℝ} (hx : 1 < x) (hu : x ≤ Real.exp 36)
    (hL : 25000 ≤ L) (hh : 1000000000000 ≤ h) (hroot : (5313 / 10000 : ℝ) * L ≤ Real.sqrt x)
    (hmargin :
      (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) +
          (72 - Real.log x) * L +
          9961 <
        (220 - 4 * Real.log x) * Real.sqrt x - (4576 - 78 * Real.log x) * x ^ (1 / 4 : ℝ)) :
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((36 + triangularKernelProfile 18 x) * L + 11964) <
      h *
        ((220 - 4 * Real.log x + 4 * Real.exp (-18)) * Real.sqrt x -
              (4576 - 78 * Real.log x) * x ^ (1 / 4 : ℝ) +
            2104 -
          36 * L / (Real.sqrt x - 1)) := by
  have hLp : 0 < L := by linarith only [hL]
  have hhp : 0 < h := by linarith only [hh]
  have hy := Real.log_le_log (zero_lt_one.trans hx) hu
  rw [Real.log_exp] at hy
  have hp : triangularKernelProfile 18 x = 36 - Real.log x := by
    unfold triangularKernelProfile
    rw [abs_of_nonneg (Real.log_nonneg hx.le)]
    norm_num only
    exact max_eq_right (sub_nonneg.mpr hy)
  have hp0 : 0 ≤ triangularKernelProfile 18 x := triangularKernelProfile_nonneg 18 x
  have hinv : x⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans hx)).2 hx.le
  have hinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hx).le
  have hsInv : Real.sqrt x⁻¹ ≤ 1 := Real.sqrt_le_one.mpr hinv
  have hrInv : (x⁻¹) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hinv0 hinv (by norm_num only)
  have hden : 0 < Real.sqrt x - 1 := by nlinarith only [hroot, hL]
  have hpole : 36 * L / (Real.sqrt x - 1) ≤ 100 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hroot, hL]
  have hS : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hQ : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hpc : 0 ≤ (36 + triangularKernelProfile 18 x) * L + 11964 :=
    add_nonneg (mul_nonneg (add_nonneg (by norm_num only) hp0) hLp.le) (by norm_num only)
  have hidx := mul_le_mul_of_nonneg_right (by linarith only [] : h - 1 ≤ h) hpc
  have hpr := mul_le_mul_of_nonneg_right hh hS
  have hpq := mul_le_mul_of_nonneg_right hh hQ
  have hb :
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((36 + triangularKernelProfile 18 x) * L + 11964) ≤
      h *
        ((3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) +
          (72 - Real.log x) * L +
          11965) := by
    rw [hp] at hidx ⊢
    nlinarith only [hidx, hpr, hpq, hsInv, hrInv, hh]
  have hE := mul_nonneg hS (Real.exp_pos (-18)).le
  have hg :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + (72 - Real.log x) * L +
        11965 <
      (220 - 4 * Real.log x + 4 * Real.exp (-18)) * Real.sqrt x -
            (4576 - 78 * Real.log x) * x ^ (1 / 4 : ℝ) +
          2104 -
        36 * L / (Real.sqrt x - 1) := by
    nlinarith only [hmargin, hpole, hE]
  exact hb.trans_lt (mul_lt_mul_of_pos_left hg hhp)

/-- A rational cell margin implies the normalized interior gap throughout its interval.
Use the root and fourth-root bounds and the monotonic dependence on the logarithmic
endpoints; no enumeration of intermediate inputs is required. -/
theorem scaleOne_margin_of_cell {x L T v y0 y1 : ℝ} (hT : 25000 ≤ T) (hL : T ≤ L)
    (hylo : y0 ≤ Real.log x) (hyhi : Real.log x ≤ y1) (hy1 : y1 ≤ 36)
    (hroot : (5313 / 10000 : ℝ) * L ≤ Real.sqrt x) (hq0 : 0 ≤ x ^ (1 / 4 : ℝ))
    (hquarter : x ^ (1 / 4 : ℝ) ≤ (147 / 200 : ℝ) * L / v)
    (hcell :
      9961 <
        ((220 - 4 * y1 - 3 / 10000) * (5313 / 10000) - (72 - y1) -
            (4576 - 78 * y0 + 13 / 10000000) * (147 / 200) / v) *
          T) :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + (72 - Real.log x) * L +
        9961 <
      (220 - 4 * Real.log x) * Real.sqrt x - (4576 - 78 * Real.log x) * x ^ (1 / 4 : ℝ) := by
  have hLp : 0 ≤ L := by linarith only [hT, hL]
  have hA : 0 ≤ (220 - 4 * Real.log x - 3 / 10000 : ℝ) := by linarith only [hyhi, hy1]
  have hB : 0 ≤ (4576 - 78 * y0 + 13 / 10000000 : ℝ) := by linarith only [hylo, hyhi, hy1]
  have hr := mul_le_mul_of_nonneg_left hroot hA
  have hq := mul_le_mul_of_nonneg_left hquarter hB
  have hyq :=
    mul_le_mul_of_nonneg_right
      (show (4576 - 78 * Real.log x + 13 / 10000000 : ℝ) ≤ 4576 - 78 * y0 + 13 / 10000000 by
        linarith only [hylo])
      hq0
  have hyl :=
    mul_le_mul_of_nonneg_right
      (show ((1 - 4 * (5313 / 10000 : ℝ)) * y1) ≤ ((1 - 4 * (5313 / 10000 : ℝ)) * Real.log x) by
        nlinarith only [hyhi])
      hLp
  let d :=
    (220 - 4 * y1 - 3 / 10000) * (5313 / 10000) - (72 - y1) -
      (4576 - 78 * y0 + 13 / 10000000) * (147 / 200) / v
  have hd : 0 < d := by
    have ht : 0 ≤ T := by linarith only [hT]
    by_contra hn
    have h := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) ht
    change 9961 < d * T at hcell
    linarith only [hcell, h]
  have ht := mul_le_mul_of_nonneg_left hL hd.le
  have hm : 9961 < d * L := hcell.trans_le ht
  dsimp only [d] at hm
  simp only [div_eq_mul_inv] at hq hm
  nlinarith only [hr, hq, hyq, hyl, hm]

end PseudoPrime.LLS.PaperStatements
