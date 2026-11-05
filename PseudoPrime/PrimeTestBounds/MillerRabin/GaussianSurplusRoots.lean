/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianBudgetRoots
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Gaussian surplus radius and clipped quadratic budget -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The positive Gaussian budget root at residual R and logarithmic scale L. -/
noncomputable def jointSurplusRoot (R L : ℝ) : ℝ :=
  Analysis.gaussianBudgetRoot (10971611 / 5000000) (28794111 / 12500000)
    ((20115621 / 25000000) * L + R)

/-- Clip the squared Gaussian root below by the prefix-dependent radius floor. -/
noncomputable def jointSurplusRadius (rho R L : ℝ) : ℝ :=
  max rho (jointSurplusRoot R L ^ 2)

/-- For nonnegative scale and floor and positive residual, the clipped radius retains
the Gaussian quadratic budget as an inequality. The proof uses the root equation only
before clipping, then applies the existing monotone budget theorem. -/
theorem jointSurplus_budget {rho R L : ℝ} (hrho : 0 ≤ rho) (hR : 0 < R) (hL : 0 ≤ L) :
    (20115621 / 25000000 : ℝ) * L + R +
        (28794111 / 12500000 : ℝ) * Real.sqrt (jointSurplusRadius rho R L) ≤
      (10971611 / 5000000 : ℝ) * jointSurplusRadius rho R L := by
  let D : ℝ := 10971611 / 5000000
  let V : ℝ := 28794111 / 12500000
  let C : ℝ := (20115621 / 25000000) * L + R
  let s := jointSurplusRoot R L
  let r := jointSurplusRadius rho R L
  have hD : 0 < D := by norm_num only [D]
  have hV : 0 < V := by norm_num only [V]
  have hC : 0 < C := by
    dsimp only [C]
    have h := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 20115621 / 25000000) hL
    linarith only [h, hR]
  have hs : 0 < s := Analysis.gaussianBudgetRoot_pos hD hV
  have he : D * s ^ 2 = V * s + C := Analysis.gaussianBudgetRoot_equation hD hC.le
  have hDr : V < D * s := by
    by_contra hn
    have hm := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hs.le
    nlinarith only [hm, he, hC]
  have hr0 : 0 ≤ r := hrho.trans (le_max_left _ _)
  have hsq : s ^ 2 ≤ r := le_max_right _ _
  have hsroot : s ≤ Real.sqrt r := (Real.le_sqrt hs.le hr0).mpr hsq
  have hDr' : V < D * Real.sqrt r := hDr.trans_le (mul_le_mul_of_nonneg_left hsroot hD.le)
  have hb := Analysis.gaussianBudget_of_root_le hD hV hC.le hDr' hsroot
  rw [Real.sq_sqrt hr0] at hb
  exact hb

/-- If r times t^8 is at least one, t bounds the inverse eighth root of r.
This transfers a rational endpoint certificate to every larger radius. -/
theorem jointSurplus_invEighth_le {r t : ℝ} (hr : 0 < r) (ht : 0 ≤ t) (hbound : 1 ≤ r * t ^ 8) :
    r ^ (-(1 / 8 : ℝ)) ≤ t := by
  have hinv : r⁻¹ ≤ t ^ 8 := by
    rw [← one_div]
    exact (div_le_iff₀ hr).2 (by nlinarith only [hbound])
  have hp := Real.rpow_le_rpow (inv_nonneg.mpr hr.le) hinv (by norm_num only : (0 : ℝ) ≤ 1 / 8)
  have hl : (r⁻¹) ^ (1 / 8 : ℝ) = r ^ (-(1 / 8 : ℝ)) := by
    rw [Real.inv_rpow hr.le, Real.rpow_neg hr.le]
  have ht8 : (t ^ 8) ^ (1 / 8 : ℝ) = t := by
    rw [← Real.rpow_natCast t 8, ← Real.rpow_mul ht]
    norm_num only [Real.rpow_one]
  simpa only [hl, ht8] using hp

/-- A rational discriminant inequality gives a uniform strict quadratic upper bound.
Complete the square; no sampling of the inverse-radius variable is needed. -/
theorem jointSurplus_quadratic_lt {b0 b1 H R z : ℝ} (hH : 0 < H)
    (hcert : b1 ^ 2 < 4 * H * (R - b0)) : b0 + b1 * z - H * z ^ 2 < R := by
  have hs := sq_nonneg (2 * H * z - b1)
  have hid : 4 * H * (b1 * z - H * z ^ 2) = b1 ^ 2 - (2 * H * z - b1) ^ 2 := by ring
  have hu : 4 * H * (b1 * z - H * z ^ 2) ≤ b1 ^ 2 := by linarith only [hid, hs]
  have hm : 4 * H * (b1 * z - H * z ^ 2) < 4 * H * (R - b0) := hu.trans_lt hcert
  have h4 : 0 < 4 * H := mul_pos (by norm_num only) hH
  by_contra hn
  have hz : 0 ≤ (4 * H) * ((b1 * z - H * z ^ 2) - (R - b0)) :=
    mul_nonneg h4.le (by linarith only [hn])
  nlinarith only [hm, hz]

/-- Rewrite the Gaussian ninth-eighth tail as an inverse radius times an inverse
eighth root. This form permits a rational endpoint bound. -/
theorem jointSurplus_tail_eq {r : ℝ} (hr : 0 < r) :
    (r ^ 2) ^ (-9 / 16 : ℝ) = r⁻¹ * r ^ (-(1 / 8 : ℝ)) := by
  have h : (r ^ 2) ^ (-9 / 16 : ℝ) = r ^ (-(9 / 8 : ℝ)) := by
    rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr.le]
    norm_num only
  rw [h, show (-(9 / 8 : ℝ)) = -1 + (-(1 / 8 : ℝ)) by norm_num only, Real.rpow_add hr,
    Real.rpow_neg_one]

end PseudoPrime.PrimeTestBounds.MillerRabin
