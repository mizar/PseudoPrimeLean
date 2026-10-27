/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Signed alpha-18 numerical gap at logarithmic scale 22 trillion -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L at least 22 trillion, the quadratic scale exceeds one, its square root
lies between L/2 and L, and its fourth root is at most L/10^6.
These power estimates support the improved signed numerical comparison. -/
theorem triangular18_signed_large_scale_bounds {L : ℝ} (hL : (22000000000000 : ℝ) ≤ L) :
    let x := (282924 / 1000000 : ℝ) * L ^ 2;
    1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 := by
  let x := (282924 / 1000000 : ℝ) * L ^ 2
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hx : 1 < x := by
    dsimp only [x]
    nlinarith only [hL]
  have hcl : (1 / 4 : ℝ) ≤ 282924 / 1000000 := by norm_num only
  have hcu : (282924 / 1000000 : ℝ) ≤ 1 := by norm_num only
  have hcl' := mul_le_mul_of_nonneg_right hcl (sq_nonneg L)
  have hcu' := mul_le_mul_of_nonneg_right hcu (sq_nonneg L)
  have hquad : (L / 2) ^ 2 ≤ x := by
    change (L / 2) ^ 2 ≤ (282924 / 1000000 : ℝ) * L ^ 2
    nlinarith only [hcl']
  have hl : L / 2 ≤ Real.sqrt x := by exact (Real.le_sqrt (by positivity) (by positivity)).2 hquad
  have hu : Real.sqrt x ≤ L := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hLp.le
    · change (282924 / 1000000 : ℝ) * L ^ 2 ≤ L ^ 2
      nlinarith only [hcu']
  have ht : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul (zero_lt_one.trans hx).le (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hpow :=
    mul_le_mul_of_nonneg_right ((by norm_num only : (1000000000000 : ℝ) ≤ 22000000000000).trans hL)
      hLp.le
  have hquarter : x ^ (1 / 4 : ℝ) ≤ L / 1000000 := by
    have hp := Real.rpow_nonneg (zero_lt_one.trans hx).le (1 / 4)
    nlinarith only [ht, hu, hpow, hp, hLp]
  exact ⟨hx, hl, hu, hquarter⟩

/-- For L at least 22 trillion, use x^(1/16) ≥ 43 and sqrt(x) ≥ 531L/1000
to bound the signed cost by L/125. The square-root correction remains at most 100. -/
theorem triangular18_signed_large_scale_costs {L : ℝ} (hL : (22000000000000 : ℝ) ≤ L) :
    let x := (282924 / 1000000 : ℝ) * L ^ 2;
    (165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) ≤ L / 125 ∧
      36 * L / (Real.sqrt x - 1) ≤ 100 := by
  let x := (282924 / 1000000 : ℝ) * L ^ 2
  have h := triangular18_signed_large_scale_bounds hL
  change 1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 at h
  have hLp : 0 < L := by linarith only [hL]
  have hsmall : x ^ (-9 / 16 : ℝ) ≤ ((1000 / 531 : ℝ) / L) * (1 / 43 : ℝ) := by
    have hxlarge : (43 : ℝ) ^ 16 ≤ x := by
      dsimp only [x]; nlinarith only [hL]
    have hpos : 0 < x := by linarith only [h.1]
    have hpowfac : x ^ (-9 / 16 : ℝ) = (Real.sqrt x)⁻¹ * (x ^ (1 / 16 : ℝ))⁻¹ := by
      calc
        x ^ (-9 / 16 : ℝ) = x ^ ((-1 / 2 : ℝ) + (-1 / 16 : ℝ)) := by
          congr 1; ring
        _ = x ^ (-1 / 2 : ℝ) * x ^ (-1 / 16 : ℝ) := Real.rpow_add hpos _ _
        _ = (Real.sqrt x)⁻¹ * (x ^ (1 / 16 : ℝ))⁻¹ := by
          rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hpos.le]
          rw [← Real.sqrt_eq_rpow]
          rw [show (-1 / 16 : ℝ) = -(1 / 16) by ring, Real.rpow_neg hpos.le]
    have hsqrtLower : (531 / 1000 : ℝ) * L ≤ Real.sqrt x := by
      have hc : (531 / 1000 : ℝ) ^ 2 ≤ 282924 / 1000000 := by norm_num only
      have hsq := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
      have hy : 0 ≤ (531 / 1000 : ℝ) * L := mul_nonneg (by norm_num only) (le_of_lt hLp)
      dsimp only [x]
      exact (Real.le_sqrt hy (by positivity)).2 (by nlinarith only [hsq])
    have hsqrtInv : (Real.sqrt x)⁻¹ ≤ ((1000 / 531 : ℝ) / L) := by
      have h := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < (531 / 1000) * L) hsqrtLower
      have heq : (1 : ℝ) / ((531 / 1000 : ℝ) * L) = (1000 / 531 : ℝ) / L := by field_simp
      rw [heq] at h
      simpa only [one_div] using h
    have hroot16 : (43 : ℝ) ≤ x ^ (1 / 16 : ℝ) := by
      have hm :=
        Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (43 : ℝ) ^ 16) hxlarge
          (by norm_num only : (0 : ℝ) ≤ (1 / 16 : ℝ))
      have he : ((43 : ℝ) ^ 16) ^ (1 / 16 : ℝ) = 43 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 43)]
        norm_num only
      rw [he] at hm
      exact hm
    have hinv' : 1 / (x ^ (1 / 16 : ℝ)) ≤ 1 / 43 :=
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 43) hroot16
    have hinv : (x ^ (1 / 16 : ℝ))⁻¹ ≤ (1 / 43 : ℝ) := by simpa only [one_div] using hinv'
    rw [hpowfac]
    exact mul_le_mul hsqrtInv hinv (by positivity) (by positivity)
  have hratio : (L + 284) / L ≤ (1001 / 1000 : ℝ) := by
    apply (div_le_iff₀ hLp).2
    nlinarith only [hL]
  have ht : 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ 175400000000 := by
    have h1 := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 4000000000000 * (L + 284) by positivity)
    have h2 :
      4000000000000 * (L + 284) * (((1000 / 531 : ℝ) / L) * (1 / 43 : ℝ)) ≤ 175400000000 := by
      have heq :
        4000000000000 * (L + 284) * (((1000 / 531 : ℝ) / L) * (1 / 43 : ℝ)) =
          (4000000000000000 / 22833 : ℝ) * ((L + 284) / L) := by
        field_simp
        ring
      rw [heq]
      have hd :=
        mul_le_mul_of_nonneg_left hratio (by norm_num only : (0 : ℝ) ≤ 4000000000000000 / 22833)
      have hc : (4000000000000000 / 22833 : ℝ) * (1001 / 1000) ≤ 175400000000 := by norm_num only
      nlinarith only [hd, hc]
    exact h1.trans h2
  have hC : 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ L / 125 := by
    linarith only [ht, hL]
  have hd : 0 < Real.sqrt x - 1 := by linarith only [h.2.1, hL]
  have hB : 36 * L / (Real.sqrt x - 1) ≤ 100 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [h.2.1, hL]
  exact ⟨hC, hB⟩

/-- For L at least 22 trillion, the rational coefficient-0.282924 margin gives
(3601/100)L < (677/10)sqrt((282924/1000000)L^2).
This is the strict leading margin in the signed comparison. -/
theorem triangular18_signed_large_scale_main_margin {L : ℝ} (hL : (22000000000000 : ℝ) ≤ L) :
    (3601 / 100 : ℝ) * L < (677 / 10 : ℝ) * Real.sqrt ((282924 / 1000000 : ℝ) * L ^ 2) := by
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hxp : 0 < (282924 / 1000000 : ℝ) * L ^ 2 := mul_pos (by norm_num only) (sq_pos_of_pos hLp)
  have hs := Real.sq_sqrt hxp.le
  have hn := Real.sqrt_nonneg ((282924 / 1000000 : ℝ) * L ^ 2)
  have hnum : (3601 / 100 : ℝ) ^ 2 < (282924 / 1000000 : ℝ) * (677 / 10 : ℝ) ^ 2 := by norm_num only
  have hscale := mul_lt_mul_of_pos_right hnum (sq_pos_of_pos hLp)
  nlinarith only [hscale, hs, hn, hLp]

/-- For L at least 22 trillion and index h at least 10^9, the signed alpha-18
large-factor budget has a strict gap at x=(283/1000)L^2. Absorb the independent
scale-one cost by the index and apply the power and remainder bounds.
This removes the scalar-gap premise from the improved large-index witness. -/
theorem triangular18_signed_large_index_gap {L h : ℝ} (hL : (22000000000000 : ℝ) ≤ L)
    (hh : 1000000000 ≤ h) :
    let x := (282924 / 1000000 : ℝ) * L ^ 2;
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 +
        (h - 1) * (36 * L + 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  let x := (282924 / 1000000 : ℝ) * L ^ 2
  let C := 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hhp : 0 < h := lt_of_lt_of_le (by norm_num only) hh
  have hb := triangular18_signed_large_scale_bounds hL
  change 1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 at hb
  have hc := triangular18_signed_large_scale_costs hL
  change C ≤ L / 125 ∧ 36 * L / (Real.sqrt x - 1) ≤ 100 at hc
  have hm := triangular18_signed_large_scale_main_margin hL
  change (3601 / 100 : ℝ) * L < (677 / 10 : ℝ) * Real.sqrt x at hm
  have hn := Real.sqrt_nonneg x
  have ht := Real.rpow_nonneg (zero_lt_one.trans hb.1).le (1 / 4)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      add_nonneg (by norm_num only : (0 : ℝ) ≤ 165000)
        (mul_nonneg
          (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4000000000000)
            (by linarith only [hLp] : 0 ≤ L + 284))
          (Real.rpow_nonneg (zero_lt_one.trans hb.1).le _))
  have hC : 0 ≤ 36 * L + C := add_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 36) hLp.le) hC0
  have hpr := mul_le_mul_of_nonneg_right hh hn
  have hpt := mul_le_mul_of_nonneg_right hh ht
  have hcost0 := mul_le_mul_of_nonneg_right (by linarith only : h - 1 ≤ h) hC
  have hcost1 := mul_le_mul_of_nonneg_left (add_le_add_left hc.1 (36 * L)) hhp.le
  have hu :
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 + (h - 1) * (36 * L + C) ≤
      h *
        ((3 / 10 : ℝ) * Real.sqrt x + (13 / 10000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L + L / 125 +
          1) := by
    nlinarith only [hpr, hpt, hcost0, hcost1, hh]
  have hE := mul_nonneg hn (Real.exp_pos (-18)).le
  have hg :
    (3 / 10 : ℝ) * Real.sqrt x + (13 / 10000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L + L / 125 + 1 <
      Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        36 * L / (Real.sqrt x - 1) := by
    nlinarith only [hm, hb.2.2.2, hc.2, hL, hE]
  have hfinal := hu.trans_lt (mul_lt_mul_of_pos_left hg hhp)
  simpa only [C, add_assoc] using hfinal

end PseudoPrime.Analysis
