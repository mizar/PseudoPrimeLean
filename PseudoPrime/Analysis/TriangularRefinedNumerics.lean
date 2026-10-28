/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.TriangularSignedLargeIndexNumerics

/-! # Earlier and sharper triangular large-index profiles -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L>=1.1 trillion, the quadratic scale exceeds one, its square root lies between
L/2 and L, and its fourth root is at most L/1000000.
Rational square comparisons and the rpow identity prove the size bounds. -/
theorem triangularEarlier_scale_bounds {L : ℝ} (hL : (1100000000000 : ℝ) ≤ L) :
    let x := (71 / 250 : ℝ) * L ^ 2;
    1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 := by
  let x := (71 / 250 : ℝ) * L ^ 2
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hx : 1 < x := by
    dsimp only [x]
    nlinarith only [hL]
  have hcl : (1 / 4 : ℝ) ≤ 71 / 250 := by norm_num only
  have hcu : (71 / 250 : ℝ) ≤ 1 := by norm_num only
  have hcl' := mul_le_mul_of_nonneg_right hcl (sq_nonneg L)
  have hcu' := mul_le_mul_of_nonneg_right hcu (sq_nonneg L)
  have hquad : (L / 2) ^ 2 ≤ x := by
    change (L / 2) ^ 2 ≤ (71 / 250 : ℝ) * L ^ 2
    nlinarith only [hcl']
  have hl : L / 2 ≤ Real.sqrt x := by
    exact
      (Real.le_sqrt (by linarith only [hLp] : (0 : ℝ) ≤ L / 2) (zero_lt_one.trans hx).le).2 hquad
  have hu : Real.sqrt x ≤ L := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hLp.le
    · change (71 / 250 : ℝ) * L ^ 2 ≤ L ^ 2
      nlinarith only [hcu']
  have ht : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul (zero_lt_one.trans hx).le (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hpow :=
    mul_le_mul_of_nonneg_right ((by norm_num only : (1000000000000 : ℝ) ≤ 1100000000000).trans hL)
      hLp.le
  have hquarter : x ^ (1 / 4 : ℝ) ≤ L / 1000000 := by
    have hp := Real.rpow_nonneg (zero_lt_one.trans hx).le (1 / 4)
    nlinarith only [ht, hu, hpow, hp, hLp]
  exact ⟨hx, hl, hu, hquarter⟩

/-- For L>=1.1 trillion, the signed secondary cost is at most (11777/50000)L
and the square-root pole correction is at most 100. Use x^(1/16)>=29 and
sqrt(x)>=(5329/10000)L, using the alpha-18 triangular kernel. -/
theorem triangularEarlier_scale_costs {L : ℝ} (hL : (1100000000000 : ℝ) ≤ L) :
    let x := (71 / 250 : ℝ) * L ^ 2;
    (165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) ≤ (11777 / 50000 : ℝ) * L ∧
      36 * L / (Real.sqrt x - 1) ≤ 100 := by
  let x := (71 / 250 : ℝ) * L ^ 2
  have h := triangularEarlier_scale_bounds hL
  change 1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 at h
  have hLp : 0 < L := by linarith only [hL]
  have hsmall : x ^ (-9 / 16 : ℝ) ≤ ((10000 / 5329 : ℝ) / L) * (1 / 29 : ℝ) := by
    have hxlarge : (29 : ℝ) ^ 16 ≤ x := by
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
    have hsqrtLower : (5329 / 10000 : ℝ) * L ≤ Real.sqrt x := by
      have hc : (5329 / 10000 : ℝ) ^ 2 ≤ 71 / 250 := by norm_num only
      have hsq := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
      have hy : 0 ≤ (5329 / 10000 : ℝ) * L := mul_nonneg (by norm_num only) (le_of_lt hLp)
      dsimp only [x]
      exact
        (Real.le_sqrt hy (mul_nonneg (by norm_num only) (sq_nonneg L))).2 (by nlinarith only [hsq])
    have hsqrtInv : (Real.sqrt x)⁻¹ ≤ ((10000 / 5329 : ℝ) / L) := by
      have h :=
        one_div_le_one_div_of_le (mul_pos (by norm_num only) hLp : (0 : ℝ) < (5329 / 10000) * L)
          hsqrtLower
      have heq : (1 : ℝ) / ((5329 / 10000 : ℝ) * L) = (10000 / 5329 : ℝ) / L := by
        simp only [one_div, mul_inv_rev, inv_div]
        ring
      rw [heq] at h
      simpa only [one_div] using h
    have hroot16 : (29 : ℝ) ≤ x ^ (1 / 16 : ℝ) := by
      have hm :=
        Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ (29 : ℝ) ^ 16) hxlarge
          (by norm_num only : (0 : ℝ) ≤ (1 / 16 : ℝ))
      have he : ((29 : ℝ) ^ 16) ^ (1 / 16 : ℝ) = 29 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 29)]
        norm_num only
      rw [he] at hm
      exact hm
    have hinv' : 1 / (x ^ (1 / 16 : ℝ)) ≤ 1 / 29 :=
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 29) hroot16
    have hinv : (x ^ (1 / 16 : ℝ))⁻¹ ≤ (1 / 29 : ℝ) := by simpa only [one_div] using hinv'
    rw [hpowfac]
    exact
      mul_le_mul hsqrtInv hinv (inv_nonneg.mpr (Real.rpow_nonneg hpos.le _))
        (div_nonneg (by norm_num only) hLp.le)
  have hratio : (L + 284) / L ≤ (1001 / 1000 : ℝ) := by
    apply (div_le_iff₀ hLp).2
    nlinarith only [hL]
  have ht : 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ 259090000000 := by
    have h1 :=
      mul_le_mul_of_nonneg_left hsmall
        (show 0 ≤ 4000000000000 * (L + 284) from
          mul_nonneg (by norm_num only) (by linarith only [hLp]))
    have h2 :
      4000000000000 * (L + 284) * (((10000 / 5329 : ℝ) / L) * (1 / 29 : ℝ)) ≤ 259090000000 := by
      have heq :
        4000000000000 * (L + 284) * (((10000 / 5329 : ℝ) / L) * (1 / 29 : ℝ)) =
          (40000000000000000 / 154541 : ℝ) * ((L + 284) / L) := by
        ring
      rw [heq]
      have hd :=
        mul_le_mul_of_nonneg_left hratio (by norm_num only : (0 : ℝ) ≤ 40000000000000000 / 154541)
      have hc : (40000000000000000 / 154541 : ℝ) * (1001 / 1000) ≤ 259090000000 := by norm_num only
      nlinarith only [hd, hc]
    exact h1.trans h2
  have hC : 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ (11777 / 50000 : ℝ) * L := by
    linarith only [ht, hL]
  have hd : 0 < Real.sqrt x - 1 := by linarith only [h.2.1, hL]
  have hB : 36 * L / (Real.sqrt x - 1) ≤ 100 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [h.2.1, hL]
  exact ⟨hC, hB⟩

/-- For L>=1.1 trillion, the square root of (71/250)L^2 is at least
(5329/10000)L. Compare nonnegative squares using the strict rational coefficient margin. -/
theorem triangularEarlier_root_lower {L : ℝ} (hL : (1100000000000 : ℝ) ≤ L) :
    (5329 / 10000 : ℝ) * L ≤ Real.sqrt ((71 / 250 : ℝ) * L ^ 2) := by
  have hLp : 0 ≤ L := by linarith only [hL]
  apply
    (Real.le_sqrt (mul_nonneg (by norm_num only) hLp)
        (mul_nonneg (by norm_num only) (sq_nonneg L))).mpr
  nlinarith only [sq_nonneg L]

/-- For L>=1.1 trillion and subgroup index h>=10^12, the original alpha-18 signed
comparison has a strict gap at x=(71/250)L^2. Absorb the independent cost
by the new index split and retain a positive rational leading margin.
The rational margin closes the corresponding refined large-index branch. -/
theorem triangularEarlier_gap {L h : ℝ} (hL : (1100000000000 : ℝ) ≤ L) (hh : 1000000000000 ≤ h) :
    let x := (71 / 250 : ℝ) * L ^ 2;
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 +
        (h - 1) * (36 * L + 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  let x := (71 / 250 : ℝ) * L ^ 2
  let C := 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)
  have hLp : 0 < L := by linarith only [hL]
  have hhp : 0 < h := by linarith only [hh]
  have hb := triangularEarlier_scale_bounds hL
  change 1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 at hb
  have hc := triangularEarlier_scale_costs hL
  change C ≤ (11777 / 50000 : ℝ) * L ∧ 36 * L / (Real.sqrt x - 1) ≤ 100 at hc
  have hs := triangularEarlier_root_lower hL
  change (5329 / 10000 : ℝ) * L ≤ Real.sqrt x at hs
  have hn := Real.sqrt_nonneg x
  have ht := Real.rpow_nonneg (zero_lt_one.trans hb.1).le (1 / 4)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      add_nonneg (by norm_num only)
        (mul_nonneg (mul_nonneg (by norm_num only) (by linarith only [hLp]))
          (Real.rpow_nonneg (zero_lt_one.trans hb.1).le _))
  have hC : 0 ≤ 36 * L + C := add_nonneg (mul_nonneg (by norm_num only) hLp.le) hC0
  have hpr := mul_le_mul_of_nonneg_right hh hn
  have hpt := mul_le_mul_of_nonneg_right hh ht
  have hcost0 := mul_le_mul_of_nonneg_right (by linarith only [] : h - 1 ≤ h) hC
  have hcost1 := mul_le_mul_of_nonneg_left (add_le_add_left hc.1 (36 * L)) hhp.le
  have hu :
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 + (h - 1) * (36 * L + C) ≤
      h *
        ((3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L +
          (11777 / 50000) * L +
          1) := by
    nlinarith only [hpr, hpt, hcost0, hcost1, hh]
  have hE := mul_nonneg hn (Real.exp_pos (-18)).le
  have hg :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L +
        (11777 / 50000) * L +
        1 <
      Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        36 * L / (Real.sqrt x - 1) := by
    nlinarith only [hs, hb.2.2.2, hc.2, hL, hE]
  have hfinal := hu.trans_lt (mul_lt_mul_of_pos_left hg hhp)
  simpa only [C, add_assoc] using hfinal

/-- For L>=2 trillion, the quadratic scale exceeds one, its square root lies between
L/2 and L, and its fourth root is at most L/1000000.
Rational square comparisons and the rpow identity prove the size bounds. -/
theorem triangularRefined_scale_bounds {L : ℝ} (hL : (2000000000000 : ℝ) ≤ L) :
    let x := (28237 / 100000 : ℝ) * L ^ 2;
    1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 := by
  let x := (28237 / 100000 : ℝ) * L ^ 2
  have hLp : 0 < L := lt_of_lt_of_le (by norm_num only) hL
  have hx : 1 < x := by
    dsimp only [x]
    nlinarith only [hL]
  have hcl : (1 / 4 : ℝ) ≤ 28237 / 100000 := by norm_num only
  have hcu : (28237 / 100000 : ℝ) ≤ 1 := by norm_num only
  have hcl' := mul_le_mul_of_nonneg_right hcl (sq_nonneg L)
  have hcu' := mul_le_mul_of_nonneg_right hcu (sq_nonneg L)
  have hquad : (L / 2) ^ 2 ≤ x := by
    change (L / 2) ^ 2 ≤ (28237 / 100000 : ℝ) * L ^ 2
    nlinarith only [hcl']
  have hl : L / 2 ≤ Real.sqrt x := by
    exact
      (Real.le_sqrt (by linarith only [hLp] : (0 : ℝ) ≤ L / 2) (zero_lt_one.trans hx).le).2 hquad
  have hu : Real.sqrt x ≤ L := by
    apply (Real.sqrt_le_iff).2
    constructor
    · exact hLp.le
    · change (28237 / 100000 : ℝ) * L ^ 2 ≤ L ^ 2
      nlinarith only [hcu']
  have ht : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul (zero_lt_one.trans hx).le (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hpow :=
    mul_le_mul_of_nonneg_right ((by norm_num only : (1000000000000 : ℝ) ≤ 2000000000000).trans hL)
      hLp.le
  have hquarter : x ^ (1 / 4 : ℝ) ≤ L / 1000000 := by
    have hp := Real.rpow_nonneg (zero_lt_one.trans hx).le (1 / 4)
    nlinarith only [ht, hu, hpow, hp, hLp]
  exact ⟨hx, hl, hu, hquarter⟩

/-- For L>=2 trillion, the signed secondary cost is at most (123/1000)L
and the square-root pole correction is at most 100. Use x^(1/16)>=31 and
sqrt(x)>=(5313/10000)L, using the alpha-18 triangular kernel. -/
theorem triangularRefined_scale_costs {L : ℝ} (hL : (2000000000000 : ℝ) ≤ L) :
    let x := (28237 / 100000 : ℝ) * L ^ 2;
    (165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) ≤ (123 / 1000 : ℝ) * L ∧
      36 * L / (Real.sqrt x - 1) ≤ 100 := by
  let x := (28237 / 100000 : ℝ) * L ^ 2
  have h := triangularRefined_scale_bounds hL
  change 1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 at h
  have hLp : 0 < L := by linarith only [hL]
  have hsmall : x ^ (-9 / 16 : ℝ) ≤ ((10000 / 5313 : ℝ) / L) * (1 / 31 : ℝ) := by
    have hxlarge : (31 : ℝ) ^ 16 ≤ x := by
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
    have hsqrtLower : (5313 / 10000 : ℝ) * L ≤ Real.sqrt x := by
      have hc : (5313 / 10000 : ℝ) ^ 2 ≤ 28237 / 100000 := by norm_num only
      have hsq := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
      have hy : 0 ≤ (5313 / 10000 : ℝ) * L := mul_nonneg (by norm_num only) (le_of_lt hLp)
      dsimp only [x]
      exact
        (Real.le_sqrt hy (mul_nonneg (by norm_num only) (sq_nonneg L))).2 (by nlinarith only [hsq])
    have hsqrtInv : (Real.sqrt x)⁻¹ ≤ ((10000 / 5313 : ℝ) / L) := by
      have h :=
        one_div_le_one_div_of_le (mul_pos (by norm_num only) hLp : (0 : ℝ) < (5313 / 10000) * L)
          hsqrtLower
      have heq : (1 : ℝ) / ((5313 / 10000 : ℝ) * L) = (10000 / 5313 : ℝ) / L := by
        simp only [one_div, mul_inv_rev, inv_div]
        ring
      rw [heq] at h
      simpa only [one_div] using h
    have hroot16 : (31 : ℝ) ≤ x ^ (1 / 16 : ℝ) := by
      have hm :=
        Real.rpow_le_rpow (by norm_num only : (0 : ℝ) ≤ (31 : ℝ) ^ 16) hxlarge
          (by norm_num only : (0 : ℝ) ≤ (1 / 16 : ℝ))
      have he : ((31 : ℝ) ^ 16) ^ (1 / 16 : ℝ) = 31 := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul (by norm_num only : (0 : ℝ) ≤ 31)]
        norm_num only
      rw [he] at hm
      exact hm
    have hinv' : 1 / (x ^ (1 / 16 : ℝ)) ≤ 1 / 31 :=
      one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 31) hroot16
    have hinv : (x ^ (1 / 16 : ℝ))⁻¹ ≤ (1 / 31 : ℝ) := by simpa only [one_div] using hinv'
    rw [hpowfac]
    exact
      mul_le_mul hsqrtInv hinv (inv_nonneg.mpr (Real.rpow_nonneg hpos.le _))
        (div_nonneg (by norm_num only) hLp.le)
  have hratio : (L + 284) / L ≤ (1001 / 1000 : ℝ) := by
    apply (div_le_iff₀ hLp).2
    nlinarith only [hL]
  have ht : 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ 244000000000 := by
    have h1 :=
      mul_le_mul_of_nonneg_left hsmall
        (show 0 ≤ 4000000000000 * (L + 284) from
          mul_nonneg (by norm_num only) (by linarith only [hLp]))
    have h2 :
      4000000000000 * (L + 284) * (((10000 / 5313 : ℝ) / L) * (1 / 31 : ℝ)) ≤ 244000000000 := by
      have heq :
        4000000000000 * (L + 284) * (((10000 / 5313 : ℝ) / L) * (1 / 31 : ℝ)) =
          (40000000000000000 / 164703 : ℝ) * ((L + 284) / L) := by
        ring
      rw [heq]
      have hd :=
        mul_le_mul_of_nonneg_left hratio (by norm_num only : (0 : ℝ) ≤ 40000000000000000 / 164703)
      have hc : (40000000000000000 / 164703 : ℝ) * (1001 / 1000) ≤ 244000000000 := by norm_num only
      nlinarith only [hd, hc]
    exact h1.trans h2
  have hC : 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ (123 / 1000 : ℝ) * L := by
    linarith only [ht, hL]
  have hd : 0 < Real.sqrt x - 1 := by linarith only [h.2.1, hL]
  have hB : 36 * L / (Real.sqrt x - 1) ≤ 100 := by
    apply (div_le_iff₀ hd).mpr
    nlinarith only [h.2.1, hL]
  exact ⟨hC, hB⟩

/-- For L>=2 trillion, the square root of (28237/100000)L^2 is at least
(5313/10000)L. Compare nonnegative squares using the strict rational coefficient margin. -/
theorem triangularRefined_root_lower {L : ℝ} (hL : (2000000000000 : ℝ) ≤ L) :
    (5313 / 10000 : ℝ) * L ≤ Real.sqrt ((28237 / 100000 : ℝ) * L ^ 2) := by
  have hLp : 0 ≤ L := by linarith only [hL]
  apply
    (Real.le_sqrt (mul_nonneg (by norm_num only) hLp)
        (mul_nonneg (by norm_num only) (sq_nonneg L))).mpr
  nlinarith only [sq_nonneg L]

/-- For L>=2 trillion and subgroup index h>=10^12, the original alpha-18 signed
comparison has a strict gap at x=(28237/100000)L^2. Absorb the independent cost
by the new index split and retain a positive rational leading margin.
The rational margin closes the corresponding refined large-index branch. -/
theorem triangularRefined_gap {L h : ℝ} (hL : (2000000000000 : ℝ) ≤ L) (hh : 1000000000000 ≤ h) :
    let x := (28237 / 100000 : ℝ) * L ^ 2;
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 +
        (h - 1) * (36 * L + 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  let x := (28237 / 100000 : ℝ) * L ^ 2
  let C := 165000 + 4000000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)
  have hLp : 0 < L := by linarith only [hL]
  have hhp : 0 < h := by linarith only [hh]
  have hb := triangularRefined_scale_bounds hL
  change 1 < x ∧ L / 2 ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / 1000000 at hb
  have hc := triangularRefined_scale_costs hL
  change C ≤ (123 / 1000 : ℝ) * L ∧ 36 * L / (Real.sqrt x - 1) ≤ 100 at hc
  have hs := triangularRefined_root_lower hL
  change (5313 / 10000 : ℝ) * L ≤ Real.sqrt x at hs
  have hn := Real.sqrt_nonneg x
  have ht := Real.rpow_nonneg (zero_lt_one.trans hb.1).le (1 / 4)
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact
      add_nonneg (by norm_num only)
        (mul_nonneg (mul_nonneg (by norm_num only) (by linarith only [hLp]))
          (Real.rpow_nonneg (zero_lt_one.trans hb.1).le _))
  have hC : 0 ≤ 36 * L + C := add_nonneg (mul_nonneg (by norm_num only) hLp.le) hC0
  have hpr := mul_le_mul_of_nonneg_right hh hn
  have hpt := mul_le_mul_of_nonneg_right hh ht
  have hcost0 := mul_le_mul_of_nonneg_right (by linarith only [] : h - 1 ≤ h) hC
  have hcost1 := mul_le_mul_of_nonneg_left (add_le_add_left hc.1 (36 * L)) hhp.le
  have hu :
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 + (h - 1) * (36 * L + C) ≤
      h *
        ((3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L +
          (123 / 1000) * L +
          1) := by
    nlinarith only [hpr, hpt, hcost0, hcost1, hh]
  have hE := mul_nonneg hn (Real.exp_pos (-18)).le
  have hg :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L +
        (123 / 1000) * L +
        1 <
      Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        36 * L / (Real.sqrt x - 1) := by
    nlinarith only [hs, hb.2.2.2, hc.2, hL, hE]
  have hfinal := hu.trans_lt (mul_lt_mul_of_pos_left hg hhp)
  simpa only [C, add_assoc] using hfinal

end PseudoPrime.Analysis
