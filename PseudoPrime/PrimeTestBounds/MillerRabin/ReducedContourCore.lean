/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularCore

/-! # Triangular budgets with reduced contour cost and lower entrances -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Triangular budgets for the reduced contour coefficient at entrances at least
one million. The fields certify the radius, root floors, and strict signed gap. -/
structure ReducedContourCore where
  C : ℝ
  T : ℝ
  a : ℝ
  m : ℝ
  v : ℝ
  b : ℝ
  entry : 1000000 ≤ T
  root : 1 / 2 < a
  localBudget : 14 < (a - 1 / 2) * T
  square : a ^ 2 ≤ C
  upper : C ≤ 1
  root16 : 0 < m ∧ m ^ 16 ≤ C * T ^ 2
  fourth : 0 < v ∧ v ^ 2 ≤ T
  cost : 165000 + 8000000000 * (1001 / 1000) / (a * m) ≤ b * T
  margin : (36 + b + (1456 + 13 / 10000000) / v) * T + 101 < (68 - 3 / 10000) * a * T

/-- The core profile bounds its radius and fourth root above the entrance. -/
theorem reducedContourCore_roots (f : ReducedContourCore) {L : ℝ} (hL : f.T ≤ L) :
    let x := f.C * L ^ 2;
    1 < x ∧ f.a * L ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / f.v := by
  have hLp : 0 < L := by linarith only [f.entry, hL]
  have ha : 0 < f.a := by linarith only [f.root]
  have hC : 0 ≤ f.C := (sq_nonneg f.a).trans f.square
  have hl : f.a * L ≤ Real.sqrt (f.C * L ^ 2) := by
    apply (Real.le_sqrt (mul_nonneg ha.le hLp.le) (mul_nonneg hC (sq_nonneg L))).2
    nlinarith only [mul_le_mul_of_nonneg_right f.square (sq_nonneg L)]
  have hh : L / 2 ≤ Real.sqrt (f.C * L ^ 2) := by
    nlinarith only [hl, mul_le_mul_of_nonneg_right f.root.le hLp.le]
  have hx : 1 < f.C * L ^ 2 := by
    nlinarith only [Real.sq_sqrt (mul_nonneg hC (sq_nonneg L)), hh, hL, f.entry]
  have hu : Real.sqrt (f.C * L ^ 2) ≤ L := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨hLp.le, by nlinarith only [mul_le_mul_of_nonneg_right f.upper (sq_nonneg L)]⟩
  have ht : ((f.C * L ^ 2) ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (f.C * L ^ 2) := by
    have he := Real.rpow_mul (zero_lt_one.trans hx).le (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hv : f.v ^ 2 ≤ L := f.fourth.2.trans hL
  have hquarter : (f.C * L ^ 2) ^ (1 / 4 : ℝ) ≤ L / f.v := by
    apply (le_div_iff₀ f.fourth.1).2
    have hmul := mul_le_mul_of_nonneg_right hu (sq_nonneg f.v)
    have hmul' := mul_le_mul_of_nonneg_left hv hLp.le
    have hp := Real.rpow_nonneg (zero_lt_one.trans hx).le (1 / 4)
    nlinarith only [hmul, hmul', ht, mul_nonneg hp f.fourth.1.le, hLp]
  exact ⟨hx, hl, hu, hquarter⟩

/-- The core profile bounds the negative-power error by its certified root floors. -/
theorem reducedContourCore_power (f : ReducedContourCore) {L : ℝ} (hL : f.T ≤ L) :
    (f.C * L ^ 2) ^ (-9 / 16 : ℝ) ≤ (1 / f.a / L) * (1 / f.m) := by
  let x := f.C * L ^ 2
  have hb := reducedContourCore_roots f hL
  change 1 < x ∧ f.a * L ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / f.v at hb
  have hLp : 0 < L := by linarith only [f.entry, hL]
  have ha : 0 < f.a := by linarith only [f.root]
  have hpos : 0 < x := zero_lt_one.trans hb.1
  have hxlarge : f.m ^ 16 ≤ x := by
    have hT : 0 ≤ f.T := by linarith only [f.entry]
    have hsq := (sq_le_sq₀ hT hLp.le).mpr hL
    have hC := (sq_nonneg f.a).trans f.square
    exact f.root16.2.trans (mul_le_mul_of_nonneg_left hsq hC)
  have hpowfac : x ^ (-9 / 16 : ℝ) = (Real.sqrt x)⁻¹ * (x ^ (1 / 16 : ℝ))⁻¹ := by
    calc
      x ^ (-9 / 16 : ℝ) = x ^ ((-1 / 2 : ℝ) + (-1 / 16 : ℝ)) := by
        congr 1; ring
      _ = x ^ (-1 / 2 : ℝ) * x ^ (-1 / 16 : ℝ) := Real.rpow_add hpos _ _
      _ = (Real.sqrt x)⁻¹ * (x ^ (1 / 16 : ℝ))⁻¹ := by
        rw [show (-1 / 2 : ℝ) = -(1 / 2) by ring, Real.rpow_neg hpos.le]
        rw [← Real.sqrt_eq_rpow]
        rw [show (-1 / 16 : ℝ) = -(1 / 16) by ring, Real.rpow_neg hpos.le]
  have hsqrtInv : (Real.sqrt x)⁻¹ ≤ (1 / f.a / L) := by
    have h := one_div_le_one_div_of_le (mul_pos ha hLp) hb.2.1
    simpa only [one_div, mul_inv_rev, div_eq_mul_inv, mul_comm, one_mul, mul_one] using h
  have hroot16 : f.m ≤ x ^ (1 / 16 : ℝ) := by
    have hm :=
      Real.rpow_le_rpow (pow_nonneg f.root16.1.le 16) hxlarge
        (by norm_num only : (0 : ℝ) ≤ (1 / 16 : ℝ))
    have he : (f.m ^ 16) ^ (1 / 16 : ℝ) = f.m := by
      rw [← Real.rpow_natCast]
      rw [← Real.rpow_mul f.root16.1.le]
      norm_num only [Real.rpow_one]
    rw [he] at hm
    exact hm
  have hinv : (x ^ (1 / 16 : ℝ))⁻¹ ≤ 1 / f.m := by
    simpa only [one_div] using one_div_le_one_div_of_le f.root16.1 hroot16
  rw [hpowfac]
  exact
    mul_le_mul hsqrtInv hinv (inv_nonneg.mpr (Real.rpow_nonneg hpos.le _))
      (div_nonneg (div_nonneg (by norm_num only) ha.le) hLp.le)

/-- The core profile controls the secondary cost and the pole correction. -/
theorem reducedContourCore_costs (f : ReducedContourCore) {L : ℝ} (hL : f.T ≤ L) :
    let x := f.C * L ^ 2;
    165000 + 8000000000 * (L + 284) * x ^ (-9 / 16 : ℝ) ≤ f.b * L ∧
      36 * L / (Real.sqrt x - 1) ≤ 100 := by
  have hb := reducedContourCore_roots f hL
  have hLp : 0 < L := by linarith only [f.entry, hL]
  have ha : 0 < f.a := by linarith only [f.root]
  have hratio : (L + 284) / L ≤ (1001 / 1000 : ℝ) := by
    apply (div_le_iff₀ hLp).2
    linarith only [hL, f.entry]
  have hsmall :=
    mul_le_mul_of_nonneg_left (reducedContourCore_power f hL)
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 8000000000)
        (by linarith only [hLp] : (0 : ℝ) ≤ L + 284))
  have he :
    8000000000 * (L + 284) * ((1 / f.a / L) * (1 / f.m)) =
      (8000000000 / (f.a * f.m)) * ((L + 284) / L) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he] at hsmall
  have hratio' :=
    mul_le_mul_of_nonneg_left hratio
      (div_nonneg (by norm_num only : (0 : ℝ) ≤ 8000000000) (mul_nonneg ha.le f.root16.1.le))
  have hbpos : 0 ≤ f.b := by
    have hc := f.cost
    have hnon :=
      div_nonneg (by norm_num only : (0 : ℝ) ≤ 8000000000 * (1001 / 1000))
        (mul_nonneg ha.le f.root16.1.le)
    have hT : 0 < f.T := by linarith only [f.entry]
    by_contra hn
    have hneg := mul_neg_of_neg_of_pos (lt_of_not_ge hn) hT
    linarith only [hc, hnon, hneg]
  have hbudget := mul_le_mul_of_nonneg_left hL hbpos
  have hcost : 165000 + 8000000000 * (L + 284) * (f.C * L ^ 2) ^ (-9 / 16 : ℝ) ≤ f.b * L := by
    have hc := f.cost
    simp only [div_eq_mul_inv, mul_inv_rev] at hc hratio' hsmall
    nlinarith only [hsmall, hratio', hc, hbudget]
  have hh : L / 2 ≤ Real.sqrt (f.C * L ^ 2) := by
    have hm := mul_le_mul_of_nonneg_right f.root.le hLp.le
    nlinarith only [hb.2.1, hm]
  have hd : 0 < Real.sqrt (f.C * L ^ 2) - 1 := by linarith only [hh, hL, f.entry]
  have hpole : 36 * L / (Real.sqrt (f.C * L ^ 2) - 1) ≤ 100 := by
    apply (div_le_iff₀ hd).mpr
    linarith only [hh, hL, f.entry]
  exact ⟨hcost, hpole⟩

/-- The core profile certifies the signed comparison gap at large subgroup index. -/
theorem reducedContourCore_gap (f : ReducedContourCore) {L h : ℝ} (hL : f.T ≤ L)
    (hh : 1000000000000 ≤ h) :
    let x := f.C * L ^ 2;
    300000000 * Real.sqrt x + 1300000 * x ^ (1 / 4 : ℝ) + 602600000 +
        (h - 1) * (36 * L + 165000 + 8000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  let x := f.C * L ^ 2
  let C := 165000 + 8000000000 * (L + 284) * x ^ (-9 / 16 : ℝ)
  have hLp : 0 < L := by linarith only [f.entry, hL]
  have hhp : 0 < h := by linarith only [hh]
  have hb := reducedContourCore_roots f hL
  change 1 < x ∧ f.a * L ≤ Real.sqrt x ∧ Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ L / f.v at hb
  have hc := reducedContourCore_costs f hL
  change C ≤ f.b * L ∧ 36 * L / (Real.sqrt x - 1) ≤ 100 at hc
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
        ((3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L + f.b * L +
          1) := by
    nlinarith only [hpr, hpt, hcost0, hcost1, hh]
  let d := (68 - 3 / 10000 : ℝ) * f.a - (36 + f.b + (1456 + 13 / 10000000 : ℝ) / f.v)
  have hmargin : 101 < d * f.T := by
    dsimp only [d]
    nlinarith only [f.margin]
  have hd : 0 < d := by
    by_contra hn
    have hT : 0 ≤ f.T := by linarith only [f.entry]
    have hm := mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hn) hT
    linarith only [hm, hmargin]
  have hmul := mul_le_mul_of_nonneg_left hL hd.le
  have hE := mul_nonneg hn (Real.exp_pos (-18)).le
  have hg :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L + f.b * L + 1 <
      Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        36 * L / (Real.sqrt x - 1) := by
    have hm : 101 < d * L := hmargin.trans_le hmul
    dsimp only [d] at hm
    have hquarter := hb.2.2.2
    simp only [div_eq_mul_inv] at hm hquarter
    nlinarith only [hb.2.1, hquarter, hc.2, hm, hE]
  have hfinal := hu.trans_lt (mul_lt_mul_of_pos_left hg hhp)
  simpa only [C, add_assoc] using hfinal



end PseudoPrime.PrimeTestBounds.MillerRabin
