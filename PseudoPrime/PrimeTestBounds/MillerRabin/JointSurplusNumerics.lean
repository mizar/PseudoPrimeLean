/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusAllFactors
public import PseudoPrime.LLS.PaperStatements.TriangularJointGap
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneNumerics

/-! # Uniform root bounds for surplus Gaussian cutoffs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- On a certified entrance range, a clipped surplus cutoff lies between the root
floor and 0.46 times the squared scale, with the fourth-root bound needed for the
joint triangular cells. The quadratic root is bounded before applying the radius floor. -/
theorem jointSurplus_cutoff_roots {rho R T L v : ℝ} (hT : 280 ≤ T) (hL : T ≤ L) (hR : 29 ≤ R)
    (hRup : R ≤ 30) (hrho : 130 ≤ rho) (hrhoT : rho ≤ (467 / 1000 : ℝ) * T) (hv : 0 < v)
    (hv2 : v ^ 2 ≤ T) :
    let r := jointSurplusRadius rho R L
    let x := (21 / 10 : ℝ) * r ^ 2
    16 ≤ x ∧
      (5313 / 10000 : ℝ) * L ≤ Real.sqrt x ∧
      x ≤ (46 / 100 : ℝ) * L ^ 2 ∧ x ^ (1 / 4 : ℝ) ≤ (83 / 100 : ℝ) * L / v := by
  let r := jointSurplusRadius rho R L
  let x := (21 / 10 : ℝ) * r ^ 2
  let u := Real.sqrt ((467 / 1000 : ℝ) * L)
  have hLp : 0 < L := by linarith only [hT, hL]
  have hRpos : 0 < R := by linarith only [hR]
  have hrhopos : 0 ≤ rho := by linarith only [hrho]
  have hr : rho ≤ r := le_max_left _ _
  have hr130 : (130 : ℝ) ≤ r := hrho.trans hr
  have hx0 : 0 ≤ x := mul_nonneg (by norm_num only) (sq_nonneg r)
  have hx : 16 ≤ x := by
    dsimp only [x]; nlinarith only [hr130]
  have hbudget := jointSurplus_budget hrhopos hRpos hLp.le
  change
    (20115621 / 25000000 : ℝ) * L + R + (28794111 / 12500000 : ℝ) * Real.sqrt r ≤
      (10971611 / 5000000 : ℝ) * r at hbudget
  have hrlower : (3666849 / 10000000 : ℝ) * L ≤ r := by
    have hs : 0 ≤ Real.sqrt r := Real.sqrt_nonneg r
    nlinarith only [hbudget, hs, hR, hLp]
  have hroot : (5313 / 10000 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hLp.le) hx0).mpr
    have hs :=
      (sq_le_sq₀ (mul_nonneg (by norm_num only) hLp.le) (by linarith only [hr130] : 0 ≤ r)).mpr
        hrlower
    dsimp only [x]
    nlinarith only [hs]
  have hu0 : 0 ≤ (467 / 1000 : ℝ) * L := mul_nonneg (by norm_num only) hLp.le
  have hu2 : u ^ 2 = (467 / 1000 : ℝ) * L := Real.sq_sqrt hu0
  have hu10 : (10 : ℝ) ≤ u := by
    apply (Real.le_sqrt (by norm_num only) hu0).mpr
    nlinarith only [hT, hL]
  have huup : u ≤ (21 / 500 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨mul_nonneg (by norm_num only) hLp.le, by nlinarith only [hT, hL]⟩
  have hC : 0 ≤ (20115621 / 25000000 : ℝ) * L + R := by
    have h := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 20115621 / 25000000) hLp.le
    linarith only [h, hR]
  have huV : (28794111 / 12500000 : ℝ) < (10971611 / 5000000 : ℝ) * u := by nlinarith only [hu10]
  have huBudget :
    (20115621 / 25000000 : ℝ) * L + R + (28794111 / 12500000 : ℝ) * u ≤
      (10971611 / 5000000 : ℝ) * u ^ 2 := by
    nlinarith only [hu2, huup, hT, hL, hRup]
  have hrootup : jointSurplusRoot R L ≤ u :=
    Analysis.gaussianBudgetRoot_le_of_budget (by norm_num only) (by norm_num only) hC huV huBudget
  have hspos : 0 ≤ jointSurplusRoot R L :=
    (Analysis.gaussianBudgetRoot_pos (by norm_num only) (by norm_num only)).le
  have hrootsq := pow_le_pow_left₀ hspos hrootup 2
  have hrad : r ≤ (467 / 1000 : ℝ) * L := by
    apply max_le
    · have hm := mul_le_mul_of_nonneg_left hL (by norm_num only : (0 : ℝ) ≤ 467 / 1000)
      linarith only [hrhoT, hm]
    · linarith only [hrootsq, hu2]
  have hr0 : 0 ≤ r := by linarith only [hr130]
  have hrsq := pow_le_pow_left₀ hr0 hrad 2
  have hupper : x ≤ (46 / 100 : ℝ) * L ^ 2 := by
    dsimp only [x]
    nlinarith only [hrsq]
  have hrootup' : Real.sqrt x ≤ (83 / 100 : ℝ) ^ 2 * L := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨mul_nonneg (by norm_num only) hLp.le, by nlinarith only [hupper]⟩
  have hq2 : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul hx0 (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hq0 : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0 _
  have hq : x ^ (1 / 4 : ℝ) ≤ (83 / 100 : ℝ) * Real.sqrt L := by
    have hh : 0 ≤ (83 / 100 : ℝ) * Real.sqrt L := mul_nonneg (by norm_num only) (Real.sqrt_nonneg _)
    nlinarith only [hrootup', hq2, Real.sq_sqrt hLp.le, hq0, hh]
  have hs : Real.sqrt L ≤ L / v := by
    apply (le_div_iff₀ hv).2
    have hh := Real.sq_sqrt hLp.le
    have hp : 0 ≤ v * Real.sqrt L := mul_nonneg hv.le (Real.sqrt_nonneg _)
    have hm := mul_le_mul_of_nonneg_left (hv2.trans hL) hLp.le
    nlinarith only [hh, hp, hm]
  refine ⟨hx, hroot, hupper, ?_⟩
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 83 / 100)
  exact hq.trans (by simpa only [mul_div_assoc] using hm)

/-- A cutoff above 35490 and below 0.46 L^2 has logarithm in [10, 18]
when the scale is at most 10000. Both endpoints use rational logarithm certificates. -/
theorem jointSurplus_log_first {x L : ℝ} (hx : 35490 ≤ x) (hL : 0 ≤ L) (hU : L ≤ 10000)
    (hcap : x ≤ (46 / 100 : ℝ) * L ^ 2) : (10 : ℝ) ≤ Real.log x ∧ Real.log x ≤ 18 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 35490 15 32 10 11 = true from by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 46000000 25 32 17 18 = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hl hu
  have hs := (sq_le_sq₀ hL (by norm_num only : (0 : ℝ) ≤ 10000)).mpr hU
  have htop : x ≤ 46000000 := by nlinarith only [hs, hcap]
  constructor
  · exact hl.trans (Real.log_le_log (by norm_num only) hx)
  · exact (Real.log_le_log (by linarith only [hx]) htop).trans hu

/-- From scale 10000, the certified square-root floor puts the cutoff logarithm
above 17. -/
theorem jointSurplus_log_second {x L : ℝ} (hL : 10000 ≤ L)
    (hroot : (5313 / 10000 : ℝ) * L ≤ Real.sqrt x) : (17 : ℝ) ≤ Real.log x := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 28227969 24 32 17 18 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hl
  have hx0 : 0 ≤ x := by
    by_contra hn
    have hs : Real.sqrt x = 0 := Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hn)
    nlinarith only [hs, hroot, hL]
  have hsq := Real.sq_sqrt hx0
  have hbase : (28227969 : ℝ) ≤ x := by nlinarith only [hsq, hroot, hL]
  exact hl.trans (Real.log_le_log (by norm_num only) hbase)

/-- The two rational cells imply the joint interior margin for either surplus cutoff
on its certified entrance range. The cutoff remains inside triangular support. -/
theorem jointSurplus_interior_margin {rho R T L : ℝ} (hT : 280 ≤ T) (hL : T ≤ L) (hR : 29 ≤ R)
    (hRup : R ≤ 30) (hrho : 130 ≤ rho) (hrhoMax : rho ≤ 155) (hrhoT : rho ≤ (467 / 1000 : ℝ) * T)
    (hu : (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2 ≤ Real.exp 36) :
    let x := (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + (72 - Real.log x) * L +
        856 <
      (220 - 4 * Real.log x) * Real.sqrt x -
        (1064 / 5 - (19 / 5 : ℝ) * Real.log x) * x ^ (1 / 4 : ℝ) := by
  let x := (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2
  have hL0 : 0 ≤ L := by linarith only [hT, hL]
  have hr : (130 : ℝ) ≤ jointSurplusRadius rho R L := hrho.trans (le_max_left _ _)
  have hxbase : (35490 : ℝ) ≤ x := by
    dsimp only [x]; nlinarith only [hr]
  have hxpos : 0 < x := by linarith only [hxbase]
  have hlog : Real.log x ≤ 36 := by
    have h := Real.log_le_log hxpos hu
    simpa only [Real.log_exp] using h
  by_cases hU : L ≤ 10000
  · have hroots :=
      jointSurplus_cutoff_roots hT hL hR hRup hrho hrhoT (v := 16) (by norm_num only)
        (by nlinarith only [hT])
    have hlogs := jointSurplus_log_first hxbase hL0 hU hroots.2.2.1
    exact
      LLS.PaperStatements.joint_margin_of_cell (T := 280) (v := 16) (y0 := 10) (y1 := 18)
        (by norm_num only) (by linarith only [hT, hL]) hlogs.1 hlogs.2 (by norm_num only) hroots.2.1
        (Real.rpow_nonneg hxpos.le _) hroots.2.2.2 (by norm_num only)
  · have hlarge : 10000 ≤ L := le_of_not_ge hU
    have hroots :=
      jointSurplus_cutoff_roots (T := 10000) (L := L) (rho := rho) (R := R) (v := 100)
        (by norm_num only) hlarge hR hRup hrho (by nlinarith only [hrhoMax]) (by norm_num only)
        (by norm_num only)
    have hlogs := jointSurplus_log_second hlarge hroots.2.1
    exact
      LLS.PaperStatements.joint_margin_of_cell (T := 10000) (v := 100) (y0 := 17) (y1 := 36)
        (by norm_num only) hlarge hlogs hlog (by norm_num only) hroots.2.1
        (Real.rpow_nonneg hxpos.le _) hroots.2.2.2 (by norm_num only)

/-- From scale 25000, either clipped surplus cutoff is at most 0.29 L^2. Bound the
quadratic root by the square root of a linear radius and then include the floor. -/
theorem jointSurplus_high_upper {rho R L : ℝ} (hL : 25000 ≤ L) (hR : 0 < R) (hRup : R ≤ 30)
    (hrho : 0 ≤ rho) (hrhoMax : rho ≤ 155) :
    (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2 ≤ (29 / 100 : ℝ) * L ^ 2 := by
  let r := jointSurplusRadius rho R L
  let u := Real.sqrt ((3715 / 10000 : ℝ) * L)
  have hLp : 0 < L := by linarith only [hL]
  have hu0 : 0 ≤ (3715 / 10000 : ℝ) * L := mul_nonneg (by norm_num only) hLp.le
  have hu2 : u ^ 2 = (3715 / 10000 : ℝ) * L := Real.sq_sqrt hu0
  have hu10 : (10 : ℝ) ≤ u := by
    apply (Real.le_sqrt (by norm_num only) hu0).mpr
    nlinarith only [hL]
  have huup : u ≤ (39 / 10000 : ℝ) * L := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨mul_nonneg (by norm_num only) hLp.le, by nlinarith only [hL]⟩
  have hC : 0 ≤ (20115621 / 25000000 : ℝ) * L + R := by
    have h := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 20115621 / 25000000) hLp.le
    linarith only [h, hR]
  have huV : (28794111 / 12500000 : ℝ) < (10971611 / 5000000 : ℝ) * u := by nlinarith only [hu10]
  have huBudget :
    (20115621 / 25000000 : ℝ) * L + R + (28794111 / 12500000 : ℝ) * u ≤
      (10971611 / 5000000 : ℝ) * u ^ 2 := by
    nlinarith only [hu2, huup, hL, hRup]
  have hrootup : jointSurplusRoot R L ≤ u :=
    Analysis.gaussianBudgetRoot_le_of_budget (by norm_num only) (by norm_num only) hC huV huBudget
  have hspos : 0 ≤ jointSurplusRoot R L :=
    (Analysis.gaussianBudgetRoot_pos (by norm_num only) (by norm_num only)).le
  have hrootsq := pow_le_pow_left₀ hspos hrootup 2
  have hrad : r ≤ (3715 / 10000 : ℝ) * L := by
    apply max_le
    · nlinarith only [hrhoMax, hL]
    · linarith only [hrootsq, hu2]
  have hr0 : 0 ≤ r := hrho.trans (le_max_left _ _)
  have hrsq := pow_le_pow_left₀ hr0 hrad 2
  nlinarith only [hrsq]

/-- Beyond triangular support, either clipped surplus cutoff has logarithmic scale
at least 100000000. First use the 0.46 cap, then the sharper high-scale cap. -/
theorem jointSurplus_outer_scale {rho R T L : ℝ} (hT : 280 ≤ T) (hL : T ≤ L) (hR : 29 ≤ R)
    (hRup : R ≤ 30) (hrho : 130 ≤ rho) (hrhoMax : rho ≤ 155) (hrhoT : rho ≤ (467 / 1000 : ℝ) * T)
    (hu : Real.exp 36 ≤ (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2) :
    (100000000 : ℝ) ≤ L := by
  have hL0 : 0 ≤ L := by linarith only [hT, hL]
  have hroots :=
    jointSurplus_cutoff_roots hT hL hR hRup hrho hrhoT (v := 16) (by norm_num only)
      (by nlinarith only [hT])
  have he := scaleOne_exp36_lower
  have h25 : 25000 ≤ L := by
    by_contra hn
    have hlt : L < 25000 := lt_of_not_ge hn
    have hs := (sq_le_sq₀ hL0 (by norm_num only : (0 : ℝ) ≤ 25000)).mpr hlt.le
    nlinarith only [hu, he, hroots.2.2.1, hs]
  have hh :=
    jointSurplus_high_upper h25 (by linarith only [hR]) hRup (by linarith only [hrho]) hrhoMax
  by_contra hn
  have hlt : L < 100000000 := lt_of_not_ge hn
  have hs := (sq_le_sq₀ hL0 (by norm_num only : (0 : ℝ) ≤ 100000000)).mpr hlt.le
  nlinarith only [hu, he, hh, hs]

/-- Above scale 100000000, the high-scale cutoff cap gives the sharper fourth-root
bound required by the all-scale exterior comparison. -/
theorem jointSurplus_outer_fourth {rho R L : ℝ} (hL : 100000000 ≤ L) (hR : 29 ≤ R) (hRup : R ≤ 30)
    (hrho : 130 ≤ rho) (hrhoMax : rho ≤ 155) :
    let x := (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2
    x ^ (1 / 4 : ℝ) ≤ (147 / 200 : ℝ) * L / 10000 := by
  let x := (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2
  have hLp : 0 < L := by linarith only [hL]
  have hroots :=
    jointSurplus_cutoff_roots (rho := rho) (R := R) (T := 100000000) (L := L) (v := 10000)
      (by norm_num only) hL hR hRup hrho (by nlinarith only [hrhoMax]) (by norm_num only)
      (by norm_num only)
  have hx0 : 0 ≤ x := mul_nonneg (by norm_num only) (sq_nonneg _)
  have hupper :=
    jointSurplus_high_upper (rho := rho) (R := R) (L := L) (by linarith only [hL])
      (by linarith only [hR]) hRup (by linarith only [hrho]) hrhoMax
  change x ≤ (29 / 100 : ℝ) * L ^ 2 at hupper
  have hrootfine : Real.sqrt x ≤ (147 / 200 : ℝ) ^ 2 * L := by
    apply Real.sqrt_le_iff.mpr
    exact ⟨mul_nonneg (by norm_num only) hLp.le, by nlinarith only [hupper]⟩
  have hq2 : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul hx0 (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hq0 : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg hx0 _
  have hq : x ^ (1 / 4 : ℝ) ≤ (147 / 200 : ℝ) * Real.sqrt L := by
    have hh : 0 ≤ (147 / 200 : ℝ) * Real.sqrt L :=
      mul_nonneg (by norm_num only) (Real.sqrt_nonneg _)
    nlinarith only [hrootfine, hq2, Real.sq_sqrt hLp.le, hq0, hh]
  have hs : Real.sqrt L ≤ L / 10000 := by
    apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 10000)).2
    have hh := Real.sq_sqrt hLp.le
    have hp : 0 ≤ 10000 * Real.sqrt L := mul_nonneg (by norm_num only) (Real.sqrt_nonneg _)
    nlinarith only [hh, hp, hL]
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 147 / 200)
  exact hq.trans (by simpa only [mul_div_assoc] using hm)

/-- Beyond triangular support, either surplus cutoff satisfies the all-scale dual
gap for every large index. The high-scale cutoff cap recovers the sharper fourth-root
bound, so no interior signed Gamma estimate is used outside its range. -/
theorem jointSurplus_outer_gap {rho R T L h : ℝ} (hT : 280 ≤ T) (hL : T ≤ L) (hR : 29 ≤ R)
    (hRup : R ≤ 30) (hrho : 130 ≤ rho) (hrhoMax : rho ≤ 155) (hrhoT : rho ≤ (467 / 1000 : ℝ) * T)
    (hh : 1000000000000 ≤ h) (hu : Real.exp 36 ≤ (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2) :
    let x := (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  let x := (21 / 10 : ℝ) * (jointSurplusRadius rho R L) ^ 2
  have hbig := jointSurplus_outer_scale hT hL hR hRup hrho hrhoMax hrhoT hu
  have hLp : 0 < L := by linarith only [hbig]
  have hhp : 0 < h := by linarith only [hh]
  have hb :=
    jointSurplus_cutoff_roots (rho := rho) (R := R) (T := 100000000) (L := L) (v := 10000)
      (by norm_num only) hbig hR hRup hrho (by nlinarith only [hrhoMax]) (by norm_num only)
      (by norm_num only)
  have hx16 : 16 ≤ x := hb.1
  have hx : 1 < x := by linarith only [hx16]
  have hroot : (5313 / 10000 : ℝ) * L ≤ Real.sqrt x := hb.2.1
  have hquarter := jointSurplus_outer_fourth hbig hR hRup hrho hrhoMax
  have hp : LLS.PaperStatements.triangularKernelProfile 18 x = 0 := by
    unfold LLS.PaperStatements.triangularKernelProfile
    have hlog := Real.log_le_log (Real.exp_pos 36) hu
    rw [Real.log_exp] at hlog
    rw [abs_of_nonneg (Real.log_nonneg hx.le)]
    norm_num only
    exact max_eq_left (by linarith only [hlog])
  have hinv : x⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans hx)).2 hx.le
  have hinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hx).le
  have hsInv : Real.sqrt x⁻¹ ≤ 1 := Real.sqrt_le_one.mpr hinv
  have hrInv : (x⁻¹) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hinv0 hinv (by norm_num only)
  have hden : 0 < Real.sqrt x - 1 := by nlinarith only [hroot, hbig]
  have hpole : 36 * L / (Real.sqrt x - 1) ≤ 100 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hroot, hbig]
  have hS : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hQ : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hpc : 0 ≤ (36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964 :=
    add_nonneg
      (mul_nonneg
        (add_nonneg (by norm_num only) (LLS.PaperStatements.triangularKernelProfile_nonneg 18 x))
        hLp.le)
      (by norm_num only)
  have hidx := mul_le_mul_of_nonneg_right (by linarith only [] : h - 1 ≤ h) hpc
  have hpr := mul_le_mul_of_nonneg_right hh hS
  have hpq := mul_le_mul_of_nonneg_right hh hQ
  have hcost :
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964) ≤
      h *
        ((3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L +
          11965) := by
    rw [hp] at hidx ⊢
    nlinarith only [hidx, hpr, hpq, hsInv, hrInv, hh]
  have ha := mul_le_mul_of_nonneg_left hroot (by norm_num only : (0 : ℝ) ≤ 68 - 3 / 10000)
  have hq := mul_le_mul_of_nonneg_left hquarter (by norm_num only : (0 : ℝ) ≤ 1456 + 13 / 10000000)
  have hm :
    12065 <
      ((68 - 3 / 10000 : ℝ) * (5313 / 10000) - 36 - (1456 + 13 / 10000000) * (147 / 200) / 10000) *
        L := by
    nlinarith only [hbig]
  have hE := mul_nonneg hS (Real.exp_pos (-18)).le
  have hg :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L + 11965 <
      Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        36 * L / (Real.sqrt x - 1) := by
    nlinarith only [ha, hq, hm, hpole, hE]
  exact hcost.trans_lt (mul_lt_mul_of_pos_left hg hhp)

end PseudoPrime.PrimeTestBounds.MillerRabin
