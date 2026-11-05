/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneEnvelopeA
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianSurplusShape

/-! # Dominance of the scale-one Gaussian cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- From scale 25000, the 50000-prefix cutoff is strictly below the earlier adaptive
Gaussian cutoff. Compare the roots at residuals 29 and 30, retaining the radius floor. -/
theorem jointSurplus_lt_adaptive {L : ℝ} (hL : 25000 ≤ L) :
    jointSurplusCutoff 155 29 L < ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2 := by
  let a := adaptiveGaussianA L
  let r := a * L
  let s := Real.sqrt r
  have hLp : 0 < L := by linarith only [hL]
  have ha := scaleOne_gaussian_slope L hL
  change (36 / 100 : ℝ) ≤ a ∧ a ≤ 3715 / 10000 at ha
  have hr : (36 / 100 : ℝ) * L ≤ r := mul_le_mul_of_nonneg_right ha.1 hLp.le
  have hrpos : 0 < r := by nlinarith only [hr, hL]
  have hs10 : (10 : ℝ) ≤ s := by
    apply (Real.le_sqrt (by norm_num only) hrpos.le).mpr
    norm_num only
    nlinarith only [hr, hL]
  have hs2 : s ^ 2 = r := Real.sq_sqrt hrpos.le
  have hsupper : s ≤ (61 / 100 : ℝ) * Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) (Real.sqrt_nonneg L)
    · have h := mul_le_mul_of_nonneg_right ha.2 hLp.le
      nlinarith only [h, Real.sq_sqrt hLp.le]
  have hform :
    (10971611 / 5000000 : ℝ) * a =
      2 * (20115621 / 50000000) + (61 / 100) * (28794111 / 12500000) / Real.sqrt L + 39 / L := by
    dsimp only [a, adaptiveGaussianA]
    ring
  have hh : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hLp).ne'
  have hsquare := Real.sq_sqrt hLp.le
  have hdiv : L / Real.sqrt L = Real.sqrt L := by
    apply (div_eq_iff hh).2
    nlinarith only [hsquare]
  have he :
    ((61 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L) * L =
      (61 / 100 : ℝ) * (28794111 / 12500000) * Real.sqrt L := by
    rw [div_mul_eq_mul_div, mul_div_assoc, hdiv]
  have h39 : (39 : ℝ) / L * L = 39 := div_mul_cancel₀ _ hLp.ne'
  have hmul := congrArg (fun z : ℝ ↦ z * L) hform
  have hbudget :
    (20115621 / 25000000 : ℝ) * L + 30 + (28794111 / 12500000 : ℝ) * s ≤
      (10971611 / 5000000 : ℝ) * s ^ 2 := by
    rw [hs2]
    dsimp only [r]
    nlinarith only [hmul, he, h39, hsupper]
  have hV : (28794111 / 12500000 : ℝ) < (10971611 / 5000000 : ℝ) * s := by nlinarith only [hs10]
  have hC0 : 0 ≤ (20115621 / 25000000 : ℝ) * L + 30 := by
    have hp := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 20115621 / 25000000) hLp.le
    linarith only [hp]
  have hroot30 : jointSurplusRoot 30 L ≤ s :=
    Analysis.gaussianBudgetRoot_le_of_budget (by norm_num only) (by norm_num only) hC0 hV hbudget
  have hC29 : 0 ≤ (20115621 / 25000000 : ℝ) * L + 29 := by
    have hp := mul_nonneg (by norm_num only : (0 : ℝ) ≤ 20115621 / 25000000) hLp.le
    linarith only [hp]
  have hstrict : jointSurplusRoot 29 L < jointSurplusRoot 30 L :=
    Analysis.gaussianBudgetRoot_strictMono (by norm_num only) hC29 (by linarith only [])
  have hrootpos : 0 ≤ jointSurplusRoot 29 L :=
    (Analysis.gaussianBudgetRoot_pos (by norm_num only) (by norm_num only)).le
  have hrootlt : jointSurplusRoot 29 L ^ 2 < r := by
    have hsq :=
      (sq_lt_sq₀ hrootpos (by linarith only [hs10] : 0 ≤ s)).mpr (hstrict.trans_le hroot30)
    linarith only [hsq, hs2]
  have hfloor : (155 : ℝ) < r := by nlinarith only [hr, hL]
  have hrad : jointSurplusRadius 155 29 L < r := max_lt hfloor hrootlt
  have hrad0 : 0 ≤ jointSurplusRadius 155 29 L :=
    (by norm_num only : (0 : ℝ) ≤ 155).trans (le_max_left _ _)
  have hsq := (sq_lt_sq₀ hrad0 hrpos.le).mpr hrad
  unfold jointSurplusCutoff
  dsimp only [r, a] at hsq
  nlinarith only [hsq]

/-- Any radius strictly above 155 whose Gaussian budget has residual 39 strictly exceeds
    the cutoff obtained with residual 29. The budget comparison is valid for all nonnegative
    scales and retains the radius floor. -/
theorem jointSurplus_lt_budget {L r : ℝ} (hL : 0 ≤ L) (hr : 155 < r)
    (hb :
      (20115621 / 25000000 : ℝ) * L + 39 + (28794111 / 12500000 : ℝ) * Real.sqrt r ≤
        (10971611 / 5000000 : ℝ) * r) :
    jointSurplusCutoff 155 29 L < (21 / 10 : ℝ) * r ^ 2 := by
  let s := Real.sqrt r
  have hr0 : 0 ≤ r := by linarith only [hr]
  have hs10 : (10 : ℝ) ≤ s := by
    apply (Real.le_sqrt (by norm_num only) hr0).2
    norm_num only
    linarith only [hr]
  have hs2 : s ^ 2 = r := Real.sq_sqrt hr0
  have hV : (28794111 / 12500000 : ℝ) < (10971611 / 5000000 : ℝ) * s := by nlinarith only [hs10]
  have hC30 : 0 ≤ (20115621 / 25000000 : ℝ) * L + 30 :=
    add_nonneg (mul_nonneg (by norm_num only) hL) (by norm_num only)
  have hC29 : 0 ≤ (20115621 / 25000000 : ℝ) * L + 29 :=
    add_nonneg (mul_nonneg (by norm_num only) hL) (by norm_num only)
  have hb30 :
    (20115621 / 25000000 : ℝ) * L + 30 + (28794111 / 12500000 : ℝ) * s ≤
      (10971611 / 5000000 : ℝ) * s ^ 2 := by
    rw [hs2]
    linarith only [hb]
  have hroot30 : jointSurplusRoot 30 L ≤ s :=
    Analysis.gaussianBudgetRoot_le_of_budget (by norm_num only) (by norm_num only) hC30 hV hb30
  have hstrict : jointSurplusRoot 29 L < jointSurplusRoot 30 L :=
    Analysis.gaussianBudgetRoot_strictMono (by norm_num only) hC29 (by linarith only [])
  have hrootpos : 0 ≤ jointSurplusRoot 29 L :=
    (Analysis.gaussianBudgetRoot_pos (by norm_num only) (by norm_num only)).le
  have hrootlt : jointSurplusRoot 29 L ^ 2 < r := by
    have hsq :=
      (sq_lt_sq₀ hrootpos (by linarith only [hs10] : 0 ≤ s)).mpr (hstrict.trans_le hroot30)
    linarith only [hsq, hs2]
  have hrad : jointSurplusRadius 155 29 L < r := max_lt hr hrootlt
  have hrad0 : 0 ≤ jointSurplusRadius 155 29 L :=
    (by norm_num only : (0 : ℝ) ≤ 155).trans (le_max_left _ _)
  have hsq := (sq_lt_sq₀ hrad0 hr0).mpr hrad
  unfold jointSurplusCutoff
  nlinarith only [hsq]

/-- The slope used by the earlier 4000-entrance proposal, with parameter 0.62.
    Its radius is this slope multiplied by the logarithmic scale. -/
noncomputable def scaleOneSlope062 (L : ℝ) : ℝ :=
  ((20115621 / 25000000 : ℝ) + (62 / 100) * (28794111 / 12500000) / Real.sqrt L + 39 / L) /
    (10971611 / 5000000)

/-- From scale 4000 the old proposal's slope is positive and at most the square of 0.62.
    Bound the reciprocal correction terms using the entrance scale. -/
theorem scaleOneSlope062_bounds (L : ℝ) (hL : 4000 ≤ L) :
    (36 / 100 : ℝ) ≤ scaleOneSlope062 L ∧ scaleOneSlope062 L ≤ (62 / 100 : ℝ) ^ 2 := by
  have hL0 : 0 ≤ L := by linarith only [hL]
  have h1 : 0 ≤ (62 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L :=
    div_nonneg (by norm_num only) (Real.sqrt_nonneg _)
  have h2 : 0 ≤ (39 : ℝ) / L := div_nonneg (by norm_num only) hL0
  have hs : (63 : ℝ) ≤ Real.sqrt L := by
    apply (Real.le_sqrt (by norm_num only) hL0).2
    nlinarith only [hL]
  have hd :
    (62 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L ≤
      (62 / 100 : ℝ) * (28794111 / 12500000) / 63 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hs
  have he : (39 : ℝ) / L ≤ 39 / 4000 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hL
  dsimp only [scaleOneSlope062]
  constructor
  · apply (le_div_iff₀ (by norm_num only)).2
    linarith only [h1, h2]
  · apply (div_le_iff₀ (by norm_num only)).2
    linarith only [hd, he]

/-- Above scale 4000 the 50000-prefix cutoff strictly improves the old 0.62-slope proposal.
    The old slope pays the residual-39 budget and its radius exceeds the prefix floor. -/
theorem jointSurplus_lt_slope062 {L : ℝ} (hL : 4000 ≤ L) :
    jointSurplusCutoff 155 29 L < ((21 / 10 : ℝ) * scaleOneSlope062 L ^ 2) * L ^ 2 := by
  let a := scaleOneSlope062 L
  let r := a * L
  let s := Real.sqrt r
  have hLp : 0 < L := by linarith only [hL]
  have ha := scaleOneSlope062_bounds L hL
  change (36 / 100 : ℝ) ≤ a ∧ a ≤ (62 / 100 : ℝ) ^ 2 at ha
  have hr : (36 / 100 : ℝ) * L ≤ r := mul_le_mul_of_nonneg_right ha.1 hLp.le
  have hrpos : 0 < r := by nlinarith only [hr, hL]
  have hsupper : s ≤ (62 / 100 : ℝ) * Real.sqrt L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) (Real.sqrt_nonneg L)
    · have h := mul_le_mul_of_nonneg_right ha.2 hLp.le
      nlinarith only [h, Real.sq_sqrt hLp.le]
  have hform :
    (10971611 / 5000000 : ℝ) * a =
      (20115621 / 25000000) + (62 / 100) * (28794111 / 12500000) / Real.sqrt L + 39 / L := by
    dsimp only [a, scaleOneSlope062]
    ring
  have hh : Real.sqrt L ≠ 0 := (Real.sqrt_pos.mpr hLp).ne'
  have hsquare := Real.sq_sqrt hLp.le
  have hdiv : L / Real.sqrt L = Real.sqrt L := by
    apply (div_eq_iff hh).2
    nlinarith only [hsquare]
  have he :
    ((62 / 100 : ℝ) * (28794111 / 12500000) / Real.sqrt L) * L =
      (62 / 100 : ℝ) * (28794111 / 12500000) * Real.sqrt L := by
    rw [div_mul_eq_mul_div, mul_div_assoc, hdiv]
  have h39 : (39 : ℝ) / L * L = 39 := div_mul_cancel₀ _ hLp.ne'
  have hmul := congrArg (fun z : ℝ ↦ z * L) hform
  have hbudget :
    (20115621 / 25000000 : ℝ) * L + 39 + (28794111 / 12500000 : ℝ) * Real.sqrt r ≤
      (10971611 / 5000000 : ℝ) * r := by
    dsimp only [r] at hmul ⊢
    nlinarith only [hmul, he, h39, hsupper]
  have hfloor : (155 : ℝ) < r := by nlinarith only [hr, hL]
  have h := jointSurplus_lt_budget hLp.le hfloor hbudget
  dsimp only [r, a] at h
  nlinarith only [h]

/-- The global minimum strictly improves the old 0.62-slope proposal from scale 4000.
    This follows by selecting its 50000-prefix cutoff. -/
theorem jointSurplusGlobal_lt_slope062 {L : ℝ} (hL : 4000 ≤ L) :
    jointSurplusGlobal L < ((21 / 10 : ℝ) * scaleOneSlope062 L ^ 2) * L ^ 2 := by
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (jointSurplus_lt_slope062 hL)

/-- The global minimum strictly improves the old 0.61-slope proposal from scale 25000.
    This follows by selecting its 50000-prefix cutoff. -/
theorem jointSurplusGlobal_lt_adaptive {L : ℝ} (hL : 25000 ≤ L) :
    jointSurplusGlobal L < ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2 := by
  exact ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (jointSurplus_lt_adaptive hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
