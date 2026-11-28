/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxNumerics656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope656

import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Centered conductor polynomial for section 132 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational multipliers for the coefficient of degree j after shifting
the logarithmic variable by 23/2. -/
private def coeffWeight (j : ℕ) (i : Fin 7) : ℚ :=
  -(quarterAuxCoeffRat656 i) * (Nat.choose 5 j) * (23 / 2 - quarterAuxShift656 i) ^ (5 - j)

/-- The six real coefficients obtained by binomial expansion. -/
noncomputable def thetaCoeff656 (j : ℕ) : ℝ :=
  ∑ i, (coeffWeight j i : ℝ) * Real.exp ((11 / 10 : ℚ) * quarterAuxShift656 i : ℚ)

/-- The exact rational approximation uses the existing exponential certificate. -/
private def coeffApprox (j : ℕ) : ℚ :=
  ∑ i, coeffWeight j i * auxExpTaylor656 ((11 / 10) * quarterAuxShift656 i)

/-- Outward upper endpoints for the six centered coefficients. -/
@[expose]
def thetaCoeffUpper656 (j : Fin 6) : ℚ :=
  ![46019.244960, 15803.818334, 1353.139717, 41.370178, 21.941657, 2.439033] j

/-- The total rounding error is at most seven times the bound for one
weighted exponential. -/
private theorem coeff_error (j : Fin 6) :
    |thetaCoeff656 j - (coeffApprox j : ℝ)| ≤ 7 / 10 ^ 10 := by
  have hw : ∀ k : Fin 6, ∀ i : Fin 7, |coeffWeight k i| ≤ 1000000 := by decide +kernel
  have hx : ∀ i : Fin 7, |(11 / 10 : ℚ) * quarterAuxShift656 i| ≤ 10 := by decide +kernel
  unfold thetaCoeff656 coeffApprox
  rw [Rat.cast_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h (i : Fin 7) :
    |(coeffWeight j i : ℝ) * Real.exp ((11 / 10 : ℚ) * quarterAuxShift656 i : ℚ) -
          ((coeffWeight j i * auxExpTaylor656 ((11 / 10) * quarterAuxShift656 i) : ℚ) : ℝ)| ≤
      1 / 10 ^ 10 := by
    simp only [Rat.cast_mul, ← mul_sub, abs_mul]
    have hw' : |(coeffWeight j i : ℝ)| ≤ 1000000 := by exact_mod_cast hw j i
    have he := aux_exp_error_656 ((11 / 10) * quarterAuxShift656 i) (by exact_mod_cast hx i)
    simp only [Rat.cast_mul] at he
    exact (mul_le_mul hw' he (abs_nonneg _) (by norm_num only)).trans (by norm_num only)
  calc
    _ ≤ ∑ _ : Fin 7, (1 / 10 ^ 10 : ℝ) := Finset.sum_le_sum fun i _ ↦ h i
    _ = _ := by
      norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]

/-- The rational upper endpoints bound all six real coefficients. -/
theorem theta_coeff_upper_656 (j : Fin 6) : thetaCoeff656 j ≤ thetaCoeffUpper656 j := by
  have h : ∀ k : Fin 6, coeffApprox k + 7 / 10 ^ 10 ≤ thetaCoeffUpper656 k := by decide +kernel
  have hc : (coeffApprox j : ℝ) + 7 / 10 ^ 10 ≤ (thetaCoeffUpper656 j : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (h j)
  linarith only [(abs_le.mp (coeff_error j)).2, hc]

/-- Centering at 23/2 leaves a degree-five polynomial in the displacement. -/
theorem theta_poly_expand_656 (v : ℝ) :
    quarterAuxConductorPoly656 v = ∑ j : Fin 6, thetaCoeff656 j * (v - 23 / 2) ^ (j : ℕ) := by
  unfold quarterAuxConductorPoly656 thetaCoeff656
  rw [← Finset.sum_neg_distrib]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coeffWeight, quarterAuxCoeff656, Rat.cast_neg, Rat.cast_mul, Rat.cast_div,
    Rat.cast_ofNat, Rat.cast_sub, Rat.cast_pow, Rat.cast_natCast]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    Nat.reduceSub, Nat.choose, Nat.cast_ofNat, Nat.cast_one, add_zero]
  ring

/-- Above the centering point, the upper coefficients give a polynomial
upper bound on the entire interval. -/
theorem theta_poly_upper_656 {v : ℝ} (hv : 23 / 2 ≤ v) :
    quarterAuxConductorPoly656 v ≤
      ∑ j : Fin 6, (thetaCoeffUpper656 j : ℝ) * (v - 23 / 2) ^ (j : ℕ) := by
  rw [theta_poly_expand_656]
  exact
    Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_right (theta_coeff_upper_656 j) (pow_nonneg (sub_nonneg.mpr hv) _)

/-- Over radii at least 322, the decay factor can increase by at most
0.00000365 times the distance to the right endpoint. -/
private theorem theta_decay_affine {r u : ℝ} (hr : 322 ≤ r) (hru : r ≤ u) :
    r ^ (-(6 / 5) : ℝ) ≤ u ^ (-(6 / 5) : ℝ) + 0.00000365 * (u - r) := by
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 322) (p := 11) (d := 5)
        (lo := 0) (hi := 0.000003038905) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hp
  let f := fun t : ℝ ↦ t ^ (-(6 / 5) : ℝ) + 0.00000365 * t
  have hd (t : ℝ) (ht : 322 ≤ t) :=
    (Real.hasDerivAt_rpow_const (p := -(6 / 5 : ℝ))
          (Or.inl ((by norm_num only : (0 : ℝ) < 322).trans_le ht).ne')).add
      ((hasDerivAt_id t).const_mul (0.00000365 : ℝ))
  have hm : MonotoneOn f (Set.Ici 322) := by
    apply
      monotoneOn_of_deriv_nonneg (convex_Ici _)
        (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
        (fun t ht ↦ (hd t (interior_subset ht)).differentiableAt.differentiableWithinAt)
    intro t ht
    have ht₁ : 322 ≤ t := interior_subset ht
    rw [(hd t ht₁).deriv]
    have ht₂ :=
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 322) ht₁
            (by norm_num only : (-(11 / 5) : ℝ) ≤ 0)).trans
        hp
    norm_num only [id_eq, mul_one, show -(6 / 5 : ℝ) - 1 = -(11 / 5) by norm_num only]
    linarith only [ht₂]
  have h := hm hr (hr.trans hru) hru
  dsimp only [f] at h
  linarith only [h]

/-- A polynomial upper bound at the right endpoint also bounds the
auxiliary polynomial at all smaller radii in the comparison range. -/
private theorem theta_poly_radius_box {r u z P : ℝ} (hr : 322 ≤ r) (hru : r ≤ u)
    (hz : 2 * Real.log u ≤ z)
    (hP : (∑ j : Fin 6, (thetaCoeffUpper656 j : ℝ) * (z - 23 / 2) ^ (j : ℕ)) ≤ P) :
    quarterAuxConductorPoly656 (2 * Real.log r) ≤ P := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 24) (lo := 23 / 4) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have h₀ := Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hr
  have h₁ := Real.log_le_log ((by norm_num only : (0 : ℝ) < 322).trans_le hr) hru
  have hv : 23 / 2 ≤ 2 * Real.log r := by linarith only [hc, h₀]
  refine (theta_poly_upper_656 hv).trans ((Finset.sum_le_sum fun j _ ↦ ?_).trans hP)
  have hcoef : ∀ j : Fin 6, 0 ≤ thetaCoeffUpper656 j := by decide +kernel
  exact
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sub_nonneg.mpr hv) (by linarith only [h₁, hz]) _)
      (Rat.cast_nonneg.mpr (hcoef j))

/-- Replace the auxiliary conductor by a right-endpoint lower estimate
and a linear correction for its possible variation. -/
private theorem theta_affine_box {r u z P p C : ℝ} (hr : 322 ≤ r) (hru : r ≤ u)
    (hz : 2 * Real.log u ≤ z)
    (hP : (∑ j : Fin 6, (thetaCoeffUpper656 j : ℝ) * (z - 23 / 2) ^ (j : ℕ)) ≤ P)
    (hp : u ^ (-(6 / 5) : ℝ) ≤ p) (hP₀ : 0 ≤ P) (hbase : C ≤ -((11 / 10 : ℝ) ^ 5 / 30) * p * P)
    (hslope : (11 / 10 : ℝ) ^ 5 / 30 * 0.00000365 * P ≤ 0.01) :
    C - 0.01 * (u - r) ≤ quarterAuxTheta656 r := by
  have hpoly := theta_poly_radius_box hr hru hz hP
  have hpow := (theta_decay_affine hr hru).trans (add_le_add hp le_rfl)
  have hmul :=
    (mul_le_mul_of_nonneg_left hpoly (Real.rpow_nonneg (by linarith only [hr]) (-(6 / 5)))).trans
      (mul_le_mul_of_nonneg_right hpow hP₀)
  have hdist := mul_le_mul_of_nonneg_right hslope (sub_nonneg.mpr hru)
  unfold quarterAuxTheta656
  nlinarith only [hmul, hbase, hdist]

/-- The auxiliary conductor lower bound for radii 322 through 325,
using the right-endpoint certificate and the common affine slope. -/
theorem theta_affine_325_656 {r : ℝ} (hr : 322 ≤ r) (hu : r ≤ 325) :
    -2.446546 - 0.01 * (325 - r) ≤ quarterAuxTheta656 r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 325) (j := 9) (n := 27) (lo := 5) (hi :=
        11.567651 / 2) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 325) (p := 6) (d := 5)
        (lo := 0) (hi := 0.0009676983) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hl hp
  refine
    theta_affine_box (P := 47094.6) (z := 11.567651) hr hu (by linarith only [hl]) ?_ hp
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [thetaCoeffUpper656, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Rat.cast_ofScientific, Rat.cast_div, Rat.cast_ofNat, Fin.val_zero,
    Fin.val_succ, Nat.reduceAdd, Nat.cast_one, add_zero]

/-- The auxiliary conductor lower bound for radii 322 through 328,
using the right-endpoint certificate and the common affine slope. -/
theorem theta_affine_328_656 {r : ℝ} (hr : 322 ≤ r) (hu : r ≤ 328) :
    -2.434837 - 0.01 * (328 - r) ≤ quarterAuxTheta656 r := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5) (hi :=
        11.586028 / 2) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 328) (p := 6) (d := 5)
        (lo := 0) (hi := 0.000957087) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hl hp
  refine
    theta_affine_box (P := 47388.86) (z := 11.586028) hr hu (by linarith only [hl]) ?_ hp
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [thetaCoeffUpper656, Fin.sum_univ_succ, Fin.sum_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Rat.cast_ofScientific, Rat.cast_div, Rat.cast_ofNat, Fin.val_zero,
    Fin.val_succ, Nat.reduceAdd, Nat.cast_one, add_zero]

/-- The exponential factor in the main conductor profile has a
kernel-checked rational upper bound. -/
private theorem main_conductor_exp_656 : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.055715328 := by
  have h :=
    aux_exp_error_656 (-(231 / 80))
      (by norm_num only [Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat, abs_neg, abs_of_nonneg])
  have hr : auxExpTaylor656 (-(231 / 80)) + 1 / 10 ^ 16 ≤ 0.055715328 := by decide +kernel
  have hc := (Rat.cast_le (K := ℝ)).mpr hr
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_ofScientific,
    Rat.cast_neg] at hc h
  rw [show (11 / 10 : ℝ) * -(21 / 8) = -(231 / 80) by norm_num only]
  linarith only [hc, (abs_le.mp h).2]

/-- At positive comparison radii, the unshifted conductor has the same
power decay as the auxiliary conductor. -/
private theorem main_conductor_factor_656 {r : ℝ} (hr : 1 ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re =
      ((11 / 10 : ℝ) ^ 5 / 30 * r ^ (-(6 / 5) : ℝ)) *
        (Real.exp ((11 / 10) * -(21 / 8)) * (2 * Real.log r + 21 / 8) ^ 5) := by
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have hp := inv_pos.mpr (zero_lt_one.trans_le hx)
  rw [quarter_transform_656 hp
      ((Real.log_nonpos hp.le (inv_le_one_of_one_le₀ hx)).trans (by norm_num only)),
    Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  have h := aux_conductor_factor (zero_lt_one.trans_le hr) (-(21 / 8))
  dsimp only at h
  rw [sub_neg_eq_add] at h
  rw [sub_neg_eq_add, add_comm (21 / 8 : ℝ)]
  exact h

/-- A right-endpoint bound and the affine decay estimate control the
unshifted conductor at every earlier radius in the interval. -/
private theorem main_conductor_box {r u z p C : ℝ} (hr : 322 ≤ r) (hru : r ≤ u)
    (hz : 2 * Real.log u ≤ z) (hp : u ^ (-(6 / 5) : ℝ) ≤ p)
    (hb : (11 / 10 : ℝ) ^ 5 / 30 * p * (0.055715328 * (z + 21 / 8) ^ 5) ≤ C)
    (hd : (11 / 10 : ℝ) ^ 5 / 30 * 0.00000365 * (0.055715328 * (z + 21 / 8) ^ 5) ≤ 0.007) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C + 0.007 * (u - r) := by
  have hr₁ : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 322).trans hr
  have hl := Real.log_nonneg hr₁
  have hlr := Real.log_le_log (zero_lt_one.trans_le hr₁) hru
  have hpow := (theta_decay_affine hr hru).trans (add_le_add hp le_rfl)
  have hlog : 0 ≤ 2 * Real.log r + 21 / 8 := by linarith only [hl]
  have hv : 2 * Real.log r + 21 / 8 ≤ z + 21 / 8 := by linarith only [hlr, hz]
  have hpoly :=
    mul_le_mul main_conductor_exp_656 (pow_le_pow_left₀ hlog hv 5) (pow_nonneg hlog _)
      (by norm_num only)
  have hmul :=
    mul_le_mul hpow hpoly (mul_nonneg (Real.exp_pos _).le (pow_nonneg hlog _))
      ((Real.rpow_nonneg (zero_le_one.trans hr₁) _).trans hpow)
  rw [main_conductor_factor_656 hr₁]
  nlinarith only [hmul, hb, mul_le_mul_of_nonneg_right hd (sub_nonneg.mpr hru)]

/-- The unshifted conductor on radii 322 through 325 is bounded by
its certified right-endpoint value and the common affine correction. -/
theorem main_conductor_325_656 {r : ℝ} (hr : 322 ≤ r) (hu : r ≤ 325) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.666766 + 0.007 * (325 - r) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 325) (j := 9) (n := 27) (lo := 5) (hi :=
        11.567651 / 2) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 325) (p := 6) (d := 5)
        (lo := 0) (hi := 0.0009676983) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hl hp
  exact
    main_conductor_box (z := 11.567651) hr hu (by linarith only [hl]) hp (by norm_num only)
      (by norm_num only)

/-- The unshifted conductor on radii 322 through 328 is bounded by
its certified right-endpoint value and the common affine correction. -/
theorem main_conductor_328_656 {r : ℝ} (hr : 322 ≤ r) (hu : r ≤ 328) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.659189 + 0.007 * (328 - r) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5) (hi :=
        11.586028 / 2) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 328) (p := 6) (d := 5)
        (lo := 0) (hi := 0.000957087) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at hl hp
  exact
    main_conductor_box (z := 11.586028) hr hu (by linarith only [hl]) hp (by norm_num only)
      (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
