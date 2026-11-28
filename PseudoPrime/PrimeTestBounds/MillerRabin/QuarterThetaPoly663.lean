/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSeries656

/-! # Centered conductor polynomial for section 137 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The displacement of a section 137 frequency from the main shift. -/
def quarterShift663 (i : Fin 6) : ℚ :=
  quarterFreq663 i - 21 / 8

/-- The signed degree-five conductor polynomial from (137.30). -/
noncomputable def quarterAuxConductorPoly663 (v : ℝ) : ℝ :=
  -(∑ i,
      (quarterCoeff663 i : ℝ) * Real.exp ((11 / 10 : ℝ) * quarterShift663 i) *
        (v - quarterShift663 i) ^ 5)

/-- The shifted conductor contribution at radius r in (137.30). -/
noncomputable def quarterAuxTheta663 (r : ℝ) : ℝ :=
  -(11 / 10) ^ 5 / 30 * r ^ (-(6 / 5) : ℝ) * quarterAuxConductorPoly663 (2 * Real.log r)

/-- Rational multipliers for the coefficient of degree j after shifting
the logarithmic variable by 23/2. -/
private def coeffWeight (j : ℕ) (i : Fin 6) : ℚ :=
  -(quarterCoeff663 i) * (Nat.choose 5 j) * (23 / 2 - quarterShift663 i) ^ (5 - j)

/-- The six real coefficients obtained by binomial expansion. -/
noncomputable def thetaCoeff663 (j : ℕ) : ℝ :=
  ∑ i, (coeffWeight j i : ℝ) * Real.exp ((11 / 10 : ℚ) * quarterShift663 i : ℚ)

/-- The exact rational approximation uses the existing exponential certificate. -/
private def coeffApprox (j : ℕ) : ℚ :=
  ∑ i, coeffWeight j i * profileExpTaylor ((11 / 10) * quarterShift663 i)

/-- Outward upper endpoints for the six centered coefficients. -/
@[expose]
def thetaCoeffUpper663 (j : Fin 6) : ℚ :=
  ![47907.520567, 13411.802344, -421.931434, -321.153792, -1.404987, 2.507016] j

/-- The total rounding error is at most six times the bound for one
weighted exponential. -/
private theorem coeff_error (j : Fin 6) :
    |thetaCoeff663 j - (coeffApprox j : ℝ)| ≤ 6 / 10 ^ 10 := by
  have hw : ∀ k : Fin 6, ∀ i : Fin 6, |coeffWeight k i| ≤ 1000000 := by decide +kernel
  have hx : ∀ i : Fin 6, |(11 / 10 : ℚ) * quarterShift663 i| ≤ 11 := by decide +kernel
  unfold thetaCoeff663 coeffApprox
  rw [Rat.cast_sum, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h (i : Fin 6) :
    |(coeffWeight j i : ℝ) * Real.exp ((11 / 10 : ℚ) * quarterShift663 i : ℚ) -
          ((coeffWeight j i * profileExpTaylor ((11 / 10) * quarterShift663 i) : ℚ) : ℝ)| ≤
      1 / 10 ^ 10 := by
    simp only [Rat.cast_mul, ← mul_sub, abs_mul]
    have hw' : |(coeffWeight j i : ℝ)| ≤ 1000000 := by exact_mod_cast hw j i
    have he := profile_exp_error ((11 / 10) * quarterShift663 i) (by exact_mod_cast hx i)
    rw [Rat.cast_mul] at he
    exact (mul_le_mul hw' he (abs_nonneg _) (by norm_num only)).trans (by norm_num only)
  calc
    _ ≤ ∑ _ : Fin 6, (1 / 10 ^ 10 : ℝ) := Finset.sum_le_sum fun i _ ↦ h i
    _ = _ := by
      norm_num only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_ofNat]

/-- The rational upper endpoints bound all six real coefficients. -/
theorem theta_coeff_upper_663 (j : Fin 6) : thetaCoeff663 j ≤ thetaCoeffUpper663 j := by
  have h : ∀ k : Fin 6, coeffApprox k + 6 / 10 ^ 10 ≤ thetaCoeffUpper663 k := by decide +kernel
  have hc : (coeffApprox j : ℝ) + 6 / 10 ^ 10 ≤ (thetaCoeffUpper663 j : ℝ) := by
    simpa only [Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using
      (Rat.cast_le (K := ℝ)).mpr (h j)
  linarith only [(abs_le.mp (coeff_error j)).2, hc]

/-- Centering at 23/2 leaves a degree-five polynomial in the displacement. -/
theorem theta_poly_expand_663 (v : ℝ) :
    quarterAuxConductorPoly663 v = ∑ j : Fin 6, thetaCoeff663 j * (v - 23 / 2) ^ (j : ℕ) := by
  unfold quarterAuxConductorPoly663 thetaCoeff663
  rw [← Finset.sum_neg_distrib]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp only [coeffWeight, Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_natCast]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ, Nat.reduceAdd,
    Nat.reduceSub, Nat.choose, Nat.cast_ofNat, Nat.cast_one, add_zero]
  ring

/-- For a nonnegative displacement from 23/2, the powers preserve each
coefficient inequality, including the negative coefficients. -/
theorem theta_poly_upper_663 {v : ℝ} (hv : 23 / 2 ≤ v) :
    quarterAuxConductorPoly663 v ≤
      ∑ j : Fin 6, (thetaCoeffUpper663 j : ℝ) * (v - 23 / 2) ^ (j : ℕ) := by
  rw [theta_poly_expand_663]
  exact
    Finset.sum_le_sum fun j _ ↦
      mul_le_mul_of_nonneg_right (theta_coeff_upper_663 j) (pow_nonneg (sub_nonneg.mpr hv) _)

/-- At radius at least 328 all six shifts are on the inverse transform support. -/
theorem quarter_aux_scale_ge_one_663 {r : ℝ} (hr : 328 ≤ r) (i : Fin 6) :
    1 ≤ r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)) := by
  have hr₀ : 0 < r := by linarith only [hr]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofScientific, Rat.cast_ofNat] at hlo
  have hl := hlo.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr)
  have hf : ∀ i, quarterFreq663 i ≤ 10 := by decide +kernel
  have hfi : (quarterFreq663 i : ℝ) ≤ 10 := by exact_mod_cast hf i
  rw [← Real.exp_log hr₀, ← Real.exp_natCast_mul, ← Real.exp_add, ← Real.exp_zero, Real.exp_le_exp]
  norm_num only [Nat.cast_ofNat]
  linarith only [hl, hfi]

private theorem conductor_profile {r : ℝ} (hr : 328 ≤ r) (i : Fin 6) :
    let x := r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))
    let z := (11 / 10 : ℝ) * (2 * Real.log r - quarterShift663 i)
    (quarterKernel656.transform x⁻¹).re = z ^ 5 * Real.exp (-z) / 120 := by
  intro x z
  have hr₀ : 0 < r := by linarith only [hr]
  have hx : 1 ≤ x := quarter_aux_scale_ge_one_663 hr i
  have hx₀ := zero_lt_one.trans_le hx
  have hl : Real.log x⁻¹ = (quarterFreq663 i : ℝ) - 2 * Real.log r := by
    dsimp only [x]
    rw [Real.log_inv, Real.log_mul (pow_ne_zero _ hr₀.ne') (Real.exp_pos _).ne', Real.log_pow,
      Real.log_exp]
    ring
  have hs : Real.log x⁻¹ ≤ 21 / 8 :=
    (Real.log_nonpos (inv_pos.mpr hx₀).le (inv_le_one_of_one_le₀ hx)).trans (by norm_num only)
  rw [quarter_transform_656 (inv_pos.mpr hx₀) hs, hl]
  have hz : (11 / 10 : ℝ) * (21 / 8 - ((quarterFreq663 i : ℝ) - 2 * Real.log r)) = z := by
    simp only [z, quarterShift663, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    ring
  rw [hz]

/-- Summing the six inverse transform terms gives the conductor contribution
in (137.30) at every radius at least 328. -/
theorem quarter_aux_theta_sum_663 {r : ℝ} (hr : 328 ≤ r) :
    (∑ i,
        (quarterCoeff663 i : ℝ) *
          (4 * r *
            (quarterKernel656.transform (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)))⁻¹).re)) =
      quarterAuxTheta663 r := by
  have hr₀ : 0 < r := by linarith only [hr]
  have he (i : Fin 6) := conductor_profile hr i
  have hf (i : Fin 6) := aux_conductor_factor hr₀ (quarterShift663 i : ℝ)
  dsimp only at he hf
  unfold quarterAuxTheta663 quarterAuxConductorPoly663
  simp only [he, hf, mul_assoc, mul_left_comm (quarterCoeff663 _ : ℝ), ← Finset.mul_sum]
  ring

/-- The six negative half-point terms sum to the signed coefficient
divided by the radius. The sign matches the residual in (137.31). -/
theorem quarter_aux_neg_pole_sum_663 {r : ℝ} (hr : 0 < r) :
    -3 *
        (∑ i,
          (quarterCoeff663 i : ℝ) *
            (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) *
                ((r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)) : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re) =
      quarterAuxNegPole663 / r := by
  have h (i : Fin 6) := quarter_shifted_neg_pole_656 hr (quarterShift663 i : ℝ)
  have hs (i : Fin 6) : 21 / 8 + (quarterShift663 i : ℝ) = quarterFreq663 i := by
    simp only [quarterShift663, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    ring
  have he (i : Fin 6) : ((-halfArg i : ℚ) : ℝ) = (quarterShift663 i : ℝ) / 2 := by
    simp only [halfArg, quarterShift663, Rat.cast_div, neg_div, neg_neg, Rat.cast_ofNat]
  unfold quarterAuxNegPole663
  simp only [he, ← hs, h]
  simp only [mul_left_comm (quarterCoeff663 _ : ℝ), ← Finset.mul_sum]
  ring

/-- The six positive half-point terms for three characters contribute the
linear coefficient from (137.27) times the radius. -/
theorem quarter_aux_half_pole_sum_663 {r : ℝ} (hr : 0 < r) :
    3 *
        (∑ i,
          (quarterCoeff663 i : ℝ) *
            (quarterKernel656.function (1 / 2) *
                ((r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)) : ℝ) : ℂ) ^ (1 / 2 : ℂ)).re) =
      quarterAuxHalfCoeff663 * r := by
  have hs (i : Fin 6) : 21 / 8 + (quarterShift663 i : ℝ) = quarterFreq663 i := by
    simp only [quarterShift663, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    ring
  have h (i : Fin 6) := quarter_shifted_half_pole_656 hr (quarterShift663 i : ℝ)
  dsimp only at h
  simp only [hs] at h
  unfold quarterAuxHalfCoeff663
  simp only [halfArg, quarterShift663, Rat.cast_sub, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, h]
  simp only [mul_assoc, mul_left_comm (quarterCoeff663 _ : ℝ), ← Finset.mul_sum]
  ring

/-- Four times the symmetric transform at the inverse exponential scale
is the conductor profile used in the six-frequency coefficient. -/
theorem quarter_conductor_profile_eq_663 (s : ℚ) :
    quarterConductorProfile663 s = 4 * quarterSymmetricProfile656 (Real.exp (s : ℝ))⁻¹ := by
  rw [symmetric_profile_value (inv_pos.mpr (Real.exp_pos _)), Real.log_inv, Real.log_exp, abs_neg]
  simp only [quarterConductorProfile663, Rat.cast_mul, Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat,
    Rat.cast_abs]
  ring

/-- At total log conductor four times the radius, the mixed symmetric
transform contributes the conductor coefficient times the radius. -/
theorem quarter_aux_conductor_sum_663 {L r : ℝ} (hL : L = 4 * r) :
    L * quarterAuxMix663 (fun s ↦ quarterSymmetricProfile656 (Real.exp (s : ℝ))⁻¹) =
      quarterAuxMix663 quarterConductorProfile663 * r := by
  subst L
  unfold quarterAuxMix663
  simp only [quarter_conductor_profile_eq_663, ← Finset.mul_sum, mul_left_comm]
  ring

/-- The six shifted conductor and negative half-point terms factor into
the two contributions used in the residual estimate. -/
theorem quarter_aux_shift_signed_663 {r : ℝ} (hr : 328 ≤ r) :
    let x := fun i : Fin 6 ↦ r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))
    (∑ i,
        (quarterCoeff663 i : ℝ) *
          (4 * r * (quarterKernel656.transform (x i)⁻¹).re -
            3 *
              (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) * (x i : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re)) =
      quarterAuxTheta663 r + quarterAuxNegPole663 / r := by
  intro x
  have hc := quarter_aux_theta_sum_663 hr
  have hp := quarter_aux_neg_pole_sum_663 (by linarith only [hr] : 0 < r)
  simp only [mul_sub, Finset.sum_sub_distrib, mul_left_comm (quarterCoeff663 _ : ℝ) 3,
    ← Finset.mul_sum]
  dsimp only [x]
  linarith only [hc, hp]

/-- The centered polynomial upper bound on a logarithmic interval. Negative
coefficients use the left endpoint and nonnegative coefficients the right. -/
noncomputable def thetaIntervalUpper663 (l u : ℝ) : ℝ :=
  ∑ j : Fin 6, (thetaCoeffUpper663 j : ℝ) * (if thetaCoeffUpper663 j < 0 then l else u) ^ (j : ℕ)

/-- The signed endpoint choices bound the polynomial throughout the interval. -/
theorem theta_poly_interval_663 {v l u : ℝ} (hl : 0 ≤ l) (hv : v - 23 / 2 ∈ Set.Icc l u) :
    quarterAuxConductorPoly663 v ≤ thetaIntervalUpper663 l u := by
  have hv₀ := hl.trans hv.1
  refine (theta_poly_upper_663 (sub_nonneg.mp hv₀)).trans ?_
  refine Finset.sum_le_sum fun j _ ↦ ?_
  by_cases hj : thetaCoeffUpper663 j < 0
  · rw [ite_eq_left hj]
    exact mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hl hv.1 _) (by exact_mod_cast hj.le)
  · rw [ite_eq_right hj]
    exact
      mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hv₀ hv.2 _) (by exact_mod_cast le_of_not_gt hj)

/-- An upper bound on the inverse power at the left radius and the signed
polynomial interval bound give a lower bound for the conductor contribution. -/
theorem theta_interval_lower_663 {r l u M : ℝ} (hr : 0 < r) (hl : 0 ≤ l)
    (hv : 2 * Real.log r - 23 / 2 ∈ Set.Icc l u) (hM : r ^ (-(6 / 5) : ℝ) ≤ M)
    (hU : 0 ≤ thetaIntervalUpper663 l u) :
    -(11 / 10) ^ 5 / 30 * M * thetaIntervalUpper663 l u ≤ quarterAuxTheta663 r := by
  have h :=
    (mul_le_mul_of_nonneg_left (theta_poly_interval_663 hl hv)
          (Real.rpow_nonneg hr.le (-(6 / 5) : ℝ))).trans
      (mul_le_mul_of_nonneg_right hM hU)
  unfold quarterAuxTheta663
  have hc : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30 := by norm_num only
  nlinarith only [mul_le_mul_of_nonneg_left h hc]

/-- Combine the conductor bound with the positive contribution of the
signed negative half-point residues. The right radius bounds the denominator. -/
theorem theta_pole_lower_663 {r R l u M : ℝ} (hr : 0 < r) (hR : r ≤ R) (hl : 0 ≤ l)
    (hv : 2 * Real.log r - 23 / 2 ∈ Set.Icc l u) (hM : r ^ (-(6 / 5) : ℝ) ≤ M)
    (hU : 0 ≤ thetaIntervalUpper663 l u) :
    -(11 / 10) ^ 5 / 30 * M * thetaIntervalUpper663 l u + 18.29172549 / R ≤
      quarterAuxTheta663 r + quarterAuxNegPole663 / r := by
  have hp :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 18.29172549) hr hR).trans
      (div_le_div_of_nonneg_right quarter_aux_neg_pole_box_663.1 hr.le)
  exact add_le_add (theta_interval_lower_663 hr hl hv hM hU) hp

end PseudoPrime.PrimeTestBounds.MillerRabin
