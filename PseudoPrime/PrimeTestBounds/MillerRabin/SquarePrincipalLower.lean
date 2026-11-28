/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleUnitPrincipal
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredFull
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCenteredCombinedError
import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleCenteredConstants
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareRecoveryWeight
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Psi70Window

/-! # Principal term and boundary savings through log 556 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem cutoff_exp_upper : Real.exp (567 / 200 : ℝ) ≤ 17030401 / 1000000 := by
  have h :=
    Analysis.exp_le_taylor_add_two_next (x := (567 / 200 : ℝ)) (n := 22) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h
  linarith only [h]

/-- The actual six-pole principal coefficient exceeds 0.71819. Evaluate the
integral and the half point and use upper Taylor bounds for their exponentials. -/
theorem square_principal_delta :
    71819 / 100000 < 4 * refinedPrincipalMain 1 - (refinedSixPoleKernel.function (1 / 2)).re := by
  have h :=
    Analysis.exp_le_taylor_add_two_next (x := (21 / 16 : ℝ)) (n := 18) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h
  rw [refined_unit_main_eq, refined_six_pole_cutoff, refined_six_pole_half, Real.exp_neg, ← one_div]
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) cutoff_exp_upper
  linarith only [hi, h]

private theorem unit_weight_lower : 896 / 10000 < refinedWeight 1 := by
  rw [refinedWeight, refinedCoord, Real.log_one, mul_zero, sub_zero, Real.sqrt_one, mul_one,
    Real.exp_neg, ← one_div]
  linarith only [one_div_le_one_div_of_le (Real.exp_pos _) cutoff_exp_upper]

/-- The finite four-fifths psi envelope controls the lower endpoint while
retaining a positive log(2 pi) boundary of more than 0.00236 on this interval. -/
theorem square_principal_boundary {r : ℝ} (hr : 465 / 2 ≤ r) (hu : r ≤ 278) :
    -(4 * (89611 / 1000000) * (4 / 5)) + 236 / 100000 <
      4 * refinedWeight 1 * (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) / r := by
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have hp :=
    AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (x := r ^ 2)
      (by nlinarith only [hr, sq_nonneg (r - 465 / 2)])
      (by nlinarith only [pow_le_pow_left₀ h0.le hu 2])
  rw [Real.sqrt_sq h0.le] at hp
  have hpos : 0 ≤ refinedWeight 1 := by linarith only [unit_weight_lower]
  have hpsi := mul_le_mul_of_nonneg_left (abs_le.mp hp).1 hpos
  have hlog := mul_le_mul unit_weight_lower.le Analysis.log_two_mul_pi_gt.le (by norm_num only) hpos
  apply (lt_div_iff₀ h0).mpr
  nlinarith only [hpsi, hlog, mul_lt_mul_of_pos_right refinedWeight_one_upper h0, hu]

/-- The centered-error contribution before division by the radius. The two
integrals and the unit derivative are kept together for zero cancellation. -/
noncomputable def squareCenteredError (x : ℝ) : ℝ :=
  4 * (∫ u : ℝ in (0 : ℝ)..1, LLS.clippedShiftError x u * refinedSecondDensity u) -
    (∫ u : ℝ in (0 : ℝ)..Real.exp (21 / 8), LLS.clippedShiftError x u * refinedSecondDensity u) -
    4 * refinedWeightDeriv 1 * LLS.clippedShiftError x 1

/-- On the first extension interval the actual principal deficit has an explicit
linear lower bound retaining the signed centered error and the half-point term.
Combine the exact Abel identity with the certified delta and psi boundary. -/
theorem square_principal_lower {r : ℝ} (hr : 465 / 2 ≤ r) (hu : r ≤ 278) :
    let X := r ^ 2
    71819 / 100000 * r - 4 * (89611 / 1000000) * (4 / 5) + 236 / 100000 +
          squareCenteredError X / r -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / X) / r <
      4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re := by
  intro X
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have hx : 1 ≤ X := by
    exact
      le_trans (by norm_num only : (1 : ℝ) ≤ (465 / 2) ^ 2)
        (pow_le_pow_left₀ (by norm_num only) hr 2)
  rw [refined_combined_centered_identity hx, show Real.sqrt X = r from Real.sqrt_sq h0.le]
  dsimp only [squareCenteredError, X]
  simp only [sub_div, add_div]
  linarith only [square_principal_boundary hr hu, mul_lt_mul_of_pos_right square_principal_delta h0]

/-- The existing combined variation estimate bounds the centered error below
by -0.062 times the radius throughout the first extension interval. -/
theorem square_centered_variation {r : ℝ} (hr : 465 / 2 ≤ r) (hRH : RiemannHypothesis) :
    -(62 / 1000) * r ≤ squareCenteredError (r ^ 2) := by
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have h :=
    quarter_centered_combined_error hRH (x := r ^ 2)
      (by nlinarith only [hr, sq_nonneg (r - 465 / 2)])
  rw [Real.sqrt_sq h0.le] at h
  unfold squareCenteredError
  linarith only [h, refined_unit_deriv_centered, hr,
    mul_le_mul_of_nonneg_right refined_unit_deriv_centered h0.le]

/-- A one-sided psi bound at the chosen radius gives a principal lower bound under RH.
The coefficient of the boundary error is kept explicit for finite subintervals. -/
theorem square_principal_of_psi_lower {r : ℝ} (hr : 465 / 2 ≤ r) (hu : r ≤ 278)
    (hRH : RiemannHypothesis) {c : ℝ} (hc : 0 ≤ c) (hp : r ^ 2 - c * r ≤ Chebyshev.psi (r ^ 2)) :
    let X := r ^ 2
    71819 / 100000 * r - 4 * (89611 / 1000000) * c + 236 / 100000 - 62 / 1000 -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / X) / r <
      4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re := by
  intro X
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have hx : 1 ≤ X :=
    le_trans (by norm_num only : (1 : ℝ) ≤ (465 / 2) ^ 2) (pow_le_pow_left₀ (by norm_num only) hr 2)
  have hw : 0 ≤ refinedWeight 1 := by linarith only [unit_weight_lower]
  have hpsi := mul_le_mul_of_nonneg_left hp hw
  have hlog := mul_le_mul unit_weight_lower.le Analysis.log_two_mul_pi_gt.le (by norm_num only) hw
  have hv := square_centered_variation hr hRH
  have hm := mul_lt_mul_of_pos_right square_principal_delta h0
  rw [refined_combined_centered_identity hx, show Real.sqrt X = r from Real.sqrt_sq h0.le]
  change _ < r * _ + (squareCenteredError X + _ - _) / r
  have he : -(62 / 1000) ≤ squareCenteredError X / r := (le_div_iff₀ h0).mpr hv
  have hb :
    -(4 * (89611 / 1000000) * c) + 236 / 100000 <
      4 * refinedWeight 1 * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) / r := by
    apply (lt_div_iff₀ h0).mpr
    dsimp only [X]
    have hwc := mul_le_mul_of_nonneg_right refinedWeight_one_upper.le hc
    nlinarith only [hpsi, hlog, mul_le_mul_of_nonneg_right hwc h0.le, hu]
  rw [sub_div, add_div]
  linarith only [he, hb, hm]

/-- A seven-tenths one-sided finite psi estimate absorbs the variation error
without estimating individual zeta zeros. This yields the principal lower
bound used in the first extension, including the positive log boundary. -/
theorem square_principal_of_psi70 {r : ℝ} (hr : 465 / 2 ≤ r) (hu : r ≤ 278)
    (hRH : RiemannHypothesis) :
    let X := r ^ 2
    71819 / 100000 * r - 4 * (89611 / 1000000) * (4 / 5) + 236 / 100000 - 283 / 10000 -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / X) / r <
      4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re := by
  intro X
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 465 / 2).trans_le hr
  have hp :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi70_window (x := r ^ 2)
      (le_trans (by norm_num only : (51539 : ℝ) ≤ (465 / 2) ^ 2)
        (pow_le_pow_left₀ (by norm_num only) hr 2))
      ((pow_le_pow_left₀ h0.le hu 2).trans_lt (by norm_num only))
  rw [Real.sqrt_sq h0.le] at hp
  have h := square_principal_of_psi_lower hr hu hRH (by norm_num only : (0 : ℝ) ≤ 7 / 10) hp
  dsimp only [X] at h ⊢
  linarith only [h]

/-- For radii from 268 to 278, the one-third psi certificate improves the principal lower bound.
The bound includes the centered variation and the positive logarithmic boundary. -/
theorem square_principal_268_278 {r : ℝ} (hr : 268 ≤ r) (hu : r ≤ 278) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    71819 / 100000 * r - 4 * (89611 / 1000000) * (1 / 3) + 236 / 100000 - 62 / 1000 -
        3 * Real.log (2 * Real.pi) * refinedWeight (1 / X) / r <
      4 *
          (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re := by
  intro X
  have h0 : 0 < r := (by norm_num only : (0 : ℝ) < 268).trans_le hr
  have hp :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_third_window (x := r ^ 2)
      (le_trans (by norm_num only : (71539 : ℝ) ≤ (268 : ℝ) ^ 2)
        (pow_le_pow_left₀ (by norm_num only) hr 2))
      ((pow_le_pow_left₀ h0.le hu 2).trans_lt (by norm_num only))
  rw [Real.sqrt_sq h0.le] at hp
  exact
    square_principal_of_psi_lower ((by norm_num only : (465 / 2 : ℝ) ≤ 268).trans hr) hu hRH
      (by norm_num only : (0 : ℝ) ≤ 1 / 3) hp

end PseudoPrime.PrimeTestBounds.MillerRabin
