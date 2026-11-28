/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighCompensation
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMiddlePrincipalAbel
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK186ForwardMoment
public import PseudoPrime.Analysis.ExponentialFixedPointBounds

/-! # The main forward integral of the high Gaussian kernels -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The physical forward weight agrees with the weight used in the principal
Abel identity at every positive argument. -/
theorem high_forward_weight_eq (K : HighGaussianKernel) (x : ℝ) {t : ℝ} (ht : 0 < t) :
    let z := x + 5
    let a := (K.pole : ℝ)
    let v := 5 - Real.log (t / Real.exp x)
    t ^ (-(1 / 2) : ℝ) * Real.exp (-a * v) * K.realProfile.eval v =
      middlePrincipalWeight K.realProfile (Real.exp (-a * z)) z (a - 1 / 2) t := by
  simpa only [one_mul, middleCompWeight] using
    middle_principal_physical K.realProfile 1 (K.pole : ℝ) 5 x ht

/-- The main forward integral is determined by two fixed Laplace values and
one exponentially damped boundary value. The rational profile already
includes the Gram normalization. -/
theorem high_forward_main_integral (K : HighGaussianKernel) {x : ℝ} (hx : 0 ≤ x) :
    let z := x + 5
    let a := (K.pole : ℝ)
    let M := (middleMomentPoly K.ratProfile (K.pole + 1 / 2) 0).map (Rat.castHom ℝ)
    let W := middlePrincipalWeight K.realProfile (Real.exp (-a * z)) z (a - 1 / 2)
    4 * (∫ t in (1 : ℝ)..Real.exp x, W t) - (∫ t in (1 : ℝ)..Real.exp z, W t) =
      Real.exp (x / 2) * (4 * Real.exp (-a * 5) * M.eval 5 - Real.exp (5 / 2) * M.eval 0) -
        3 * (Real.exp (-a * z) * M.eval z) := by
  have hσ : K.pole + 1 / 2 ≠ 0 := by cases K <;> norm_num only [HighGaussianKernel.pole]
  have h := middle_principal_main_slope K.ratProfile 1 5 x hσ hx (by norm_num only)
  dsimp only at h ⊢
  have ha : ((K.pole + 1 / 2 : ℚ) : ℝ) - 1 / 2 = (K.pole : ℝ) := by
    simp only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, add_sub_cancel_right]
  have hd : ((K.pole + 1 / 2 : ℚ) : ℝ) - 1 = (K.pole : ℝ) - 1 / 2 := by
    simp only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
    ring
  simpa only [ha, hd, one_mul, mul_one, high_comp_profile_map] using h

/-- The rational Taylor upper bound includes twice the first omitted term. -/
private def expUpper (x : ℚ) (n : ℕ) : ℚ :=
  (∑ j ∈ Finset.range n, x ^ j / (j.factorial : ℚ)) + x ^ n / (n.factorial : ℚ) * 2

/-- An exact rational comparison with the Taylor upper bound controls the real exponential. -/
private theorem exp_le_of_check {x u : ℚ} {n : ℕ} (hx : 0 ≤ x) (hs : (x : ℝ) / (n + 1 : ℕ) ≤ 1 / 2)
    (hc : expUpper x n ≤ u) : Real.exp (x : ℝ) ≤ (u : ℝ) := by
  have h := (Rat.cast_le (K := ℝ)).mpr hc
  simp only [expUpper, Rat.cast_add, Rat.cast_sum, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_natCast, Rat.cast_ofNat] at h
  exact (Analysis.exp_le_taylor_add_two_next (Rat.cast_nonneg.mpr hx) hs).trans h

/-- A 64-term upper bound at 55/4 gives the reciprocal lower bound at -55/4. -/
private theorem k186_exp_lower : (106770401003478 : ℝ) / 10 ^ 20 ≤ Real.exp (-55 / 4) := by
  have h :=
    exp_le_of_check (x := 55 / 4) (u := 10 ^ 20 / 106770401003478) (n := 64) (by norm_num only)
      (by norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat]) (by decide +kernel)
  simp only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at h
  rw [show (-55 / 4 : ℝ) = -(55 / 4) by ring, Real.exp_neg, ← one_div]
  exact
    (show (106770401003478 : ℝ) / 10 ^ 20 = 1 / (10 ^ 20 / 106770401003478) by
          norm_num only).le.trans
      (one_div_le_one_div_of_le (Real.exp_pos _) h)

/-- A 40-term upper bound suffices at the compensation exponent 5/2. -/
private theorem k186_exp_upper : Real.exp (5 / 2) ≤ (1218249396070347343808 : ℝ) / 10 ^ 20 := by
  have h :=
    exp_le_of_check (x := 5 / 2) (u := 1218249396070347343808 / 10 ^ 20) (n := 40)
      (by norm_num only) (by norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat])
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] using h

/-- Fixed outward-rounded endpoint values and the scaled compensation
integral supply the linear coefficient in the K186 forward estimate. -/
theorem k186_forward_slope_of_caps {m₅ m₀ I : ℝ} (hm₅ : 249979212898005394200 / 10 ^ 15 ≤ m₅)
    (hm₀ : m₀ ≤ 28393155821834 / 10 ^ 15) (hI : I ≤ 13765063832627 / 500000000000000000) :
    0.7216056623106 ≤ 4 * Real.exp (-55 / 4) * m₅ - Real.exp (5 / 2) * m₀ - 4 * I := by
  have hl := mul_le_mul k186_exp_lower hm₅ (by norm_num only) (Real.exp_pos _).le
  have hu := mul_le_mul hm₀ k186_exp_upper (Real.exp_pos _).le (by norm_num only)
  rw [mul_comm m₀, mul_comm (28393155821834 / 10 ^ 15 : ℝ)] at hu
  linarith only [hl, hu, hI]

/-- The certified K186 Laplace values supply the forward slope as soon
as the scaled compensation integral is bounded. -/
theorem k186_forward_slope {I : ℝ} (hI : I ≤ 13765063832627 / 500000000000000000) :
    let K := HighGaussianKernel.k186
    let M := (middleMomentPoly K.ratProfile (K.pole + 1 / 2) 0).map (Rat.castHom ℝ)
    0.7216056623106 ≤ 4 * Real.exp (-55 / 4) * M.eval 5 - Real.exp (5 / 2) * M.eval 0 - 4 * I := by
  exact k186_forward_slope_of_caps k186_forward_moment_caps.1 k186_forward_moment_caps.2 hI

/-- An outward-rounded cap on the unscaled compensation integral
implies the scaled cap used for the K186 main coefficient. -/
theorem k186_scaled_comp_of_cap {I : ℝ} (hI : I ≤ 225981049151000 / 10 ^ 20) :
    Real.exp (5 / 2) * I ≤ 13765063832627 / 500000000000000000 := by
  calc
    _ ≤ Real.exp (5 / 2) * (225981049151000 / 10 ^ 20) :=
      mul_le_mul_of_nonneg_left hI (Real.exp_nonneg _)
    _ ≤ (1218249396070347343808 / 10 ^ 20) * (225981049151000 / 10 ^ 20) :=
      mul_le_mul_of_nonneg_right k186_exp_upper (by norm_num only)
    _ ≤ _ := by norm_num only

/-- A quadratic error in the shifted log coordinate fits the far log-square
budget. The bound leaves 300 for the remaining constant-size forward costs. -/
theorem k186_forward_shifted_error (u : ℝ) :
    (1 / 12 : ℝ) * (2 * u + 5) ^ 2 + 300 ≤ 7 / 20 * u ^ 2 + 350 := by
  nlinarith only [sq_nonneg (u - 50)]

end PseudoPrime.PrimeTestBounds.MillerRabin
