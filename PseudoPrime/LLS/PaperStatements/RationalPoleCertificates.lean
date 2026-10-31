/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleCutoff
public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import PseudoPrime.LLS.PaperStatements.RationalPoleMajorant

/-! # Small rational certificates for the fourth- and sixth-order kernels -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- A rational Taylor upper bound for a fixed positive exponential.
Use finitely many positive Taylor terms and twice the next term as a certified tail.
The coefficient certificate below consumes this small scalar inequality. -/
private theorem rationalPole_exp_three_upper : Real.exp (3 : ℝ) ≤ 2008554 / 100000 := by
  have ht :=
    Analysis.exp_le_taylor_add_two_next (x := (3 : ℝ)) (n := 16) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  linarith only [ht]

/-- A rational lower bound for the required negative exponential.
Invert a positive Taylor upper bound with order reversal.
This provides an exact lower bound for the corresponding cutoff integral. -/
private theorem rationalPole_exp_neg_three_lower : (100000 / 2008554 : ℝ) ≤ Real.exp (-3) := by
  rw [Real.exp_neg, ← one_div]
  have h := one_div_le_one_div_of_le (Real.exp_pos (3 : ℝ)) rationalPole_exp_three_upper
  norm_num only at h ⊢
  exact h

/-- A rational Taylor upper bound for a fixed positive exponential.
Use finitely many positive Taylor terms and twice the next term as a certified tail.
The coefficient certificate below consumes this small scalar inequality. -/
private theorem rationalPole_exp_half_three_upper : Real.exp (3 / 2 : ℝ) ≤ 44817 / 10000 := by
  have ht :=
    Analysis.exp_le_taylor_add_two_next (x := (3 / 2 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  linarith only [ht]

/-- A rational Taylor upper bound for a fixed positive exponential.
Use finitely many positive Taylor terms and twice the next term as a certified tail.
The coefficient certificate below consumes this small scalar inequality. -/
private theorem rationalPole_exp_ratio_upper : Real.exp (14 / 13 : ℝ) ≤ 293564 / 100000 := by
  have ht :=
    Analysis.exp_le_taylor_add_two_next (x := (14 / 13 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  linarith only [ht]

/-- A rational Taylor upper bound for a fixed positive exponential.
Use finitely many positive Taylor terms and twice the next term as a certified tail.
The coefficient certificate below consumes this small scalar inequality. -/
private theorem rationalPole_exp_phase_upper : Real.exp (14 / 25 : ℝ) ≤ 175068 / 100000 := by
  have ht :=
    Analysis.exp_le_taylor_add_two_next (x := (14 / 25 : ℝ)) (n := 10) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  linarith only [ht]

/-- A rational lower bound for the required negative exponential.
Invert a positive Taylor upper bound with order reversal.
This provides an exact lower bound for the corresponding cutoff integral. -/
private theorem rationalPole_exp_neg_ratio_lower :
    (100000 / 293564 : ℝ) ≤ Real.exp (-(14 / 13)) := by
  rw [Real.exp_neg, ← one_div]
  have h := one_div_le_one_div_of_le (Real.exp_pos (14 / 13 : ℝ)) rationalPole_exp_ratio_upper
  norm_num only at h ⊢
  exact h

/-- A rational lower bound for the actual unit cutoff integral.
Insert the exact cutoff formula and the certified reciprocal exponential bound.
This supplies the positive principal margin in the coefficient certificate. -/
private theorem rationalPole_six_integral_lower :
    (2765708 / 10000000 : ℝ) ≤
      ∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u := by
  rw [rationalPole_six_cutoff]
  have h :=
    mul_le_mul_of_nonneg_left rationalPole_exp_neg_three_lower
      (by norm_num only : (0 : ℝ) ≤ 80993 / 14580)
  linarith only [h]

/-- A rational upper bound for the actual kernel value at one half.
Apply the exact endpoint formula and a finite Taylor upper bound.
This bounds the subtracted endpoint term in the principal margin. -/
private theorem rationalPole_six_endpoint_upper :
    (rationalPoleSixKernel.function (1 / 2)).re ≤ (393456 / 1000000 : ℝ) := by
  rw [rationalPoleSixKernel, rationalPole_half_value]
  norm_num only
  nlinarith only [rationalPole_exp_half_three_upper]

/-- A rational lower bound for the actual unit cutoff integral.
Insert the exact cutoff formula and the certified reciprocal exponential bound.
This supplies the positive principal margin in the coefficient certificate. -/
private theorem rationalPole_four_integral_lower :
    (312439 / 1000000 : ℝ) ≤
      ∫ u : ℝ in (0 : ℝ)..1, (rationalPoleFourKernel.transform u).re / Real.sqrt u := by
  rw [rationalPole_four_cutoff]
  have h :=
    mul_le_mul_of_nonneg_left rationalPole_exp_neg_ratio_lower
      (by norm_num only : (0 : ℝ) ≤ 484820459 / 528581976)
  linarith only [h]

/-- A rational upper bound for the actual kernel value at one half.
Apply the exact endpoint formula and a finite Taylor upper bound.
This bounds the subtracted endpoint term in the principal margin. -/
private theorem rationalPole_four_endpoint_upper :
    (rationalPoleFourKernel.function (1 / 2)).re ≤ (341088 / 1000000 : ℝ) := by
  rw [rationalPoleFourKernel, rationalPole_half_value]
  norm_num only
  nlinarith only [rationalPole_exp_phase_upper]

/-- A positive lower principal margin preserves a strict squared certificate.
Monotonicity of squaring on nonnegative reals transports the rational check. -/
private theorem coeff_of_lower {A d M c : ℝ} (hd : 0 < d) (hA : d ≤ A) (hc : 0 ≤ c)
    (hcert : M ^ 2 < c * d ^ 2) : 0 < A ∧ M ^ 2 < c * A ^ 2 := by
  have hs := mul_self_le_mul_self hd.le hA
  have hm := mul_le_mul_of_nonneg_left hs hc
  exact ⟨hd.trans_le hA, hcert.trans_le (by simpa only [pow_two] using hm)⟩

/-- The actual fourth-pole principal gap is at least 28379/100000.
Combine the existing rational cutoff lower bound and endpoint upper bound.
This retains the sharper margin needed to make the coefficient 777/1000 finite. -/
theorem rationalPole_four_principal_gap :
    (28379 / 100000 : ℝ) ≤
      2 * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleFourKernel.transform u).re / Real.sqrt u) -
        (rationalPoleFourKernel.function (1 / 2)).re := by
  linarith only [rationalPole_four_integral_lower, rationalPole_four_endpoint_upper]

/-- The actual cutoff, mass and half-value satisfy a positive strict coefficient certificate.
Use the rational lower integral and upper endpoint, then square a positive lower bound.
This certifies the kernel data consumed by the conductor-sensitive least-prime theorem. -/
theorem rationalPole_quadratic_certificate :
    0 <
        (2 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleFourKernel.transform u).re / Real.sqrt u) -
          (rationalPoleFourKernel.function (1 / 2)).re ∧
      (((2 : ℝ) - 1) * rationalPoleFourKernel.mass) ^ 2 <
        (777 / 1000) *
          ((2 : ℝ) *
                (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleFourKernel.transform u).re / Real.sqrt u) -
              (rationalPoleFourKernel.function (1 / 2)).re) ^
            2 := by
  have hA :
    (28379 / 100000 : ℝ) ≤
      (2 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleFourKernel.transform u).re / Real.sqrt u) -
        (rationalPoleFourKernel.function (1 / 2)).re := by
    linarith only [rationalPole_four_integral_lower, rationalPole_four_endpoint_upper]
  have hm : rationalPoleFourKernel.mass = 1 / 4 :=
    rationalPole_four_mass (by norm_num only) (by norm_num only)
  rw [hm]
  exact coeff_of_lower (by norm_num only) hA (by norm_num only) (by norm_num only)

/-- The actual cutoff, mass and half-value satisfy a positive strict coefficient certificate.
Use the rational lower integral and upper endpoint, then square a positive lower bound.
This certifies the kernel data consumed by the conductor-sensitive least-prime theorem. -/
theorem rationalPole_index_four_certificate :
    0 <
        (4 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
          (rationalPoleSixKernel.function (1 / 2)).re ∧
      (((4 : ℝ) - 1) * rationalPoleSixKernel.mass) ^ 2 <
        (623 / 1000) *
          ((4 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
              (rationalPoleSixKernel.function (1 / 2)).re) ^
            2 := by
  have hA :
    (71282 / 100000 : ℝ) ≤
      (4 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
        (rationalPoleSixKernel.function (1 / 2)).re := by
    linarith only [rationalPole_six_integral_lower, rationalPole_six_endpoint_upper]
  have hm : rationalPoleSixKernel.mass = 3 / 16 :=
    rationalPole_six_mass (by norm_num only) (by norm_num only)
  rw [hm]
  exact coeff_of_lower (by norm_num only) hA (by norm_num only) (by norm_num only)

/-- The actual cutoff, mass and half-value satisfy a positive strict coefficient certificate.
Use the rational lower integral and upper endpoint, then square a positive lower bound.
This certifies the kernel data consumed by the conductor-sensitive least-prime theorem. -/
theorem rationalPole_index_five_certificate :
    0 <
        (5 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
          (rationalPoleSixKernel.function (1 / 2)).re ∧
      (((5 : ℝ) - 1) * rationalPoleSixKernel.mass) ^ 2 <
        (23 / 40) *
          ((5 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
              (rationalPoleSixKernel.function (1 / 2)).re) ^
            2 := by
  have hA :
    (98939 / 100000 : ℝ) ≤
      (5 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
        (rationalPoleSixKernel.function (1 / 2)).re := by
    linarith only [rationalPole_six_integral_lower, rationalPole_six_endpoint_upper]
  have hm : rationalPoleSixKernel.mass = 3 / 16 :=
    rationalPole_six_mass (by norm_num only) (by norm_num only)
  rw [hm]
  exact coeff_of_lower (by norm_num only) hA (by norm_num only) (by norm_num only)

/-- The actual cutoff, mass and half-value satisfy a positive strict coefficient certificate.
Use the rational lower integral and upper endpoint, then square a positive lower bound.
This certifies the kernel data consumed by the conductor-sensitive least-prime theorem. -/
theorem rationalPole_index_six_certificate :
    0 <
        (6 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
          (rationalPoleSixKernel.function (1 / 2)).re ∧
      (((6 : ℝ) - 1) * rationalPoleSixKernel.mass) ^ 2 <
        (549 / 1000) *
          ((6 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
              (rationalPoleSixKernel.function (1 / 2)).re) ^
            2 := by
  have hA :
    (126596 / 100000 : ℝ) ≤
      (6 : ℝ) * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleSixKernel.transform u).re / Real.sqrt u) -
        (rationalPoleSixKernel.function (1 / 2)).re := by
    linarith only [rationalPole_six_integral_lower, rationalPole_six_endpoint_upper]
  have hm : rationalPoleSixKernel.mass = 3 / 16 :=
    rationalPole_six_mass (by norm_num only) (by norm_num only)
  rw [hm]
  exact coeff_of_lower (by norm_num only) hA (by norm_num only) (by norm_num only)

/-- The actual fourth-order cutoff retains coefficient 777/1000 even after
replacing its mass by the larger two-node Poisson majorant conductor coefficient.
The exact rational margin survives the certified cutoff and endpoint bounds.
This is a prerequisite for finite-scale work, not a finite entrance theorem. -/
theorem rationalPole_four_majorant_margin :
    ((poleFourUpperWeight - poleFourLowerWeight) / 2) ^ 2 <
      (777 / 1000 : ℝ) *
        (2 * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleFourKernel.transform u).re / Real.sqrt u) -
            (rationalPoleFourKernel.function (1 / 2)).re) ^
          2 := by
  have hA :
    (28379 / 100000 : ℝ) ≤
      2 * (∫ u : ℝ in (0 : ℝ)..1, (rationalPoleFourKernel.transform u).re / Real.sqrt u) -
        (rationalPoleFourKernel.function (1 / 2)).re := by
    linarith only [rationalPole_four_integral_lower, rationalPole_four_endpoint_upper]
  rw [poleFour_majorant_coefficient]
  exact (coeff_of_lower (by norm_num only) hA (by norm_num only) (by norm_num only)).2

end PseudoPrime.LLS.PaperStatements
