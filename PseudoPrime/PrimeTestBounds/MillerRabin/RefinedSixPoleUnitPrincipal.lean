/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleFullPrincipal
public import PseudoPrime.LLS.PaperStatements.RationalPolePrincipalSharp

/-! # Unit-cutoff principal main term for the refined sixth-pole kernel -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive `u`, expand a real-power multiple of the second density into three
shifted logarithmic moments. Normalize the exponential and the logarithmic coordinate. -/
theorem refined_second_expansion {u : ℝ} (hu : 0 < u) (p : ℝ) :
    u ^ p * refinedSecondDensity u =
      (Real.exp (-(567 / 200 : ℝ)) / 120) *
        ((29 / 50 : ℝ) ^ 2 * (27 / 25 : ℝ) ^ 5 * (u ^ (p - 21 / 50) * (21 / 8 - Real.log u) ^ 5) -
            (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) ^ 5) *
              (u ^ (p - 21 / 50) * (21 / 8 - Real.log u) ^ 4) +
          (20 * (27 / 25 : ℝ) ^ 5) * (u ^ (p - 21 / 50) * (21 / 8 - Real.log u) ^ 3)) := by
  have hv : refinedCoord u = (27 / 25 : ℝ) * (21 / 8 - Real.log u) := by
    dsimp only [refinedCoord]
    ring
  calc
    _ =
        (u ^ p * Real.exp (-refinedCoord u) / (u * Real.sqrt u)) / 120 *
          ((29 / 50 : ℝ) ^ 2 * refinedCoord u ^ 5 -
              10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) * refinedCoord u ^ 4 +
            20 * (27 / 25 : ℝ) ^ 2 * refinedCoord u ^ 3) :=
      by
      dsimp only [refinedSecondDensity]
      ring
    _ = _ := by
      rw [refined_second_power_factor hu p, hv]
      ring

/-- Evaluate the unit-cutoff linear second-density moment exactly. Apply the shifted
logarithmic moment formulas to its three polynomial terms. -/
theorem refined_second_main_unit :
    (∫ u : ℝ in (0 : ℝ)..1, u * refinedSecondDensity u) =
      (156190800626193058607811771 / 155575971533440000000000000 : ℝ) *
        Real.exp (-(567 / 200 : ℝ)) := by
  have h3 := Analysis.shifted_log_moment 3 (21 / 8) (s := 79 / 50) (by norm_num only)
  have h4 := Analysis.shifted_log_moment 4 (21 / 8) (s := 79 / 50) (by norm_num only)
  have h5 := Analysis.shifted_log_moment 5 (21 / 8) (s := 79 / 50) (by norm_num only)
  norm_num only at h3 h4 h5
  have he :
    (fun u : ℝ ↦ u * refinedSecondDensity u) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 1)]
      (fun u : ℝ ↦
        (Real.exp (-(567 / 200 : ℝ)) / 120) *
          ((29 / 50 : ℝ) ^ 2 * (27 / 25 : ℝ) ^ 5 * (u ^ (29 / 50 : ℝ) * (21 / 8 - Real.log u) ^ 5) -
              (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) ^ 5) *
                (u ^ (29 / 50 : ℝ) * (21 / 8 - Real.log u) ^ 4) +
            (20 * (27 / 25 : ℝ) ^ 5) * (u ^ (29 / 50 : ℝ) * (21 / 8 - Real.log u) ^ 3))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have h := refined_second_expansion hu.1 1
    norm_num only [Real.rpow_one] at h ⊢
    exact h
  rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_congr_ae he,
    MeasureTheory.integral_const_mul]
  have hi5 := h5.1.const_mul ((29 / 50 : ℝ) ^ 2 * (27 / 25 : ℝ) ^ 5)
  have hi4 := h4.1.const_mul (10 * (29 / 50 : ℝ) * (27 / 25 : ℝ) ^ 5)
  have hi3 := h3.1.const_mul (20 * (27 / 25 : ℝ) ^ 5)
  have hsum := MeasureTheory.integral_add (hi5.sub hi4) hi3
  have hsum2 := MeasureTheory.integral_sub hi5 hi4
  simp only [Pi.sub_apply] at hsum
  rw [hsum, hsum2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h5.2, h4.2, h3.2]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.choose_one_right, Nat.choose, Nat.factorial, Nat.reduceAdd, Nat.reduceSub,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  ring

/-- The unit-cutoff double Abel main coefficient equals the actual kernel cutoff mass.
Evaluate the density moment and both boundary terms and compare their rational constants. -/
theorem refined_unit_main_eq :
    refinedPrincipalMain 1 =
      ∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u := by
  rw [refinedPrincipalMain, refined_second_main_unit, refined_six_pole_cutoff]
  norm_num only [refinedWeight, refinedWeightDeriv, refinedCoord, Real.log_one, Real.sqrt_one,
    mul_zero, sub_zero, mul_one, one_pow]
  ring

/-- Under RH, the actual unit-cutoff principal sum differs from the kernel cutoff
mass by the explicit integral allowance and the two genuine endpoint errors. -/
theorem refined_unit_sharp_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
          Real.sqrt x *
            (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u)| ≤
      ((231 / 5000 : ℝ) * (6889 / 2700) +
          ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
              ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
            Real.sqrt x) +
        (|refinedWeightDeriv 1| * |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| +
            |refinedWeight 1| * |Chebyshev.psi x - x|) /
          Real.sqrt x := by
  have hb : (1 : ℝ) ≤ Real.exp (21 / 8 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  have h := refined_principal_sharp_error hRH hx zero_le_one hb
  rw [refined_unit_main_eq] at h
  simpa only [mul_one, one_mul] using h

/-- A finite exponential Taylor sum bounds the unit-cutoff exponential factor.
The reciprocal inequality gives the explicit rational upper bound. -/
theorem refined_exp_neg_unit_le : Real.exp (-(567 / 200 : ℝ)) ≤ (588 / 10000 : ℝ) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 567 / 200) 10
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    pow_zero, pow_one] at h
  have hb : (10000 / 588 : ℝ) ≤ Real.exp (567 / 200 : ℝ) := by linarith only [h]
  rw [Real.exp_neg, ← one_div]
  have hi := one_div_le_one_div_of_le (by norm_num only : (0 : ℝ) < 10000 / 588) hb
  norm_num only at hi ⊢
  exact hi

/-- The unit-cutoff principal weight has absolute value below `9/100`. Evaluate its
explicit formula and apply the rational exponential bound. -/
theorem refined_weight_unit_lt : |refinedWeight 1| < (9 / 100 : ℝ) := by
  have he := refined_exp_neg_unit_le
  norm_num only [refinedWeight, refinedCoord, Real.log_one, Real.sqrt_one, mul_zero, sub_zero,
    mul_one]
  rw [abs_div, abs_mul, abs_of_pos (Real.exp_pos _)]
  norm_num only
  nlinarith only [he]

/-- The absolute unit-cutoff derivative is below `119/1000`. Evaluate its explicit
formula and apply the rational exponential bound. -/
theorem refined_deriv_unit_lt : |refinedWeightDeriv 1| < (119 / 1000 : ℝ) := by
  have he := refined_exp_neg_unit_le
  norm_num only [refinedWeightDeriv, refinedCoord, Real.log_one, Real.sqrt_one, mul_zero, sub_zero,
    mul_one]
  rw [abs_mul, abs_div, abs_of_pos (Real.exp_pos _)]
  norm_num only
  nlinarith only [he]

/-- Under RH, the unit-cutoff principal error is bounded using explicit rational
endpoint coefficients. The remaining endpoint arithmetic errors are kept for the
one-sided Chebyshev estimates used at the target scale. -/
theorem refined_unit_rational_error (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
          Real.sqrt x *
            (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u)| ≤
      ((231 / 5000 : ℝ) * (6889 / 2700) +
          ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
              ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
            Real.sqrt x) +
        ((119 / 1000 : ℝ) * |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| +
            (9 / 100 : ℝ) * |Chebyshev.psi x - x|) /
          Real.sqrt x := by
  have h := refined_unit_sharp_error hRH hx
  have h1 :=
    mul_le_mul_of_nonneg_right refined_deriv_unit_lt.le
      (abs_nonneg (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x))
  have h2 := mul_le_mul_of_nonneg_right refined_weight_unit_lt.le (abs_nonneg (Chebyshev.psi x - x))
  have h3 := div_le_div_of_nonneg_right (add_le_add h1 h2) (Real.sqrt_nonneg x)
  linarith only [h, h3]

/-- Under RH, the actual cutoff-minus-full principal gap is bounded below by its
kernel main mass minus the explicit sharp integral and cutoff endpoint errors. Combine
the finite lower estimate and the full-series upper estimate at the same scale. -/
theorem refined_principal_gap_lower (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    Real.sqrt x *
          (4 * (∫ u : ℝ in (0 : ℝ)..1, (refinedSixPoleKernel.transform u).re / Real.sqrt u) -
            (refinedSixPoleKernel.function (1 / 2)).re) -
        5 *
          ((231 / 5000 : ℝ) * (6889 / 2700) +
            ((1839 / 1000 : ℝ) * (Real.log x + 21 / 8) + 2) *
                ((918330048 / 17682025 : ℝ) * Real.exp (-(21 / 16 : ℝ))) /
              Real.sqrt x) -
        4 *
            ((119 / 1000 : ℝ) * |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x| +
              (9 / 100 : ℝ) * |Chebyshev.psi x - x|) /
          Real.sqrt x ≤
      4 *
          (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊,
            (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re) -
        (∑' n : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have hf := (abs_le.mp (refined_unit_rational_error hRH hx)).1
  have ht := (abs_le.mp (refined_full_sharp_error hRH hx)).2
  ring_nf at hf ht ⊢
  linarith only [hf, ht]

end PseudoPrime.PrimeTestBounds.MillerRabin
