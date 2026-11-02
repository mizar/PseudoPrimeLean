/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleDoubleAbel
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialLogWeightedSummation

/-!
# Sharp principal gap from the actual fourth-pole double Abel identity

The logarithmic moment evaluations and actual arithmetic error integral improve the
principal gap error to 2*x^(1/4)+14. The unit-cutoff Chebyshev boundary is retained.
Only the principal contribution changes: character and ambient local costs are not
estimated in this module. Finite entrance certificates belong to their own downstream leaf.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive u and arbitrary real p, express u^p times the second density
as three shifted logarithmic moments. Normalize the exponential factor and coordinate.
This supplies the fixed-cutoff main-term evaluation without differentiating at zero. -/
private theorem fourPole_second_expansion {u : ℝ} (hu : 0 < u) (p : ℝ) :
    u ^ p * fourPoleSecondDensity u =
      (Real.exp (-(14 / 13 : ℝ)) / 6) *
        ((6 / 13 : ℝ) ^ 2 * (25 / 26 : ℝ) ^ 3 * (u ^ (p - 7 / 13) * (28 / 25 - Real.log u) ^ 3) -
            (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ)) * (25 / 26 : ℝ) ^ 2 *
              (u ^ (p - 7 / 13) * (28 / 25 - Real.log u) ^ 2) +
          (6 * (25 / 26 : ℝ) ^ 2) * (25 / 26 : ℝ) *
            (u ^ (p - 7 / 13) * (28 / 25 - Real.log u))) := by
  have hv : fourPoleCoord u = (25 / 26 : ℝ) * (28 / 25 - Real.log u) := by
    dsimp only [fourPoleCoord]
    ring
  calc
    _ =
        (u ^ p * Real.exp (-fourPoleCoord u) / (u * Real.sqrt u)) / 6 *
          ((6 / 13 : ℝ) ^ 2 * fourPoleCoord u ^ 3 -
              6 * (25 / 26 : ℝ) * (6 / 13 : ℝ) * fourPoleCoord u ^ 2 +
            6 * (25 / 26 : ℝ) ^ 2 * fourPoleCoord u) :=
      by
      dsimp only [fourPoleSecondDensity]
      ring
    _ = _ := by
      rw [fourPole_second_power_factor hu p, hv]; ring

/-- The linear second-density moment through the unit cutoff has the displayed
exact rational coefficient times exp(-14/13). Evaluate three shifted log moments
at parameter 19/13. This recovers the main term while keeping both unit boundaries. -/
theorem fourPole_second_main_unit :
    (∫ u : ℝ in (0 : ℝ)..1, u * fourPoleSecondDensity u) =
      (7371049433 / 29776784648 : ℝ) * Real.exp (-(14 / 13 : ℝ)) := by
  have h1 := Analysis.shifted_log_moment 1 (28 / 25) (s := 19 / 13) (by norm_num only)
  have h2 := Analysis.shifted_log_moment 2 (28 / 25) (s := 19 / 13) (by norm_num only)
  have h3 := Analysis.shifted_log_moment 3 (28 / 25) (s := 19 / 13) (by norm_num only)
  norm_num only at h1 h2 h3
  simp only [pow_one] at h1
  have he :
    (fun u : ℝ ↦ u * fourPoleSecondDensity u) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 1)]
      (fun u : ℝ ↦
        (Real.exp (-(14 / 13 : ℝ)) / 6) *
          ((6 / 13 : ℝ) ^ 2 * (25 / 26 : ℝ) ^ 3 * (u ^ (6 / 13 : ℝ) * (28 / 25 - Real.log u) ^ 3) -
              (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ)) * (25 / 26 : ℝ) ^ 2 *
                (u ^ (6 / 13 : ℝ) * (28 / 25 - Real.log u) ^ 2) +
            (6 * (25 / 26 : ℝ) ^ 2) * (25 / 26 : ℝ) *
              (u ^ (6 / 13 : ℝ) * (28 / 25 - Real.log u)))) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have h := fourPole_second_expansion hu.1 1
    norm_num only [Real.rpow_one] at h ⊢
    exact h
  rw [intervalIntegral.integral_of_le zero_le_one, MeasureTheory.integral_congr_ae he,
    MeasureTheory.integral_const_mul]
  have hi3 := h3.1.const_mul ((6 / 13 : ℝ) ^ 2 * (25 / 26 : ℝ) ^ 3)
  have hi2 := h2.1.const_mul (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ) * (25 / 26 : ℝ) ^ 2)
  have hi1 := h1.1.const_mul (6 * (25 / 26 : ℝ) ^ 2 * (25 / 26 : ℝ))
  have hsum := MeasureTheory.integral_add (hi3.sub hi2) hi1
  have hsum2 := MeasureTheory.integral_sub hi3 hi2
  simp only [Pi.sub_apply] at hsum
  rw [hsum, hsum2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h3.2, h2.2, h1.2]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose_zero_right,
    Nat.choose_self, Nat.choose_one_right, Nat.choose, Nat.factorial, Nat.reduceAdd, Nat.reduceSub,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  ring

/-- The full linear second-density moment equals the exact full K4 principal mass.
Evaluate the three density moments at p=1 and combine the exponential factors.
This identifies the main term in the actual full-series double Abel formula. -/
theorem fourPole_second_main_full :
    (∫ u : ℝ in (0 : ℝ)..Real.exp (28 / 25 : ℝ), u * fourPoleSecondDensity u) =
      2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4 := by
  have h1 := fourPole_density_moment 1 1 (by norm_num only)
  have h2 := fourPole_density_moment 2 1 (by norm_num only)
  have h3 := fourPole_density_moment 3 1 (by norm_num only)
  simp only [Real.rpow_one, pow_one] at h1 h2 h3
  have he :
    (fun u : ℝ ↦ u * fourPoleSecondDensity u) =
      (fun u : ℝ ↦
        (6 / 13 : ℝ) ^ 2 *
              (u * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) * fourPoleCoord u ^ 3) -
            (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ)) *
              (u * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) * fourPoleCoord u ^ 2) +
          (6 * (25 / 26 : ℝ) ^ 2) *
            (u * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) * fourPoleCoord u)) := by
    funext u
    dsimp only [fourPoleSecondDensity]
    ring
  rw [he, intervalIntegral.integral_of_le (Real.exp_pos _).le]
  have hi3 := h3.1.const_mul ((6 / 13 : ℝ) ^ 2)
  have hi2 := h2.1.const_mul (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ))
  have hi1 := h1.1.const_mul (6 * (25 / 26 : ℝ) ^ 2)
  have hsum := MeasureTheory.integral_add (hi3.sub hi2) hi1
  have hsum2 := MeasureTheory.integral_sub hi3 hi2
  simp only [Pi.sub_apply] at hsum
  rw [hsum, hsum2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h3.2, h2.2, h1.2]
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.cast_ofNat]
  have hexp : Real.exp (-(14 / 13 : ℝ)) * Real.exp (532 / 325 : ℝ) = Real.exp (14 / 25 : ℝ) := by
    rw [← Real.exp_add]
    norm_num only
  nlinarith only [hexp]

/-- A function continuous on a nonnegative supported interval can multiply the
actual second density integrably. Restrict the integrable density and use compactness.
This justifies the main-term and arithmetic-error integral decompositions. -/
private theorem fourPole_density_mul_integrable {f : ℝ → ℝ} {y : ℝ} (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (28 / 25 : ℝ)) (hf : ContinuousOn f (Set.Icc 0 y)) :
    IntervalIntegrable (fun u : ℝ ↦ f u * fourPoleSecondDensity u) MeasureTheory.volume 0 y := by
  have hQ := fourPole_second_integrable.mono_set (Set.Ioc_subset_Ioc le_rfl hyb)
  have hprod :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset hQ hf measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) y ⊆ _)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mpr
  simpa only [mul_comm] using hprod

/-- Under RH and positive scale, the actual logarithmic Mangoldt error integral
through any supported nonnegative cutoff is at most (1369/325)*sqrt(x) in absolute value.
Use the global 2*sqrt(t) arithmetic bound and the actual second variation certificate.
This supplies both the unit-cutoff and full-support principal error estimates. -/
theorem fourPole_error_integral_le (hRH : RiemannHypothesis) {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (28 / 25 : ℝ)) :
    |∫ u : ℝ in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            fourPoleSecondDensity u| ≤
      (1369 / 325 : ℝ) * Real.sqrt x := by
  let E : ℝ → ℝ := fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u
  have hEc : ContinuousOn E (Set.Icc 0 y) :=
    (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y).sub
      (continuous_const.mul continuous_id).continuousOn
  have hiE := fourPole_density_mul_integrable hy hyb hEc
  have hiF := (intervalIntegrable_iff_integrableOn_Ioc_of_le hy).mp hiE
  have hiAbs :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ |E u * fourPoleSecondDensity u|) (Set.Ioc 0 y) := by
    change
      MeasureTheory.Integrable (fun u : ℝ ↦ |E u * fourPoleSecondDensity u|)
        (MeasureTheory.volume.restrict (Set.Ioc 0 y))
    simpa only [Real.norm_eq_abs] using hiF.norm
  have hsub : Set.Ioc (0 : ℝ) y ⊆ Set.Ioc 0 (Real.exp (28 / 25 : ℝ)) :=
    Set.Ioc_subset_Ioc le_rfl hyb
  have hiV := fourPole_second_variation.1.mono_set hsub
  have hiG := hiV.const_mul (2 * Real.sqrt x)
  have hn :=
    MeasureTheory.norm_integral_le_integral_norm (f := fun u : ℝ ↦ E u * fourPoleSecondDensity u)
      (μ := MeasureTheory.volume.restrict (Set.Ioc 0 y))
  simp only [Real.norm_eq_abs] at hn
  have hm :
    (∫ u : ℝ in Set.Ioc 0 y, |E u * fourPoleSecondDensity u|) ≤
      ∫ u : ℝ in Set.Ioc 0 y, (2 * Real.sqrt x) * (Real.sqrt u * |fourPoleSecondDensity u|) := by
    apply MeasureTheory.integral_mono_ae hiAbs hiG
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have he := mangoldt_log_error_le_two_sqrt hRH (mul_nonneg hx.le hu.1.le)
    rw [Real.sqrt_mul hx.le] at he
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right he (abs_nonneg _)).trans_eq (by ring)
  have hV :=
    MeasureTheory.setIntegral_mono_set fourPole_second_variation.1
      (Filter.Eventually.of_forall
        (fun u : ℝ ↦ mul_nonneg (Real.sqrt_nonneg u) (abs_nonneg (fourPoleSecondDensity u))))
      (Filter.Eventually.of_forall (fun u hu ↦ hsub hu))
  have hVbound := hV.trans fourPole_second_variation.2
  have hscaled :=
    mul_le_mul_of_nonneg_left hVbound
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg x))
  rw [MeasureTheory.integral_const_mul] at hm
  rw [intervalIntegral.integral_of_le hy]
  exact hn.trans (hm.trans (hscaled.trans_eq (by ring)))

/-- Split the actual logarithmic Mangoldt integral into its linear main term
and genuine arithmetic error. Continuity times the integrable density justifies
subtraction and the scale factor. This preserves the exact normalization in both sums. -/
private theorem fourPole_log_integral_split {x y : ℝ} (hx : 0 < x) (hy : 0 ≤ y)
    (hyb : y ≤ Real.exp (28 / 25 : ℝ)) :
    (∫ u : ℝ in (0 : ℝ)..y,
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) * fourPoleSecondDensity u) =
      x * (∫ u : ℝ in (0 : ℝ)..y, u * fourPoleSecondDensity u) +
        ∫ u : ℝ in (0 : ℝ)..y,
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            fourPoleSecondDensity u := by
  have hiM :=
    fourPole_density_mul_integrable hy hyb
      (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y)
  have hiL :=
    fourPole_density_mul_integrable (f := fun u : ℝ ↦ x * u) hy hyb
      (continuous_const.mul continuous_id).continuousOn
  have h := intervalIntegral.integral_sub hiM hiL
  have he :
    (fun u : ℝ ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) * fourPoleSecondDensity u -
          (x * u) * fourPoleSecondDensity u) =
      (fun u : ℝ ↦
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
          fourPoleSecondDensity u) := by
    funext u
    ring
  rw [he] at h
  simp only [mul_assoc, intervalIntegral.integral_const_mul] at h
  linarith only [h]

/-- The two unit boundaries and the linear second-density moment give the exact
existing unit principal mass. Evaluate the boundaries and moment by rational algebra.
This identifies the unchanged main term before bounding the three arithmetic errors. -/
private theorem fourPole_cutoff_main_identity :
    fourPoleWeight 1 - fourPoleWeightDeriv 1 +
        (∫ u : ℝ in (0 : ℝ)..1, u * fourPoleSecondDensity u) =
      ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) := by
  rw [fourPole_second_main_unit]
  norm_num only [fourPoleWeight, fourPoleWeightDeriv, fourPoleCoord, Real.log_one, Real.sqrt_one,
    mul_zero, sub_zero, mul_one]
  ring

/-- At positive scale, the actual cutoff principal error equals its normalized
integral error and the two genuine boundary errors. Insert the exact double Abel identity,
split its integral and use the exact main-mass relation.
This retains the small Chebyshev coefficient rather than discarding the hard cutoff. -/
private theorem fourPole_cutoff_error_identity {x : ℝ} (hx : 0 < x) :
    (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        Real.sqrt x * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) =
      (∫ u : ℝ in (0 : ℝ)..1,
              (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
                fourPoleSecondDensity u) /
            Real.sqrt x -
          fourPoleWeightDeriv 1 * (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x) /
            Real.sqrt x +
        fourPoleWeight 1 * (Chebyshev.psi x - x) / Real.sqrt x := by
  have hb : (1 : ℝ) ≤ Real.exp (28 / 25 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  rw [fourPole_cutoff_double_abel hx, fourPole_log_integral_split hx zero_le_one hb, ←
    fourPole_cutoff_main_identity]
  have hs := (Real.sqrt_pos.mpr hx).ne'
  field_simp (disch :=
    first
    | exact hs
    | norm_num only)
  rw [Real.sq_sqrt hx.le]
  ring

/-- At positive scale, the full actual principal error is exactly the normalized
logarithmic Mangoldt error integral. Insert the supported double Abel identity and its
linear moment. This removes no character or local term from later witness comparisons. -/
private theorem fourPole_full_error_identity {x : ℝ} (hx : 0 < x) :
    (∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re -
        Real.sqrt x * (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4) =
      (∫ u : ℝ in (0 : ℝ)..Real.exp (28 / 25 : ℝ),
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
            fourPoleSecondDensity u) /
        Real.sqrt x := by
  rw [fourPole_full_double_abel hx, fourPole_log_integral_split hx (Real.exp_pos _).le le_rfl,
    fourPole_second_main_full]
  have hs := (Real.sqrt_pos.mpr hx).ne'
  field_simp (disch :=
    first
    | exact hs
    | norm_num only)
  rw [Real.sq_sqrt hx.le]
  ring

/-- Under RH at scales at least two, the actual cutoff principal error is at most
x^(1/4)+1499/325. Bound the retained Chebyshev boundary using w(1)<1/13, the logarithmic
boundary using |w'(1)|<1/5, and the actual error integral using the variation certificate.
This is the improved prefix contribution in twice-prefix minus full-series comparison. -/
theorem fourPole_cutoff_error_sharp (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |(∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
          Real.sqrt x * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13)))| ≤
      x ^ (1 / 4 : ℝ) + (1499 / 325 : ℝ) := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  have hb : (1 : ℝ) ≤ Real.exp (28 / 25 : ℝ) := Real.one_le_exp_iff.mpr (by norm_num only)
  let E :=
    ∫ u : ℝ in (0 : ℝ)..1,
      (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) *
        fourPoleSecondDensity u
  let D := AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum x - x
  let J := Chebyshev.psi x - x
  have hE : |E / Real.sqrt x| ≤ (1369 / 325 : ℝ) := by
    rw [abs_div, abs_of_pos hs]
    exact (div_le_iff₀ hs).mpr (fourPole_error_integral_le hRH hx0 zero_le_one hb)
  have hM : |fourPoleWeightDeriv 1 * D / Real.sqrt x| ≤ (2 / 5 : ℝ) := by
    rw [abs_div, abs_mul, abs_of_pos hs]
    apply (div_le_iff₀ hs).mpr
    have hm := mangoldt_log_error_le_two_sqrt hRH hx0.le
    change |D| ≤ 2 * Real.sqrt x at hm
    have hmult := mul_le_mul_of_nonneg_left hm (abs_nonneg (fourPoleWeightDeriv 1))
    have hw :=
      mul_le_mul_of_nonneg_right fourPoleWeightDeriv_one_lt.le
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Real.sqrt_nonneg x))
    linarith only [hmult, hw]
  have hW := fourPoleWeight_endpoint.1
  have hJ : |fourPoleWeight 1 * J / Real.sqrt x| ≤ x ^ (1 / 4 : ℝ) := by
    rw [abs_div, abs_mul, abs_of_pos hs, abs_of_nonneg hW]
    apply (div_le_iff₀ hs).mpr
    have hj := psi_error_le_thirteen hRH hx0.le
    change |J| ≤ 13 * x ^ (3 / 4 : ℝ) at hj
    have hmult := mul_le_mul_of_nonneg_left hj hW
    have hcoeff : 13 * fourPoleWeight 1 ≤ (1 : ℝ) := by linarith only [fourPoleWeight_one_lt]
    have hw := mul_le_mul_of_nonneg_right hcoeff (Real.rpow_nonneg hx0.le (3 / 4 : ℝ))
    have hr : x ^ (1 / 4 : ℝ) * Real.sqrt x = x ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
      norm_num only
    rw [hr]
    linarith only [hmult, hw]
  rw [fourPole_cutoff_error_identity hx0]
  change
    |E / Real.sqrt x - fourPoleWeightDeriv 1 * D / Real.sqrt x +
          fourPoleWeight 1 * J / Real.sqrt x| ≤
      x ^ (1 / 4 : ℝ) + (1499 / 325 : ℝ)
  have htriangle :=
    abs_add_le (E / Real.sqrt x - fourPoleWeightDeriv 1 * D / Real.sqrt x)
      (fourPoleWeight 1 * J / Real.sqrt x)
  have hsub := abs_sub (E / Real.sqrt x) (fourPoleWeightDeriv 1 * D / Real.sqrt x)
  linarith only [htriangle, hsub, hE, hM, hJ]

/-- Under RH at scales at least two, the full actual principal error is at most
1369/325. Divide the actual supported arithmetic error integral by the positive square root.
This is the improved full-series contribution with its exact existing main term. -/
theorem fourPole_full_error_sharp (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    |(∑' n : ℕ, (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re -
          Real.sqrt x * (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4)| ≤
      (1369 / 325 : ℝ) := by
  have hx0 : 0 < x := (by norm_num only : (0 : ℝ) < 2).trans_le hx
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx0
  rw [fourPole_full_error_identity hx0, abs_div, abs_of_pos hs]
  exact (div_le_iff₀ hs).mpr (fourPole_error_integral_le hRH hx0 (Real.exp_pos _).le le_rfl)

/-- Under RH at scales at least two, twice the actual cutoff principal sum minus
the full actual principal series exceeds the unchanged main gap minus (2*x^(1/4)+14).
Combine the proved prefix and full errors; their constant is 4367/325, strictly below 14.
This supplies the principal improvement for witness criteria with unchanged other costs. -/
theorem fourPole_principal_gap_sharp (hRH : RiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    Real.sqrt x *
          (2 * ((484820459 / 528581976 : ℝ) * Real.exp (-(14 / 13))) -
            (2 * (13 / 25 : ℝ) * Real.exp (14 / 25) / (1 + 13 / 25) ^ 4)) -
        (2 * x ^ (1 / 4 : ℝ) + 14) ≤
      2 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, ArithmeticFunction.vonMangoldt n * fourScaledWeight x n) -
        (∑' n : ℕ,
            (MellinKernel.summand rationalPoleFourKernel) (1 : DirichletCharacter ℂ 1) x n).re := by
  have hc := (abs_le.mp (fourPole_cutoff_error_sharp hRH hx)).1
  have hf := (abs_le.mp (fourPole_full_error_sharp hRH hx)).2
  nlinarith only [hc, hf]

end PseudoPrime.LLS.PaperStatements
