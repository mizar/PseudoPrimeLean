/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflected570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMoments570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedTail
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion

/-! # Complementary moment bounds for the section 31 reflected Euler sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The main moment derivative agrees with the logarithmic Mangoldt weight derivative. -/
private theorem moment_deriv {t : ℝ} (ht : 0 < t) (j : ℕ) :
    deriv (eulerMoment570 (13 / 25) j) t =
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv (38 / 25) j t := by
  have he :
    eulerMoment570 (13 / 25) j =
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (38 / 25) j := by
    funext x
    unfold eulerMoment570 AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight
    rw [show -(13 / 25 : ℝ) - 1 = -(38 / 25 : ℝ) by norm_num only, mul_comm]
  rw [he]
  exact (AnalyticNumberTheory.Arithmetic.mangoldt_moment_weight_deriv _ _ ht).deriv

/-- From 2701 onwards the moment is decreasing through degree five. Dropping the
nonnegative logarithmic derivative term bounds its absolute slope. -/
private theorem moment_slope {t : ℝ} (ht : 2701 ≤ t) (j : ℕ) (hj : j ≤ 5) :
    |deriv (eulerMoment570 (13 / 25) j) t| ≤
      (38 / 25 : ℝ) * Real.log t ^ j * t ^ (-(63 / 25 : ℝ)) := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hp := zero_lt_one.trans_le ht1
  have hl := quarter_log2701_lower.trans (Real.log_le_log (by norm_num only) ht)
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast hj
  rw [moment_deriv hp,
    abs_of_nonpos
      (AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_nonpos j (by norm_num only) ht1
        (by linarith only [hl, hj']))]
  unfold AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv
  rw [show -(38 / 25 : ℝ) - 1 = -(63 / 25 : ℝ) by norm_num only]
  have hlog := Real.log_nonneg ht1
  have h : 0 ≤ t ^ (-(38 / 25 : ℝ)) * ((j : ℝ) * Real.log t ^ (j - 1) * t⁻¹) := by positivity
  linarith only [h]

/-- Multiplying the power weight by a square root shifts its decay exponent by one half. -/
private theorem sqrt_times_power {t : ℝ} (ht : 0 < t) (d : ℝ) :
    Real.sqrt t * t ^ (-(d + 1 / 2)) = t ^ (-d) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
  congr 1
  ring

/-- On the finite certificate range, the centered Abel error density is bounded by
a logarithmic moment of the same degree. -/
theorem reflected_error_low_570 {t : ℝ} (ht : 2701 ≤ t) (hu : t ≤ 1000000) (j : ℕ) (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (13 / 25) j) t| ≤
      (4 / 5 * (38 / 25) : ℝ) * eulerMoment570 (51 / 50) j t := by
  rw [abs_mul]
  have he := AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (by linarith only [ht]) hu
  have hh := mul_le_mul he (moment_slope ht j hj) (abs_nonneg _) (by positivity)
  have hr := sqrt_times_power (show 0 < t by linarith only [ht]) (101 / 50)
  norm_num only at hr
  apply hh.trans_eq
  unfold eulerMoment570
  norm_num only
  linear_combination (4 / 5 * (38 / 25) * Real.log t ^ j) * hr

/-- Above one million the RH log-square error contributes a moment two degrees higher. -/
theorem reflected_error_high_570 (hRH : RiemannHypothesis) {t : ℝ} (ht : 1000000 ≤ t) (j : ℕ)
    (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (13 / 25) j) t| ≤
      (38 / 25 / 24 : ℝ) * eulerMoment570 (51 / 50) (j + 2) t := by
  rw [abs_mul]
  have he := euler570_psi_high hRH ht
  have hh :=
    mul_le_mul he (moment_slope (by linarith only [ht]) j hj) (abs_nonneg _) (by positivity)
  have hr := sqrt_times_power (show 0 < t by linarith only [ht]) (101 / 50)
  norm_num only at hr
  apply hh.trans_eq
  unfold eulerMoment570
  rw [pow_add]
  norm_num only
  linear_combination ((38 / 25 / 24) * Real.log t ^ j * Real.log t ^ 2) * hr

/-- An integrable envelope for the centered error on the entire tail. The high-range
term is supported only above one million. -/
private noncomputable def errorMajor (j : ℕ) (t : ℝ) : ℝ :=
  (4 / 5 * (38 / 25) : ℝ) * eulerMoment570 (51 / 50) j t +
    (Set.Ioi (1000000 : ℝ)).indicator
      (fun u ↦ (38 / 25 / 24 : ℝ) * eulerMoment570 (51 / 50) (j + 2) u) t

/-- Both power moments in the split envelope are integrable on their respective supports. -/
private theorem major_integrable (j : ℕ) :
    MeasureTheory.IntegrableOn (errorMajor j) (Set.Ioi 2701) := by
  apply MeasureTheory.Integrable.add
  · exact
      (Analysis.log_power_tail_integrable (r := 51 / 50) (by norm_num only)
            (by norm_num only : (1 : ℝ) ≤ 2701) j).const_mul
        _
  · apply (MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
    exact
      MeasureTheory.IntegrableOn.mono_set
        ((Analysis.log_power_tail_integrable (r := 51 / 50) (by norm_num only)
              (by norm_num only : (1 : ℝ) ≤ 1000000) (j + 2)).const_mul
          _)
        Set.inter_subset_left

/-- Evaluating the two improper moments gives the explicit envelope integral. -/
private theorem major_integral (j : ℕ) :
    (∫ t in Set.Ioi 2701, errorMajor j t) =
      (4 / 5 * (38 / 25) : ℝ) * eulerMomentValue570 (51 / 50) j 2701 +
        (38 / 25 / 24 : ℝ) * eulerMomentValue570 (51 / 50) (j + 2) 1000000 := by
  have hl :=
    (Analysis.log_power_tail_integrable (r := 51 / 50) (by norm_num only)
          (by norm_num only : (1 : ℝ) ≤ 2701) j).const_mul
      (4 / 5 * (38 / 25) : ℝ)
  have hh :=
    (Analysis.log_power_tail_integrable (r := 51 / 50) (by norm_num only)
          (by norm_num only : (1 : ℝ) ≤ 1000000) (j + 2)).const_mul
      (38 / 25 / 24 : ℝ)
  unfold errorMajor eulerMoment570 eulerMomentValue570
  rw [MeasureTheory.integral_add hl
      ((MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
        (MeasureTheory.IntegrableOn.mono_set hh Set.inter_subset_left)),
    MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi,
    max_eq_right (by norm_num only : (2701 : ℝ) ≤ 1000000), MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul,
    Analysis.log_power_tail_integral (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 2701),
    Analysis.log_power_tail_integral (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 1000000)]

/-- The finite psi bound and RH bound majorize the centered error on the two ranges. -/
private theorem point_major (hRH : RiemannHypothesis) {t : ℝ} (ht : 2701 < t) (j : ℕ) (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (13 / 25) j) t| ≤ errorMajor j t := by
  by_cases hv : 1000000 < t
  · rw [errorMajor, Set.indicator_of_mem (show t ∈ Set.Ioi (1000000 : ℝ) from hv)]
    have hl := Real.log_nonneg (show 1 ≤ t by linarith only [ht])
    have hp : 0 ≤ t := by linarith only [ht]
    apply (reflected_error_high_570 hRH hv.le j hj).trans
    apply le_add_of_nonneg_left
    unfold eulerMoment570
    positivity
  · rw [errorMajor, Set.indicator_of_notMem (show t ∉ Set.Ioi (1000000 : ℝ) from hv), add_zero]
    exact reflected_error_low_570 ht.le (le_of_not_gt hv) j hj

/-- The RH log-square bound makes the upper Abel boundary vanish for every fixed degree. -/
private theorem boundary_zero (hRH : RiemannHypothesis) (j : ℕ) :
    Filter.Tendsto (fun t ↦ (Chebyshev.psi t - t) * eulerMoment570 (13 / 25) j t) Filter.atTop
      (nhds 0) := by
  have h :=
    (Analysis.log_pow_mul_neg_rpow_tendsto (by norm_num only : 0 < (51 / 50 : ℝ)) (j + 2)).div_const
      24
  rw [zero_div] at h
  apply squeeze_zero_norm' _ h
  · filter_upwards [Filter.eventually_ge_atTop (1000000 : ℝ)] with t ht
    have hp : 0 < t := by linarith only [ht]
    have hl := Real.log_nonneg (show 1 ≤ t by linarith only [ht])
    have hw : 0 ≤ eulerMoment570 (13 / 25) j t := by
      unfold eulerMoment570; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_right (euler570_psi_high hRH ht) hw).trans_eq
    unfold eulerMoment570
    rw [show -(13 / 25 : ℝ) - 1 = -(51 / 50 + 1 / 2 : ℝ) by norm_num only, pow_add]
    linear_combination (Real.log t ^ j * Real.log t ^ 2 / 24) * sqrt_times_power hp (51 / 50)

/-- The explicit complementary moment bound in equation (31.5.3), including the main
integral, the correction at 2701 and the two error integrals. -/
noncomputable def reflectedCap570 (j : ℕ) : ℝ :=
  eulerMomentValue570 (13 / 25) j 2701 + 4 / 5 * Real.sqrt 2701 * eulerMoment570 (13 / 25) j 2701 +
    (4 / 5 * (38 / 25)) * eulerMomentValue570 (51 / 50) j 2701 +
    (38 / 25 / 24) * eulerMomentValue570 (51 / 50) (j + 2) 1000000

/-- For degrees zero through five, centered Abel summation under RH bounds the reflected
moment tail by its explicit endpoint expression. -/
theorem reflected_tail_cap_570 (hRH : RiemannHypothesis) (j : ℕ) (hj : j ≤ 5) :
    (∑' n, reflectedMoment570 j n) - (∑ n ∈ Finset.Ioc 0 2701, reflectedMoment570 j n) ≤
      reflectedCap570 j := by
  let f := eulerMoment570 (13 / 25) j
  let E := fun t ↦ (Chebyshev.psi t - t) * deriv f t
  have hp : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioi 2701), ‖E t‖ ≤ errorMajor j t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (Real.norm_eq_abs _).trans_le (point_major hRH ht j hj)
  have hi : MeasureTheory.IntegrableOn E (Set.Ioi 2701) :=
    (major_integrable j).mono'
      (((Chebyshev.psi_mono.measurable.sub measurable_id).mul
          (measurable_deriv f)).aestronglyMeasurable)
      hp
  have he := MeasureTheory.norm_integral_le_of_norm_le (major_integrable j) hp
  rw [Real.norm_eq_abs, major_integral] at he
  have hn (n : ℕ) : ArithmeticFunction.vonMangoldt n * f n = reflectedMoment570 j n := by
    unfold f eulerMoment570 reflectedMoment570
    rw [show -(13 / 25 : ℝ) - 1 = -(38 / 25 : ℝ) by norm_num only, mul_assoc]
  have hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n) := by
    apply
      (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
          (by norm_num only) j).congr
    intro n
    rw [hn, reflectedMoment570, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hd (t : ℝ) (ht : 2701 ≤ t) : DifferentiableAt ℝ f t := by
    have hpos : 0 < t := by linarith only [ht]
    exact
      (((Real.differentiableAt_log hpos.ne').pow j).mul
        (Real.differentiableAt_rpow_const_of_ne _ hpos.ne'))
  have hdi (b : ℝ) : MeasureTheory.IntegrableOn (deriv f) (Set.Icc 2701 b) := by
    apply ContinuousOn.integrableOn_Icc
    apply
      (AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_continuous (38 / 25) j
          (by norm_num only : (0 : ℝ) < 2701)).congr
    exact fun t ht ↦ moment_deriv (by linarith only [ht.1]) j
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral
      (by norm_num only : (0 : ℝ) ≤ 2701) (fun b _ t ht ↦ hd t ht.1) (fun b _ ↦ hdi b)
      (Analysis.log_power_tail_integrable (by norm_num only) (by norm_num only) j) hi
      (boundary_zero hRH j) hs
  simp only [hn, Nat.floor_ofNat] at h
  have hmain : (∫ t in Set.Ioi 2701, f t) = eulerMomentValue570 (13 / 25) j 2701 :=
    Analysis.log_power_tail_integral (by norm_num only) (by norm_num only) j
  have hf : 0 ≤ f 2701 := by
    unfold f eulerMoment570; positivity
  have hb :=
    mul_le_mul_of_nonneg_right
      (abs_le.mp
          (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million
            (by norm_num only : (1423 : ℝ) ≤ 2701) (by norm_num only))).1
      hf
  unfold reflectedCap570
  change _ = (∫ t in Set.Ioi 2701, f t) - _ - ∫ t in Set.Ioi 2701, E t at h
  rw [h, hmain]
  change _ ≤ _ + 4 / 5 * Real.sqrt 2701 * f 2701 + _ + _
  linarith only [hb, (abs_le.mp he).1]

/-- Under RH the six proved moment caps give the signed reflected polynomial bound
for a character sum equal to three on the prefix Mangoldt support. -/
theorem reflected_polynomial_570 (hRH : RiemannHypothesis) {z : ℝ} (hz : 0 ≤ z) (τ : ℕ → ℝ)
    (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 2701, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    -(∑' n : ℕ, τ n * reflectedWeight570 z n) ≤
      ∑ j ∈ Finset.range 6,
        (Nat.choose 5 j : ℝ) * z ^ (5 - j) * (reflectedCap570 j - 3 * reflectedFloor570 j) := by
  exact
    reflected_moment_caps_570 hz τ ht hp _
      (fun j hj ↦ reflected_tail_cap_570 hRH j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))

end PseudoPrime.PrimeTestBounds.MillerRabin
