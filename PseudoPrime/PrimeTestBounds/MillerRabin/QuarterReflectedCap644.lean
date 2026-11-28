/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedPrefix644
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMoments570
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedTail
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterRecoveryNumeric644
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion

/-! # Complementary moment bounds for the section 122 reflected Euler sum -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The main moment derivative agrees with the logarithmic Mangoldt weight derivative. -/
private theorem moment_deriv {t : ℝ} (ht : 0 < t) (j : ℕ) :
    deriv (eulerMoment570 (57 / 100) j) t =
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv (157 / 100) j t := by
  have he :
    eulerMoment570 (57 / 100) j =
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (157 / 100) j := by
    funext x
    unfold eulerMoment570 AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight
    rw [show -(57 / 100 : ℝ) - 1 = -(157 / 100 : ℝ) by norm_num only, mul_comm]
  rw [he]
  exact (AnalyticNumberTheory.Arithmetic.mangoldt_moment_weight_deriv _ _ ht).deriv

/-- From 2701 onwards the moment is decreasing through degree five. Dropping the
nonnegative logarithmic derivative term bounds its absolute slope. -/
private theorem moment_slope {t : ℝ} (ht : 2701 ≤ t) (j : ℕ) (hj : j ≤ 5) :
    |deriv (eulerMoment570 (57 / 100) j) t| ≤
      (157 / 100 : ℝ) * Real.log t ^ j * t ^ (-(257 / 100 : ℝ)) := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hp := zero_lt_one.trans_le ht1
  have hl := quarter_log2701_lower.trans (Real.log_le_log (by norm_num only) ht)
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast hj
  rw [moment_deriv hp,
    abs_of_nonpos
      (AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_nonpos j (by norm_num only) ht1
        (by linarith only [hl, hj']))]
  unfold AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv
  rw [show -(157 / 100 : ℝ) - 1 = -(257 / 100 : ℝ) by norm_num only]
  have hlog := Real.log_nonneg ht1
  have h : 0 ≤ t ^ (-(157 / 100 : ℝ)) * ((j : ℝ) * Real.log t ^ (j - 1) * t⁻¹) := by positivity
  linarith only [h]

/-- Multiplying the power weight by a square root shifts its decay exponent by one half. -/
private theorem sqrt_times_power {t : ℝ} (ht : 0 < t) (d : ℝ) :
    Real.sqrt t * t ^ (-(d + 1 / 2)) = t ^ (-d) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
  congr 1
  ring

/-- On the finite certificate range, the centered Abel error density is bounded by
a logarithmic moment of the same degree. -/
theorem reflected_error_low_644 {t : ℝ} (ht : 2701 ≤ t) (hu : t ≤ 1000000) (j : ℕ) (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (57 / 100) j) t| ≤
      (4 / 5 * (157 / 100) : ℝ) * eulerMoment570 (107 / 100) j t := by
  rw [abs_mul]
  have he := AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (by linarith only [ht]) hu
  have hh := mul_le_mul he (moment_slope ht j hj) (abs_nonneg _) (by positivity)
  have hr := sqrt_times_power (show 0 < t by linarith only [ht]) (207 / 100)
  norm_num only at hr
  apply hh.trans_eq
  unfold eulerMoment570
  norm_num only
  linear_combination (4 / 5 * (157 / 100) * Real.log t ^ j) * hr

/-- Above one million the RH log-square error contributes a moment two degrees higher. -/
theorem reflected_error_high_644 (hRH : RiemannHypothesis) {t : ℝ} (ht : 1000000 ≤ t) (j : ℕ)
    (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (57 / 100) j) t| ≤
      (157 / 100 / 24 : ℝ) * eulerMoment570 (107 / 100) (j + 2) t := by
  rw [abs_mul]
  have he := euler570_psi_high hRH ht
  have hh :=
    mul_le_mul he (moment_slope (by linarith only [ht]) j hj) (abs_nonneg _) (by positivity)
  have hr := sqrt_times_power (show 0 < t by linarith only [ht]) (207 / 100)
  norm_num only at hr
  apply hh.trans_eq
  unfold eulerMoment570
  rw [pow_add]
  norm_num only
  linear_combination ((157 / 100 / 24) * Real.log t ^ j * Real.log t ^ 2) * hr

/-- An integrable envelope for the centered error on the entire tail. The high-range
term is supported only above one million. -/
private noncomputable def errorMajor (j : ℕ) (t : ℝ) : ℝ :=
  (4 / 5 * (157 / 100) : ℝ) * eulerMoment570 (107 / 100) j t +
    (Set.Ioi (1000000 : ℝ)).indicator
      (fun u ↦ (157 / 100 / 24 : ℝ) * eulerMoment570 (107 / 100) (j + 2) u) t

/-- Both power moments in the split envelope are integrable on their respective supports. -/
private theorem major_integrable {B : ℝ} (hB : 1 ≤ B) (j : ℕ) :
    MeasureTheory.IntegrableOn (errorMajor j) (Set.Ioi B) := by
  apply MeasureTheory.Integrable.add
  · exact (Analysis.log_power_tail_integrable (r := 107 / 100) (by norm_num only) hB j).const_mul _
  · apply (MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
    exact
      MeasureTheory.IntegrableOn.mono_set
        ((Analysis.log_power_tail_integrable (r := 107 / 100) (by norm_num only)
              (by norm_num only : (1 : ℝ) ≤ 1000000) (j + 2)).const_mul
          _)
        Set.inter_subset_left

/-- Evaluating the two improper moments gives the explicit envelope integral. -/
private theorem major_integral {B : ℝ} (hB : 1 ≤ B) (hU : B ≤ 1000000) (j : ℕ) :
    (∫ t in Set.Ioi B, errorMajor j t) =
      (4 / 5 * (157 / 100) : ℝ) * eulerMomentValue570 (107 / 100) j B +
        (157 / 100 / 24 : ℝ) * eulerMomentValue570 (107 / 100) (j + 2) 1000000 := by
  have hl :=
    (Analysis.log_power_tail_integrable (r := 107 / 100) (by norm_num only) hB j).const_mul
      (4 / 5 * (157 / 100) : ℝ)
  have hh :=
    (Analysis.log_power_tail_integrable (r := 107 / 100) (by norm_num only)
          (by norm_num only : (1 : ℝ) ≤ 1000000) (j + 2)).const_mul
      (157 / 100 / 24 : ℝ)
  unfold errorMajor eulerMoment570 eulerMomentValue570
  rw [MeasureTheory.integral_add hl
      ((MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
        (MeasureTheory.IntegrableOn.mono_set hh Set.inter_subset_left)),
    MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hU,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    Analysis.log_power_tail_integral (by norm_num only) hB,
    Analysis.log_power_tail_integral (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 1000000)]

/-- The finite psi bound and RH bound majorize the centered error on the two ranges. -/
private theorem point_major (hRH : RiemannHypothesis) {t : ℝ} (ht : 2701 < t) (j : ℕ) (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (57 / 100) j) t| ≤ errorMajor j t := by
  by_cases hv : 1000000 < t
  · rw [errorMajor, Set.indicator_of_mem (show t ∈ Set.Ioi (1000000 : ℝ) from hv)]
    have hl := Real.log_nonneg (show 1 ≤ t by linarith only [ht])
    have hp : 0 ≤ t := by linarith only [ht]
    apply (reflected_error_high_644 hRH hv.le j hj).trans
    apply le_add_of_nonneg_left
    unfold eulerMoment570
    positivity
  · rw [errorMajor, Set.indicator_of_notMem (show t ∉ Set.Ioi (1000000 : ℝ) from hv), add_zero]
    exact reflected_error_low_644 ht.le (le_of_not_gt hv) j hj

/-- The RH log-square bound makes the upper Abel boundary vanish for every fixed degree. -/
private theorem boundary_zero (hRH : RiemannHypothesis) (j : ℕ) :
    Filter.Tendsto (fun t ↦ (Chebyshev.psi t - t) * eulerMoment570 (57 / 100) j t) Filter.atTop
      (nhds 0) := by
  have h :=
    (Analysis.log_pow_mul_neg_rpow_tendsto (by norm_num only : 0 < (107 / 100 : ℝ))
          (j + 2)).div_const
      24
  rw [zero_div] at h
  apply squeeze_zero_norm' _ h
  · filter_upwards [Filter.eventually_ge_atTop (1000000 : ℝ)] with t ht
    have hp : 0 < t := by linarith only [ht]
    have hl := Real.log_nonneg (show 1 ≤ t by linarith only [ht])
    have hw : 0 ≤ eulerMoment570 (57 / 100) j t := by
      unfold eulerMoment570; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_right (euler570_psi_high hRH ht) hw).trans_eq
    unfold eulerMoment570
    rw [show -(57 / 100 : ℝ) - 1 = -(107 / 100 + 1 / 2 : ℝ) by norm_num only, pow_add]
    linear_combination (Real.log t ^ j * Real.log t ^ 2 / 24) * sqrt_times_power hp (107 / 100)

/-- The explicit complementary moment bound in equation (122.23), including the main
integral, the correction at 2701 and the two error integrals. -/
noncomputable def reflectedCapFrom644 (B : ℝ) (j : ℕ) : ℝ :=
  eulerMomentValue570 (57 / 100) j B + 4 / 5 * Real.sqrt B * eulerMoment570 (57 / 100) j B +
    (4 / 5 * (157 / 100)) * eulerMomentValue570 (107 / 100) j B +
    (157 / 100 / 24) * eulerMomentValue570 (107 / 100) (j + 2) 1000000

/-- For degrees zero through five, centered Abel summation under RH bounds the reflected
moment tail by its explicit endpoint expression. -/
theorem reflected_tail_cap_from_644 (hRH : RiemannHypothesis) {B : ℕ} (hB : 2701 ≤ (B : ℝ))
    (hU : (B : ℝ) ≤ 1000000) (j : ℕ) (hj : j ≤ 5) :
    (∑' n, reflectedMoment644 j n) - (∑ n ∈ Finset.Ioc 0 B, reflectedMoment644 j n) ≤
      reflectedCapFrom644 B j := by
  let f := eulerMoment570 (57 / 100) j
  let E := fun t ↦ (Chebyshev.psi t - t) * deriv f t
  have hp : ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.Ioi (B : ℝ)), ‖E t‖ ≤ errorMajor j t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (Real.norm_eq_abs _).trans_le (point_major hRH (hB.trans_lt ht) j hj)
  have hB₁ : (1 : ℝ) ≤ B := by linarith only [hB]
  have hB₀ : (0 : ℝ) < B := by linarith only [hB]
  have hi : MeasureTheory.IntegrableOn E (Set.Ioi (B : ℝ)) :=
    (major_integrable hB₁ j).mono'
      (((Chebyshev.psi_mono.measurable.sub measurable_id).mul
          (measurable_deriv f)).aestronglyMeasurable)
      hp
  have he := MeasureTheory.norm_integral_le_of_norm_le (major_integrable hB₁ j) hp
  rw [Real.norm_eq_abs, major_integral hB₁ hU] at he
  have hn (n : ℕ) : ArithmeticFunction.vonMangoldt n * f n = reflectedMoment644 j n := by
    unfold f eulerMoment570 reflectedMoment644
    rw [show -(57 / 100 : ℝ) - 1 = -(157 / 100 : ℝ) by norm_num only, mul_assoc]
  have hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n) := by
    apply
      (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 157 / 100)
          (by norm_num only) j).congr
    intro n
    rw [hn, reflectedMoment644, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hd (t : ℝ) (ht : (B : ℝ) ≤ t) : DifferentiableAt ℝ f t := by
    have hpos : 0 < t := by linarith only [ht, hB]
    exact
      (((Real.differentiableAt_log hpos.ne').pow j).mul
        (Real.differentiableAt_rpow_const_of_ne _ hpos.ne'))
  have hdi (b : ℝ) : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (B : ℝ) b) := by
    apply ContinuousOn.integrableOn_Icc
    apply (AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_continuous (157 / 100) j hB₀).congr
    exact fun t ht ↦ moment_deriv (by linarith only [ht.1, hB]) j
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral hB₀.le
      (fun b _ t ht ↦ hd t ht.1) (fun b _ ↦ hdi b)
      (Analysis.log_power_tail_integrable (by norm_num only) hB₁ j) hi (boundary_zero hRH j) hs
  simp only [hn, Nat.floor_natCast] at h
  have hmain : (∫ t in Set.Ioi (B : ℝ), f t) = eulerMomentValue570 (57 / 100) j B :=
    Analysis.log_power_tail_integral (by norm_num only) hB₁ j
  have hf : 0 ≤ f B := by
    unfold f eulerMoment570; positivity
  have hb :=
    mul_le_mul_of_nonneg_right
      (abs_le.mp
          (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (by linarith only [hB])
            hU)).1
      hf
  unfold reflectedCapFrom644
  change _ = (∫ t in Set.Ioi (B : ℝ), f t) - _ - ∫ t in Set.Ioi (B : ℝ), E t at h
  rw [h, hmain]
  change _ ≤ _ + 4 / 5 * Real.sqrt B * f B + _ + _
  linarith only [hb, (abs_le.mp he).1]

/-- The complementary moment bound at the original prefix endpoint 2701. -/
noncomputable def reflectedCap644 (j : ℕ) : ℝ :=
  reflectedCapFrom644 2701 j

/-- The complementary reflected moment above 2701 obeys the original cap. -/
theorem reflected_tail_cap_644 (hRH : RiemannHypothesis) (j : ℕ) (hj : j ≤ 5) :
    (∑' n, reflectedMoment644 j n) - (∑ n ∈ Finset.Ioc 0 2701, reflectedMoment644 j n) ≤
      reflectedCap644 j := by
  exact reflected_tail_cap_from_644 hRH (B := 2701) (by norm_num only) (by norm_num only) j hj

private theorem moment_summable (j : ℕ) : Summable (reflectedMoment644 j) := by
  apply
    (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 157 / 100)
        (by norm_num only) j).congr
  intro n
  rw [reflectedMoment644, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

/-- Under RH the unweighted complementary reflected series is bounded by
the binomial combination of its six explicit tail caps. -/
theorem reflected_weight_tail_from_644 (hRH : RiemannHypothesis) {B : ℕ} (hB : 2701 ≤ (B : ℝ))
    (hU : (B : ℝ) ≤ 1000000) {z : ℝ} (hz : 0 ≤ z) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n
    (∑' n, W n) - (∑ n ∈ Finset.Ioc 0 B, W n) ≤
      ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCapFrom644 B j := by
  intro W
  dsimp only [W]
  simp only [reflected_expand_644]
  rw [Summable.tsum_finsetSum (fun j _ ↦ (moment_summable j).mul_left _),
    Finset.sum_comm (s := Finset.Ioc 0 B)]
  simp only [tsum_mul_left, ← Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub]
  exact
    mul_le_mul_of_nonneg_left
      (reflected_tail_cap_from_644 hRH hB hU j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))

/-- Under RH the unweighted complementary reflected series is bounded by
the binomial combination of its six explicit tail caps. -/
theorem reflected_weight_tail_644 (hRH : RiemannHypothesis) {z : ℝ} (hz : 0 ≤ z) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n
    (∑' n, W n) - (∑ n ∈ Finset.Ioc 0 2701, W n) ≤
      ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCap644 j := by
  exact reflected_weight_tail_from_644 hRH (B := 2701) (by norm_num only) (by norm_num only) hz

/-- For a nonnegative shifted logarithm, the reflected weight above the
fixed prefix obeys the same six tail caps at the shifted main scale. -/
theorem quarter_shift_reflected_tail_644 (hRH : RiemannHypothesis) {r h : ℝ} (hr : 0 < r)
    (hz : 0 ≤ 2 * Real.log r - h) :
    let z := 2 * Real.log r - h
    let D := (107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ) * Real.exp ((107 / 100) * h)
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n
    D * ((∑' n, W n) - ∑ n ∈ Finset.Ioc 0 2701, W n) ≤
      D * ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCap644 j := by
  intro z D W
  exact
    mul_le_mul_of_nonneg_left (reflected_weight_tail_644 hRH hz)
      (by
        dsimp only [D]
        positivity)

/-- Removing a nonnegative shift only increases the reflected power-log
weight, provided the smaller logarithmic argument is nonnegative. -/
theorem quarter_reflected_shift_le_644 {z h : ℝ} (hh : 0 ≤ h) (hz : h ≤ z) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * quarterReflectedWeight (z - h) n ≤
      ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n := by
  unfold quarterReflectedWeight
  have h₀ := add_nonneg (sub_nonneg.mpr hz) (Real.log_natCast_nonneg n)
  have h₁ : z - h + Real.log n ≤ z + Real.log n := by linarith only [hh]
  exact
    mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h₀ h₁ 5)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      ArithmeticFunction.vonMangoldt_nonneg

private theorem weight_summable (z : ℝ) :
    Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n) := by
  simp only [reflected_expand_644]
  exact summable_sum (fun j _ ↦ (moment_summable j).mul_left _)

private theorem signed_prefix_bound {z : ℝ} (hz : 0 ≤ z) (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 99000, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n
    0 - (∑' n, τ n * W n) ≤
      (∑' n, W n) - 4 * ((∑ n ∈ Finset.Ioc 0 2701, W n) + (∑ n ∈ Finset.Ioc 2701 99000, W n)) := by
  intro W
  have hw (n : ℕ) : 0 ≤ W n :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (pow_nonneg (add_nonneg hz (Real.log_natCast_nonneg n)) _))
  have hs : Summable W := weight_summable z
  have hsτ : Summable (fun n ↦ τ n * W n) := by
    apply (hs.mul_left 3).of_norm_bounded
    intro n
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n)]
    exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith only [(ht n).1], (ht n).2⟩) (hw n)
  have h :=
    (hs.add hsτ).sum_le_tsum (Finset.Ioc 0 99000)
      (fun n _ ↦ by
        have hsign := mul_le_mul_of_nonneg_right (ht n).1 (hw n)
        change 0 ≤ W n + τ n * W n
        linarith only [hsign])
  change (∑ n ∈ Finset.Ioc 0 99000, (W n + τ n * W n)) ≤ _ at h
  rw [hs.tsum_add hsτ] at h
  have he : (∑ n ∈ Finset.Ioc 0 99000, (W n + τ n * W n)) = 4 * ∑ n ∈ Finset.Ioc 0 99000, W n := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases h0 : ArithmeticFunction.vonMangoldt n = 0
    · simp only [W, h0, zero_mul, mul_zero, add_zero]
    · rw [hp n hn h0]
      ring
  rw [he, ← Finset.Ioc_union_Ioc_eq_Ioc (by decide : 0 ≤ 2701) (by decide : 2701 ≤ 99000),
    Finset.sum_union (Finset.Ioc_disjoint_Ioc_of_le le_rfl)] at h
  linarith only [h]

/-- A trace between minus one and three yields an absolutely summable
deficit for every nonnegative logarithmic shift. -/
private theorem deficit_summable {z : ℝ} (hz : 0 ≤ z) (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3) :
    Summable
      (fun n : ℕ ↦
        (3 - τ n) * (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n)) := by
  apply ((weight_summable z).mul_left (4 : ℝ)).of_norm_bounded
  intro n
  have hw : 0 ≤ ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (pow_nonneg (add_nonneg hz (Real.log_natCast_nonneg n)) _))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sub_nonneg.mpr (ht n).2) hw)]
  exact mul_le_mul_of_nonneg_right (by linarith only [(ht n).1]) hw

/-- The reflected trace deficit at logarithmic shift `z - h` is at most
the deficit at `z` for any nonnegative `h` with `h ≤ z`. -/
theorem quarter_deficit_shift_le_644 {z h : ℝ} (hh : 0 ≤ h) (hz : h ≤ z) (τ : ℕ → ℝ)
    (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3) :
    (∑' n : ℕ, (3 - τ n) * (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight (z - h) n)) ≤
      ∑' n : ℕ, (3 - τ n) * (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n) := by
  exact
    (deficit_summable (sub_nonneg.mpr hz) τ ht).tsum_le_tsum
      (fun n ↦
        mul_le_mul_of_nonneg_left (quarter_reflected_shift_le_644 hh hz n)
          (sub_nonneg.mpr (ht n).2))
      (deficit_summable (hh.trans hz) τ ht)

/-- If the trace is three through the certified prefix, its total deficit
at a shifted logarithm is bounded by four times the six unsigned tail caps. -/
theorem quarter_reflected_deficit_644 (hRH : RiemannHypothesis) {z : ℝ} (hz : 0 ≤ z) (τ : ℕ → ℝ)
    (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 99000, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    (∑' n : ℕ, (3 - τ n) * (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n)) ≤
      4 *
        ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCapFrom644 99000 j := by
  let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n
  have hw (n : ℕ) : 0 ≤ W n :=
    mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _)
        (pow_nonneg (add_nonneg hz (Real.log_natCast_nonneg n)) _))
  have hs : Summable W := weight_summable z
  have hsτ : Summable (fun n ↦ τ n * W n) :=
    (hs.mul_left 3).of_norm_bounded fun n ↦ by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hw n)]
      exact mul_le_mul_of_nonneg_right (abs_le.mpr ⟨by linarith only [(ht n).1], (ht n).2⟩) (hw n)
  have hp' := signed_prefix_bound hz τ ht hp
  have htail :=
    reflected_weight_tail_from_644 hRH (B := 99000) (by norm_num only) (by norm_num only) hz
  have hsplit := Finset.sum_Ioc_consecutive W (Nat.zero_le 2701) (by decide : 2701 ≤ 99000)
  dsimp only at hp'
  rw [hsplit] at hp'
  change (∑' n, (3 - τ n) * W n) ≤ _
  simp only [sub_mul, (hs.mul_left (3 : ℝ)).tsum_sub hsτ, tsum_mul_left]
  dsimp only [W] at hp' htail ⊢
  norm_num only [Nat.cast_ofNat] at htail
  linarith only [hp', htail]

/-- At the shifted main scale, a trace that agrees with three on the
certified prefix loses at most four times the scaled unsigned tail bound. -/
theorem quarter_shift_deficit_644 (hRH : RiemannHypothesis) {r h : ℝ} (hr : 0 < r)
    (hz : 0 ≤ 2 * Real.log r - h) (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 99000, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 2 * Real.log r - h
    let D := (107 / 100 : ℝ) ^ 5 / 120 * r ^ (-(107 / 50) : ℝ) * Real.exp ((107 / 100) * h)
    D * (∑' n : ℕ, (3 - τ n) * (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n)) ≤
      D *
        (4 *
          ∑ j ∈ Finset.range 6,
            (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCapFrom644 99000 j) := by
  intro z D
  exact
    mul_le_mul_of_nonneg_left (quarter_reflected_deficit_644 hRH hz τ ht hp)
      (by
        dsimp only [D]
        positivity)

/-- Under RH, the section 122 reflected series is bounded by the six
signed tail coefficients after subtracting the certified additional recovery.
The trace equals three on the Mangoldt support through 99000. -/
theorem quarter_reflected_upper_644 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 316 322)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hp : ∀ n ∈ Finset.Ioc 0 99000, ArithmeticFunction.vonMangoldt n ≠ 0 → τ n = 3) :
    let z := 2687 / 1000 + 2 * Real.log r
    let D :=
      (107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120 * r ^ (-(107 / 50) : ℝ)
    0 - D * (∑' n, τ n * (ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n)) ≤
      D *
          (∑ j ∈ Finset.range 6,
            (Nat.choose 5 j : ℝ) * z ^ (5 - j) * (reflectedCap644 j - 3 * reflectedFloor644 j)) -
        0.0013281 := by
  intro z D
  let W := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterReflectedWeight z n
  have hr₁ : 1 ≤ r := by linarith only [hr.1]
  have hz : 0 ≤ z := by
    dsimp only [z]
    linarith only [Real.log_nonneg hr₁]
  have h := signed_prefix_bound hz τ ht hp
  have ht' := reflected_weight_tail_644 hRH hz
  have hp' := reflected_prefix_lower_644 hz
  have hsum :
    -(∑' n, τ n * W n) ≤
      (∑ j ∈ Finset.range 6,
          (Nat.choose 5 j : ℝ) * z ^ (5 - j) * (reflectedCap644 j - 3 * reflectedFloor644 j)) -
        4 * (∑ n ∈ Finset.Ioc 2701 99000, W n) := by
    have he :
      (∑ j ∈ Finset.range 6,
          (Nat.choose 5 j : ℝ) * z ^ (5 - j) * (reflectedCap644 j - 3 * reflectedFloor644 j)) =
        (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedCap644 j) -
          3 * (∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * reflectedFloor644 j) := by
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      ring
    rw [he]
    dsimp only [W] at h ht' ⊢
    linarith only [h, ht', hp']
  have hD : 0 ≤ D := by
    dsimp only [D]; positivity
  have hscale := mul_le_mul_of_nonneg_left hsum hD
  have hrec : quarterRecovery644 r = 4 * D * (∑ n ∈ Finset.Ioc 2701 99000, W n) := by
    unfold quarterRecovery644
    dsimp only [W, D]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    unfold quarterRecoveryFactor quarterReflectedWeight
    dsimp only [z]
    ring
  have hbound := quarter_recovery_lower_644 hr
  rw [hrec] at hbound
  nlinarith only [hscale, hbound]

end PseudoPrime.PrimeTestBounds.MillerRabin
