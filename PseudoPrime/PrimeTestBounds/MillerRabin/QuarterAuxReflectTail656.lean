/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflection656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMoments570
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflection656
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PowerLogMomentAbel
import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality
import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevSqrt1423toMillion
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedCoefficients644

/-! # Shared Abel moment bounds for the section 132 shifted reflection -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The reflected Mangoldt moment at decay exponent 8/5. -/
noncomputable def auxReflectedMoment656 (j n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log n ^ j * (n : ℝ) ^ (-(8 / 5) : ℝ)

/-- The main moment derivative agrees with the logarithmic Mangoldt weight derivative. -/
private theorem moment_deriv {t : ℝ} (ht : 0 < t) (j : ℕ) :
    deriv (eulerMoment570 (3 / 5) j) t =
      AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv (8 / 5) j t := by
  have he :
    eulerMoment570 (3 / 5) j = AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight (8 / 5) j := by
    funext x
    unfold eulerMoment570 AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight
    rw [show -(3 / 5 : ℝ) - 1 = -(8 / 5 : ℝ) by norm_num only, mul_comm]
  rw [he]
  exact (AnalyticNumberTheory.Arithmetic.mangoldt_moment_weight_deriv _ _ ht).deriv

/-- From 103684 onwards the moment is decreasing through degree five. Dropping the
nonnegative logarithmic derivative term bounds its absolute slope. -/
private theorem moment_slope {t : ℝ} (ht : 103684 ≤ t) (j : ℕ) (hj : j ≤ 5) :
    |deriv (eulerMoment570 (3 / 5) j) t| ≤ (8 / 5 : ℝ) * Real.log t ^ j * t ^ (-(13 / 5 : ℝ)) := by
  have ht1 : 1 ≤ t := by linarith only [ht]
  have hp := zero_lt_one.trans_le ht1
  have he : Real.exp 5 ≤ t := by
    rw [show (5 : ℝ) = 1 * ((5 : ℕ) : ℝ) by norm_num only, Real.exp_mul_natCast]
    exact
      (pow_le_pow_left₀ (Real.exp_pos _).le Real.exp_one_lt_three.le _).trans
        ((by norm_num only : (3 : ℝ) ^ 5 ≤ 103684).trans ht)
  have hl := (Real.le_log_iff_exp_le hp).mpr he
  have hj' : (j : ℝ) ≤ 5 := by exact_mod_cast hj
  rw [moment_deriv hp,
    abs_of_nonpos
      (AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_nonpos j (by norm_num only) ht1
        (by linarith only [hl, hj']))]
  unfold AnalyticNumberTheory.Arithmetic.mangoldtMomentWeightDeriv
  rw [show -(8 / 5 : ℝ) - 1 = -(13 / 5 : ℝ) by norm_num only]
  have hlog := Real.log_nonneg ht1
  have h : 0 ≤ t ^ (-(8 / 5 : ℝ)) * ((j : ℝ) * Real.log t ^ (j - 1) * t⁻¹) := by positivity
  linarith only [h]

/-- Multiplying the power weight by a square root shifts its decay exponent by one half. -/
private theorem sqrt_times_power {t : ℝ} (ht : 0 < t) (d : ℝ) :
    Real.sqrt t * t ^ (-(d + 1 / 2)) = t ^ (-d) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
  congr 1
  ring

/-- On the finite certificate range, the centered Abel error density is bounded by
a logarithmic moment of the same degree. -/
theorem reflected_error_low_656 {t : ℝ} (ht : 103684 ≤ t) (hu : t ≤ 1000000) (j : ℕ) (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (3 / 5) j) t| ≤
      (4 / 5 * (8 / 5) : ℝ) * eulerMoment570 (11 / 10) j t := by
  rw [abs_mul]
  have he := AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (by linarith only [ht]) hu
  have hh := mul_le_mul he (moment_slope ht j hj) (abs_nonneg _) (by positivity)
  have hr := sqrt_times_power (show 0 < t by linarith only [ht]) (21 / 10)
  norm_num only at hr
  apply hh.trans_eq
  unfold eulerMoment570
  norm_num only
  linear_combination (4 / 5 * (8 / 5) * Real.log t ^ j) * hr

/-- Above one million the RH log-square error contributes a moment two degrees higher. -/
theorem reflected_error_high_656 (hRH : RiemannHypothesis) {t : ℝ} (ht : 1000000 ≤ t) (j : ℕ)
    (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (3 / 5) j) t| ≤
      (8 / 5 / 24 : ℝ) * eulerMoment570 (11 / 10) (j + 2) t := by
  rw [abs_mul]
  have he := euler570_psi_high hRH ht
  have hh :=
    mul_le_mul he (moment_slope (by linarith only [ht]) j hj) (abs_nonneg _) (by positivity)
  have hr := sqrt_times_power (show 0 < t by linarith only [ht]) (21 / 10)
  norm_num only at hr
  apply hh.trans_eq
  unfold eulerMoment570
  rw [pow_add]
  norm_num only
  linear_combination ((8 / 5 / 24) * Real.log t ^ j * Real.log t ^ 2) * hr

/-- An integrable envelope for the centered error on the entire tail. The high-range
term is supported only above one million. -/
private noncomputable def errorMajor (j : ℕ) (t : ℝ) : ℝ :=
  (4 / 5 * (8 / 5) : ℝ) * eulerMoment570 (11 / 10) j t +
    (Set.Ioi (1000000 : ℝ)).indicator
      (fun u ↦ (8 / 5 / 24 : ℝ) * eulerMoment570 (11 / 10) (j + 2) u) t

/-- Both power moments in the split envelope are integrable on their respective supports. -/
private theorem major_integrable {B : ℝ} (hB : 1 ≤ B) (j : ℕ) :
    MeasureTheory.IntegrableOn (errorMajor j) (Set.Ioi B) := by
  apply MeasureTheory.Integrable.add
  · exact (Analysis.log_power_tail_integrable (r := 11 / 10) (by norm_num only) hB j).const_mul _
  · apply (MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
    exact
      MeasureTheory.IntegrableOn.mono_set
        ((Analysis.log_power_tail_integrable (r := 11 / 10) (by norm_num only)
              (by norm_num only : (1 : ℝ) ≤ 1000000) (j + 2)).const_mul
          _)
        Set.inter_subset_left

/-- Evaluating the two improper moments gives the explicit envelope integral. -/
private theorem major_integral {B : ℝ} (hB : 1 ≤ B) (hU : B ≤ 1000000) (j : ℕ) :
    (∫ t in Set.Ioi B, errorMajor j t) =
      (4 / 5 * (8 / 5) : ℝ) * eulerMomentValue570 (11 / 10) j B +
        (8 / 5 / 24 : ℝ) * eulerMomentValue570 (11 / 10) (j + 2) 1000000 := by
  have hl :=
    (Analysis.log_power_tail_integrable (r := 11 / 10) (by norm_num only) hB j).const_mul
      (4 / 5 * (8 / 5) : ℝ)
  have hh :=
    (Analysis.log_power_tail_integrable (r := 11 / 10) (by norm_num only)
          (by norm_num only : (1 : ℝ) ≤ 1000000) (j + 2)).const_mul
      (8 / 5 / 24 : ℝ)
  unfold errorMajor eulerMoment570 eulerMomentValue570
  rw [MeasureTheory.integral_add hl
      ((MeasureTheory.integrableOn_indicator_iff measurableSet_Ioi.nullMeasurableSet).mpr
        (MeasureTheory.IntegrableOn.mono_set hh Set.inter_subset_left)),
    MeasureTheory.setIntegral_indicator measurableSet_Ioi, Set.Ioi_inter_Ioi, max_eq_right hU,
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    Analysis.log_power_tail_integral (by norm_num only) hB,
    Analysis.log_power_tail_integral (by norm_num only) (by norm_num only : (1 : ℝ) ≤ 1000000)]

/-- The finite psi bound and RH bound majorize the centered error on the two ranges. -/
private theorem point_major (hRH : RiemannHypothesis) {t : ℝ} (ht : 103684 < t) (j : ℕ)
    (hj : j ≤ 5) :
    |(Chebyshev.psi t - t) * deriv (eulerMoment570 (3 / 5) j) t| ≤ errorMajor j t := by
  by_cases hv : 1000000 < t
  · rw [errorMajor, Set.indicator_of_mem (show t ∈ Set.Ioi (1000000 : ℝ) from hv)]
    have hl := Real.log_nonneg (show 1 ≤ t by linarith only [ht])
    have hp : 0 ≤ t := by linarith only [ht]
    apply (reflected_error_high_656 hRH hv.le j hj).trans
    apply le_add_of_nonneg_left
    unfold eulerMoment570
    positivity
  · rw [errorMajor, Set.indicator_of_notMem (show t ∉ Set.Ioi (1000000 : ℝ) from hv), add_zero]
    exact reflected_error_low_656 ht.le (le_of_not_gt hv) j hj

/-- The RH log-square bound makes the upper Abel boundary vanish for every fixed degree. -/
private theorem boundary_zero (hRH : RiemannHypothesis) (j : ℕ) :
    Filter.Tendsto (fun t ↦ (Chebyshev.psi t - t) * eulerMoment570 (3 / 5) j t) Filter.atTop
      (nhds 0) := by
  have h :=
    (Analysis.log_pow_mul_neg_rpow_tendsto (by norm_num only : 0 < (11 / 10 : ℝ)) (j + 2)).div_const
      24
  rw [zero_div] at h
  apply squeeze_zero_norm' _ h
  · filter_upwards [Filter.eventually_ge_atTop (1000000 : ℝ)] with t ht
    have hp : 0 < t := by linarith only [ht]
    have hl := Real.log_nonneg (show 1 ≤ t by linarith only [ht])
    have hw : 0 ≤ eulerMoment570 (3 / 5) j t := by
      unfold eulerMoment570; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    apply (mul_le_mul_of_nonneg_right (euler570_psi_high hRH ht) hw).trans_eq
    unfold eulerMoment570
    rw [show -(3 / 5 : ℝ) - 1 = -(11 / 10 + 1 / 2 : ℝ) by norm_num only, pow_add]
    linear_combination (Real.log t ^ j * Real.log t ^ 2 / 24) * sqrt_times_power hp (11 / 10)

/-- The complementary moment bound for the reflected tail, including the main
integral, the lower boundary and the two error integrals. -/
noncomputable def auxReflectedCap656 (B : ℝ) (j : ℕ) : ℝ :=
  eulerMomentValue570 (3 / 5) j B + 4 / 5 * Real.sqrt B * eulerMoment570 (3 / 5) j B +
    (4 / 5 * (8 / 5)) * eulerMomentValue570 (11 / 10) j B +
    (8 / 5 / 24) * eulerMomentValue570 (11 / 10) (j + 2) 1000000

/-- For degrees zero through five, centered Abel summation under RH bounds the reflected
moment tail by its explicit endpoint expression. -/
theorem reflected_tail_cap_from_656 (hRH : RiemannHypothesis) {B : ℕ} (hB : 103684 ≤ (B : ℝ))
    (hU : (B : ℝ) ≤ 1000000) (j : ℕ) (hj : j ≤ 5) :
    (∑' n, auxReflectedMoment656 j n) - (∑ n ∈ Finset.Ioc 0 B, auxReflectedMoment656 j n) ≤
      auxReflectedCap656 B j := by
  let f := eulerMoment570 (3 / 5) j
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
  have hn (n : ℕ) : ArithmeticFunction.vonMangoldt n * f n = auxReflectedMoment656 j n := by
    unfold f eulerMoment570 auxReflectedMoment656
    rw [show -(3 / 5 : ℝ) - 1 = -(8 / 5 : ℝ) by norm_num only, mul_assoc]
  have hs : Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * f n) := by
    apply
      (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
          (by norm_num only) j).congr
    intro n
    rw [hn, auxReflectedMoment656, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hd (t : ℝ) (ht : (B : ℝ) ≤ t) : DifferentiableAt ℝ f t := by
    have hpos : 0 < t := by linarith only [ht, hB]
    exact
      (((Real.differentiableAt_log hpos.ne').pow j).mul
        (Real.differentiableAt_rpow_const_of_ne _ hpos.ne'))
  have hdi (b : ℝ) : MeasureTheory.IntegrableOn (deriv f) (Set.Icc (B : ℝ) b) := by
    apply ContinuousOn.integrableOn_Icc
    apply (AnalyticNumberTheory.Arithmetic.mangoldt_moment_deriv_continuous (8 / 5) j hB₀).congr
    exact fun t ht ↦ moment_deriv (by linarith only [ht.1, hB]) j
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_integral hB₀.le
      (fun b _ t ht ↦ hd t ht.1) (fun b _ ↦ hdi b)
      (Analysis.log_power_tail_integrable (by norm_num only) hB₁ j) hi (boundary_zero hRH j) hs
  simp only [hn, Nat.floor_natCast] at h
  have hmain : (∫ t in Set.Ioi (B : ℝ), f t) = eulerMomentValue570 (3 / 5) j B :=
    Analysis.log_power_tail_integral (by norm_num only) hB₁ j
  have hf : 0 ≤ f B := by
    unfold f eulerMoment570; positivity
  have hb :=
    mul_le_mul_of_nonneg_right
      (abs_le.mp
          (AnalyticNumberTheory.Arithmetic.psi_four_fifths_1423_million (by linarith only [hB])
            hU)).1
      hf
  unfold auxReflectedCap656
  change _ = (∫ t in Set.Ioi (B : ℝ), f t) - _ - ∫ t in Set.Ioi (B : ℝ), E t at h
  rw [h, hmain]
  change _ ≤ _ + 4 / 5 * Real.sqrt B * f B + _ + _
  linarith only [hb, (abs_le.mp he).1]

private theorem moment_summable (j : ℕ) : Summable (auxReflectedMoment656 j) := by
  apply
    (AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 8 / 5)
        (by norm_num only) j).congr
  intro n
  rw [auxReflectedMoment656, Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]

private theorem aux_reflected_expand (z : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) * (z + Real.log n) ^ 5 =
      ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * auxReflectedMoment656 j n := by
  unfold auxReflectedMoment656
  rw [Real.rpow_neg (Nat.cast_nonneg n)]
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
    Nat.reduceAdd, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero, inv_inv, div_eq_mul_inv]
  ring

private theorem aux_reflected_weight_cap (hRH : RiemannHypothesis) {B : ℕ} (hB : 103684 ≤ (B : ℝ))
    (hU : (B : ℝ) ≤ 1000000) {z : ℝ} (hz : 0 ≤ z) :
    let W := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) * (z + Real.log n) ^ 5
    (∑' n, W n) - (∑ n ∈ Finset.Ioc 0 B, W n) ≤
      ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * z ^ (5 - j) * auxReflectedCap656 B j := by
  intro W
  simp only [W, aux_reflected_expand]
  rw [Summable.tsum_finsetSum (fun j _ ↦ (moment_summable j).mul_left _),
    Finset.sum_comm (s := Finset.Ioc 0 B)]
  simp only [tsum_mul_left, ← Finset.mul_sum]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub]
  exact
    mul_le_mul_of_nonneg_left
      (reflected_tail_cap_from_656 hRH hB hU j (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))
      (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hz _))

/-- The scaled sum of the six Abel moment bounds at the shared prefix endpoint. -/
noncomputable def quarterAuxReflectCap656 (r h : ℝ) (B : ℕ) : ℝ :=
  ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h)) *
    (4 *
      ∑ j ∈ Finset.range 6,
        (Nat.choose 5 j : ℝ) * (2 * Real.log r - h) ^ (5 - j) * auxReflectedCap656 B j)

private theorem prefix_sum_cap (s : Finset ℕ) {L W : ℕ → ℝ} (hl : Summable L) (hw : Summable W)
    (hp : ∑ n ∈ s, L n = 0) (h : ∀ n, L n ≤ 4 * W n) :
    (∑' n, L n) ≤ 4 * ((∑' n, W n) - ∑ n ∈ s, W n) := by
  have hL := hl.sum_add_tsum_compl (s := s)
  have hW := hw.sum_add_tsum_compl (s := s)
  have he :=
    (hl.subtype fun n : ℕ ↦ n ∉ s).tsum_le_tsum (g := fun n ↦ 4 * W n.val) (fun n ↦ h n.val)
      ((hw.mul_left 4).subtype _)
  rw [tsum_mul_left] at he
  rw [hp, zero_add] at hL
  exact
    hL.symm.le.trans
      (he.trans (mul_le_mul_of_nonneg_left (eq_sub_of_add_eq' hW).le (by norm_num only)))

/-- Under RH, agreement through B bounds the shifted reflected deficit
by the six shared moment integrals. The trace lies between zero and four. -/
theorem quarter_aux_reflect_tail_cap_656 (hRH : RiemannHypothesis) {B : ℕ} (hB : 103684 ≤ (B : ℝ))
    (hU : (B : ℝ) ≤ 1000000) (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n ∈ Finset.Ioc 0 B, ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) {r h : ℝ}
    (hr : 0 < r) (hh : h ≤ 2 * Real.log r) :
    quarterAuxReflection656 α r h ≤ quarterAuxReflectCap656 r h B := by
  let z := 2 * Real.log r - h
  let W := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (8 / 5 : ℝ) * (z + Real.log n) ^ 5
  let L := fun n : ℕ ↦ α n * W n
  have hz : 0 ≤ z := sub_nonneg.mpr hh
  have hs : Summable W := by
    simpa only [W, one_mul] using
      reflection_summable (fun _ ↦ 1)
        (by
          intro n; exact ⟨by norm_num only, by norm_num only⟩)
        z
  have hl : Summable L := by simpa only [L, W, mul_assoc] using reflection_summable α hα z
  let s := Finset.Ioc 0 B
  have hp : ∑ n ∈ s, L n = 0 :=
    Finset.sum_eq_zero fun n hn ↦ by
      by_cases hn₀ : ArithmeticFunction.vonMangoldt n = 0
      · simp only [L, W, hn₀, zero_div, zero_mul, mul_zero]
      · simp only [L, hprefix n hn hn₀, zero_mul]
  have htail :=
    prefix_sum_cap s hl hs hp
      (fun n ↦
        mul_le_mul_of_nonneg_right (hα n).2
          (mul_nonneg
            (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
              (Real.rpow_nonneg (Nat.cast_nonneg n) _))
            (pow_nonneg (add_nonneg hz (Real.log_natCast_nonneg n)) _)))
  have hcap := aux_reflected_weight_cap hRH hB hU hz
  change (∑' n, W n) - ∑ n ∈ s, W n ≤ _ at hcap
  have ht := htail.trans (mul_le_mul_of_nonneg_left hcap (by norm_num only : (0 : ℝ) ≤ 4))
  unfold quarterAuxReflection656 quarterAuxReflectCap656
  exact mul_le_mul_of_nonneg_left (by simpa only [L, W, z, mul_assoc] using ht) (by positivity)

private noncomputable def momentBox (j : ℕ) : ℝ :=
  0.000978527317 * Analysis.logPowerTailPoly (3 / 5) j 11.549104 +
    (4 / 5) * (0.000003038905 * (11.549104 : ℝ) ^ j) +
    (4 / 5 * (8 / 5)) * (0.000003038905 * Analysis.logPowerTailPoly (11 / 10) j 11.549104) +
    (8 / 5 / 24) * (0.000000251189 * Analysis.logPowerTailPoly (11 / 10) (j + 2) 13.816)

private theorem cap_numeric (j : ℕ) : auxReflectedCap656 103684 j ≤ momentBox j := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 103684) (j := 17) (n := 22) (lo := 11) (hi :=
        11549104 / 1000000) (by decide +kernel)).2
  have hd :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 3) (d :=
        5) (lo := 0) (hi := 978527317 / 10 ^ 12) (by decide +kernel)).2
  have ha :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 11) (d :=
        10) (lo := 0) (hi := 3038905 / 10 ^ 12) (by decide +kernel)).2
  have hU :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 11) (d :=
        10) (lo := 0) (hi := 251189 / 10 ^ 12) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hd ha hU
  have hm := moment_upper (by norm_num only : (0 : ℝ) < 3 / 5) (by norm_num only) hd hl j
  have he := moment_upper (by norm_num only : (0 : ℝ) < 11 / 10) (by norm_num only) ha hl j
  have hh :=
    moment_upper (by norm_num only : (0 : ℝ) < 11 / 10) (by norm_num only) hU log_million (j + 2)
  have hlog : 0 ≤ Real.log (103684 : ℝ) := Real.log_nonneg (by norm_num only)
  have hb :
    Real.sqrt 103684 * eulerMoment570 (3 / 5) j 103684 ≤
      (607781 / 200000000000 : ℝ) * (721819 / 62500 : ℝ) ^ j := by
    unfold eulerMoment570
    rw [mul_left_comm, Real.sqrt_eq_rpow, ← Real.rpow_add (by norm_num only : (0 : ℝ) < 103684),
      show (1 / 2 : ℝ) + (-(3 / 5) - 1) = -(11 / 10) by norm_num only, mul_comm]
    exact
      mul_le_mul ha (pow_le_pow_left₀ hlog hl j) (pow_nonneg hlog _)
        ((Real.rpow_nonneg (by norm_num only) _).trans ha)
  unfold auxReflectedCap656 momentBox
  have hbox :
    (607781 / 200000000000 : ℝ) * (721819 / 62500 : ℝ) ^ j =
      0.000003038905 * (11.549104 : ℝ) ^ j := by
    norm_num only
  rw [hbox] at hb
  linarith only [hm, he, hh, hb]

private theorem cap_nonneg (j : ℕ) : 0 ≤ auxReflectedCap656 103684 j := by
  have hm {d x : ℝ} (hd : 0 < d) (hx : 1 ≤ x) (k : ℕ) : 0 ≤ eulerMomentValue570 d k x :=
    mul_nonneg (Real.rpow_nonneg (zero_le_one.trans hx) _)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg hx) k)
  unfold auxReflectedCap656
  have h₁ := hm (d := 3 / 5) (x := 103684) (by norm_num only) (by norm_num only) j
  have h₂ : 0 ≤ eulerMoment570 (3 / 5) j 103684 := by
    unfold eulerMoment570; positivity
  have h₃ := hm (d := 11 / 10) (x := 103684) (by norm_num only) (by norm_num only) j
  have h₄ := hm (d := 11 / 10) (x := 1000000) (by norm_num only) (by norm_num only) (j + 2)
  positivity

private theorem cap_rectangle {r h e : ℝ} (hr : r ∈ Set.Icc 322 328) (hh : h ≤ 2 * Real.log r)
    (he : Real.exp ((11 / 10) * h) ≤ e) :
    quarterAuxReflectCap656 r h 103684 ≤
      ((11 / 10 : ℝ) ^ 5 / 30 * 0.000003038905 * e) *
        ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (11.5861 - h) ^ (5 - j) * momentBox j := by
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5) (hi :=
        579305 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hlog' := (Real.log_le_log hr₀ hr.2).trans hlog
  have hz : 2 * Real.log r - h ≤ 11.5861 - h := by linarith only [hlog']
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 103684) (p := 11) (d :=
        10) (lo := 0) (hi := 3038905 / 10 ^ 12) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hp
  rw [show (103684 : ℝ) = 322 ^ (2 : ℕ) by norm_num only, ←
    Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 322)] at hp
  norm_num only [Nat.cast_ofNat] at hp
  have hp' : r ^ (-(11 / 5) : ℝ) ≤ 0.000003038905 := by
    norm_num only
    exact
      (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 322) hr.1
            (by norm_num only : (-(11 / 5) : ℝ) ≤ 0)).trans
        hp
  have hv := sub_nonneg.mpr hh
  have he₀ := (Real.exp_pos _).le.trans he
  unfold quarterAuxReflectCap656
  rw [show
      ∀ S : ℝ,
        ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h)) * (4 * S) =
          ((11 / 10 : ℝ) ^ 5 / 30 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h)) * S
      from fun S ↦ by ring]
  gcongr
  all_goals
    first
    | exact cap_numeric _
    | exact cap_nonneg _
    | exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hv.trans hz) _)
    |
      exact
        Finset.sum_nonneg
          (fun j _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hv _)) (cap_nonneg j))

/-- The unshifted reflected deficit has a uniform upper cap on both
section 132 intervals, using the same six shared Abel moments. -/
theorem quarter_main_reflect_box_656 {r : ℝ} (hr : r ∈ Set.Icc 322 328) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.000242 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 322).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000 / 558) (j := 5) (n := 32) (lo := 2) (hi :=
        2.8875) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl
  have he : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    apply (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 0.0558)).mp
    have h : Real.log (0.0558 : ℝ)⁻¹ ≤ 2.8875 := by
      norm_num only at hl ⊢
      exact hl
    rw [Real.log_inv] at h
    linarith only [h]
  refine (cap_rectangle hr hh he).trans ?_
  norm_num only [momentBox, Rat.cast_div, Rat.cast_ofNat, Analysis.logPowerTailPoly,
    Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceAdd, Nat.reduceSub,
    Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

private theorem cap_at_shift {r : ℝ} (hr : r ∈ Set.Icc 322 328) (i : Fin 7) {h : ℚ} {e b : ℝ}
    (hi : quarterAuxShift656 i = h) (he : Real.exp ((11 / 10) * h) ≤ e)
    (hb :
      ((11 / 10 : ℝ) ^ 5 / 30 * 0.000003038905 * e) *
          ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (11.5861 - h) ^ (5 - j) * momentBox j ≤
        b) :
    quarterAuxReflectCap656 r (quarterAuxShift656 i) 103684 ≤ b := by
  have hh := aux_shift_in_range hr.1 i
  rw [hi] at hh ⊢
  exact (cap_rectangle hr hh he).trans hb

private theorem cap_exp_box {h e : ℝ} (hh : 0 ≤ (11 / 10) * h) (hs : ((11 / 10) * h) / 33 ≤ 1 / 2)
    (he :
      (∑ k ∈ Finset.range 32, ((11 / 10) * h) ^ k / (k.factorial : ℝ)) +
          ((11 / 10) * h) ^ 32 / ((32 : ℕ).factorial : ℝ) * 2 ≤
        e) :
    Real.exp ((11 / 10) * h) ≤ e :=
  (Analysis.exp_le_taylor_add_two_next hh hs).trans he

set_option maxHeartbeats 400000 in
-- The four remaining shifts share the same six numerical moment bounds.
/-- The signed reflection sum on both section 132 intervals costs at most
0.00327, using the common prefix through 322 squared. -/
theorem quarter_aux_reflection_lower_656 (hRH : RiemannHypothesis) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n ∈ Finset.Ioc 0 103684, ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) {r : ℝ}
    (hr : r ∈ Set.Icc 322 328) :
    (-(0.00327 : ℝ)) ≤
      ∑ i, quarterAuxCoeff656 i * quarterAuxReflection656 α r (quarterAuxShift656 i : ℝ) := by
  have href (i : Fin 7) :=
    quarter_aux_reflect_tail_cap_656 hRH (B := 103684) (by norm_num only) (by norm_num only) α hα
      hprefix (by linarith only [hr.1] : 0 < r) (aux_shift_in_range hr.1 i)
  have h₁ :=
    cap_at_shift hr 1 (h := (1 / 10 : ℚ)) (e := 1.116279) (b := 0.002892) (by decide +kernel)
      (by
        apply cap_exp_box <;>
          norm_num only [Rat.cast_div, Rat.cast_ofNat, Finset.sum_range_succ, Finset.sum_range_zero,
            Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [momentBox, Rat.cast_div, Rat.cast_ofNat, Analysis.logPowerTailPoly,
          Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceAdd, Nat.reduceSub,
          Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one])
  have h₃ :=
    cap_at_shift hr 3 (h := (22 / 10 : ℚ)) (e := 11.24586) (b := 0.01888) (by decide +kernel)
      (by
        apply cap_exp_box <;>
          norm_num only [Rat.cast_div, Rat.cast_ofNat, Finset.sum_range_succ, Finset.sum_range_zero,
            Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [momentBox, Rat.cast_div, Rat.cast_ofNat, Analysis.logPowerTailPoly,
          Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceAdd, Nat.reduceSub,
          Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one])
  have h₄ :=
    cap_at_shift hr 4 (h := (43 / 10 : ℚ)) (e := 113.29557) (b := 0.11846) (by decide +kernel)
      (by
        apply cap_exp_box <;>
          norm_num only [Rat.cast_div, Rat.cast_ofNat, Finset.sum_range_succ, Finset.sum_range_zero,
            Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [momentBox, Rat.cast_div, Rat.cast_ofNat, Analysis.logPowerTailPoly,
          Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceAdd, Nat.reduceSub,
          Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one])
  have h₆ :=
    cap_at_shift hr 6 (h := (64 / 10 : ℚ)) (e := 1141.388) (b := 0.709) (by decide +kernel)
      (by
        apply cap_exp_box <;>
          norm_num only [Rat.cast_div, Rat.cast_ofNat, Finset.sum_range_succ, Finset.sum_range_zero,
            Nat.factorial, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [momentBox, Rat.cast_div, Rat.cast_ofNat, Analysis.logPowerTailPoly,
          Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceAdd, Nat.reduceSub,
          Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one])
  have hb :=
    quarter_aux_reflection_caps_656 α hα hr.1 ((href 1).trans h₁) ((href 3).trans h₃)
      ((href 4).trans h₄) ((href 6).trans h₆)
  exact
    (by norm_num only :
          -(0.00327 : ℝ) ≤
            -0.08790103601 * 0.002892 - 0.07976212832 * 0.01888 - 0.012744582 * 0.11846 -
              0.00000000985 * 0.709).trans
      hb

/-- For the three pair characters, agreement on primes up to the squared
radius supplies the shared zero-deficit prefix in the reflection bound. -/
theorem quarter_aux_character_reflect_656 (hRH : RiemannHypothesis) {p q s : ℕ}
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {r : ℝ}
    (hr : r ∈ Set.Icc 322 328) (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (ha : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → a n = 1)
    (hb : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → b n = 1)
    (hc : ∀ n : ℕ, n.Prime → (n : ℝ) ≤ r ^ 2 → c n = 1) :
    let α := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-(0.00327 : ℝ)) ≤
      ∑ i, quarterAuxCoeff656 i * quarterAuxReflection656 α r (quarterAuxShift656 i : ℝ) := by
  intro α
  apply quarter_aux_reflection_lower_656 hRH α _ _ hr
  · intro n
    exact
      ⟨sub_nonneg.mpr (ht n).2, by
        dsimp only [α]; linarith only [(ht n).1]⟩
  intro n hn hΛ
  have hn' : (n : ℝ) ≤ 103684 := by exact_mod_cast (Finset.mem_Ioc.mp hn).2
  have hX : (n : ℝ) ≤ r ^ 2 :=
    hn'.trans
      (by
        rw [show (103684 : ℝ) = 322 ^ 2 by norm_num only]
        exact pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 322) hr.1 2)
  simp only [α, AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero a ha hX hΛ,
    AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero b hb hX hΛ,
    AnalyticNumberTheory.Arithmetic.character_apply_one_of_mangoldt_ne_zero c hc hX hΛ,
    Complex.one_re]
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
