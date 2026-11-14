/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCombinedIntegratedRH
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTail
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountTailError
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountIntegral
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountInverseSquare
import PseudoPrime.Analysis.LogLinearIntegral
import PseudoPrime.Analysis.LogBudgetIntegral
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountBudgetRH
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroReciprocalFrom40
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.LinearCombination

/-! # Abel identities for the combined zero-count weight -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `1 < T ≤ R`, integrating the zero count against the combined
weight equals the finite inverse-square tail minus the reciprocal-sum
increment, with the exact count at `R` retained. The count at `T` cancels
without any assumption about zeros at either endpoint. -/
theorem combined_weight_zeroCount_abel {T R : ℝ} (hT : 1 < T) (hTR : T ≤ R) :
    (∫ t in T..R, Analysis.combinedZeroWeight T t * zeroCount t) =
      T *
            (∑ ρ ∈ (zerosUpTo R).filter (fun ρ ↦ T < |ρ.im|),
              (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) -
          (zeroReciprocalSum R - zeroReciprocalSum T) +
        zeroCount R * (1 / R - T / R ^ 2) := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hi2 := zeroCount_invSq_integrable hT0 hTR
  have hi3 := zeroCount_invCube_integrable hT0 hTR
  have hcong :
    (∫ t in T..R, Analysis.combinedZeroWeight T t * zeroCount t) =
      ∫ t in T..R, T * (zeroCount t * (2 * t⁻¹ ^ 3)) - zeroCount t / t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hTR] at ht
    exact Analysis.combinedZeroWeight_mul_eq (hT0.trans_le ht.1).ne'
  rw [hcong, intervalIntegral.integral_sub (hi3.const_mul T) hi2,
    intervalIntegral.integral_const_mul]
  have hs := zeroReciprocal_abel hT hTR
  have ht := finite_tail_abel hT hTR
  have hc := mul_inv_cancel₀ hT0.ne'
  simp only [div_eq_mul_inv, ← inv_pow] at hs ht ⊢
  linear_combination hs - T * ht + (zeroCount T * T⁻¹) * hc

/-- On a positive ordered interval, the combined weight integrates the
generic logarithmic zero-count main term as the difference of its explicit
inverse-square and inverse-cube primitives. -/
theorem combined_weight_main_integral {T R k c d : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    (∫ t in T..R, Analysis.combinedZeroWeight T t * (k * t * (Real.log t - c - 1) + d)) =
      T *
          (((-2 * k * (Real.log R - c) / R - d / R ^ 2) -
            (-2 * k * (Real.log T - c) / T - d / T ^ 2))) -
        ((k / 2 * (Real.log R - c) ^ 2 - k * (Real.log R - c) - d / R) -
          (k / 2 * (Real.log T - c) ^ 2 - k * (Real.log T - c) - d / T)) := by
  let M : ℝ → ℝ := fun t ↦ k * t * (Real.log t - c - 1) + d
  have hM : ContinuousOn M (Set.Icc T R) := by
    intro t ht
    have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have h2 : IntervalIntegrable (fun t ↦ M t / t ^ 2) MeasureTheory.volume T R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTR
    intro t ht
    have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
    exact (hM t ht).div (continuousAt_id.pow 2).continuousWithinAt (pow_ne_zero 2 ht0)
  have h3 : IntervalIntegrable (fun t ↦ M t * (2 * t⁻¹ ^ 3)) MeasureTheory.volume T R := by
    apply ContinuousOn.intervalIntegrable_of_Icc hTR
    intro t ht
    have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
    exact
      (hM t ht).mul (continuousAt_const.mul ((continuousAt_id.inv₀ ht0).pow 3)).continuousWithinAt
  have heq :
    (∫ t in T..R, Analysis.combinedZeroWeight T t * M t) =
      ∫ t in T..R, T * (M t * (2 * t⁻¹ ^ 3)) - M t / t ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hTR] at ht
    exact Analysis.combinedZeroWeight_mul_eq (hT.trans_le ht.1).ne'
  rw [heq, intervalIntegral.integral_sub (h3.const_mul T) h2, intervalIntegral.integral_const_mul]
  change
    T * (∫ t in T..R, (k * t * (Real.log t - c - 1) + d) * (2 * t⁻¹ ^ 3)) -
        (∫ t in T..R, (k * t * (Real.log t - c - 1) + d) / t ^ 2) =
      _
  rw [Analysis.integral_log_main_inv_cube hT hTR, Analysis.integral_log_linear_div_sq hT hTR]

/-- For `1 < T ≤ R`, the reciprocal sum at `T` and the finite inverse-square
tail differ from the combined logarithmic main term by the reciprocal sum at
`R`, the weighted zero-count error integral, and two explicit upper-endpoint
terms. All endpoint zero multiplicities are retained by the Abel identities. -/
theorem combined_zero_finite_identity {T R : ℝ} (hT : 1 < T) (hTR : T ≤ R) :
    zeroReciprocalSum T +
          T *
            (∑ ρ ∈ (zerosUpTo R).filter (fun ρ ↦ T < |ρ.im|),
              (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) -
        ((Real.log T - Real.log (2 * Real.pi)) ^ 2 + 2 * (Real.log T - Real.log (2 * Real.pi)) +
            2) /
          (2 * Real.pi) =
      zeroReciprocalSum R - (Real.log R - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi) +
          (∫ t in T..R, Analysis.combinedZeroWeight T t * zeroCountError t) -
        T * (Real.log R - Real.log (2 * Real.pi) + 1) / (Real.pi * R) -
        zeroCountError R * (1 / R - T / R ^ 2) := by
  have hT0 : 0 < T := zero_lt_one.trans hT
  have hR0 : 0 < R := hT0.trans_le hTR
  let M : ℝ → ℝ := fun t ↦ (1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4
  have hw := (Analysis.combinedZeroWeight_absContinuous hT0 hTR).continuousOn
  have hn :
    IntervalIntegrable (fun t ↦ Analysis.combinedZeroWeight T t * zeroCount t) MeasureTheory.volume
      T R :=
    (zeroCount_integrable hT0.le hTR).continuousOn_mul hw
  have hMcont : ContinuousOn M (Set.uIcc T R) := by
    rw [Set.uIcc_of_le hTR]
    intro t ht
    have ht0 : t ≠ 0 := (hT0.trans_le ht.1).ne'
    exact
      (((continuousAt_const.mul continuousAt_id).mul
              (((Real.continuousAt_log ht0).sub continuousAt_const).sub continuousAt_const)).add
          continuousAt_const).continuousWithinAt
  have hm :
    IntervalIntegrable (fun t ↦ Analysis.combinedZeroWeight T t * M t) MeasureTheory.volume T R :=
    (hw.mul hMcont).intervalIntegrable
  have hq :
    (∫ t in T..R, Analysis.combinedZeroWeight T t * zeroCountError t) =
      (∫ t in T..R, Analysis.combinedZeroWeight T t * zeroCount t) -
        ∫ t in T..R, Analysis.combinedZeroWeight T t * M t := by
    rw [← intervalIntegral.integral_sub hn hm]
    apply intervalIntegral.integral_congr
    intro t ht
    change
      Analysis.combinedZeroWeight T t * (zeroCount t - M t) =
        Analysis.combinedZeroWeight T t * zeroCount t - Analysis.combinedZeroWeight T t * M t
    ring
  have hnval := combined_weight_zeroCount_abel hT hTR
  have hmval :=
    combined_weight_main_integral (k := 1 / Real.pi) (c := Real.log (2 * Real.pi)) (d := 7 / 4) hT0
      hTR
  change (∫ t in T..R, Analysis.combinedZeroWeight T t * M t) = _ at hmval
  rw [hnval, hmval] at hq
  have hqR : zeroCountError R = zeroCount R - M R := rfl
  have hcT := mul_inv_cancel₀ hT0.ne'
  have hcR := mul_inv_cancel₀ hR0.ne'
  rw [hqR]
  dsimp only [M] at hq ⊢
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow] at hq ⊢
  linear_combination
    -hq + (2 * Real.pi⁻¹ * (Real.log T - Real.log (2 * Real.pi)) + (7 / 4 : ℝ) * T⁻¹) * hcT +
      (Real.pi⁻¹ * (Real.log R - Real.log (2 * Real.pi) - 1) * (T * R⁻¹ - 1)) * hcR

/-- Under RH, the zero-count error divided by height tends to zero at
infinity. The explicit logarithmic pointwise count bound supplies an
integrable-order decay without requiring a zero table. -/
theorem zeroCountError_div_tendsto (hRH : RiemannHypothesis) :
    Filter.Tendsto (fun R : ℝ ↦ zeroCountError R / R) Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun R : ℝ ↦ Real.log R / R) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num only)).tendsto_div_nhds_zero
    simpa only [Real.rpow_one] using h
  have hi : Filter.Tendsto (fun R : ℝ ↦ R⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hb :=
    ((hlog.const_mul (3 / 4 : ℝ)).add (hi.const_mul (16 / 5 : ℝ))).add
      ((hi.pow 2).const_mul (2 / 5 : ℝ))
  norm_num only at hb
  apply squeeze_zero_norm' _ hb
  filter_upwards [Filter.eventually_ge_atTop (100 : ℝ)] with R hR
  have hR0 : 0 < R := by linarith only [hR]
  have hbase : 2 * Real.pi * Real.exp 1 ≤ R := by
    have hp :=
      mul_le_mul Real.pi_lt_four.le Real.exp_one_lt_three.le (Real.exp_pos 1).le
        (by norm_num only : (0 : ℝ) ≤ 4)
    nlinarith only [hp, hR]
  have hQ := zero_count_budget_of_RH hRH hbase
  change |zeroCountError R| ≤ _ at hQ
  have hdiv := div_le_div_of_nonneg_right hQ hR0.le
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hR0]
  convert hdiv using 1
  simp only [div_eq_mul_inv]
  ring

/-- Under RH, the upper count-error endpoint in the combined finite Abel
identity vanishes at infinity. -/
theorem combined_zero_error_endpoint_tendsto (hRH : RiemannHypothesis) (T : ℝ) :
    Filter.Tendsto (fun R : ℝ ↦ zeroCountError R * (1 / R - T / R ^ 2)) Filter.atTop (nhds 0) := by
  have hi : Filter.Tendsto (fun R : ℝ ↦ R⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have h := (zeroCountError_div_tendsto hRH).mul ((hi.const_mul T).const_sub (1 : ℝ))
  simp only [mul_zero, sub_zero, zero_mul] at h
  apply h.congr
  intro R
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- For fixed `T`, the upper logarithmic endpoint in the combined finite
Abel identity vanishes at infinity. -/
theorem combined_zero_main_endpoint_tendsto (T : ℝ) :
    Filter.Tendsto (fun R : ℝ ↦ T * (Real.log R - Real.log (2 * Real.pi) + 1) / (Real.pi * R))
      Filter.atTop (nhds 0) := by
  have hlog : Filter.Tendsto (fun R : ℝ ↦ Real.log R / R) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num only)).tendsto_div_nhds_zero
    simpa only [Real.rpow_one] using h
  have hi : Filter.Tendsto (fun R : ℝ ↦ R⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have h := (hlog.add (hi.const_mul (1 - Real.log (2 * Real.pi)))).const_mul (T / Real.pi)
  simp only [mul_zero, add_zero] at h
  apply h.congr
  intro R
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- Under RH, the reciprocal zero sum minus its quadratic logarithmic main
term has a finite limit. For each `T ≥ 100`, the combined reciprocal and
inverse-square zero sum differs from that limit plus its main term by at
most the explicit integrated-count remainder. The constant is obtained
from the finite Abel identity and is not assumed. -/
theorem combined_zero_exists_constant (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    ∃ h : ℝ,
      Filter.Tendsto
          (fun R : ℝ ↦
            zeroReciprocalSum R - (Real.log R - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi))
          Filter.atTop (nhds h) ∧
        |zeroReciprocalSum T + T * ordinateTail T -
              ((Real.log T - Real.log (2 * Real.pi)) ^ 2 +
                  2 * (Real.log T - Real.log (2 * Real.pi)) +
                  2) /
                (2 * Real.pi) -
              h| ≤
          ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
              (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
              1 / 10) /
            T ^ 2 := by
  obtain ⟨I, hI, hIb⟩ := combined_weight_error_remainder hRH hT
  let M : ℝ :=
    ((Real.log T - Real.log (2 * Real.pi)) ^ 2 + 2 * (Real.log T - Real.log (2 * Real.pi)) + 2) /
      (2 * Real.pi)
  let h : ℝ := zeroReciprocalSum T + T * ordinateTail T - M - I
  refine ⟨h, ?_, ?_⟩
  · have htail := (ordinateTail_limit hRH T).const_mul T
    have hlim :=
      ((((htail.const_add (zeroReciprocalSum T)).sub_const M).sub hI).add
            (combined_zero_main_endpoint_tendsto T)).add
        (combined_zero_error_endpoint_tendsto hRH T)
    simp only [add_zero] at hlim
    apply hlim.congr'
    filter_upwards [Filter.eventually_ge_atTop T] with R hR
    have he := combined_zero_finite_identity (by linarith only [hT] : 1 < T) hR
    change
      zeroReciprocalSum T +
            T *
              (∑ ρ ∈ (zerosUpTo R).filter (fun ρ ↦ T < |ρ.im|),
                (riemannZetaZeroMultiplicity ρ : ℝ) / |ρ.im| ^ 2) -
          M =
        _ at he
    linarith only [he]
  · change |zeroReciprocalSum T + T * ordinateTail T - M - h| ≤ _
    have he : zeroReciprocalSum T + T * ordinateTail T - M - h = I := by
      dsimp only [h]
      ring
    rw [he]
    exact hIb

/-- The limiting constant in the reciprocal zero sum after subtracting its
quadratic logarithmic main term. Under RH the limit exists, as proved by
`combined_zero_exists_constant`; outside RH this definition is totalized. -/
@[expose]
noncomputable def zeroReciprocalConstant : ℝ :=
  Filter.limUnder Filter.atTop
    (fun R : ℝ ↦ zeroReciprocalSum R - (Real.log R - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi))

/-- Under RH, the reciprocal zero sum with its quadratic logarithmic main
term removed converges to `zeroReciprocalConstant`. -/
theorem zeroReciprocalConstant_tendsto (hRH : RiemannHypothesis) :
    Filter.Tendsto
      (fun R : ℝ ↦ zeroReciprocalSum R - (Real.log R - Real.log (2 * Real.pi)) ^ 2 / (2 * Real.pi))
      Filter.atTop (nhds zeroReciprocalConstant) := by
  obtain ⟨h, hh, _⟩ := combined_zero_exists_constant hRH (T := 100) (by norm_num only)
  have he : zeroReciprocalConstant = h := hh.limUnder_eq
  rw [he]
  exact hh

/-- Under RH, the reciprocal-sum limiting constant is at most `2 / 5`.
This follows from the existing table-free height-40 bound by taking its
limit; it does not use a low-zero enumeration. -/
theorem zeroReciprocalConstant_le_two_fifths (hRH : RiemannHypothesis) :
    zeroReciprocalConstant ≤ 2 / 5 := by
  apply le_of_tendsto (zeroReciprocalConstant_tendsto hRH)
  filter_upwards [Filter.eventually_ge_atTop (40 : ℝ)] with R hR
  have hR0 : 0 < R := by linarith only [hR]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num only) Real.pi_ne_zero
  have h := zeroReciprocal_bound_two_fifths hRH hR
  rw [Real.log_div hR0.ne' hp] at h
  linarith only [h]

/-- Under RH and for `T ≥ 100`, the combined reciprocal zero sum and
inverse-square tail differ from the explicit quadratic main term plus the
same limiting constant by at most the integrated-count remainder. -/
theorem combined_zero_constant_error (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    |zeroReciprocalSum T + T * ordinateTail T -
          ((Real.log T - Real.log (2 * Real.pi)) ^ 2 + 2 * (Real.log T - Real.log (2 * Real.pi)) +
              2) /
            (2 * Real.pi) -
          zeroReciprocalConstant| ≤
      ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
          (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
          1 / 10) /
        T ^ 2 := by
  obtain ⟨h, hh, hb⟩ := combined_zero_exists_constant hRH hT
  have he : zeroReciprocalConstant = h := hh.limUnder_eq
  rw [he]
  exact hb

/-- Under RH and for `T ≥ 100`, the combined reciprocal zero sum and
inverse-square tail are bounded by their logarithmic main term, the
reciprocal-sum limiting constant, and the explicit integrated remainder. -/
theorem combined_zero_integrated_bound (hRH : RiemannHypothesis) {T : ℝ} (hT : 100 ≤ T) :
    zeroReciprocalSum T + T * ordinateTail T ≤
      ((Real.log (T / (2 * Real.pi))) ^ 2 + 2 * Real.log (T / (2 * Real.pi)) + 2) / (2 * Real.pi) +
        zeroReciprocalConstant +
        ((29 / 27 : ℝ) * (16 + (7 / 5 : ℝ) * Real.log T) +
            (7 / 5 : ℝ) * (37 / 162 + 2 * Real.log 3 / 27) +
            1 / 10) /
          T ^ 2 := by
  have hT0 : 0 < T := by linarith only [hT]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := mul_ne_zero (by norm_num only) Real.pi_ne_zero
  rw [Real.log_div hT0.ne' hp]
  have h := (abs_le.mp (combined_zero_constant_error hRH hT)).2
  linarith only [h]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
