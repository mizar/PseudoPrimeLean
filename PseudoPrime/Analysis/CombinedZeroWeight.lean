/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.LinearCombination

/-! # The combined reciprocal-zero weight and its variation -/

public section

namespace PseudoPrime.Analysis

/-- The signed weight that combines the reciprocal and inverse-square
zero-count remainders at scale `T`. Its zero is at `2 * T`. -/
noncomputable def combinedZeroWeight (T t : ℝ) : ℝ :=
  (2 * T - t) / t ^ 3

/-- The derivative of the combined zero weight, with its sign-changing
factor displayed. Its zero is at `3 * T`. -/
noncomputable def combinedZeroWeightDeriv (T t : ℝ) : ℝ :=
  2 * (t - 3 * T) / t ^ 4

/-- At nonzero height, multiplication by the combined weight is exactly
the difference between the scaled inverse-cube and inverse-square kernels.
This form connects the two Abel summation identities. -/
theorem combinedZeroWeight_mul_eq {T t y : ℝ} (ht : t ≠ 0) :
    combinedZeroWeight T t * y = T * (y * (2 * t⁻¹ ^ 3)) - y / t ^ 2 := by
  unfold combinedZeroWeight
  simp only [div_eq_mul_inv, ← inv_pow]
  have hc := mul_inv_cancel₀ ht
  linear_combination -y * t⁻¹ ^ 2 * hc

/-- Away from zero, the derivative of the combined weight is the displayed
rational function. The explicit form locates the change in monotonicity. -/
theorem combinedZeroWeight_hasDerivAt {T t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (combinedZeroWeight T) (combinedZeroWeightDeriv T t) t := by
  have h :=
    ((hasDerivAt_const t (2 * T)).sub (hasDerivAt_id t)).div ((hasDerivAt_id t).pow 3)
      (pow_ne_zero 3 ht)
  convert h using 1
  · funext x
    rfl
  · dsimp only [combinedZeroWeightDeriv, Pi.pow_apply, Pi.sub_apply, id_eq]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, zero_sub, mul_one]
    apply (div_eq_div_iff (pow_ne_zero 4 ht) (pow_ne_zero 2 (pow_ne_zero 3 ht))).2
    ring

/-- The combined zero weight is continuous away from its pole at zero. -/
theorem combinedZeroWeight_continuousAt {T t : ℝ} (ht : t ≠ 0) :
    ContinuousAt (combinedZeroWeight T) t :=
  (combinedZeroWeight_hasDerivAt ht).continuousAt

/-- At positive ordered endpoints, the combined zero weight is absolutely
continuous on the interval. Its denominator does not vanish there. -/
theorem combinedZeroWeight_absContinuous {T R : ℝ} (hT : 0 < T) (hTR : T ≤ R) :
    AbsolutelyContinuousOnInterval (combinedZeroWeight T) T R := by
  apply ContDiffOn.absolutelyContinuousOnInterval
  rw [Set.uIcc_of_le hTR]
  apply ContDiffOn.div
  · exact (contDiffOn_const.mul contDiffOn_const).sub contDiffOn_id
  · exact contDiffOn_id.pow 3
  · intro t ht
    exact pow_ne_zero 3 (hT.trans_le ht.1).ne'

/-- On a positive ordered interval, the derivative of the combined
weight is continuous. This supplies the integrability required for the
weighted moving-primitive estimate. -/
theorem combinedZeroWeightDeriv_continuousOn {T R : ℝ} (hT : 0 < T) :
    ContinuousOn (combinedZeroWeightDeriv T) (Set.Icc T R) := by
  intro t ht
  have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
  have h : ContinuousAt (combinedZeroWeightDeriv T) t :=
    (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div (continuousAt_id.pow 4)
      (pow_ne_zero 4 ht0)
  exact h.continuousWithinAt

/-- The combined weight is nonincreasing between positive `T` and `3T`.
Only the sign of the numerator matters because the denominator is positive. -/
theorem combinedZeroWeightDeriv_nonpos {T t : ℝ} (ht : 0 < t) (hle : t ≤ 3 * T) :
    combinedZeroWeightDeriv T t ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg
  · have h := sub_nonpos.mpr hle
    nlinarith only [h]
  · exact (pow_pos ht 4).le

/-- The combined weight is nondecreasing beyond `3T` at positive heights.
This identifies the second half of its total variation. -/
theorem combinedZeroWeightDeriv_nonneg {T t : ℝ} (ht : 0 < t) (hle : 3 * T ≤ t) :
    0 ≤ combinedZeroWeightDeriv T t := by
  apply div_nonneg
  · have h := sub_nonneg.mpr hle
    nlinarith only [h]
  · exact (pow_pos ht 4).le

/-- For fixed scale, the combined weight tends to zero at positive
infinity. Rewrite it as a linear combination of inverse powers. -/
theorem tendsto_combinedZeroWeight (T : ℝ) :
    Filter.Tendsto (combinedZeroWeight T) Filter.atTop (nhds 0) := by
  have hi : Filter.Tendsto (fun t : ℝ ↦ t⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have h := ((hi.pow 3).const_mul (2 * T)).sub (hi.pow 2)
  norm_num only at h
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp only [combinedZeroWeight]
  rw [div_eq_mul_inv, ← inv_pow]
  have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hm := congrArg (fun z : ℝ ↦ z * t⁻¹ ^ 2) hcancel
  nlinarith only [hm]

/-- Multiplying the combined weight by the logarithm still tends to zero
at positive infinity. The logarithm is dominated by the inverse squares
and cubes in the weight. -/
theorem tendsto_combinedZeroWeight_mul_log (T : ℝ) :
    Filter.Tendsto (fun t : ℝ ↦ combinedZeroWeight T t * Real.log t) Filter.atTop (nhds 0) := by
  have hlog2 : Filter.Tendsto (fun t : ℝ ↦ Real.log t / t ^ 2) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (2 : ℝ)) (by norm_num only)).tendsto_div_nhds_zero
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] using h
  have hlog3 : Filter.Tendsto (fun t : ℝ ↦ Real.log t / t ^ 3) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (3 : ℝ)) (by norm_num only)).tendsto_div_nhds_zero
    simpa only [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] using h
  have h := (hlog3.const_mul (2 * T)).sub hlog2
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp only [combinedZeroWeight]
  simp only [div_eq_mul_inv, ← inv_pow]
  have hc := mul_inv_cancel₀ ht.ne'
  have hm := congrArg (fun z : ℝ ↦ z * t⁻¹ ^ 2 * Real.log t) hc
  nlinarith only [hm]

/-- At the lower endpoint, the combined weight equals `1 / T²`. -/
theorem combinedZeroWeight_at_scale {T : ℝ} (hT : 0 < T) : combinedZeroWeight T T = 1 / T ^ 2 := by
  dsimp only [combinedZeroWeight]
  apply (div_eq_div_iff (pow_ne_zero 3 hT.ne') (pow_ne_zero 2 hT.ne')).2
  ring

/-- At the derivative's zero, the combined weight equals `-1 / (27 T²)`. -/
theorem combinedZeroWeight_at_triple {T : ℝ} (hT : 0 < T) :
    combinedZeroWeight T (3 * T) = -(1 / (27 * T ^ 2)) := by
  dsimp only [combinedZeroWeight]
  rw [← neg_div]
  apply
    (div_eq_div_iff (pow_ne_zero 3 (mul_ne_zero (by norm_num only) hT.ne'))
        (mul_ne_zero (by norm_num only) (pow_ne_zero 2 hT.ne'))).2
  ring

/-- The total variation on `[T, 3T]` is `28 / (27 T²)`. The derivative
is nonpositive throughout this interval, so the fundamental theorem of
calculus reduces the integral to the two endpoint values. -/
theorem combinedZeroWeight_variation_head {T : ℝ} (hT : 0 < T) :
    (∫ t in T..3 * T, |combinedZeroWeightDeriv T t|) = 28 / (27 * T ^ 2) := by
  have hle : T ≤ 3 * T := by linarith only [hT]
  have hc : ContinuousOn (combinedZeroWeightDeriv T) (Set.Icc T (3 * T)) := by
    intro t ht
    have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
    have h : ContinuousAt (combinedZeroWeightDeriv T) t :=
      (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div (continuousAt_id.pow 4)
        (pow_ne_zero 4 ht0)
    exact h.continuousWithinAt
  have hi : IntervalIntegrable (combinedZeroWeightDeriv T) MeasureTheory.volume T (3 * T) :=
    hc.intervalIntegrable_of_Icc hle
  have hint :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := combinedZeroWeight T) (f' :=
      combinedZeroWeightDeriv T)
      (by
        intro x hx
        rw [Set.uIcc_of_le hle] at hx
        exact combinedZeroWeight_hasDerivAt (hT.trans_le hx.1).ne')
      hi
  have heq :
    (∫ t in T..3 * T, |combinedZeroWeightDeriv T t|) =
      -(∫ t in T..3 * T, combinedZeroWeightDeriv T t) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact abs_of_nonpos (combinedZeroWeightDeriv_nonpos (hT.trans_le ht.1) ht.2)
  rw [heq, hint, combinedZeroWeight_at_triple hT, combinedZeroWeight_at_scale hT]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num only
  ring

/-- Beyond `3T`, the absolute derivative is integrable and its integral
is `1 / (27 T²)`. Monotonicity and the zero limit evaluate the tail. -/
theorem combinedZeroWeight_variation_tail {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t ↦ |combinedZeroWeightDeriv T t|) (Set.Ioi (3 * T)) ∧
      (∫ t in Set.Ioi (3 * T), |combinedZeroWeightDeriv T t|) = 1 / (27 * T ^ 2) := by
  have h3T : 0 < 3 * T := by linarith only [hT]
  have hd :
    ∀ t ∈ Set.Ici (3 * T), HasDerivAt (combinedZeroWeight T) (combinedZeroWeightDeriv T t) t := by
    intro t ht
    exact combinedZeroWeight_hasDerivAt (h3T.trans_le ht).ne'
  have hpos : ∀ t ∈ Set.Ioi (3 * T), 0 ≤ combinedZeroWeightDeriv T t := by
    intro t ht
    exact combinedZeroWeightDeriv_nonneg (h3T.trans ht) ht.le
  have hint :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hd hpos (tendsto_combinedZeroWeight T)
  have heval :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos (tendsto_combinedZeroWeight T)
  have hae :
    (fun t ↦ combinedZeroWeightDeriv T t) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (3 * T))]
      (fun t ↦ |combinedZeroWeightDeriv T t|) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (abs_of_nonneg (hpos t ht)).symm
  constructor
  · exact hint.congr hae
  · rw [← MeasureTheory.integral_congr_ae hae, heval, combinedZeroWeight_at_triple hT]
    ring

/-- The total variation of the combined weight on `[T, ∞)` is exactly
`29 / (27 T²)`. Split at the derivative's sign change `3T` and add the
two rigorously evaluated contributions. -/
theorem combinedZeroWeight_total_variation {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Ioi T, |combinedZeroWeightDeriv T t|) = 29 / (27 * T ^ 2) := by
  have hle : T ≤ 3 * T := by linarith only [hT]
  have hc : ContinuousOn (fun t ↦ |combinedZeroWeightDeriv T t|) (Set.Icc T (3 * T)) := by
    apply ContinuousOn.abs
    intro t ht
    have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
    have h : ContinuousAt (combinedZeroWeightDeriv T) t :=
      (continuousAt_const.mul (continuousAt_id.sub continuousAt_const)).div (continuousAt_id.pow 4)
        (pow_ne_zero 4 ht0)
    exact h.continuousWithinAt
  have hi :
    IntervalIntegrable (fun t ↦ |combinedZeroWeightDeriv T t|) MeasureTheory.volume T (3 * T) :=
    hc.intervalIntegrable_of_Icc hle
  have htail := combinedZeroWeight_variation_tail hT
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hi htail.1
  rw [combinedZeroWeight_variation_head hT, htail.2] at hsplit
  rw [← hsplit]
  simp only [div_eq_mul_inv]
  ring

/-- The absolute derivative of the combined weight is integrable above a
positive scale. A continuous finite part joins the integrable tail. -/
theorem combinedZeroWeight_variation_integrable {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t ↦ |combinedZeroWeightDeriv T t|) (Set.Ioi T) := by
  have hle : T ≤ 3 * T := by linarith only [hT]
  have hd := combinedZeroWeightDeriv_continuousOn (R := 3 * T) hT
  have hi :
    IntervalIntegrable (fun t ↦ |combinedZeroWeightDeriv T t|) MeasureTheory.volume T (3 * T) :=
    hd.abs.intervalIntegrable_of_Icc hle
  have htotal :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hi).union
      (combinedZeroWeight_variation_tail hT).1
  rw [Set.Ioc_union_Ioi_eq_Ioi hle] at htotal
  exact htotal

/-- The signed combined weight divided by the height. It is the kernel
used to integrate a reciprocal bound for the Gamma-phase error. -/
noncomputable def combinedGammaWeight (T t : ℝ) : ℝ :=
  (2 * T - t) / t ^ 4

/-- A primitive of the signed Gamma kernel. It vanishes at infinity and
its derivative changes sign at `2T`. -/
noncomputable def combinedGammaPrimitive (T t : ℝ) : ℝ :=
  (3 * t - 4 * T) / (6 * t ^ 3)

/-- Away from zero, the displayed rational function is a primitive of
the combined Gamma weight. -/
theorem combinedGammaPrimitive_hasDerivAt {T t : ℝ} (ht : t ≠ 0) :
    HasDerivAt (combinedGammaPrimitive T) (combinedGammaWeight T t) t := by
  have h :=
    (((hasDerivAt_id t).const_mul 3).sub_const (4 * T)).div (((hasDerivAt_id t).pow 3).const_mul 6)
      (mul_ne_zero (by norm_num only) (pow_ne_zero 3 ht))
  convert h using 1
  · funext x
    rfl
  · dsimp only [combinedGammaWeight, Pi.mul_apply, Pi.pow_apply, Pi.sub_apply, id_eq]
    norm_num only [Nat.cast_ofNat, Nat.reduceSub, mul_one]
    apply
      (div_eq_div_iff (pow_ne_zero 4 ht)
          (pow_ne_zero 2 (mul_ne_zero (by norm_num only) (pow_ne_zero 3 ht)))).2
    ring

/-- For a positive height, the Gamma kernel is nonnegative up to `2T`. -/
theorem combinedGammaWeight_nonneg {T t : ℝ} (ht : 0 < t) (hle : t ≤ 2 * T) :
    0 ≤ combinedGammaWeight T t := by apply div_nonneg (sub_nonneg.mpr hle) (pow_pos ht 4).le

/-- For a positive height, the Gamma kernel is nonpositive beyond `2T`. -/
theorem combinedGammaWeight_nonpos {T t : ℝ} (ht : 0 < t) (hle : 2 * T ≤ t) :
    combinedGammaWeight T t ≤ 0 := by
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hle) (pow_pos ht 4).le

/-- The Gamma kernel primitive tends to zero at infinity. -/
theorem tendsto_combinedGammaPrimitive (T : ℝ) :
    Filter.Tendsto (combinedGammaPrimitive T) Filter.atTop (nhds 0) := by
  have hi : Filter.Tendsto (fun t : ℝ ↦ t⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have h := ((hi.pow 2).const_mul (1 / 2 : ℝ)).sub ((hi.pow 3).const_mul (2 * T / 3))
  norm_num only at h
  simp only [mul_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with t ht
  dsimp only [combinedGammaPrimitive]
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  have hcancel : t * t⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
  have hm := congrArg (fun z : ℝ ↦ z * t⁻¹ ^ 2) hcancel
  norm_num only
  nlinarith only [hm]

/-- The Gamma kernel primitive at `T` is `-1 / (6 T²)`. -/
theorem combinedGammaPrimitive_at_scale {T : ℝ} (hT : 0 < T) :
    combinedGammaPrimitive T T = -(1 / (6 * T ^ 2)) := by
  dsimp only [combinedGammaPrimitive]
  rw [← neg_div]
  apply
    (div_eq_div_iff (mul_ne_zero (by norm_num only) (pow_ne_zero 3 hT.ne'))
        (mul_ne_zero (by norm_num only) (pow_ne_zero 2 hT.ne'))).2
  ring

/-- The Gamma kernel primitive at its maximum is `1 / (24 T²)`. -/
theorem combinedGammaPrimitive_at_double {T : ℝ} (hT : 0 < T) :
    combinedGammaPrimitive T (2 * T) = 1 / (24 * T ^ 2) := by
  dsimp only [combinedGammaPrimitive]
  apply
    (div_eq_div_iff
        (mul_ne_zero (by norm_num only) (pow_ne_zero 3 (mul_ne_zero (by norm_num only) hT.ne')))
        (mul_ne_zero (by norm_num only) (pow_ne_zero 2 hT.ne'))).2
  ring

/-- The absolute Gamma kernel integrates to `5 / (24 T²)` on `[T, 2T]`.
Its sign is nonnegative on this interval. -/
theorem combinedGammaWeight_integral_head {T : ℝ} (hT : 0 < T) :
    (∫ t in T..2 * T, |combinedGammaWeight T t|) = 5 / (24 * T ^ 2) := by
  have hle : T ≤ 2 * T := by linarith only [hT]
  have hc : ContinuousOn (combinedGammaWeight T) (Set.Icc T (2 * T)) := by
    intro t ht
    have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
    have h : ContinuousAt (combinedGammaWeight T) t :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_id.pow 4) (pow_ne_zero 4 ht0)
    exact h.continuousWithinAt
  have hi : IntervalIntegrable (combinedGammaWeight T) MeasureTheory.volume T (2 * T) :=
    hc.intervalIntegrable_of_Icc hle
  have hint :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := combinedGammaPrimitive T) (f' :=
      combinedGammaWeight T)
      (by
        intro x hx
        rw [Set.uIcc_of_le hle] at hx
        exact combinedGammaPrimitive_hasDerivAt (hT.trans_le hx.1).ne')
      hi
  have heq :
    (∫ t in T..2 * T, |combinedGammaWeight T t|) = ∫ t in T..2 * T, combinedGammaWeight T t := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    exact abs_of_nonneg (combinedGammaWeight_nonneg (hT.trans_le ht.1) ht.2)
  rw [heq, hint, combinedGammaPrimitive_at_double hT, combinedGammaPrimitive_at_scale hT]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num only
  ring

/-- Beyond `2T`, the absolute Gamma kernel is integrable with integral
`1 / (24 T²)`. The primitive is nonincreasing and tends to zero. -/
theorem combinedGammaWeight_integral_tail {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t ↦ |combinedGammaWeight T t|) (Set.Ioi (2 * T)) ∧
      (∫ t in Set.Ioi (2 * T), |combinedGammaWeight T t|) = 1 / (24 * T ^ 2) := by
  have h2T : 0 < 2 * T := by linarith only [hT]
  have hd :
    ∀ t ∈ Set.Ici (2 * T), HasDerivAt (combinedGammaPrimitive T) (combinedGammaWeight T t) t := by
    intro t ht
    exact combinedGammaPrimitive_hasDerivAt (h2T.trans_le ht).ne'
  have hneg : ∀ t ∈ Set.Ioi (2 * T), combinedGammaWeight T t ≤ 0 := by
    intro t ht
    exact combinedGammaWeight_nonpos (h2T.trans ht) ht.le
  have hint :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonpos' hd hneg (tendsto_combinedGammaPrimitive T)
  have heval :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonpos' hd hneg (tendsto_combinedGammaPrimitive T)
  have hae :
    (fun t ↦ -combinedGammaWeight T t) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (2 * T))]
      (fun t ↦ |combinedGammaWeight T t|) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (abs_of_nonpos (hneg t ht)).symm
  constructor
  · exact hint.neg.congr hae
  · rw [← MeasureTheory.integral_congr_ae hae, MeasureTheory.integral_neg, heval,
      combinedGammaPrimitive_at_double hT]
    ring

/-- The absolute Gamma kernel has integral `1 / (4 T²)` above `T`.
Splitting at `2T` preserves its sign on each side. -/
theorem combinedGammaWeight_integral {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Ioi T, |combinedGammaWeight T t|) = 1 / (4 * T ^ 2) := by
  have hle : T ≤ 2 * T := by linarith only [hT]
  have hc : ContinuousOn (fun t ↦ |combinedGammaWeight T t|) (Set.Icc T (2 * T)) := by
    apply ContinuousOn.abs
    intro t ht
    have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
    have h : ContinuousAt (combinedGammaWeight T) t :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_id.pow 4) (pow_ne_zero 4 ht0)
    exact h.continuousWithinAt
  have hi : IntervalIntegrable (fun t ↦ |combinedGammaWeight T t|) MeasureTheory.volume T (2 * T) :=
    hc.intervalIntegrable_of_Icc hle
  have htail := combinedGammaWeight_integral_tail hT
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hi htail.1
  rw [combinedGammaWeight_integral_head hT, htail.2] at hsplit
  rw [← hsplit]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num only
  ring

/-- The absolute Gamma kernel is integrable above a positive scale. The
finite part is continuous and the tail was integrated by monotonicity. -/
theorem combinedGammaWeight_integrable {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t ↦ |combinedGammaWeight T t|) (Set.Ioi T) := by
  have hle : T ≤ 2 * T := by linarith only [hT]
  have hc : ContinuousOn (fun t ↦ |combinedGammaWeight T t|) (Set.Icc T (2 * T)) := by
    apply ContinuousOn.abs
    intro t ht
    have ht0 : t ≠ 0 := (hT.trans_le ht.1).ne'
    have h : ContinuousAt (combinedGammaWeight T) t :=
      (continuousAt_const.sub continuousAt_id).div (continuousAt_id.pow 4) (pow_ne_zero 4 ht0)
    exact h.continuousWithinAt
  have hi : IntervalIntegrable (fun t ↦ |combinedGammaWeight T t|) MeasureTheory.volume T (2 * T) :=
    hc.intervalIntegrable_of_Icc hle
  have htotal :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hi).union
      (combinedGammaWeight_integral_tail hT).1
  rw [Set.Ioc_union_Ioi_eq_Ioi hle] at htotal
  exact htotal

/-- At positive height, dividing the absolute combined weight by height
equals the absolute Gamma kernel. This transfers the reciprocal phase bound. -/
theorem abs_combinedZeroWeight_div {T t : ℝ} (ht : 0 < t) :
    |combinedZeroWeight T t| / t = |combinedGammaWeight T t| := by
  unfold combinedZeroWeight combinedGammaWeight
  rw [abs_div, abs_div, abs_of_pos (pow_pos ht 3), abs_of_pos (pow_pos ht 4)]
  rw [div_div, ← pow_succ]

/-- A primitive of the derivative of the combined zero weight multiplied
by `log (t / T)`. This retains the logarithmic moment in the moving
primitive estimate. -/
noncomputable def combinedZeroLogPrimitive (T t : ℝ) : ℝ :=
  -(Real.log t - Real.log T + 1 / 2) / t ^ 2 + 2 * T * (Real.log t - Real.log T + 1 / 3) / t ^ 3

/-- At positive scale and height, the logarithmic primitive differentiates
to the signed derivative of the combined weight times `log (t / T)`. -/
theorem combinedZeroLogPrimitive_hasDerivAt {T t : ℝ} (ht : 0 < t) (hT : 0 < T) :
    HasDerivAt (combinedZeroLogPrimitive T) (combinedZeroWeightDeriv T t * Real.log (t / T)) t := by
  have hlog := (Real.hasDerivAt_log ht.ne').sub_const (Real.log T)
  have h1 := ((hlog.add_const (1 / 2)).neg).div ((hasDerivAt_id t).pow 2) (pow_ne_zero 2 ht.ne')
  have h2 :=
    (((hlog.add_const (1 / 3)).const_mul (2 * T))).div ((hasDerivAt_id t).pow 3)
      (pow_ne_zero 3 ht.ne')
  have h := h1.add h2
  convert h using 1
  · funext x
    rfl
  · dsimp only [combinedZeroLogPrimitive, combinedZeroWeightDeriv, id_eq, Pi.pow_apply,
      Pi.neg_apply]
    rw [Real.log_div ht.ne' hT.ne']
    norm_num only [Nat.reduceSub, pow_one, zero_mul, sub_zero, mul_one]
    have hc := mul_inv_cancel₀ ht.ne'
    simp only [div_eq_mul_inv, ← inv_pow]
    norm_num only [mul_pow, inv_pow]
    linear_combination
      (6 * T * t⁻¹ ^ 4 * (Real.log t - Real.log T) - 2 * T * t⁻¹ ^ 6 * t ^ 2 +
          t * (6 * (Real.log t - Real.log T) * T * t⁻¹ ^ 5 + t⁻¹ ^ 4)) *
        hc

/-- The logarithmic primitive tends to zero at infinity. Positive powers
of the height dominate the logarithm. -/
theorem tendsto_combinedZeroLogPrimitive (T : ℝ) :
    Filter.Tendsto (combinedZeroLogPrimitive T) Filter.atTop (nhds 0) := by
  have hlog2 : Filter.Tendsto (fun t : ℝ ↦ Real.log t / t ^ 2) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (2 : ℝ)) (by norm_num only)).tendsto_div_nhds_zero
    simpa only [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] using h
  have hlog3 : Filter.Tendsto (fun t : ℝ ↦ Real.log t / t ^ 3) Filter.atTop (nhds 0) := by
    have h := (isLittleO_log_rpow_atTop (r := (3 : ℝ)) (by norm_num only)).tendsto_div_nhds_zero
    simpa only [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num only, Real.rpow_natCast] using h
  have hi : Filter.Tendsto (fun t : ℝ ↦ t⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have ha := hlog2.add ((hi.pow 2).const_mul (-Real.log T + 1 / 2))
  have hb := hlog3.add ((hi.pow 3).const_mul (-Real.log T + 1 / 3))
  have h := ha.neg.add (hb.const_mul (2 * T))
  norm_num only at h
  simp only [mul_zero, add_zero, neg_zero] at h
  apply h.congr
  intro t
  dsimp only [combinedZeroLogPrimitive]
  simp only [div_eq_mul_inv, ← inv_pow]
  ring

/-- The logarithmic primitive at `T` equals `1 / (6 T²)`. -/
theorem combinedZeroLogPrimitive_at_scale {T : ℝ} (hT : 0 < T) :
    combinedZeroLogPrimitive T T = 1 / (6 * T ^ 2) := by
  dsimp only [combinedZeroLogPrimitive]
  simp only [sub_self, zero_add]
  simp only [div_eq_mul_inv, mul_inv_rev, ← inv_pow]
  norm_num only
  have hc := mul_inv_cancel₀ hT.ne'
  linear_combination (2 / 3 : ℝ) * T⁻¹ ^ 2 * hc

/-- The logarithmic primitive at `3T` has an explicit value involving
`log 3`; this is the sign-change point for the weight derivative. -/
theorem combinedZeroLogPrimitive_at_triple {T : ℝ} (hT : 0 < T) :
    combinedZeroLogPrimitive T (3 * T) = -((5 + 6 * Real.log 3) / (162 * T ^ 2)) := by
  dsimp only [combinedZeroLogPrimitive]
  rw [Real.log_mul (by norm_num only : (3 : ℝ) ≠ 0) hT.ne']
  simp only [add_sub_cancel_right, div_eq_mul_inv, mul_inv_rev, mul_pow, ← inv_pow]
  norm_num only
  have hc := mul_inv_cancel₀ hT.ne'
  linear_combination (2 / 27 : ℝ) * (Real.log 3 + 1 / 3) * T⁻¹ ^ 2 * hc

/-- On `[T, 3T]`, the logarithmic variation of the combined weight is
given by the difference of its explicit primitive at the two endpoints. -/
theorem combinedZeroLogVariation_head {T : ℝ} (hT : 0 < T) :
    (∫ t in T..3 * T, |combinedZeroWeightDeriv T t| * Real.log (t / T)) =
      (32 + 6 * Real.log 3) / (162 * T ^ 2) := by
  have hle : T ≤ 3 * T := by linarith only [hT]
  have hd := combinedZeroWeightDeriv_continuousOn (R := 3 * T) hT
  have hl : ContinuousOn (fun t : ℝ ↦ Real.log (t / T)) (Set.Icc T (3 * T)) := by
    intro t ht
    have h : ContinuousAt (fun x : ℝ ↦ Real.log (x / T)) t :=
      ContinuousAt.comp (f := fun x : ℝ ↦ x / T)
        (Real.continuousAt_log (div_ne_zero (hT.trans_le ht.1).ne' hT.ne'))
        (continuousAt_id.div_const T)
    exact h.continuousWithinAt
  have hi :
    IntervalIntegrable (fun t ↦ combinedZeroWeightDeriv T t * Real.log (t / T)) MeasureTheory.volume
      T (3 * T) :=
    (hd.mul hl).intervalIntegrable_of_Icc hle
  have hint :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := combinedZeroLogPrimitive T) (f' := fun t ↦
      combinedZeroWeightDeriv T t * Real.log (t / T))
      (by
        intro t ht
        rw [Set.uIcc_of_le hle] at ht
        exact combinedZeroLogPrimitive_hasDerivAt (hT.trans_le ht.1) hT)
      hi
  have heq :
    (∫ t in T..3 * T, |combinedZeroWeightDeriv T t| * Real.log (t / T)) =
      -(∫ t in T..3 * T, combinedZeroWeightDeriv T t * Real.log (t / T)) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hle] at ht
    change
      |combinedZeroWeightDeriv T t| * Real.log (t / T) =
        -(combinedZeroWeightDeriv T t * Real.log (t / T))
    rw [abs_of_nonpos (combinedZeroWeightDeriv_nonpos (hT.trans_le ht.1) ht.2), neg_mul]
  rw [heq, hint, combinedZeroLogPrimitive_at_triple hT, combinedZeroLogPrimitive_at_scale hT]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num only
  ring

/-- Beyond `3T`, the logarithmic variation kernel is nonnegative,
integrable and has the stated integral. Its primitive tends to zero. -/
theorem combinedZeroLogVariation_tail {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t ↦ |combinedZeroWeightDeriv T t| * Real.log (t / T))
        (Set.Ioi (3 * T)) ∧
      (∫ t in Set.Ioi (3 * T), |combinedZeroWeightDeriv T t| * Real.log (t / T)) =
        (5 + 6 * Real.log 3) / (162 * T ^ 2) := by
  have h3T : 0 < 3 * T := by linarith only [hT]
  have hd :
    ∀ t ∈ Set.Ici (3 * T),
      HasDerivAt (combinedZeroLogPrimitive T) (combinedZeroWeightDeriv T t * Real.log (t / T))
        t := by
    intro t ht
    exact combinedZeroLogPrimitive_hasDerivAt (h3T.trans_le ht) hT
  have hpos : ∀ t ∈ Set.Ioi (3 * T), 0 ≤ combinedZeroWeightDeriv T t * Real.log (t / T) := by
    intro t ht
    change 3 * T < t at ht
    have ht0 : 0 < t := h3T.trans ht
    have htT : T ≤ t := by linarith only [hT, ht]
    exact
      mul_nonneg (combinedZeroWeightDeriv_nonneg ht0 ht.le)
        (Real.log_nonneg ((one_le_div hT).2 htT))
  have hint :=
    MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' hd hpos (tendsto_combinedZeroLogPrimitive T)
  have heval :=
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' hd hpos (tendsto_combinedZeroLogPrimitive T)
  have hae :
    (fun t ↦
        combinedZeroWeightDeriv T t *
          Real.log (t / T)) =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (3 * T))]
      (fun t ↦ |combinedZeroWeightDeriv T t| * Real.log (t / T)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := h3T.trans ht
    rw [abs_of_nonneg (combinedZeroWeightDeriv_nonneg ht0 ht.le)]
  constructor
  · exact hint.congr hae
  · rw [← MeasureTheory.integral_congr_ae hae, heval, combinedZeroLogPrimitive_at_triple hT]
    ring

/-- The logarithmic moment of the combined weight's variation equals
`(37 / 162 + 2 log 3 / 27) / T²`. The derivative changes sign at `3T`,
so its two positive contributions are evaluated separately. -/
theorem combinedZeroLogVariation_integral {T : ℝ} (hT : 0 < T) :
    (∫ t in Set.Ioi T, |combinedZeroWeightDeriv T t| * Real.log (t / T)) =
      (37 / 162 + 2 * Real.log 3 / 27) / T ^ 2 := by
  have hle : T ≤ 3 * T := by linarith only [hT]
  have hd := combinedZeroWeightDeriv_continuousOn (R := 3 * T) hT
  have hl : ContinuousOn (fun t : ℝ ↦ Real.log (t / T)) (Set.Icc T (3 * T)) := by
    intro t ht
    have h : ContinuousAt (fun x : ℝ ↦ Real.log (x / T)) t :=
      ContinuousAt.comp (f := fun x : ℝ ↦ x / T)
        (Real.continuousAt_log (div_ne_zero (hT.trans_le ht.1).ne' hT.ne'))
        (continuousAt_id.div_const T)
    exact h.continuousWithinAt
  have hi :
    IntervalIntegrable (fun t ↦ |combinedZeroWeightDeriv T t| * Real.log (t / T))
      MeasureTheory.volume T (3 * T) :=
    (hd.abs.mul hl).intervalIntegrable_of_Icc hle
  have htail := combinedZeroLogVariation_tail hT
  have hsplit := intervalIntegral.integral_interval_add_Ioi' hi htail.1
  rw [combinedZeroLogVariation_head hT, htail.2] at hsplit
  rw [← hsplit]
  simp only [div_eq_mul_inv, mul_inv_rev]
  norm_num only
  ring

/-- The logarithmic variation kernel is integrable above a positive
scale. The finite part is continuous and the nonnegative tail has an
explicit integrable primitive. -/
theorem combinedZeroLogVariation_integrable {T : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t ↦ |combinedZeroWeightDeriv T t| * Real.log (t / T))
      (Set.Ioi T) := by
  have hle : T ≤ 3 * T := by linarith only [hT]
  have hd := combinedZeroWeightDeriv_continuousOn (R := 3 * T) hT
  have hl : ContinuousOn (fun t : ℝ ↦ Real.log (t / T)) (Set.Icc T (3 * T)) := by
    intro t ht
    have h : ContinuousAt (fun x : ℝ ↦ Real.log (x / T)) t :=
      ContinuousAt.comp (f := fun x : ℝ ↦ x / T)
        (Real.continuousAt_log (div_ne_zero (hT.trans_le ht.1).ne' hT.ne'))
        (continuousAt_id.div_const T)
    exact h.continuousWithinAt
  have hi :
    IntervalIntegrable (fun t ↦ |combinedZeroWeightDeriv T t| * Real.log (t / T))
      MeasureTheory.volume T (3 * T) :=
    (hd.abs.mul hl).intervalIntegrable_of_Icc hle
  have htotal :=
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp hi).union
      (combinedZeroLogVariation_tail hT).1
  rw [Set.Ioc_union_Ioi_eq_Ioi hle] at htotal
  exact htotal

/-- A nonnegative affine logarithmic budget integrated against the
combined weight's absolute derivative has the exact value given by the
two variation constants. This is the majorant for the moving primitive. -/
theorem combinedZeroWeight_budget_integral {T A B : ℝ} (hT : 0 < T) :
    MeasureTheory.IntegrableOn (fun t ↦ |combinedZeroWeightDeriv T t| * (A + B * Real.log (t / T)))
        (Set.Ioi T) ∧
      (∫ t in Set.Ioi T, |combinedZeroWeightDeriv T t| * (A + B * Real.log (t / T))) =
        ((29 / 27 : ℝ) * A + B * (37 / 162 + 2 * Real.log 3 / 27)) / T ^ 2 := by
  have h1 := (combinedZeroWeight_variation_integrable hT).const_mul A
  have h2 := (combinedZeroLogVariation_integrable hT).const_mul B
  have heq :
    (fun t : ℝ ↦ |combinedZeroWeightDeriv T t| * (A + B * Real.log (t / T))) =
      (fun t : ℝ ↦
        A * |combinedZeroWeightDeriv T t| +
          B * (|combinedZeroWeightDeriv T t| * Real.log (t / T))) := by
    funext t
    ring
  rw [heq]
  constructor
  · exact h1.add h2
  · rw [MeasureTheory.integral_add h1 h2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, combinedZeroWeight_total_variation hT,
      combinedZeroLogVariation_integral hT]
    simp only [div_eq_mul_inv]
    ring

/-- On a finite interval `[T,R]`, a nonnegative logarithmic budget against
the combined weight's variation is bounded by its evaluated full tail. -/
theorem combinedZeroWeight_budget_interval {T R A B : ℝ} (hT : 0 < T) (hTR : T ≤ R) (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    (∫ t in T..R, |combinedZeroWeightDeriv T t| * (A + B * Real.log (t / T))) ≤
      ((29 / 27 : ℝ) * A + B * (37 / 162 + 2 * Real.log 3 / 27)) / T ^ 2 := by
  have hbudget := combinedZeroWeight_budget_integral (A := A) (B := B) hT
  have hnon :
    ∀ᵐ t : ℝ ∂(MeasureTheory.volume.restrict (Set.Ioi T)),
      0 ≤ |combinedZeroWeightDeriv T t| * (A + B * Real.log (t / T)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hlog : 0 ≤ Real.log (t / T) := Real.log_nonneg ((one_le_div hT).2 ht.le)
    exact mul_nonneg (abs_nonneg _) (add_nonneg hA (mul_nonneg hB hlog))
  have hsub : Set.Ioc T R ≤ᵐ[MeasureTheory.volume] Set.Ioi T :=
    Filter.Eventually.of_forall (fun _ ht ↦ ht.1)
  have h := MeasureTheory.setIntegral_mono_set hbudget.1 hnon hsub
  rw [← intervalIntegral.integral_of_le hTR, hbudget.2] at h
  exact h

end PseudoPrime.Analysis
