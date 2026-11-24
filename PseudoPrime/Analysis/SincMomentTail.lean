/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.MeanValue
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds
import all PseudoPrime.Analysis.SincMomentDerivatives
public import PseudoPrime.Analysis.SincMomentDerivatives
import all PseudoPrime.Analysis.SineMajorant

/-! # Oscillatory tail estimates for the sinc moments -/

public section

namespace PseudoPrime.Analysis

/-- A decreasing weight with nonnegative terminal value bounds a cosine integral
at positive frequency by twice its initial weight divided by the frequency.
The second mean value theorem reduces the integral to a difference of sines. -/
theorem weighted_cos_integral_le {a b k : ℝ} {w : ℝ → ℝ} (hab : a ≤ b) (hk : 0 < k) (hw : 0 ≤ w b)
    (hm : AntitoneOn w (Set.Icc a b)) : |∫ x in a..b, w x * Real.cos (k * x)| ≤ 2 * w a / k := by
  have hc : Continuous (fun x : ℝ ↦ Real.cos (k * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  obtain ⟨z, _, hz⟩ :=
    exists_eq_const_mul_intervalIntegral_of_nonneg_of_antitoneOn hab hw hm
      (hc.intervalIntegrable a b)
  have ha := hw.trans (hm (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hab)
  rw [hz, intervalIntegral.integral_comp_mul_left Real.cos hk.ne', integral_cos, smul_eq_mul,
    abs_mul, abs_of_nonneg ha, abs_mul, abs_of_pos (inv_pos.mpr hk)]
  have hs : |Real.sin (k * z) - Real.sin (k * a)| ≤ 2 :=
    abs_le.mpr
      ⟨by linarith only [Real.neg_one_le_sin (k * z), Real.sin_le_one (k * a)], by
        linarith only [Real.sin_le_one (k * z), Real.neg_one_le_sin (k * a)]⟩
  calc
    _ ≤ w a * (k⁻¹ * 2) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr hk.le)) ha
    _ = _ := by ring

/-- Specializing to the reciprocal-square weight controls each plain-moment
harmonic uniformly in the finite upper limit. -/
theorem plain_cos_tail_le {b k : ℝ} (hb : 16 ≤ b) (hk : 0 < k) :
    |∫ x in (16 : ℝ)..b, (1 / x ^ 2) * Real.cos (k * x)| ≤ 2 * (1 / 16 ^ 2) / k := by
  apply
    weighted_cos_integral_le (w := fun x ↦ 1 / x ^ 2) hb hk (div_nonneg zero_le_one (sq_nonneg _))
  intro x hx y _ hxy
  have hp : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 16) hx.1
  exact one_div_le_one_div_of_le (sq_pos_of_pos hp) (pow_le_pow_left₀ hp.le hxy 2)

/-- Above sixteen the derivative of the logarithmic weight is negative. -/
private theorem logWeight_antitone : AntitoneOn (fun x : ℝ ↦ Real.log x / x ^ 2) (Set.Ici 16) := by
  have hd {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun z : ℝ ↦ Real.log z / z ^ 2) ((-2) * (Real.log x - 1 / 2) / x ^ 3) x := by
    convert hasDerivAt_momentWeightTerm 0 1 0 hx using 1 <;>
      norm_num only [momentWeightTerm, momentLogShift, Nat.factorial, Rat.cast_add, Rat.cast_div,
        Rat.cast_natCast, Rat.cast_one, Rat.cast_zero, Rat.cast_ofNat, pow_zero, pow_one, one_mul,
        add_zero, zero_add, sub_zero, mul_one]
    funext z
    norm_num only [momentWeightTerm, momentLogShift, Nat.factorial, Rat.cast_zero, pow_zero,
      one_mul, add_zero, sub_zero, Nat.cast_one]
  apply StrictAntiOn.antitoneOn
  apply strictAntiOn_of_deriv_neg (convex_Ici 16)
  · intro x hx
    have hp := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 16) hx
    exact (hd hp).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hp := lt_trans (by norm_num only : (0 : ℝ) < 16) hx
    rw [(hd hp).deriv]
    have hl :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 2)
        ((by norm_num only : (2 : ℝ) ≤ 16).trans hx.le)
    exact
      div_neg_of_neg_of_pos
        (mul_neg_of_neg_of_pos (by norm_num only) (by linarith only [hl, Real.log_two_gt_d9]))
        (pow_pos hp 3)

/-- The logarithmic moment has the same uniform oscillatory bound, multiplied by log 16. -/
theorem log_cos_tail_le {b k : ℝ} (hb : 16 ≤ b) (hk : 0 < k) :
    |∫ x in (16 : ℝ)..b, (Real.log x / x ^ 2) * Real.cos (k * x)| ≤
      2 * (Real.log 16 / 16 ^ 2) / k := by
  apply
    weighted_cos_integral_le (w := fun x ↦ Real.log x / x ^ 2) hb hk
      (div_nonneg (Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 16).trans hb)) (sq_nonneg _))
  exact logWeight_antitone.mono (fun _ hx ↦ hx.1)

/-- A uniform finite cosine bound passes to the improper integral when the weight
is absolutely integrable. The cosine factor has absolute value at most one. -/
theorem cos_tail_limit_le {w : ℝ → ℝ} {a k C : ℝ} (hw : MeasureTheory.IntegrableOn w (Set.Ioi a))
    (h : ∀ b ≥ a, |∫ x in a..b, w x * Real.cos (k * x)| ≤ C) :
    |∫ x in Set.Ioi a, w x * Real.cos (k * x)| ≤ C := by
  have hc : Continuous (fun x : ℝ ↦ Real.cos (k * x)) :=
    Real.continuous_cos.comp (continuous_const.mul continuous_id)
  have hi :=
    hw.mul_bdd hc.aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ (Real.abs_cos_le_one (k * x) : ‖Real.cos (k * x)‖ ≤ 1)))
  exact
    le_of_tendsto (MeasureTheory.intervalIntegral_tendsto_integral_Ioi a hi Filter.tendsto_id).abs
      ((Filter.eventually_ge_atTop a).mono (fun b hb ↦ h b hb))

/-- The plain reciprocal-square weight is integrable above sixteen. -/
theorem plainWeight_integrable :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ 1 / x ^ 2) (Set.Ioi 16) := by
  apply
    (integrableOn_Ioi_rpow_of_lt (by norm_num only : (-2 : ℝ) < -1)
          (by norm_num only : (0 : ℝ) < 16)).congr_fun
      _ measurableSet_Ioi
  intro x hx
  change x ^ (-(2 : ℝ)) = 1 / x ^ 2
  rw [Real.rpow_neg (by linarith only [hx.out] : 0 ≤ x), one_div]
  norm_num only [Real.rpow_ofNat]

/-- The plain reciprocal-square harmonic has the same bound over the entire tail. -/
theorem plain_cos_Ioi_le {k : ℝ} (hk : 0 < k) :
    |∫ x in Set.Ioi (16 : ℝ), (1 / x ^ 2) * Real.cos (k * x)| ≤ 2 * (1 / 16 ^ 2) / k :=
  cos_tail_limit_le plainWeight_integrable (fun _ hb ↦ plain_cos_tail_le hb hk)

private theorem logTail_derivative (x : ℝ) (hx : x ∈ Set.Ici (16 : ℝ)) :
    HasDerivAt (fun t : ℝ ↦ -((Real.log t + 1) / t)) (Real.log x / x ^ 2) x := by
  have hp : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 16) hx
  have hd := (((Real.hasDerivAt_log hp.ne').add_const 1).div (hasDerivAt_id x) hp.ne').neg
  apply hd.congr_deriv
  simp only [id_eq, inv_mul_cancel₀ hp.ne', mul_one]
  ring

private theorem logTail_limit :
    Filter.Tendsto (fun t : ℝ ↦ -((Real.log t + 1) / t)) Filter.atTop (nhds 0) := by
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hi : Filter.Tendsto (fun t : ℝ ↦ t⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  simpa only [add_div, one_div, id_eq, add_zero, neg_zero] using (hl.add hi).neg

private theorem logTail_nonneg (x : ℝ) (hx : x ∈ Set.Ioi (16 : ℝ)) : 0 ≤ Real.log x / x ^ 2 :=
  div_nonneg (Real.log_nonneg ((by norm_num only : (1 : ℝ) ≤ 16).trans hx.le)) (sq_nonneg _)

/-- Absolute integrability of the logarithmic weight follows from its nonnegative
values and its primitive tending to zero at infinity. -/
theorem logWeight_integrable :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ Real.log x / x ^ 2) (Set.Ioi 16) :=
  MeasureTheory.integrableOn_Ioi_deriv_of_nonneg' logTail_derivative logTail_nonneg logTail_limit

/-- The constant Fourier mode of the logarithmically weighted tail has exact mass. -/
theorem logWeight_integral :
    (∫ x in Set.Ioi (16 : ℝ), Real.log x / x ^ 2) = (Real.log 16 + 1) / 16 := by
  simpa only [zero_sub, neg_neg] using
    MeasureTheory.integral_Ioi_of_hasDerivAt_of_nonneg' logTail_derivative logTail_nonneg
      logTail_limit

/-- Every positive frequency satisfies the logarithmic cosine bound on the entire tail. -/
theorem log_cos_Ioi_le {k : ℝ} (hk : 0 < k) :
    |∫ x in Set.Ioi (16 : ℝ), (Real.log x / x ^ 2) * Real.cos (k * x)| ≤
      2 * (Real.log 16 / 16 ^ 2) / k :=
  cos_tail_limit_le logWeight_integrable (fun _ hb ↦ log_cos_tail_le hb hk)

/-- Integrating the shifted two-frequency numerator against any integrable tail
weight separates its mean and its two cosine integrals exactly. -/
theorem momentTail_decompose {w : ℝ → ℝ} (hw : MeasureTheory.IntegrableOn w (Set.Ioi 16)) :
    (∫ x in Set.Ioi 16, sincMomentNumerator x * w x) =
      (2 / 3 + sineMajorantShift) * (∫ x in Set.Ioi 16, w x) -
        (7 / 18) * (∫ x in Set.Ioi 16, w x * Real.cos (2 * x)) -
        (1 / 18) * (∫ x in Set.Ioi 16, w x * Real.cos (4 * x)) := by
  have hi (k : ℝ) : MeasureTheory.IntegrableOn (fun x ↦ w x * Real.cos (k * x)) (Set.Ioi 16) :=
    hw.mul_bdd (Real.continuous_cos.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun x ↦ (Real.abs_cos_le_one (k * x) : ‖Real.cos (k * x)‖ ≤ 1)))
  have he (x : ℝ) :
    sincMomentNumerator x * w x =
      (2 / 3 + sineMajorantShift) * w x - (7 / 18) * (w x * Real.cos (2 * x)) -
        (1 / 18) * (w x * Real.cos (4 * x)) := by
    unfold sincMomentNumerator sineMajorant
    ring
  simp_rw [he]
  have hm := hw.const_mul (2 / 3 + sineMajorantShift)
  have h₂ := (hi 2).const_mul (7 / 18 : ℝ)
  have h₄ := (hi 4).const_mul (1 / 18 : ℝ)
  have hs := MeasureTheory.integral_sub (hm.sub h₂) h₄
  simp only [Pi.sub_apply] at hs
  rw [hs, MeasureTheory.integral_sub hm h₂]
  simp only [MeasureTheory.integral_const_mul]

/-- The full logarithmic tail is bounded by the exact mean contribution plus the
two weighted oscillatory errors. -/
theorem logMoment_tail_le :
    (∫ x in Set.Ioi (16 : ℝ), sincMomentNumerator x * (Real.log x / x ^ 2)) ≤
      (2 / 3 + sineMajorantShift) * ((Real.log 16 + 1) / 16) + (5 / 12) * Real.log 16 / 16 ^ 2 := by
  rw [momentTail_decompose logWeight_integrable, logWeight_integral]
  linarith only [(abs_le.mp (log_cos_Ioi_le (by norm_num only : (0 : ℝ) < 2))).1,
    (abs_le.mp (log_cos_Ioi_le (by norm_num only : (0 : ℝ) < 4))).1]

/-- The mean and the two cosine errors together bound the plain tail. -/
theorem plainMoment_tail_le :
    (∫ x in Set.Ioi (16 : ℝ), sincMomentNumerator x * (1 / x ^ 2)) ≤
      (2 / 3 + sineMajorantShift) / 16 + (5 / 12) / 16 ^ 2 := by
  have hm :=
    integral_Ioi_rpow_of_lt (by norm_num only : (-2 : ℝ) < -1) (by norm_num only : (0 : ℝ) < 16)
  have he : (∫ x in Set.Ioi (16 : ℝ), 1 / x ^ 2) = 1 / 16 := by
    convert hm using 1
    · apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 1 / x ^ 2 = x ^ (-(2 : ℝ))
      rw [Real.rpow_neg (by linarith only [hx.out] : 0 ≤ x), Real.rpow_ofNat, one_div]
    · norm_num
  rw [momentTail_decompose plainWeight_integrable, he]
  linarith only [(abs_le.mp (plain_cos_Ioi_le (by norm_num only : (0 : ℝ) < 2))).1,
    (abs_le.mp (plain_cos_Ioi_le (by norm_num only : (0 : ℝ) < 4))).1]

end PseudoPrime.Analysis
