/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampCutoff
public import PseudoPrime.Analysis.LogWeightedVariation

/-! # Logarithmic reconstruction of the exponential ramp with both jumps -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- On a positive interval [a,b], log(u/v)Q(u) is interval integrable when
v>0 and Q is continuous. Use the logarithm derivative to establish continuity
on that interval. This discharges the hypotheses of the smooth variation formula. -/
private theorem log_kernel_integrable {v a b : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b)
    {Q : ℝ → ℝ} (hQ : Continuous Q) :
    IntervalIntegrable (fun u ↦ Real.log (u / v) * Q u) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  have hlog : ContinuousOn (fun u ↦ Real.log (u / v)) (Set.Icc a b) := fun u hu ↦
    (log_div_derivative hv (ha.trans_le hu.1)).continuousAt.continuousWithinAt
  exact hlog.mul hQ.continuousOn

/-- For 0<v<=247/100, the two smooth logarithmic variation integrals plus
the negative left jump and positive right jump equal the actual ramp weight at v.
Apply the smooth primitive on both pieces and cancel endpoint values.
This reconstructs each finite-sum atom before the ramp. -/
theorem ramp_atom_left {v : ℝ} (hv : 0 < v) (hva : v ≤ 247 / 100) :
    (∫ u in v..(247 / 100), Real.log (u / v) * ((u - 1) * Real.exp (-u))) +
            (∫ u in (247 / 100 : ℝ)..(99 / 40),
              Real.log (u / v) *
                (Real.exp (-u) *
                  ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200)))) -
          Real.log ((247 / 100) / v) * ((247 / 100) * Real.exp (-(247 / 100 : ℝ)) / (1 / 200)) +
        Real.log ((99 / 40) / v) * ((99 / 40) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200)) =
      exponentialRampWeight v := by
  have hleft :=
    log_variation_integral hv hv hva (fun u _ ↦ exponentialRamp_first_derivative u)
      (fun u _ ↦ exponentialRamp_first_variation u)
      (log_kernel_integrable hv hv hva
        ((continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)))
  have hright :=
    log_variation_integral hv (by norm_num only : (0 : ℝ) < 247 / 100)
      (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40) (fun u _ ↦ exponentialRamp_middle_derivative u)
      (fun u _ ↦ exponentialRamp_middle_variation u)
      (log_kernel_integrable hv (by norm_num only) (by norm_num only)
        ((Real.continuous_exp.comp continuous_id.neg).mul
          (((continuous_id.sub continuous_const).mul
                ((continuous_const.sub continuous_id).div_const (1 / 200))).add
            ((continuous_const.mul continuous_id).sub continuous_const |>.div_const (1 / 200)))))
  rw [hleft, hright, exponentialRampWeight_eq_exp_of_le_left hva, Real.log_div_self]
  ring

/-- For v in the positive ramp interval, the middle logarithmic variation
integral plus the right jump equals the actual ramp weight at v. Apply the
smooth primitive and use the zero value at the right endpoint.
This reconstructs atoms lying inside the ramp, including its joins. -/
theorem ramp_atom_middle {v : ℝ} (hv : 0 < v) (hav : 247 / 100 ≤ v) (hvl : v ≤ 99 / 40) :
    (∫ u in v..(99 / 40),
          Real.log (u / v) *
            (Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200)))) +
        Real.log ((99 / 40) / v) * ((99 / 40) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200)) =
      exponentialRampWeight v := by
  have h :=
    log_variation_integral hv hv hvl (fun u _ ↦ exponentialRamp_middle_derivative u)
      (fun u _ ↦ exponentialRamp_middle_variation u)
      (log_kernel_integrable hv hv hvl
        ((Real.continuous_exp.comp continuous_id.neg).mul
          (((continuous_id.sub continuous_const).mul
                ((continuous_const.sub continuous_id).div_const (1 / 200))).add
            ((continuous_const.mul continuous_id).sub continuous_const |>.div_const (1 / 200)))))
  rw [h, exponentialRampWeight_eq_middle hav hvl, Real.log_div_self]
  ring

/-- The logarithmic atom log(max(v,u)/v). For v>0 it equals zero below v
and log(u/v) above v, and is continuous at the join. This permits finite
summation under integrals without a moving lower endpoint. -/
noncomputable def positiveLogRatio (v u : ℝ) : ℝ :=
  Real.log (max v u / v)

/-- Below v, the clipped logarithmic atom is zero. Use max(v,u)=v and
log(v/v)=0. This removes terms above each arithmetic cutoff. -/
theorem positiveLogRatio_zero {v u : ℝ} (hu : u ≤ v) : positiveLogRatio v u = 0 := by
  rw [positiveLogRatio, max_eq_left hu, Real.log_div_self]

/-- At or above v, the clipped logarithmic atom is log(u/v).
Use max(v,u)=u. This identifies the ordinary logarithmic weight on its support. -/
theorem positiveLogRatio_eq_log {v u : ℝ} (hu : v ≤ u) :
    positiveLogRatio v u = Real.log (u / v) := by rw [positiveLogRatio, max_eq_right hu]

/-- For positive v, the clipped logarithmic atom is continuous on the real line.
The max numerator stays positive, so division and logarithm preserve continuity.
This supplies integrability for the finite interchange of sum and integral. -/
theorem positiveLogRatio_continuous {v : ℝ} (hv : 0 < v) : Continuous (positiveLogRatio v) := by
  apply ((continuous_const.max continuous_id).div_const v).log
  intro u
  exact (div_pos (hv.trans_le (le_max_left v u)) hv).ne'

/-- If a<=b<=v, the clipped logarithm times any density has zero interval
integral. The logarithmic factor vanishes at every point.
This removes the part below an atom's support. -/
private theorem clipped_integral_zero {v a b : ℝ} (hab : a ≤ b) (hb : b ≤ v) (Q : ℝ → ℝ) :
    (∫ u in a..b, positiveLogRatio v u * Q u) = 0 := by
  rw [← intervalIntegral.integral_zero (a := a) (b := b)]
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  dsimp only
  rw [positiveLogRatio_zero (hu.2.trans hb), zero_mul]

/-- If v<=a<=b, the clipped and ordinary logarithmic integrals agree.
Replace the clipped logarithm pointwise on the closed interval.
This reduces supported atoms to the smooth variation identity. -/
private theorem clipped_integral_eq_log {v a b : ℝ} (hab : a ≤ b) (ha : v ≤ a) (Q : ℝ → ℝ) :
    (∫ u in a..b, positiveLogRatio v u * Q u) = ∫ u in a..b, Real.log (u / v) * Q u := by
  apply intervalIntegral.integral_congr
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  dsimp only
  rw [positiveLogRatio_eq_log (ha.trans hu.1)]

/-- For positive v between a and b and a continuous density Q, the clipped
logarithmic integral on [a,b] equals the ordinary one on [v,b]. Split at v,
use the zero lower piece, and identify the upper piece.
This aligns the fixed integration intervals with each positive atom. -/
theorem clipped_integral_from_join {v a b : ℝ} (hv : 0 < v) (ha : a ≤ v) (hb : v ≤ b) {Q : ℝ → ℝ}
    (hQ : Continuous Q) :
    (∫ u in a..b, positiveLogRatio v u * Q u) = ∫ u in v..b, Real.log (u / v) * Q u := by
  have hc : Continuous (fun u ↦ positiveLogRatio v u * Q u) :=
    (positiveLogRatio_continuous hv).mul hQ
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable a v)
      (hc.intervalIntegrable v b)]
  rw [clipped_integral_zero ha le_rfl, clipped_integral_eq_log hb le_rfl, zero_add]

/-- The left variation density is continuous on the real line.
Multiply its polynomial and exponential factors.
This supplies the finite clipped-kernel integrability certificate. -/
private theorem ramp_density_left_continuous : Continuous (fun u : ℝ ↦ (u - 1) * Real.exp (-u)) :=
  (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)

/-- The middle variation density is continuous on the real line.
Combine its polynomial, constant-width division and exponential factors.
This supplies the finite clipped-kernel integrability certificate. -/
private theorem ramp_density_middle_continuous :
    Continuous
      (fun u : ℝ ↦
        Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200))) :=
  (Real.continuous_exp.comp continuous_id.neg).mul
    (((continuous_id.sub continuous_const).mul
          ((continuous_const.sub continuous_id).div_const (1 / 200))).add
      ((continuous_const.mul continuous_id).sub continuous_const |>.div_const (1 / 200)))

/-- The fixed-interval logarithmic reconstruction of the ramp weight.
It contains two smooth integrals and the two signed endpoint jumps.
For positive atom locations it equals the actual ramp weight; finite linear
combinations will become the double-partial-summation formula. -/
noncomputable def exponentialRampLogKernel (v : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..(247 / 100), positiveLogRatio v u * ((u - 1) * Real.exp (-u))) +
        (∫ u in (247 / 100 : ℝ)..(99 / 40),
          positiveLogRatio v u *
            (Real.exp (-u) * ((u - 1) * ((99 / 40 - u) / (1 / 200)) + (2 * u - 1) / (1 / 200)))) -
      positiveLogRatio v (247 / 100) * ((247 / 100) * Real.exp (-(247 / 100 : ℝ)) / (1 / 200)) +
    positiveLogRatio v (99 / 40) * ((99 / 40) * Real.exp (-(99 / 40 : ℝ)) / (1 / 200))

/-- For an atom before the ramp, the clipped kernel equals the ramp weight.
Remove the zero lower interval and apply the two-piece reconstruction identity.
This is the first case of the global atom theorem. -/
private theorem ramp_kernel_left {v : ℝ} (hv : 0 < v) (ha : v ≤ 247 / 100) :
    exponentialRampLogKernel v = exponentialRampWeight v := by
  rw [exponentialRampLogKernel, clipped_integral_from_join hv hv.le ha ramp_density_left_continuous,
    clipped_integral_eq_log (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40) ha,
    positiveLogRatio_eq_log ha,
    positiveLogRatio_eq_log (ha.trans (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40))]
  exact ramp_atom_left hv ha

/-- For an atom in the ramp, the clipped kernel equals the ramp weight.
The first interval and left jump vanish; use the middle-piece reconstruction.
This is the second case of the global atom theorem. -/
private theorem ramp_kernel_middle {v : ℝ} (hv : 0 < v) (ha : 247 / 100 ≤ v) (hb : v ≤ 99 / 40) :
    exponentialRampLogKernel v = exponentialRampWeight v := by
  rw [exponentialRampLogKernel, clipped_integral_zero (by norm_num only : (0 : ℝ) ≤ 247 / 100) ha,
    clipped_integral_from_join hv ha hb ramp_density_middle_continuous, positiveLogRatio_zero ha,
    zero_mul, sub_zero, zero_add, positiveLogRatio_eq_log hb]
  exact ramp_atom_middle hv ha hb

/-- At or after the cutoff, both clipped intervals and jumps vanish, as does
the ramp weight. Replace each clipped logarithm by zero.
This is the final case of the global atom theorem. -/
private theorem ramp_kernel_right {v : ℝ} (hb : 99 / 40 ≤ v) :
    exponentialRampLogKernel v = exponentialRampWeight v := by
  have ha : (247 / 100 : ℝ) ≤ v := (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40).trans hb
  rw [exponentialRampLogKernel, clipped_integral_zero (by norm_num only : (0 : ℝ) ≤ 247 / 100) ha,
    clipped_integral_zero (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40) hb,
    positiveLogRatio_zero ha, positiveLogRatio_zero hb, exponentialRampWeight_eq_zero hb]
  ring

/-- For every positive atom location, the fixed-interval logarithmic kernel
equals the actual ramp weight. Split before, inside and after the ramp.
This removes an abstract reconstruction premise from the finite-sum formula. -/
theorem exponentialRampLogKernel_eq_weight {v : ℝ} (hv : 0 < v) :
    exponentialRampLogKernel v = exponentialRampWeight v := by
  by_cases ha : v ≤ 247 / 100
  · exact ramp_kernel_left hv ha
  · by_cases hb : v ≤ 99 / 40
    · exact ramp_kernel_middle hv (le_of_not_ge ha) hb
    · exact ramp_kernel_right (le_of_not_ge hb)

end PseudoPrime.Analysis
