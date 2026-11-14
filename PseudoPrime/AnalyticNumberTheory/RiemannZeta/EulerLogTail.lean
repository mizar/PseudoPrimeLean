/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaTailDecay
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.EulerLog
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

/-! # Decay of the Euler logarithm on vertical edges -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For real part at least two, the Euler logarithm decays exponentially,
uniformly in the imaginary part. The positive real Euler logarithm and the
Dirichlet tail provide successive bounds. -/
theorem norm_eulerLog_le_decay {s : ℂ} (hs : 2 ≤ s.re) :
    ‖backlundZetaLog s‖ ≤ (2 : ℝ) ^ (2 - s.re) := by
  have hs1 : 1 < s.re := by linarith only [hs]
  exact (norm_backlundZetaLog_le hs1).trans (log_zeta_real_le_decay hs).2

/-- The exponential bound for the Euler logarithm tends to zero as the
real part tends to infinity. Rewrite the bound as a power of one half. -/
theorem tendsto_eulerLog_decay :
    Filter.Tendsto (fun b : ℝ ↦ (2 : ℝ) ^ (2 - b)) Filter.atTop (nhds 0) := by
  have h : Filter.Tendsto (fun b : ℝ ↦ (2 : ℝ)⁻¹ ^ b) Filter.atTop (nhds 0) :=
    tendsto_rpow_atTop_of_base_lt_one _ (by norm_num only) (by norm_num only)
  have h' := h.const_mul (4 : ℝ)
  simp only [mul_zero] at h'
  apply h'.congr
  intro b
  rw [Real.rpow_sub (by norm_num only : (0 : ℝ) < 2), Real.rpow_two,
    Real.inv_rpow (by norm_num only : (0 : ℝ) ≤ 2)]
  norm_num only
  ring

/-- The Euler logarithm on a vertical segment at real part at least two has
integral norm bounded by the segment length times the uniform decay bound.
The endpoints may occur in either order. -/
theorem norm_eulerLog_vertical_le (b u v : ℝ) (hb : 2 ≤ b) :
    ‖∫ y in u..v, backlundZetaLog ((b : ℂ) + (y : ℂ) * Complex.I)‖ ≤
      (2 : ℝ) ^ (2 - b) * |v - u| := by
  apply intervalIntegral.norm_integral_le_of_norm_le_const
  intro y hy
  have hs : 2 ≤ (((b : ℂ) + (y : ℂ) * Complex.I)).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using hb
  have h := norm_eulerLog_le_decay hs
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using h

/-- For fixed endpoints, the Euler-log integral along a vertical edge tends
to zero as its real part tends to infinity. This removes the far edge in
the right-half-plane rectangle identity. -/
theorem tendsto_eulerLog_vertical (u v : ℝ) :
    Filter.Tendsto (fun b : ℝ ↦ ∫ y in u..v, backlundZetaLog ((b : ℂ) + (y : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  have hlim := tendsto_eulerLog_decay.mul_const |v - u|
  simp only [zero_mul] at hlim
  apply squeeze_zero_norm' _ hlim
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with b hb
  exact norm_eulerLog_vertical_le b u v hb

/-- The Euler logarithm is interval integrable along a horizontal segment
to the right of one, by complex differentiability and continuity. -/
theorem eulerLog_horizontal_integrable {a b t : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun x : ℝ ↦ backlundZetaLog ((x : ℂ) + (t : ℂ) * Complex.I))
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le hab]
  intro x hx
  have hlin : ContinuousAt (fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) x :=
    (Complex.continuous_ofReal.add continuous_const).continuousAt
  have hz : 1 < (((x : ℂ) + (t : ℂ) * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact ha.trans_le hx.1
  exact
    (ContinuousAt.comp (f := fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I)
        (differentiableAt_backlundZetaLog hz).continuousAt hlin).continuousWithinAt

/-- The Euler logarithm is interval integrable along a vertical segment
to the right of one, by complex differentiability and continuity. -/
theorem eulerLog_vertical_integrable {a u v : ℝ} (ha : 1 < a) (huv : u ≤ v) :
    IntervalIntegrable (fun y : ℝ ↦ backlundZetaLog ((a : ℂ) + (y : ℂ) * Complex.I))
      MeasureTheory.volume u v := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le huv]
  intro y hy
  have hlin : ContinuousAt (fun x : ℝ ↦ (a : ℂ) + (x : ℂ) * Complex.I) y :=
    (continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).continuousAt
  have hz : 1 < (((a : ℂ) + (y : ℂ) * Complex.I)).re := by
    simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using ha
  exact
    (ContinuousAt.comp (f := fun x : ℝ ↦ (a : ℂ) + (x : ℂ) * Complex.I)
        (differentiableAt_backlundZetaLog hz).continuousAt hlin).continuousWithinAt

/-- The contour integral of the Euler logarithm vanishes on every rectangle
to the right of one. The Euler series is holomorphic on that half-plane. -/
theorem eulerLog_rectangle_zero {a b u v : ℝ} (ha : 1 < a) (hab : a ≤ b) (huv : u ≤ v) :
    (∫ x in a..b, backlundZetaLog ((x : ℂ) + (u : ℂ) * Complex.I)) -
            (∫ x in a..b, backlundZetaLog ((x : ℂ) + (v : ℂ) * Complex.I)) +
          Complex.I * (∫ y in u..v, backlundZetaLog ((b : ℂ) + (y : ℂ) * Complex.I)) -
        Complex.I * (∫ y in u..v, backlundZetaLog ((a : ℂ) + (y : ℂ) * Complex.I)) =
      0 := by
  let z : ℂ := (a : ℂ) + (u : ℂ) * Complex.I
  let w : ℂ := (b : ℂ) + (v : ℂ) * Complex.I
  have hzre : z.re = a := by
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hzim : z.im = u := by
    simp only [z, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hwre : w.re = b := by
    simp only [w, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hwim : w.im = v := by
    simp only [w, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  have hd : DifferentiableOn ℂ backlundZetaLog (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) := by
    intro s hs
    rw [Complex.mem_reProdIm, hzre, hwre, hzim, hwim, Set.uIcc_of_le hab, Set.uIcc_of_le huv] at hs
    exact (differentiableAt_backlundZetaLog (ha.trans_le hs.1.1)).differentiableWithinAt
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiableOn backlundZetaLog z w hd
  simpa only [hzre, hwre, hzim, hwim, smul_eq_mul] using h

/-- The real part of the Euler-log rectangle identity relates horizontal
logarithmic norms to the imaginary parts of the two vertical edges. -/
theorem eulerLog_rectangle_real {a b u v : ℝ} (ha : 1 < a) (hab : a ≤ b) (huv : u ≤ v) :
    (∫ x in a..b, (backlundZetaLog ((x : ℂ) + (v : ℂ) * Complex.I)).re) -
        (∫ x in a..b, (backlundZetaLog ((x : ℂ) + (u : ℂ) * Complex.I)).re) =
      (∫ y in u..v, (backlundZetaLog ((a : ℂ) + (y : ℂ) * Complex.I)).im) -
        (∫ y in u..v, (backlundZetaLog ((b : ℂ) + (y : ℂ) * Complex.I)).im) := by
  have hiu := eulerLog_horizontal_integrable (t := u) ha hab
  have hiv := eulerLog_horizontal_integrable (t := v) ha hab
  have hia := eulerLog_vertical_integrable ha huv
  have hib := eulerLog_vertical_integrable (ha.trans_le hab) huv
  have h := congrArg Complex.re (eulerLog_rectangle_zero ha hab huv)
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul,
    one_mul, zero_sub, Complex.zero_re] at h
  have hreU := Complex.reCLM.intervalIntegral_comp_comm hiu
  have hreV := Complex.reCLM.intervalIntegral_comp_comm hiv
  have himA := Complex.imCLM.intervalIntegral_comp_comm hia
  have himB := Complex.imCLM.intervalIntegral_comp_comm hib
  simp only [Complex.reCLM_apply] at hreU hreV
  simp only [Complex.imCLM_apply] at himA himB
  rw [← hreU, ← hreV, ← himA, ← himB] at h
  linarith only [h]

/-- The Euler-log exponential majorant is integrable on the half-line
starting at two. Rewrite the real power as a negative exponential. -/
theorem integrable_eulerLog_decay :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ (2 : ℝ) ^ (2 - x)) (Set.Ioi (2 : ℝ)) := by
  have hl : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have hi := (integrableOn_exp_mul_Ioi (neg_neg_of_pos hl) 2).const_mul (Real.exp (Real.log 2 * 2))
  have he :
    (fun x : ℝ ↦ (2 : ℝ) ^ (2 - x)) =
      (fun x : ℝ ↦ Real.exp (Real.log 2 * 2) * Real.exp (-Real.log 2 * x)) := by
    funext x
    rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 2), ← Real.exp_add]
    congr 1
    ring
  rw [he]
  exact hi

/-- At every real height, the complex Euler logarithm is integrable on the
horizontal tail from two. Continuity and the exponential bound supply the
measurability and domination needed for the improper rectangle limit. -/
theorem integrable_eulerLog_horizontal (t : ℝ) :
    MeasureTheory.IntegrableOn (fun x : ℝ ↦ backlundZetaLog ((x : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ioi (2 : ℝ)) := by
  have hc :
    ContinuousOn (fun x : ℝ ↦ backlundZetaLog ((x : ℂ) + (t : ℂ) * Complex.I))
      (Set.Ioi (2 : ℝ)) := by
    intro x hx
    change (2 : ℝ) < x at hx
    have hlin : ContinuousAt (fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) x :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    have hs : 1 < (((x : ℂ) + (t : ℂ) * Complex.I)).re := by
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
        Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith only [hx]
    exact
      (ContinuousAt.comp (f := fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I)
          (differentiableAt_backlundZetaLog hs).continuousAt hlin).continuousWithinAt
  apply integrable_eulerLog_decay.mono' (hc.aestronglyMeasurable measurableSet_Ioi)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  change (2 : ℝ) < x at hx
  have hs : 2 ≤ (((x : ℂ) + (t : ℂ) * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    exact hx.le
  have h := norm_eulerLog_le_decay hs
  simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] using h

/-- For ordered heights, the difference of the two Euler-log horizontal
tail integrals equals the imaginary Euler-log integral on the line of real
part two. Let the right edge of the finite rectangle tend to infinity. -/
theorem eulerLog_tail_rectangle {u v : ℝ} (huv : u ≤ v) :
    (∫ x in Set.Ioi (2 : ℝ), (backlundZetaLog ((x : ℂ) + (v : ℂ) * Complex.I)).re) -
        (∫ x in Set.Ioi (2 : ℝ), (backlundZetaLog ((x : ℂ) + (u : ℂ) * Complex.I)).re) =
      ∫ y in u..v, (backlundZetaLog (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im := by
  have hiu := Complex.reCLM.integrable_comp (integrable_eulerLog_horizontal u)
  have hiv := Complex.reCLM.integrable_comp (integrable_eulerLog_horizontal v)
  have hlimu := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 2 hiu Filter.tendsto_id
  have hlimv := MeasureTheory.intervalIntegral_tendsto_integral_Ioi 2 hiv Filter.tendsto_id
  have hlimr := (Complex.continuous_im.tendsto 0).comp (tendsto_eulerLog_vertical u v)
  have hlimr' :
    Filter.Tendsto (fun b : ℝ ↦ ∫ y in u..v, (backlundZetaLog ((b : ℂ) + (y : ℂ) * Complex.I)).im)
      Filter.atTop (nhds 0) := by
    apply hlimr.congr'
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with b hb
    have h :=
      Complex.imCLM.intervalIntegral_comp_comm
        (eulerLog_vertical_integrable (by linarith only [hb] : 1 < b) huv)
    simpa only [Complex.imCLM_apply, Function.comp_apply] using h.symm
  have hlim := hlimv.sub hlimu
  have hlim' :=
    Filter.Tendsto.const_sub
      (∫ y in u..v, (backlundZetaLog (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im) hlimr'
  simp only [sub_zero] at hlim'
  apply tendsto_nhds_unique hlim
  apply hlim'.congr'
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ)] with b hb
  exact (eulerLog_rectangle_real (by norm_num only : (1 : ℝ) < 2) hb huv).symm

/-- On the horizontal tail, the Euler logarithm's real part is the
logarithm of the zeta norm. Exponentiation identifies the integrands. -/
theorem eulerLog_horizontal_tail_re (t : ℝ) :
    (∫ x in Set.Ioi (2 : ℝ), (backlundZetaLog ((x : ℂ) + (t : ℂ) * Complex.I)).re) =
      ∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ := by
  apply MeasureTheory.integral_congr_ae
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
  change (2 : ℝ) < x at hx
  have hs : 1 < (((x : ℂ) + (t : ℂ) * Complex.I)).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    linarith only [hx]
  rw [← exp_backlundZetaLog hs, Complex.norm_exp, Real.log_exp]

/-- The difference of the horizontal zeta logarithmic tails equals the
Euler-log argument integral on the line of real part two. This is the
right-half-plane contribution to the critical-line rectangle identity. -/
theorem zeta_log_tail_rectangle {u v : ℝ} (huv : u ≤ v) :
    (∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (v : ℂ) * Complex.I)‖) -
        (∫ x in Set.Ioi (2 : ℝ), Real.log ‖riemannZeta ((x : ℂ) + (u : ℂ) * Complex.I)‖) =
      ∫ y in u..v, (backlundZetaLog (((2 : ℝ) : ℂ) + (y : ℂ) * Complex.I)).im := by
  simpa only [eulerLog_horizontal_tail_re] using eulerLog_tail_rectangle huv

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
