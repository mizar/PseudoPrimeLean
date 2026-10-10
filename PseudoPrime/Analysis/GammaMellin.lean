/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaCriticalLine
public import PseudoPrime.Analysis.ExponentialAbsoluteIntegral
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
public import Mathlib.Analysis.MellinInversion

/-! # Integrability and Mellin inversion for the shifted gamma function

The reflection bound supplies an integrable exponential majorant on the
imaginary axis. Euler's integral then identifies the Mellin transform.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The gamma function on the half line is continuous, since its arguments
avoid all nonpositive integer poles. Comparing real parts excludes each pole.
This supplies measurability for the vertical integral. -/
theorem continuous_Gamma_half_add_I :
    Continuous (fun t : ℝ ↦ Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply
    (Complex.continuousAt_Gamma _ ?_).comp
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt)
  intro m he
  have hr := congrArg Complex.re he
  change ((1 / 2 : ℂ) + Complex.I * t).re = (-(m : ℂ)).re at hr
  simp only [Complex.add_re, Complex.div_ofNat_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.one_re,
    Complex.neg_re, Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith only [hr, hn]

/-- The gamma function on the half line is integrable. Its continuous values
are bounded by a positive multiple of exponential absolute-value decay.
This establishes absolute convergence of the gamma-kernel mass. -/
theorem integrable_Gamma_half_add_I :
    MeasureTheory.Integrable (fun t : ℝ ↦ Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t)) := by
  have hi := (integrable_exp_neg_mul_abs (half_pos Real.pi_pos)).const_mul (Real.sqrt (2 * Real.pi))
  apply hi.mono' continuous_Gamma_half_add_I.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  have he : -(Real.pi / 2) * |t| = -|Real.pi * t| / 2 := by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    ring
  rw [he]
  exact norm_Gamma_half_add_I_le_exp t

/-- The complex density `u^(1/2) exp(-u)` whose Mellin transform is shifted gamma.
On positive real inputs it equals the real square-root density.
It supplies the function to which Mellin inversion is applied. -/
noncomputable def gammaMellinDensity (u : ℝ) : ℂ :=
  (u : ℂ) ^ (1 / 2 : ℂ) * (Real.exp (-u) : ℂ)

/-- On a positive real argument the complex density equals `sqrt(u) exp(-u)`.
The real-to-complex power identity converts the half power to a square root.
This identifies the nonnegative inverse transform used for gamma kernels. -/
theorem gammaMellinDensity_eq {u : ℝ} (hu : 0 < u) :
    gammaMellinDensity u = (Real.sqrt u * Real.exp (-u) : ℝ) := by
  unfold gammaMellinDensity
  rw [Real.sqrt_eq_rpow, Complex.ofReal_mul, Complex.ofReal_cpow hu.le]
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]

/-- In the half-plane `Re(s+1/2)>0`, the density has Mellin transform
`Gamma(s+1/2)`. The shift rule and Euler's integral prove the identity.
This identifies the analytic gamma kernel from its real density. -/
theorem mellin_gammaMellinDensity {s : ℂ} (hs : 0 < (s + 1 / 2).re) :
    mellin gammaMellinDensity s = Complex.Gamma (s + 1 / 2) := by
  change mellin (fun u : ℝ ↦ (u : ℂ) ^ (1 / 2 : ℂ) • (Real.exp (-u) : ℂ)) s = _
  rw [mellin_cpow_smul, ← Complex.GammaIntegral_eq_mellin, ← Complex.Gamma_eq_integral hs]

/-- The density has an absolutely convergent Mellin integral at zero.
Euler convergence at one half and the power shift establish convergence.
This supplies the spatial convergence hypothesis for Mellin inversion. -/
theorem mellinConvergent_gammaMellinDensity : MellinConvergent gammaMellinDensity (0 : ℂ) := by
  change MellinConvergent (fun u : ℝ ↦ (u : ℂ) ^ (1 / 2 : ℂ) • (Real.exp (-u) : ℂ)) (0 : ℂ)
  apply MellinConvergent.cpow_smul.mpr
  have hi :=
    Complex.GammaIntegral_convergent
      (by norm_num only [Complex.div_ofNat_re, Complex.one_re] : 0 < (1 / 2 : ℂ).re)
  simpa only [zero_add, MellinConvergent, smul_eq_mul, mul_comm] using hi

/-- The density's Mellin transform is vertically integrable at zero.
Its values on that line are the integrable gamma values on the half line.
This supplies the frequency convergence hypothesis for Mellin inversion. -/
theorem verticalIntegrable_mellin_gammaMellinDensity :
    Complex.VerticalIntegrable (mellin gammaMellinDensity) 0 := by
  change MeasureTheory.Integrable (fun t : ℝ ↦ mellin gammaMellinDensity ((0 : ℂ) + t * Complex.I))
  apply integrable_Gamma_half_add_I.congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [mellin_gammaMellinDensity
      (by
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, zero_add, Complex.div_ofNat_re,
          Complex.one_re]
        norm_num only)]
  congr 1
  ring

/-- At every positive argument the density is continuous.
Locally it is the product of the continuous square root and exponential.
This permits pointwise Mellin inversion at all positive arguments. -/
theorem continuousAt_gammaMellinDensity {u : ℝ} (hu : 0 < u) :
    ContinuousAt gammaMellinDensity u := by
  apply
    ContinuousAt.congr_of_eventuallyEq
      ((Complex.continuous_ofReal.comp
          (Real.continuous_sqrt.mul (Real.continuous_exp.comp continuous_neg))).continuousAt)
  filter_upwards [Ioi_mem_nhds hu] with v hv
  exact gammaMellinDensity_eq (Set.mem_Ioi.mp hv)

/-- On the imaginary axis, inverse Mellin transformation of
`Gamma(s+1/2)` gives `sqrt(u) exp(-u)` for every positive `u`.
Apply Mellin inversion with spatial and vertical absolute convergence.
This proves the transform identity needed by the Section 6.3 kernel. -/
theorem mellinInv_gamma_half {u : ℝ} (hu : 0 < u) :
    mellinInv 0 (fun s : ℂ ↦ Complex.Gamma (s + 1 / 2)) u = (Real.sqrt u * Real.exp (-u) : ℝ) := by
  have hi :=
    mellinInv_mellin_eq 0 gammaMellinDensity hu mellinConvergent_gammaMellinDensity
      verticalIntegrable_mellin_gammaMellinDensity (continuousAt_gammaMellinDensity hu)
  rw [gammaMellinDensity_eq hu] at hi
  apply Eq.trans ?_ hi
  unfold mellinInv
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [mellin_gammaMellinDensity
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, Complex.div_ofNat_re,
          Complex.one_re]
        norm_num only)]

/-- In the positive real half-plane, the complex gamma norm is at most the
real gamma value at the real part. Take the norm inside Euler's integral.
This supplies a height-independent upper bound before recurrence is applied. -/
theorem norm_Gamma_le_realGamma {s : ℂ} (hs : 0 < s.re) : ‖Complex.Gamma s‖ ≤ Real.Gamma s.re := by
  rw [Complex.Gamma_eq_integral hs, Real.Gamma_eq_integral hs]
  unfold Complex.GammaIntegral
  apply (MeasureTheory.norm_integral_le_integral_norm _).trans_eq
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u hu
  dsimp only
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos (-u)),
    Complex.norm_cpow_eq_rpow_re_of_pos (Set.mem_Ioi.mp hu), Complex.sub_re, Complex.one_re]

/-- If `Re(s)>-2` and the imaginary part is nonzero, two gamma recurrences
give a quadratic bound in the height. The positive-half-plane integral bounds
the numerator, and each recurrence factor has norm at least `abs(Im(s))`.
This provides vertical decay away from the real axis. -/
theorem norm_Gamma_le_im_sq {s : ℂ} (hs : -2 < s.re) (hi : s.im ≠ 0) :
    ‖Complex.Gamma s‖ ≤ Real.Gamma (s.re + 2) / s.im ^ 2 := by
  have hzero : s ≠ 0 := by
    intro he
    exact hi (congrArg Complex.im he)
  have hone : s + 1 ≠ 0 := by
    intro he
    have him := congrArg Complex.im he
    simp only [Complex.add_im, Complex.one_im, add_zero, Complex.zero_im] at him
    exact hi him
  have he : Complex.Gamma (s + 2) = (s + 1) * s * Complex.Gamma s := by
    calc
      _ = Complex.Gamma ((s + 1) + 1) := by
        congr 1; ring
      _ = (s + 1) * (s * Complex.Gamma s) := by
        rw [Complex.Gamma_add_one _ hone, Complex.Gamma_add_one _ hzero]
      _ = _ := by ring
  have hr : 0 < (s + 2).re := by
    rw [Complex.add_re]
    change 0 < s.re + 2
    linarith only [hs]
  have hn := norm_Gamma_le_realGamma hr
  rw [he, norm_mul, norm_mul] at hn
  have hleft := Complex.abs_im_le_norm (s + 1)
  simp only [Complex.add_im, Complex.one_im, add_zero] at hleft
  have hprod := mul_le_mul hleft (Complex.abs_im_le_norm s) (abs_nonneg s.im) (norm_nonneg (s + 1))
  have hmul := mul_le_mul_of_nonneg_right hprod (norm_nonneg (Complex.Gamma s))
  apply (le_div_iff₀ (sq_pos_of_ne_zero hi)).mpr
  have heq : (s + 2).re = s.re + 2 := rfl
  rw [heq] at hn
  have hsquare : |s.im| * |s.im| = s.im ^ 2 := by rw [← pow_two, sq_abs]
  rw [hsquare] at hmul
  calc
    _ = s.im ^ 2 * ‖Complex.Gamma s‖ := mul_comm _ _
    _ ≤ _ := hmul
    _ ≤ _ := hn

/-- For positive fixed real part `c`, the gamma norm is bounded by an
explicit integrable quadratic majorant. Use Euler's bound at small heights
and two recurrence factors at large heights. This controls each vertical line. -/
theorem norm_Gamma_vertical_bound {c t : ℝ} (hc : 0 < c) :
    ‖Complex.Gamma ((c : ℂ) + Complex.I * t)‖ ≤
      2 * (Real.Gamma c + Real.Gamma (c + 2)) / (1 + t ^ 2) := by
  have hr : ((c : ℂ) + Complex.I * t).re = c := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have him : ((c : ℂ) + Complex.I * t).im = t := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, zero_mul, one_mul, zero_add]
  have hnc := (Real.Gamma_pos_of_pos hc).le
  have hnp := (Real.Gamma_pos_of_pos (by linarith only [hc] : 0 < c + 2)).le
  have hn := norm_nonneg (Complex.Gamma ((c : ℂ) + Complex.I * t))
  apply (le_div_iff₀ (by linarith only [sq_nonneg t] : 0 < 1 + t ^ 2)).mpr
  by_cases ht : t ^ 2 ≤ 1
  · have hb := norm_Gamma_le_realGamma (hr ▸ hc)
    rw [hr] at hb
    have hp := mul_le_mul_of_nonneg_left ht hn
    nlinarith only [hb, hp, hnp]
  · have htp : 0 < t ^ 2 := by linarith only [lt_of_not_ge ht]
    have htz : t ≠ 0 := (sq_pos_iff.mp htp)
    have hb :=
      norm_Gamma_le_im_sq (s := (c : ℂ) + Complex.I * t)
        (by
          rw [hr]; linarith only [hc])
        (by
          rw [him]; exact htz)
    rw [hr, him] at hb
    have hp := (le_div_iff₀ htp).mp hb
    have hs := mul_le_mul_of_nonneg_left (le_of_lt (lt_of_not_ge ht)) hn
    nlinarith only [hp, hs, hnc]

/-- On a vertical line with positive real part gamma is continuous.
All arguments avoid the poles, as their real parts are positive.
This supplies measurability for the general vertical integral. -/
theorem continuous_Gamma_vertical {c : ℝ} (hc : 0 < c) :
    Continuous (fun t : ℝ ↦ Complex.Gamma ((c : ℂ) + Complex.I * t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply
    (Complex.continuousAt_Gamma _ ?_).comp
      ((continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousAt)
  intro m he
  have hr := congrArg Complex.re he
  change ((c : ℂ) + Complex.I * t).re = (-(m : ℂ)).re at hr
  simp only [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, Complex.neg_re,
    Complex.natCast_re] at hr
  have hn : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  linarith only [hr, hn, hc]

/-- Gamma is absolutely integrable on every vertical line of positive
real part. Its continuous values are bounded by an integrable quadratic
majorant. This supports Mellin inversion on all allowed gamma-kernel lines. -/
theorem integrable_Gamma_vertical {c : ℝ} (hc : 0 < c) :
    MeasureTheory.Integrable (fun t : ℝ ↦ Complex.Gamma ((c : ℂ) + Complex.I * t)) := by
  have hi := integrable_inv_one_add_sq.const_mul (2 * (Real.Gamma c + Real.Gamma (c + 2)))
  apply hi.mono' (continuous_Gamma_vertical hc).aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  simpa only [div_eq_mul_inv] using norm_Gamma_vertical_bound (t := t) hc

/-- For `Re(s+1/2)>0`, the density's Mellin integral converges absolutely.
Use convergence of Euler's gamma integral and the Mellin power shift.
This supplies spatial convergence on all allowed inversion lines. -/
theorem mellinConvergent_gammaMellinDensity_of_re_pos {s : ℂ} (hs : 0 < (s + 1 / 2).re) :
    MellinConvergent gammaMellinDensity s := by
  change MellinConvergent (fun u : ℝ ↦ (u : ℂ) ^ (1 / 2 : ℂ) • (Real.exp (-u) : ℂ)) s
  apply MellinConvergent.cpow_smul.mpr
  simpa only [MellinConvergent, smul_eq_mul, mul_comm] using Complex.GammaIntegral_convergent hs

/-- The Mellin transform of the density is vertically integrable whenever
`c+1/2>0`. Identify its values with gamma on the corresponding positive line.
This supplies frequency convergence for inversion on that line. -/
theorem verticalIntegrable_mellin_gammaMellinDensity_of_pos {c : ℝ} (hc : 0 < c + 1 / 2) :
    Complex.VerticalIntegrable (mellin gammaMellinDensity) c := by
  change MeasureTheory.Integrable (fun t : ℝ ↦ mellin gammaMellinDensity ((c : ℂ) + t * Complex.I))
  apply (integrable_Gamma_vertical hc).congr
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [mellin_gammaMellinDensity
      (by
        simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.div_ofNat_re,
          Complex.one_re]
        exact hc)]
  congr 1
  rw [Complex.ofReal_add, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
  ring

/-- For every inversion line with `c+1/2>0` and positive argument `u`,
the inverse transform of `Gamma(s+1/2)` equals `sqrt(u) exp(-u)`.
Absolute convergence and continuity give pointwise Mellin inversion.
The value is independent of the allowed line. -/
theorem mellinInv_gamma_half_of_pos {c u : ℝ} (hc : 0 < c + 1 / 2) (hu : 0 < u) :
    mellinInv c (fun s : ℂ ↦ Complex.Gamma (s + 1 / 2)) u = (Real.sqrt u * Real.exp (-u) : ℝ) := by
  have hs : 0 < ((c : ℂ) + 1 / 2).re := by
    simp only [Complex.add_re, Complex.ofReal_re, Complex.div_ofNat_re, Complex.one_re]
    exact hc
  have hi :=
    mellinInv_mellin_eq c gammaMellinDensity hu (mellinConvergent_gammaMellinDensity_of_re_pos hs)
      (verticalIntegrable_mellin_gammaMellinDensity_of_pos hc) (continuousAt_gammaMellinDensity hu)
  rw [gammaMellinDensity_eq hu] at hi
  apply Eq.trans ?_ hi
  unfold mellinInv
  congr 1
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro t
  dsimp only
  rw [mellin_gammaMellinDensity
      (by
        simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, Complex.div_ofNat_re,
          Complex.one_re]
        exact hc)]

end PseudoPrime.Analysis
