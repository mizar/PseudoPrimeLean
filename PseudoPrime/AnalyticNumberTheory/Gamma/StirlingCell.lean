/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.EndpointLimits
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Stirling main term and unit-cell integral -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The elementary Stirling main part used in the Gamma phase remainder.
It is subtracted from the Euler logarithm and its finite approximations. -/
noncomputable def backlundStirlingMain (z : ℂ) : ℂ :=
  (z - 1 / 2) * Complex.log z - z

private noncomputable def cellPrimitive (b v : ℂ) : ℂ :=
  -(b + v) / 2 + (b + 1 / 2) * Complex.log (b + v) + (b * (b + 1) / 2) * (b + v)⁻¹

private theorem cellPrimitive_deriv (b v : ℂ) (hv : b + v ∈ Complex.slitPlane) :
    HasDerivAt (cellPrimitive b) ((v * (1 - v) / 2) * (b + v)⁻¹ ^ 2) v := by
  have hn : b + v ≠ 0 := Complex.slitPlane_ne_zero hv
  have h :=
    ((((hasDerivAt_id v).const_add b).neg.div_const 2).add
          (((hasDerivAt_id v).const_add b).clog hv |>.const_mul (b + 1 / 2))).add
      ((((hasDerivAt_id v).const_add b).inv hn).const_mul (b * (b + 1) / 2))
  dsimp only [id_eq, Pi.add_apply, Pi.neg_apply, Pi.div_apply, Pi.inv_apply] at h
  have hm : (b + v) * (b + v)⁻¹ = 1 := mul_inv_cancel₀ hn
  unfold cellPrimitive
  convert h using 1
  simp only [one_div, neg_div, ← inv_pow]
  linear_combination (-((1 - (b - v + 1) * (b + v)⁻¹) / 2)) * hm

private theorem cellPrimitive_deriv_real (b : ℂ) {v : ℝ} (hv : b + v ∈ Complex.slitPlane) :
    HasDerivAt (fun u : ℝ ↦ cellPrimitive b u) (((v : ℂ) * (1 - v) / 2) * (b + v)⁻¹ ^ 2) v := by
  have hc : HasDerivAt (fun u : ℝ ↦ (u : ℂ)) 1 v := by
    have h := Complex.ofRealCLM.hasDerivAt (x := v)
    rw [Complex.ofRealCLM_apply, Complex.ofReal_one] at h
    convert h using 1
    funext x
    exact (Complex.ofRealCLM_apply x).symm
  have h := (cellPrimitive_deriv b v hv).comp v hc
  simpa only [Function.comp_def, mul_one] using h

private theorem cellPrimitive_endpoint (b : ℂ) (hb : 0 < b.re) :
    cellPrimitive b 1 - cellPrimitive b 0 =
      backlundStirlingMain (b + 1) - backlundStirlingMain b - Complex.log b := by
  have hb0 : b ≠ 0 := Complex.ne_zero_of_re_pos hb
  have hb1 : b + 1 ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.one_re]
    linarith only [hb]
  have h0 := mul_inv_cancel₀ hb0
  have h1 := mul_inv_cancel₀ hb1
  unfold cellPrimitive backlundStirlingMain
  simp only [add_zero]
  linear_combination ((b / 2) * h1) - (((b + 1) / 2) * h0)

/-- For `Re b > 0`, the integral of the quadratic Gamma kernel over `[0,1]`
is the difference of consecutive Stirling main terms minus `log b`. The
explicit primitive is valid throughout the interval because `b + v` stays
in the right half-plane. -/
theorem gamma_quadratic_integral_cell (b : ℂ) (hb : 0 < b.re) :
    (∫ v in (0 : ℝ)..1, (((v : ℂ) * (1 - v) / 2) * (b + v)⁻¹ ^ 2)) =
      backlundStirlingMain (b + 1) - backlundStirlingMain b - Complex.log b := by
  have hc : ContinuousOn (fun v : ℝ ↦ b + (v : ℂ)) (Set.Icc 0 1) :=
    (continuous_const.add Complex.continuous_ofReal).continuousOn
  have hn : ∀ v ∈ Set.Icc (0 : ℝ) 1, b + (v : ℂ) ≠ 0 := by
    intro v hv
    apply Complex.ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hb, hv.1]
  have hi := hc.inv₀ hn
  have hnum : Continuous (fun v : ℝ ↦ ((v : ℂ) * (1 - v) / 2)) := by fun_prop
  have hint :
    IntervalIntegrable (fun v : ℝ ↦ (((v : ℂ) * (1 - v) / 2) * (b + v)⁻¹ ^ 2)) MeasureTheory.volume
      0 1 :=
    (hnum.continuousOn.mul (hi.pow 2)).intervalIntegrable_of_Icc (by norm_num only)
  have hd :
    ∀ v ∈ Set.uIcc (0 : ℝ) 1,
      HasDerivAt (fun u : ℝ ↦ cellPrimitive b u) (((v : ℂ) * (1 - v) / 2) * (b + v)⁻¹ ^ 2) v := by
    intro v hv
    rw [Set.uIcc_of_le (by norm_num only)] at hv
    apply cellPrimitive_deriv_real
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Complex.add_re, Complex.ofReal_re]
    linarith only [hb, hv.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hint]
  simpa only [Complex.ofReal_one, Complex.ofReal_zero] using cellPrimitive_endpoint b hb

end PseudoPrime.AnalyticNumberTheory.Gamma
