/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic

/-! Monotonicity of inverse-square-root and inverse-scale expressions. -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The real-valued slope `(a + b / sqrt x + c / x) / d` at scale `x`.
The coefficients and denominator are arbitrary real inputs, and real division is total.
This form describes Gaussian radius bounds without fixing their numerical constants. -/
noncomputable def sqrtReciprocalSlope (a b c d x : ℝ) : ℝ :=
  (a + b / Real.sqrt x + c / x) / d

/-- For arbitrary real coefficients and denominator, the slope tends to `a / d` as the
scale tends to infinity. Both reciprocal correction terms vanish, including when the
denominator is zero because real division is total. This supplies asymptotic comparisons
for any profile expressed by `sqrtReciprocalSlope`. -/
theorem sqrtReciprocalSlope_tendsto (a b c d : ℝ) :
    Filter.Tendsto (sqrtReciprocalSlope a b c d) Filter.atTop (nhds (a / d)) := by
  have hs : Filter.Tendsto (fun x : ℝ ↦ (Real.sqrt x)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hi : Filter.Tendsto (fun x : ℝ ↦ x⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hc : Filter.Tendsto (fun _ : ℝ ↦ a) Filter.atTop (nhds a) := tendsto_const_nhds
  have h := ((hc.add (hs.const_mul b)).add (hi.const_mul c)).div_const d
  change Filter.Tendsto (fun x : ℝ ↦ sqrtReciprocalSlope a b c d x) Filter.atTop (nhds (a / d))
  simpa only [sqrtReciprocalSlope, mul_zero, add_zero, div_eq_mul_inv] using h

/-- At a positive scale, multiplying the slope by the scale cancels both denominators.
The result is `(a * x + b * sqrt x + c) / d`. The square-root identity proves the
cancellation and exposes the terms used in the scaled monotonicity comparison. -/
theorem sqrtReciprocalSlope_mul (a b c d : ℝ) {x : ℝ} (hx : 0 < x) :
    sqrtReciprocalSlope a b c d x * x = (a * x + b * Real.sqrt x + c) / d := by
  have hp : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  dsimp only [sqrtReciprocalSlope]
  have hxr : x / Real.sqrt x = Real.sqrt x := by
    apply (div_eq_iff hp.ne').2
    simpa only [pow_two] using (Real.sq_sqrt hx.le).symm
  have hterm : (b / Real.sqrt x) * x = b * Real.sqrt x := by
    rw [div_mul_eq_mul_div, mul_div_assoc, hxr]
  rw [div_mul_eq_mul_div, add_mul, add_mul, hterm, div_mul_cancel₀ _ hx.ne']

/-- Nonnegative coefficients, denominator and scale give a nonnegative slope.
Each term in the numerator is nonnegative. This includes scale zero, where real division
is total, and supplies the sign needed for squared and scaled comparisons. -/
theorem sqrtReciprocalSlope_nonneg {a b c d x : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hx : 0 ≤ x) : 0 ≤ sqrtReciprocalSlope a b c d x := by
  exact
    div_nonneg (add_nonneg (add_nonneg ha (div_nonneg hb (Real.sqrt_nonneg x))) (div_nonneg hc hx))
      hd

/-- Nonnegative correction coefficients and a nonnegative denominator bound the slope
below by `a / d` at any nonnegative scale. Both correction terms are nonnegative, so
the comparison holds even when the scale or denominator is zero. -/
theorem sqrtReciprocalSlope_base_le {a b c d x : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hx : 0 ≤ x) : a / d ≤ sqrtReciprocalSlope a b c d x := by
  have hb0 : 0 ≤ b / Real.sqrt x := div_nonneg hb (Real.sqrt_nonneg x)
  have hc0 : 0 ≤ c / x := div_nonneg hc hx
  dsimp only [sqrtReciprocalSlope]
  exact
    div_le_div_of_nonneg_right ((le_add_of_nonneg_right hb0).trans (le_add_of_nonneg_right hc0)) hd

/-- With nonnegative correction coefficients and denominator, the slope is antitone
between positive ordered scales. Compare the two reciprocal terms separately and preserve
their order under division. No sign assumption on the constant term is needed. -/
theorem sqrtReciprocalSlope_anti {a b c d L M : ℝ} (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hL : 0 < L) (hLM : L ≤ M) : sqrtReciprocalSlope a b c d M ≤ sqrtReciprocalSlope a b c d L := by
  have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
  have h1 : b / Real.sqrt M ≤ b / Real.sqrt L :=
    div_le_div_of_nonneg_left hb (Real.sqrt_pos.2 hL) hs
  have h2 : c / M ≤ c / L := div_le_div_of_nonneg_left hc hL hLM
  dsimp only [sqrtReciprocalSlope]
  exact div_le_div_of_nonneg_right (add_le_add (add_le_add_right h1 a) h2) hd

/-- With nonnegative parameters, the slope multiplied by its scale is nondecreasing
on nonnegative scales. At zero use nonnegativity; at positive scales use the cancellation
identity and monotonicity of the square root. This transports radius bounds to later scales. -/
theorem sqrtReciprocalSlope_scaled_mono {a b c d L M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hL : 0 ≤ L) (hLM : L ≤ M) :
    sqrtReciprocalSlope a b c d L * L ≤ sqrtReciprocalSlope a b c d M * M := by
  by_cases hz : L = 0
  · subst L
    rw [mul_zero]
    exact mul_nonneg (sqrtReciprocalSlope_nonneg ha hb hc hd hLM) hLM
  · have hl : 0 < L := lt_of_le_of_ne hL (Ne.symm hz)
    have hm : 0 < M := hl.trans_le hLM
    have hs : Real.sqrt L ≤ Real.sqrt M := Real.sqrt_le_sqrt hLM
    rw [sqrtReciprocalSlope_mul a b c d hl, sqrtReciprocalSlope_mul a b c d hm]
    exact
      div_le_div_of_nonneg_right
        (add_le_add_left
          (add_le_add (mul_le_mul_of_nonneg_left hLM ha) (mul_le_mul_of_nonneg_left hs hb)) c)
        hd

/-- A nonnegative multiple of the squared slope is antitone on positive scales when all
parameters are nonnegative. The slope is nonnegative and antitone, so squaring and
multiplying by a nonnegative factor preserve the comparison. -/
theorem sqrtReciprocalSlope_sq_anti {a b c d k L M : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (hk : 0 ≤ k) (hL : 0 < L) (hLM : L ≤ M) :
    k * (sqrtReciprocalSlope a b c d M) ^ 2 ≤ k * (sqrtReciprocalSlope a b c d L) ^ 2 := by
  exact
    mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (sqrtReciprocalSlope_nonneg ha hb hc hd (hL.le.trans hLM))
        (sqrtReciprocalSlope_anti hb hc hd hL hLM) 2)
      hk

end PseudoPrime.Analysis
