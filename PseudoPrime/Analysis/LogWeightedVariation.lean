/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Smooth logarithmic variation identity for double partial summation -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For positive v and u, log(t/v) has derivative 1/u at u. Differentiate
the quotient and cancel the nonzero denominator. This is the logarithmic factor
in the concrete double-partial-summation primitive. -/
theorem log_div_derivative {v u : ℝ} (hv : 0 < v) (hu : 0 < u) :
    HasDerivAt (fun t : ℝ ↦ Real.log (t / v)) (1 / u) u := by
  have h := ((hasDerivAt_id u).div_const v).log (div_ne_zero hu.ne' hv.ne')
  apply h.congr_deriv
  change (1 / v) / (u / v) = 1 / u
  rw [div_div_div_cancel_right₀ hv.ne']

/-- At a positive point u, if V'=P and (tP)'=Q, then
log(t/v)tP(t)-V(t) has derivative log(u/v)Q(u). Apply the product rule and
cancel u. This primitive retains endpoint terms and later derivative jumps. -/
theorem log_variation_primitive {V P Q : ℝ → ℝ} {v u : ℝ} (hv : 0 < v) (hu : 0 < u)
    (hV : HasDerivAt V (P u) u) (hP : HasDerivAt (fun t ↦ t * P t) (Q u) u) :
    HasDerivAt (fun t ↦ Real.log (t / v) * (t * P t) - V t) (Real.log (u / v) * Q u) u := by
  have h := ((log_div_derivative hv hu).mul hP).sub hV
  apply h.congr_deriv
  change 1 / u * (u * P u) + Real.log (u / v) * Q u - P u = _
  rw [one_div, inv_mul_cancel_left₀ hu.ne']
  ring

/-- For a positive interval [a,b] and positive reference v, integrate the
logarithmic variation kernel using the supplied derivative and integrability proofs.
The fundamental theorem of calculus gives both endpoint terms explicitly.
This is the smooth-piece identity used to assemble the ramp's two jumps. -/
theorem log_variation_integral {V P Q : ℝ → ℝ} {v a b : ℝ} (hv : 0 < v) (ha : 0 < a) (hab : a ≤ b)
    (hV : ∀ u ∈ Set.Icc a b, HasDerivAt V (P u) u)
    (hP : ∀ u ∈ Set.Icc a b, HasDerivAt (fun t ↦ t * P t) (Q u) u)
    (hi : IntervalIntegrable (fun u ↦ Real.log (u / v) * Q u) MeasureTheory.volume a b) :
    (∫ u in a..b, Real.log (u / v) * Q u) =
      Real.log (b / v) * (b * P b) - V b - (Real.log (a / v) * (a * P a) - V a) := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro u hu
  rw [Set.uIcc_of_le hab] at hu
  exact log_variation_primitive hv (ha.trans_le hu.1) (hV u hu) (hP u hu)

/-- If V'=P and (tP)'=Q, the derivative of t(tP)-tV is tQ-V.
The product rule cancels the two tP terms. This primitive separates the linear
main term from the variation functional without a positivity restriction. -/
theorem linear_variation_primitive {V P Q : ℝ → ℝ} {u : ℝ} (hV : HasDerivAt V (P u) u)
    (hP : HasDerivAt (fun t ↦ t * P t) (Q u) u) :
    HasDerivAt (fun t ↦ t * (t * P t) - t * V t) (u * Q u - V u) u := by
  have h := ((hasDerivAt_id u).mul hP).sub ((hasDerivAt_id u).mul hV)
  apply h.congr_deriv
  change 1 * (u * P u) + u * Q u - (1 * V u + u * P u) = _
  ring

/-- Integrate the linear variation density on a finite interval.
With the two derivative identities and integrability certificates, tQ integrates
to the displayed boundary terms plus the integral of V. Apply the fundamental
theorem of calculus to t(tP)-tV. This evaluates the ramp functional on the identity. -/
theorem linear_variation_integral {V P Q : ℝ → ℝ} {a b : ℝ}
    (hV : ∀ u ∈ Set.uIcc a b, HasDerivAt V (P u) u)
    (hP : ∀ u ∈ Set.uIcc a b, HasDerivAt (fun t ↦ t * P t) (Q u) u)
    (hiQ : IntervalIntegrable (fun u ↦ u * Q u) MeasureTheory.volume a b)
    (hiV : IntervalIntegrable V MeasureTheory.volume a b) :
    (∫ u in a..b, u * Q u) =
      b * (b * P b) - b * V b - (a * (a * P a) - a * V a) + ∫ u in a..b, V u := by
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun u hu ↦ linear_variation_primitive (hV u hu) (hP u hu)) (hiQ.sub hiV)
  rw [intervalIntegral.integral_sub hiQ hiV] at h
  linarith only [h]

end PseudoPrime.Analysis
