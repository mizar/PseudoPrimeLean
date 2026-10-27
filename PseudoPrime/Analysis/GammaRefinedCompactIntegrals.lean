/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRefinedVerticalBounds
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Compact integrals for the refined Gamma moment envelopes

Exact primitives retain the curved compact bound before adding the power tails.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The compact zeroth-moment envelope in normalized height coordinates.
Definition: 256/15 divided by sqrt(1+(16t)^2), for any real height.
Output: a positive continuous function to integrate on the unit interval.
Role: the inverse-norm Gamma bound in real coordinates. -/
noncomputable def gammaRefinedCompactZero (t : ℝ) : ℝ :=
  (256 / 15 : ℝ) / Real.sqrt (1 + (16 * t) ^ 2)

/-- Input: any real height.
Claim: the scaled inverse hyperbolic sine differentiates to the compact envelope.
Proof: chain rule and exact rational simplification.
Role: compute the zeroth compact moment without a coarse constant envelope. -/
theorem hasDerivAt_gammaRefinedCompactZero (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ (16 / 15 : ℝ) * Real.arsinh (16 * u)) (gammaRefinedCompactZero t)
      t := by
  have h :=
    ((Real.hasDerivAt_arsinh (16 * t)).comp t ((hasDerivAt_id t).const_mul 16)).const_mul
      (16 / 15 : ℝ)
  convert h using 1
  · rfl
  · simp only [gammaRefinedCompactZero, mul_one, div_eq_mul_inv]
    ring

/-- Claim: the compact envelope is continuous on the whole real line.
Proof: its squared denominator argument is positive everywhere.
Role: justify integration of the exact compact primitive. -/
theorem continuous_gammaRefinedCompactZero : Continuous gammaRefinedCompactZero := by
  exact
    continuous_const.div
      (Real.continuous_sqrt.comp
        (continuous_const.add ((continuous_const.mul continuous_id).pow 2)))
      (fun t ↦ (Real.sqrt_pos.mpr (by nlinarith only [sq_nonneg (16 * t)])).ne')

/-- Claim: the compact zeroth moment is sixteen fifteenths times arsinh sixteen.
Proof: apply the fundamental theorem to the certified primitive.
Role: exact compact contribution to the normalized Gamma moment. -/
theorem integral_gammaRefinedCompactZero :
    (∫ t in (0 : ℝ)..1, gammaRefinedCompactZero t) = (16 / 15 : ℝ) * Real.arsinh 16 := by
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t _ ↦ hasDerivAt_gammaRefinedCompactZero t)
      (continuous_gammaRefinedCompactZero.intervalIntegrable 0 1)
  simpa only [mul_one, mul_zero, Real.arsinh_zero, sub_zero] using h

/-- Input: any real height.
Claim: the scaled square-root primitive differentiates to the height-weighted envelope.
Proof: square-root chain rule with a strictly positive denominator argument.
Role: compute the compact first-moment contribution. -/
theorem hasDerivAt_gammaRefinedCompactFirst (t : ℝ) :
    HasDerivAt (fun u : ℝ ↦ (1 / 15 : ℝ) * Real.sqrt (1 + (16 * u) ^ 2))
      (t * gammaRefinedCompactZero t) t := by
  have hp : 1 + (16 * t) ^ 2 ≠ 0 := ne_of_gt (by nlinarith only [sq_nonneg (16 * t)])
  have h :=
    ((Real.hasDerivAt_sqrt hp).comp t
          ((((hasDerivAt_id t).const_mul 16).pow 2).const_add 1)).const_mul
      (1 / 15 : ℝ)
  convert h using 1
  · rfl
  · simp only [gammaRefinedCompactZero, mul_one, div_eq_mul_inv, id_eq]
    ring

/-- Claim: the compact first moment is (sqrt 257 minus one) divided by fifteen.
Proof: apply the fundamental theorem to the square-root primitive.
Role: exact compact contribution to the refined first Gamma moment. -/
theorem integral_gammaRefinedCompactFirst :
    (∫ t in (0 : ℝ)..1, t * gammaRefinedCompactZero t) = (Real.sqrt 257 - 1) / 15 := by
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (a := (0 : ℝ)) (b := 1)
      (fun t _ ↦ hasDerivAt_gammaRefinedCompactFirst t)
      ((continuous_id.mul continuous_gammaRefinedCompactZero).intervalIntegrable 0 1)
  norm_num only [mul_one, mul_zero, zero_pow, zero_add, add_zero, Real.sqrt_one] at h
  convert h using 1
  ring

/-- Input: complex real part minus one sixteenth.
Claim: the normalized real square root is sixteen times the complex argument norm.
Proof: compare the nonnegative squared quantities using the complex norm-square formula.
Role: identify the inverse-norm Gamma bound with the real compact envelope. -/
theorem gammaRefinedCompact_denominator_eq {s : ℂ} (hs : s.re = -1 / 16) :
    Real.sqrt (1 + (16 * s.im) ^ 2) = 16 * ‖s‖ := by
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _) (mul_nonneg (by norm_num only) (norm_nonneg s))).mp
  have hp : (0 : ℝ) ≤ 1 + (16 * s.im) ^ 2 := by nlinarith only [sq_nonneg (16 * s.im)]
  rw [Real.sq_sqrt hp, mul_pow (16 : ℝ) ‖s‖ 2, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    hs]
  ring

/-- Input: complex real part minus one sixteenth.
Claim: the real compact envelope bounds the actual Gamma norm at its height.
Proof: rewrite the certified inverse-norm estimate using the denominator identity.
Role: connect exact compact integrals to the Gamma moments in the left integral. -/
theorem norm_Gamma_le_gammaRefinedCompactZero {s : ℂ} (hs : s.re = -1 / 16) :
    ‖Complex.Gamma s‖ ≤ gammaRefinedCompactZero s.im := by
  have h := norm_Gamma_neg_one_sixteenth_le_inv_norm hs
  have he : gammaRefinedCompactZero s.im = (16 / 15 : ℝ) / ‖s‖ := by
    rw [gammaRefinedCompactZero, gammaRefinedCompact_denominator_eq hs]
    norm_num only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  exact h

end PseudoPrime.Analysis
