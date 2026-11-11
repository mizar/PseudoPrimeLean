/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundThetaBounds
import Mathlib.Analysis.SpecialFunctions.Complex.Arg

/-! # Elementary main part of the Gamma phase -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The imaginary remainder after subtracting the elementary Stirling main
part from the analytic Gamma logarithm at `1/4 + iT/2`. Its signed integral
representation supplies the remaining Gamma-phase estimate. -/
noncomputable def backlundGammaRemainder (T : ℝ) : ℝ :=
  let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I
  (AnalyticNumberTheory.Gamma.logGammaSeries z - ((z - (1 / 2 : ℂ)) * Complex.log z - z)).im

/-- In the first quadrant, the complex argument equals `π/2 - arctan(a/y)`.
Use the tangent of the argument and the positive reciprocal arctangent identity. -/
private theorem arg_first_quadrant {a y : ℝ} (ha : 0 < a) (hy : 0 < y) :
    Complex.arg ((a : ℂ) + (y : ℂ) * Complex.I) = Real.pi / 2 - Real.arctan (a / y) := by
  let z : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have hzre : z.re = a := by
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hzim : z.im = y := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have hlo : -(Real.pi / 2) < z.arg :=
    Complex.neg_pi_div_two_lt_arg_iff.mpr
      (Or.inl
        (by
          rw [hzre]; exact ha))
  have hhi : z.arg < Real.pi / 2 :=
    Complex.arg_lt_pi_div_two_iff.mpr
      (Or.inl
        (by
          rw [hzre]; exact ha))
  have har : Real.arctan (y / a) = z.arg := by
    rw [← hzim, ← hzre, ← Complex.tan_arg, Real.arctan_tan hlo hhi]
  have hp : 0 < a / y := div_pos ha hy
  have hinv : (a / y)⁻¹ = y / a := by rw [inv_div]
  have h := Real.arctan_inv_of_pos hp
  rw [hinv, har] at h
  exact h

/-- For positive `y`, the logarithm of the norm of `a + iy` separates into
`log y` and half of `log(1 + (a/y)²)`. Square the norm and factor out `y²`. -/
private theorem log_norm_vertical {a y : ℝ} (hy : 0 < y) :
    Real.log ‖((a : ℂ) + (y : ℂ) * Complex.I)‖ =
      Real.log y + (1 / 2) * Real.log (1 + (a / y) ^ 2) := by
  let z : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have hzre : z.re = a := by
    simp only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  have hzim : z.im = y := by
    simp only [z, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, mul_one, mul_zero, add_zero, zero_add]
  have he : y ^ 2 * (a / y) ^ 2 = a ^ 2 := by
    calc
      _ = (a * (y / y)) ^ 2 := by ring
      _ = _ := by rw [div_self hy.ne', mul_one]
  have hfac : a ^ 2 + y ^ 2 = y ^ 2 * (1 + (a / y) ^ 2) := by nlinarith only [he]
  have hpos : 0 < 1 + (a / y) ^ 2 := by nlinarith only [sq_nonneg (a / y)]
  have h := Real.log_pow ‖z‖ 2
  rw [Complex.sq_norm, Complex.normSq_apply, hzre, hzim, ← pow_two, ← pow_two, hfac,
    Real.log_mul (pow_ne_zero 2 hy.ne') hpos.ne', Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  change Real.log ‖z‖ = _
  linarith only [h]

/-- At positive height, the imaginary part of the elementary Stirling main
expression differs from the Riemann–von Mangoldt Gamma main term by
`backlundThetaDeviation`. The first-quadrant argument and norm identities
give the logarithm and arctangent terms explicitly. -/
theorem backlundTheta_stirling_main {T : ℝ} (hT : 0 < T) :
    let z : ℂ := ((1 / 4 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I
    ((z - (1 / 2 : ℂ)) * Complex.log z - z).im - (T / 2) * Real.log Real.pi - backlundThetaMain T =
      backlundThetaDeviation T := by
  have hy : 0 < T / 2 := by linarith only [hT]
  have hratio :
    ((1 / 4 : ℝ) / (T / 2)) = 1 / (2 * T) ∧ ((1 / 4 : ℝ) / (T / 2)) ^ 2 = 1 / (4 * T ^ 2) := by
    simp only [div_eq_mul_inv, mul_inv, ← inv_pow]
    norm_num only
    constructor <;> ring
  have hnorm := log_norm_vertical (a := (1 / 4 : ℝ)) hy
  rw [hratio.2] at hnorm
  have harg := arg_first_quadrant (a := (1 / 4 : ℝ)) (by norm_num only) hy
  rw [hratio.1] at harg
  have hdiv : T / (2 * Real.pi) = (T / 2) / Real.pi := by
    simp only [div_eq_mul_inv, mul_inv]
    norm_num only
    ring
  have hlog : Real.log (T / (2 * Real.pi)) = Real.log (T / 2) - Real.log Real.pi := by
    rw [hdiv, Real.log_div hy.ne' Real.pi_ne_zero]
  dsimp only
  simp only [Complex.sub_im, Complex.mul_im, Complex.mul_re, Complex.sub_re, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero,
    mul_one, add_zero, zero_add, sub_zero, Complex.div_ofNat_re, Complex.div_ofNat_im,
    Complex.one_re, Complex.one_im, zero_div, Complex.log_re, Complex.log_im, hnorm, harg,
    backlundThetaMain, backlundThetaDeviation, hlog]
  ring

/-- At positive height, the Gamma-phase discrepancy is the sum of the
elementary deviation and the imaginary Stirling remainder. This rewrites the
Gamma-phase estimate as a signed bound for the remainder alone. -/
theorem backlundTheta_error_eq_remainder {T : ℝ} (hT : 0 < T) :
    backlundTheta T - backlundThetaMain T =
      backlundThetaDeviation T + backlundGammaRemainder T := by
  have hm := backlundTheta_stirling_main hT
  dsimp only at hm
  simp only [Complex.sub_im] at hm
  dsimp only [backlundTheta, backlundGammaRemainder]
  simp only [Complex.sub_im]
  linarith only [hm]

/-- A nonpositive imaginary Stirling remainder bounded below by `-1/(4T)`
implies the required Gamma-phase error bound at positive height. Combine the
remainder identity with the elementary deviation estimate. -/
theorem backlundTheta_error_of_signed_remainder {T : ℝ} (hT : 0 < T)
    (hlo : -(1 / (4 * T)) ≤ backlundGammaRemainder T) (hhi : backlundGammaRemainder T ≤ 0) :
    |backlundTheta T - backlundThetaMain T| ≤ 1 / (4 * T) := by
  apply backlundTheta_error_of_remainder hT (A := -backlundGammaRemainder T)
  · linarith only [hhi]
  · linarith only [hlo]
  · rw [backlundTheta_error_eq_remainder hT]
    ring

end PseudoPrime.PrimeTestBounds.MillerRabin
