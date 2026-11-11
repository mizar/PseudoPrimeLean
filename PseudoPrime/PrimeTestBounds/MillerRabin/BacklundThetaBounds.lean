/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundTheta
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv

/-! # Elementary Gamma-phase deviation -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The elementary deviation of the Gamma-phase main part from the
Riemann–von Mangoldt approximation. Its intended domain is positive heights. -/
noncomputable def backlundThetaDeviation (T : ℝ) : ℝ :=
  T / 4 * Real.log (1 + 1 / (4 * T ^ 2)) + (1 / 4) * Real.arctan (1 / (2 * T))

/-- At positive height, the elementary Gamma-phase deviation lies between
zero and `3/(16T)`. Bound `log(1+x)` and `arctan x` by `x`, then simplify
the two rational terms. -/
theorem backlundThetaDeviation_bounds {T : ℝ} (hT : 0 < T) :
    0 ≤ backlundThetaDeviation T ∧ backlundThetaDeviation T ≤ 3 / (16 * T) := by
  dsimp only [backlundThetaDeviation]
  have hq : 0 ≤ 1 / (4 * T ^ 2) := by
    apply one_div_nonneg.mpr
    exact mul_nonneg (by norm_num only) (sq_nonneg T)
  have hr : 0 ≤ 1 / (2 * T) := one_div_nonneg.mpr (mul_nonneg (by norm_num only) hT.le)
  have hlog0 : 0 ≤ Real.log (1 + 1 / (4 * T ^ 2)) := Real.log_nonneg (by linarith only [hq])
  have hlog : Real.log (1 + 1 / (4 * T ^ 2)) ≤ 1 / (4 * T ^ 2) := by
    have h := Real.log_le_sub_one_of_pos (show 0 < 1 + 1 / (4 * T ^ 2) by linarith only [hq])
    linarith only [h]
  have hatan0 : 0 ≤ Real.arctan (1 / (2 * T)) := Real.arctan_nonneg.mpr hr
  have hatan := Real.arctan_le_self hr
  have h1 := mul_le_mul_of_nonneg_left hlog (by linarith only [hT] : 0 ≤ T / 4)
  have h2 := mul_le_mul_of_nonneg_left hatan (by norm_num only : (0 : ℝ) ≤ 1 / 4)
  have he : T / 4 * (1 / (4 * T ^ 2)) + (1 / 4 : ℝ) * (1 / (2 * T)) = 3 / (16 * T) := by
    simp only [div_eq_mul_inv, mul_inv, ← inv_pow]
    norm_num only
    have hinv := mul_inv_cancel₀ hT.ne'
    have hinv' := congrArg (fun z : ℝ => z * T⁻¹) hinv
    nlinarith only [hinv']
  constructor
  · exact
      add_nonneg (mul_nonneg (by linarith only [hT]) hlog0) (mul_nonneg (by norm_num only) hatan0)
  · linarith only [h1, h2, he]

/-- If the Gamma-phase difference is the elementary deviation minus a
remainder between zero and `1/(4T)`, its absolute value is at most `1/(4T)`.
This is the final arithmetic step after the Euler–Maclaurin remainder and
the elementary main-part identity have been established. -/
theorem backlundTheta_error_of_remainder {T A : ℝ} (hT : 0 < T) (hA0 : 0 ≤ A) (hA : A ≤ 1 / (4 * T))
    (he : backlundTheta T - backlundThetaMain T = backlundThetaDeviation T - A) :
    |backlundTheta T - backlundThetaMain T| ≤ 1 / (4 * T) := by
  rw [he]
  apply abs_le.mpr
  have hD := backlundThetaDeviation_bounds hT
  have hInv : 0 ≤ 1 / T := one_div_nonneg.mpr hT.le
  have h1 : 3 / (16 * T) = (3 / 16 : ℝ) * (1 / T) := by ring
  have h2 : 1 / (4 * T) = (1 / 4 : ℝ) * (1 / T) := by ring
  rw [h1] at hD
  rw [h2] at hA ⊢
  constructor <;> nlinarith only [hD.1, hD.2, hA0, hA, hInv]

end PseudoPrime.PrimeTestBounds.MillerRabin
