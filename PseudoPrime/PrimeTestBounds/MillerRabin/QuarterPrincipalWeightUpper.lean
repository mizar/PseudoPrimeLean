/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteGeneralWeight
public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleFullPrincipal

/-! # Upper weight bounds throughout the sixth-pole kernel support -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A positive index inside the support has the explicit scaled-weight
formula with a single square-root denominator. The scale root cancels. -/
theorem quarter_weight_eq {X t : ℝ} (hX : 0 < X) (ht : 0 < t) (hlog : Real.log (t / X) ≤ 21 / 8) :
    refinedScaledWeight X t =
      refinedCoord (t / X) ^ 5 * Real.exp (-refinedCoord (t / X)) / (120 * Real.sqrt t) := by
  have hu : 0 < t / X := div_pos ht hX
  dsimp only [refinedScaledWeight, refinedKernelWeight]
  rw [refinedKernelWeight_eq hu hlog, refinedWeight, Real.sqrt_div ht.le]
  have hs : Real.sqrt X ≠ 0 := (Real.sqrt_pos.mpr hX).ne'
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  have hc := mul_inv_cancel₀ hs
  linear_combination
    (refinedCoord (t * X⁻¹) ^ 5 * Real.exp (-refinedCoord (t * X⁻¹)) * (Real.sqrt t)⁻¹ / 120) * hc

/-- Upper bounds for the coordinate and exponential, together with a
positive lower square-root bound, give an upper scaled weight throughout
the support. All inequalities are monotone in the nonnegative factors. -/
theorem quarter_weight_upper {X t C E R : ℝ} (hX : 0 < X) (ht : 0 < t)
    (hlog : Real.log (t / X) ≤ 21 / 8) (hc0 : 0 ≤ refinedCoord (t / X))
    (hc : refinedCoord (t / X) ≤ C) (hE : Real.exp (-refinedCoord (t / X)) ≤ E) (hR0 : 0 < R)
    (hR : R ≤ Real.sqrt t) : refinedScaledWeight X t ≤ C ^ 5 * E / (120 * R) := by
  rw [quarter_weight_eq hX ht hlog]
  have hC0 : 0 ≤ C := hc0.trans hc
  have hE0 : 0 ≤ E := (Real.exp_pos _).le.trans hE
  have hm := mul_le_mul (pow_le_pow_left₀ hc0 hc 5) hE (Real.exp_pos _).le (pow_nonneg hC0 5)
  exact
    div_le_div₀ (mul_nonneg (pow_nonneg hC0 5) hE0) hm (mul_pos (by norm_num only) hR0)
      (mul_le_mul_of_nonneg_left hR (by norm_num only))

/-- Beyond the positive support endpoint, the scaled principal weight is zero. -/
theorem quarter_weight_zero {X t : ℝ} (hX : 0 < X) (ht : X * Real.exp (21 / 8 : ℝ) < t) :
    refinedScaledWeight X t = 0 := by
  dsimp only [refinedScaledWeight]
  rw [refinedKernelWeight_zero_of_lt ((lt_div_iff₀ hX).mpr (by simpa only [mul_comm] using ht)),
    zero_div]

/-- A nonnegative coordinate envelope bounds the scaled weight both inside
and outside the kernel support. Outside the support the weight vanishes. -/
theorem quarter_weight_upper_any {X t C E R : ℝ} (hX : 0 < X) (ht : 0 < t) (hC0 : 0 ≤ C)
    (hc : refinedCoord (t / X) ≤ C) (hE : Real.exp (-refinedCoord (t / X)) ≤ E) (hR0 : 0 < R)
    (hR : R ≤ Real.sqrt t) : refinedScaledWeight X t ≤ C ^ 5 * E / (120 * R) := by
  by_cases hlog : Real.log (t / X) ≤ 21 / 8
  · have hc0 : 0 ≤ refinedCoord (t / X) := by
      dsimp only [refinedCoord]
      linarith only [hlog]
    exact quarter_weight_upper hX ht hlog hc0 hc hE hR0 hR
  · have hu : 0 < t / X := div_pos ht hX
    have hexp : Real.exp (21 / 8 : ℝ) < t / X := by
      have h := Real.exp_lt_exp.mpr (lt_of_not_ge hlog)
      simpa only [Real.exp_log hu] using h
    have hout : X * Real.exp (21 / 8 : ℝ) < t := by
      simpa only [mul_comm] using (lt_div_iff₀ hX).mp hexp
    rw [quarter_weight_zero hX hout]
    have hE0 : 0 ≤ E := (Real.exp_pos _).le.trans hE
    exact div_nonneg (mul_nonneg (pow_nonneg hC0 5) hE0) (by positivity)

end PseudoPrime.PrimeTestBounds.MillerRabin
