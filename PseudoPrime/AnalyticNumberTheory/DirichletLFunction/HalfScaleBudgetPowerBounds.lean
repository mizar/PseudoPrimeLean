/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HalfScaleBudgetMonotonicity
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Power and logarithmic bounds for uniform half-scale remainder absorption -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For scale at least two and threshold at least one half, the combined low-height
majorant is at most `(10+5 log 2) x^sigma (log(x)+1)^2`. Dominate the square-root
term by `x^sigma` and each logarithmic factor by the common square. This reduces
the low and intermediate strips to one power-log expression. -/
theorem regularizedLowHeightMajorant_le_power_log_square {x σ : ℝ} (hx : 2 ≤ x) (hσ : 1 / 2 ≤ σ) :
    regularizedLowHeightMajorant x σ ≤ (10 + 5 * Real.log 2) * x ^ σ * (Real.log x + 1) ^ 2 := by
  let L := Real.log x + 1
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith only [hx])
  have hL : 1 ≤ L := by
    dsimp only [L]; linarith only [hlog]
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num only)
  have hp : 1 ≤ x ^ σ := Real.one_le_rpow (by linarith only [hx]) (by linarith only [hσ])
  have hsqrt : Real.sqrt x ≤ x ^ σ := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith only [hx]) hσ
  have hlogsq : (Real.log x) ^ 2 ≤ L ^ 2 := by
    dsimp only [L]
    nlinarith only [hlog]
  have hleft :=
    mul_le_mul hsqrt hlogsq (sq_nonneg (Real.log x)) (Real.rpow_nonneg (by linarith only [hx]) σ)
  have hpl := mul_nonneg (sub_nonneg.mpr hp) (sq_nonneg L)
  have hLsq : 1 ≤ L ^ 2 ∧ L ≤ L ^ 2 := by constructor <;> nlinarith only [hL, sq_nonneg (L - 1)]
  have hmid : Real.log 2 * L ≤ Real.log 2 * (x ^ σ * L ^ 2) :=
    mul_le_mul_of_nonneg_left (by nlinarith only [hpl, hLsq.2]) hlog2
  have hright :=
    mul_nonneg
      (mul_nonneg (by linarith only [hlog2] : 0 ≤ 8 + 4 * Real.log 2)
        (Real.rpow_nonneg (by linarith only [hx]) σ))
      (sub_nonneg.mpr hLsq.1)
  dsimp only [regularizedLowHeightMajorant]
  change _ ≤ (10 + 5 * Real.log 2) * x ^ σ * L ^ 2
  nlinarith only [hleft, hmid, hright]

/-- For any positive real exponent and natural logarithmic degree, the power of
`log x` divided by `x^delta` tends to zero at infinity. Specialize the proved
real-power logarithmic little-o theorem. This supplies scalar remainder decay. -/
theorem tendsto_log_pow_div_rpow {δ : ℝ} (hδ : 0 < δ) (n : ℕ) :
    Filter.Tendsto (fun x : ℝ ↦ (Real.log x) ^ n / x ^ δ) Filter.atTop (nhds 0) := by
  simpa only [Real.rpow_natCast] using
    (isLittleO_log_rpow_rpow_atTop (n : ℝ) hδ).tendsto_div_nhds_zero

/-- For every positive exponent, `(log(x)+1)^3/x^delta` tends to zero at infinity.
Expand the cube and combine the four logarithmic power limits. The added one
allows one nonnegative common majorant for all logarithmic error terms. -/
theorem tendsto_log_add_one_cube_div_rpow {δ : ℝ} (hδ : 0 < δ) :
    Filter.Tendsto (fun x : ℝ ↦ (Real.log x + 1) ^ 3 / x ^ δ) Filter.atTop (nhds 0) := by
  have h3 := tendsto_log_pow_div_rpow hδ 3
  have h2 := tendsto_log_pow_div_rpow hδ 2
  have h1 : Filter.Tendsto (fun x : ℝ ↦ Real.log x / x ^ δ) Filter.atTop (nhds 0) := by
    simpa only [pow_one] using tendsto_log_pow_div_rpow hδ 1
  have h0 : Filter.Tendsto (fun x : ℝ ↦ 1 / x ^ δ) Filter.atTop (nhds 0) := by
    simpa only [pow_zero] using tendsto_log_pow_div_rpow hδ 0
  have hc := (h3.add (h2.const_mul 3)).add ((h1.const_mul 3).add h0)
  simp only [mul_zero, add_zero] at hc
  convert hc using 1
  funext x
  ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
