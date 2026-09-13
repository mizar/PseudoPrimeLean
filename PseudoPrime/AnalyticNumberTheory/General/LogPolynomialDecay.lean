/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Polynomial-in-`log` decay and monotonicity facts

Elementary real-analysis facts about `(x + 3) log(x + 3)` and ratios of `log n` to powers of `n`:
monotonicity of the former, and `atTop` decay to `0` of `log n / n²` and of
`√(K n log n) (K n log n + 1) / n²` for a fixed positive constant `K`. None of this mentions any
particular `L`-function or contour construction.
-/

namespace PseudoPrime.AnalyticNumberTheory.General

/-- `(x + 3) log(x + 3)` is monotone on `x ≥ 0`. -/
theorem add_three_mul_log_add_three_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (x + 3) * Real.log (x + 3) ≤ (y + 3) * Real.log (y + 3) :=
  mul_le_mul (by linarith) (Real.log_le_log (by linarith) (by linarith))
    (Real.log_nonneg (by linarith)) (by linarith)

/-- `log n / n² → 0`. -/
theorem tendsto_log_div_sq_atTop :
    Filter.Tendsto (fun n : ℝ => Real.log n / n ^ 2) Filter.atTop (nhds 0) := by
  have hL1 : Filter.Tendsto (fun n : ℝ => Real.log n / n) Filter.atTop (nhds 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Filter.Tendsto (fun n : ℝ => n⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hmul : Filter.Tendsto (fun n : ℝ => Real.log n / n * n⁻¹) Filter.atTop (nhds (0 * 0)) :=
    hL1.mul hinv
  rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [Filter.eventually_ne_atTop (0 : ℝ)] with n hn
  field_simp

/--
Input/assumptions: a positive constant `K`.
Conclusion: `√(K·n·log n) · (K·n·log n + 1) / n² → 0` as `n → ∞`.
Content: squaring reduces the claim to
`K·n·log n · (K·n·log n + 1)² / n⁴ = K³(log n)³/n + 2K²(log n)²/n² + K(log n)/n³ → 0`, a sum of
three `Real.tendsto_pow_log_div_mul_add_atTop`-type terms; then `√` is recovered via continuity at
`0` (the expression is eventually `≥ 0`).
Role: the general `O((log n)^{3/2}/√n) → 0` shape used to make a genus-sum-type error term vanish.
-/
theorem tendsto_sqrt_mul_add_one_div_sq_atTop (K : ℝ) (hK : 0 < K) :
    Filter.Tendsto (fun n : ℝ => Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1) / n ^ 2)
      Filter.atTop (nhds 0) := by
  set f : ℝ → ℝ := fun n => Real.sqrt (K * n * Real.log n) * (K * n * Real.log n + 1) / n ^ 2 with
    hf_def
  have hL3 : Filter.Tendsto (fun n : ℝ => Real.log n ^ 3 / n) Filter.atTop (nhds 0) := by
    simpa only [one_mul, add_zero] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 3 one_ne_zero
  have hL2 : Filter.Tendsto (fun n : ℝ => Real.log n ^ 2 / n) Filter.atTop (nhds 0) := by
    simpa only [one_mul, add_zero] using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have hL1 : Filter.Tendsto (fun n : ℝ => Real.log n / n) Filter.atTop (nhds 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hinv : Filter.Tendsto (fun n : ℝ => n⁻¹) Filter.atTop (nhds 0) := tendsto_inv_atTop_zero
  have hinv2 : Filter.Tendsto (fun n : ℝ => (n ^ 2)⁻¹) Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Filter.tendsto_pow_atTop (by norm_num only))
  have hA : Filter.Tendsto (fun n : ℝ => K ^ 3 * (Real.log n ^ 3 / n)) Filter.atTop (nhds 0) := by
    have := hL3.const_mul (K ^ 3)
    simpa only [mul_zero] using this
  have hB :
    Filter.Tendsto (fun n : ℝ => 2 * K ^ 2 * (Real.log n ^ 2 / n) * n⁻¹) Filter.atTop (nhds 0) := by
    have := (hL2.const_mul (2 * K ^ 2)).mul hinv
    simpa only [mul_zero] using this
  have hC :
    Filter.Tendsto (fun n : ℝ => K * (Real.log n / n) * (n ^ 2)⁻¹) Filter.atTop (nhds 0) := by
    have := (hL1.const_mul K).mul hinv2
    simpa only [mul_zero] using this
  have hsum :
    Filter.Tendsto
      (fun n : ℝ =>
        K ^ 3 * (Real.log n ^ 3 / n) +
          (2 * K ^ 2 * (Real.log n ^ 2 / n) * n⁻¹ + K * (Real.log n / n) * (n ^ 2)⁻¹))
      Filter.atTop (nhds 0) := by
    have := hA.add (hB.add hC)
    simpa only [add_zero] using this
  have hsq : Filter.Tendsto (fun n : ℝ => (f n) ^ 2) Filter.atTop (nhds 0) := by
    refine hsum.congr' ?_
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with n hn1
    have hn0 : (0 : ℝ) < n := by linarith
    have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hKn : 0 ≤ K * n * Real.log n := by positivity
    have hne : n ≠ 0 := hn0.ne'
    rw [hf_def]
    dsimp only
    rw [div_pow, mul_pow, Real.sq_sqrt hKn]
    field_simp
    ring
  have hnonneg : ∀ᶠ n in Filter.atTop, 0 ≤ f n := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with n hn1
    have hL : 0 ≤ Real.log n := Real.log_nonneg hn1
    have hKn : 0 ≤ K * n * Real.log n := by positivity
    rw [hf_def]
    dsimp only
    positivity
  have hsqrt_cont : Filter.Tendsto Real.sqrt (nhds (0 : ℝ)) (nhds 0) := by
    have h := Real.continuous_sqrt.tendsto (0 : ℝ)
    rwa [Real.sqrt_zero] at h
  have hcomp : Filter.Tendsto (fun n => Real.sqrt ((f n) ^ 2)) Filter.atTop (nhds 0) :=
    hsqrt_cont.comp hsq
  refine hcomp.congr' ?_
  filter_upwards [hnonneg] with n hn
  rw [Real.sqrt_sq hn]

end PseudoPrime.AnalyticNumberTheory.General
