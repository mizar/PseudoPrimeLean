/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
public import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! # Endpoint limits for the Gamma logarithm -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

private theorem nat_log_mul_limit (z : ℂ) :
    Filter.Tendsto (fun n : ℕ ↦ (n : ℂ) * Complex.log (1 + z / n)) Filter.atTop (nhds z) := by
  apply Complex.tendsto_nat_mul_log_one_add_of_tendsto
  apply tendsto_nhds_of_eventually_eq
  filter_upwards [Filter.eventually_ne_atTop (0 : ℕ)] with n hn
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  simpa only [mul_comm] using div_mul_cancel₀ z hn'

private theorem log_limit (z : ℂ) :
    Filter.Tendsto (fun n : ℕ ↦ Complex.log (1 + z / n)) Filter.atTop (nhds 0) := by
  have hi : Filter.Tendsto (fun n : ℕ ↦ (n : ℂ)⁻¹) Filter.atTop (nhds 0) := by
    have hr : Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)⁻¹) Filter.atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
    simpa only [Complex.ofReal_natCast, Complex.ofReal_inv, Complex.ofReal_zero] using hr.ofReal
  have hg := (hi.const_mul z).const_add (1 : ℂ)
  simp only [mul_zero, add_zero] at hg
  have hc :=
    (Complex.differentiableAt_log (z := (1 : ℂ))
        (Complex.mem_slitPlane_iff.mpr
          (Or.inl (by norm_num only [Complex.one_re])))).continuousAt.tendsto
  simpa only [Function.comp_def, div_eq_mul_inv, Complex.log_one] using hc.comp hg

private theorem log_ratio_eventually (z : ℂ) (hz : 0 < z.re) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Complex.log ((n : ℂ) + z) - Complex.log (n : ℂ) = Complex.log (1 + z / n) := by
  filter_upwards [Filter.eventually_gt_atTop (0 : ℕ)] with n hn
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hn)
  have hr : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : (n : ℂ) + z ≠ 0 := by
    apply Complex.ne_zero_of_re_pos
    simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hr, hz]
  have hq : (1 : ℂ) + z / n = ((n : ℂ) + z) / n := by rw [add_div, div_self hn0]
  have hnz : (1 : ℂ) + z / n ≠ 0 := by
    rw [hq]
    exact div_ne_zero hsum hn0
  have hm : (n : ℂ) * (1 + z / n) = n + z := by rw [hq, mul_comm, div_mul_cancel₀ _ hn0]
  have hl := Complex.log_ofReal_mul hr hnz
  rw [Complex.ofReal_natCast, hm, Complex.ofReal_log hr.le, Complex.ofReal_natCast] at hl
  rw [hl]
  ring

/-- For every complex `z`, the normalized logarithmic endpoint correction
`(n + z - 1/2) log(1 + z/n) - z` tends to zero. The leading term uses the
complex logarithm limit and the remaining fixed coefficient multiplies a
term tending to zero. -/
theorem gamma_endpoint_log_ratio_tendsto (z : ℂ) :
    Filter.Tendsto (fun n : ℕ ↦ ((n : ℂ) + z - 1 / 2) * Complex.log (1 + z / n) - z) Filter.atTop
      (nhds 0) := by
  have h := ((nat_log_mul_limit z).add ((log_limit z).const_mul (z - 1 / 2))).sub_const z
  simp only [mul_zero, add_zero, sub_self] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  ring

/-- If `z` lies in the right half-plane, the endpoint correction expressed
using `log(n + z) - log n` tends to zero. Positivity of `n` fixes the
logarithm branch and reduces the result to the normalized ratio limit. -/
theorem gamma_endpoint_log_difference_tendsto {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ ↦ ((n : ℂ) + z - 1 / 2) * (Complex.log ((n : ℂ) + z) - Complex.log (n : ℂ)) - z)
      Filter.atTop (nhds 0) := by
  apply (gamma_endpoint_log_ratio_tendsto z).congr'
  filter_upwards [log_ratio_eventually z hz] with n hn
  rw [hn]

/-- At positive real part, the imaginary part of the logarithmic endpoint
correction vanishes in the limit. This is the endpoint form used when
matching the finite Gamma sums to the phase remainder. -/
theorem gamma_endpoint_im_tendsto {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (((n : ℂ) + z - 1 / 2) * (Complex.log ((n : ℂ) + z) - Complex.log (n : ℂ)) - z).im)
      Filter.atTop (nhds 0) := by
  have h := (Complex.imCLM.continuous.tendsto 0).comp (gamma_endpoint_log_difference_tendsto hz)
  simpa only [Function.comp_def, Complex.imCLM_apply, map_zero] using h

/-- For `Re z > 0`, the imaginary part of the shifted Stirling main term,
after subtracting `Im z * log n`, tends to zero. This is the endpoint
limit required by the finite Euler–Maclaurin identity. -/
theorem gamma_stirling_main_im_tendsto {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ ↦
        (((n : ℂ) + z - 1 / 2) * Complex.log ((n : ℂ) + z) - ((n : ℂ) + z)).im - z.im * Real.log n)
      Filter.atTop (nhds 0) := by
  have h :
    Filter.Tendsto
      (fun n : ℕ ↦
        (((n : ℂ) + z - 1 / 2) * Complex.log ((n : ℂ) + z) - ((n : ℂ) + z)) -
          (z - 1 / 2) * Complex.log (n : ℂ) -
          ((n : ℂ) * Complex.log (n : ℂ) - n))
      Filter.atTop (nhds 0) := by
    apply (gamma_endpoint_log_difference_tendsto hz).congr'
    apply Filter.Eventually.of_forall
    intro n
    ring
  have hi := (Complex.imCLM.continuous.tendsto 0).comp h
  simp only [Function.comp_def, Complex.imCLM_apply, map_zero] at hi
  apply hi.congr'
  apply Filter.Eventually.of_forall
  intro n
  dsimp only
  rw [← Complex.ofReal_natCast n, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  simp only [Complex.sub_im, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re,
    Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero, mul_zero, zero_add, zero_mul]

/-- The harmonic contribution and the shifted Stirling phase cancel in the
limit for `Re z > 0`. This is the right-hand side of the finite imaginary
Euler–Maclaurin identity used for the Gamma logarithm. -/
theorem gamma_harmonic_phase_tendsto {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto
      (fun n : ℕ ↦
        z.im * ((harmonic n : ℝ) - Real.eulerMascheroniConstant) -
          (((n : ℂ) + z - 1 / 2) * Complex.log ((n : ℂ) + z) - ((n : ℂ) + z)).im)
      Filter.atTop (nhds 0) := by
  have hh := (Real.tendsto_harmonic_sub_log.sub_const Real.eulerMascheroniConstant).const_mul z.im
  simp only [sub_self, mul_zero] at hh
  have he := gamma_stirling_main_im_tendsto hz
  have h := hh.sub he
  simp only [sub_self] at h
  apply h.congr'
  apply Filter.Eventually.of_forall
  intro n
  ring

end PseudoPrime.AnalyticNumberTheory.Gamma
