/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PowerBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100LogChecks
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaPowerLogApprox

/-! # Certified complex-power terms at the low-zero endpoints -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For rational `0 ≤ t ≤ 100` and `1 ≤ n ≤ 128`, the internally computed
rational power approximates `n^(-(1/2+it))` within `51/100000000`. The shared
logarithm certificate and the rounded exponential bound are combined without
assuming numerical values of zeta. -/
theorem norm_endpoint_term_approx (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100) (n : ℕ)
    (hn : n ∈ Finset.Icc (1 : ℕ) 128) :
    ‖(n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I))) -
          Analysis.rationalComplexCast (endpointPowerApprox t (gridLogApprox n))‖ ≤
      (51 / 100000000 : ℝ) := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I
  have htR0 : (0 : ℝ) ≤ t := by exact_mod_cast ht0
  have htR : (t : ℝ) ≤ 100 := by exact_mod_cast ht
  have hs0 : 0 ≤ s.re := by
    dsimp only [s]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero]
    norm_num only
  have hs : ‖s‖ ≤ 101 := by
    have h := Complex.norm_le_abs_re_add_abs_im s
    simp only [s, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero,
      add_zero, zero_add, abs_of_nonneg htR0] at h
    norm_num only at h
    linarith only [h, htR]
  have hc := endpoint_log_checks n hn
  have hq := endpoint_log_range n hc
  have hl := endpoint_log_error n hc
  have h1 := norm_cpow_log_approx s hs0 n (Finset.mem_Icc.mp hn).1 (gridLogApprox n) hq.1 hl
  have h2 := norm_endpoint_power_approx t (gridLogApprox n) ht0 ht hq.1 hq.2
  change
    ‖(n : ℂ) ^ (-s) - Analysis.rationalComplexCast (endpointPowerApprox t (gridLogApprox n))‖ ≤ _
  have h :=
    norm_sub_le_norm_sub_add_norm_sub ((n : ℂ) ^ (-s)) (Complex.exp ((-s) * (gridLogApprox n : ℂ)))
      (Analysis.rationalComplexCast (endpointPowerApprox t (gridLogApprox n)))
  linarith only [h, h1, h2, hs]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
