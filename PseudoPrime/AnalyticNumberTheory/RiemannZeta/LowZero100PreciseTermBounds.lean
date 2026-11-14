/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PowerBounds
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogArithmetic
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100PreciseLogs
import PseudoPrime.Analysis.PreciseLogBounds
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZetaPowerLogApprox

/-! # Precise complex-power terms at low-zero endpoints -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

private theorem endpoint_precise_log_sound (n : ℕ) (h : endpointPreciseLogCheck n = true) :
    0 ≤ endpointPreciseLog n ∧
      endpointPreciseLog n ≤ 7 ∧ |Real.log n - (endpointPreciseLog n : ℝ)| ≤ 1 / 100000000000 := by
  have hh := Bool.and_eq_true_iff.mp h
  have hr : 0 ≤ endpointPreciseLog n ∧ endpointPreciseLog n ≤ 7 := of_decide_eq_true hh.1
  have hl := Analysis.rational_precise_log_check_sound hh.2
  simp only [Rat.cast_natCast, Rat.cast_sub, Rat.cast_add, Rat.cast_div, Rat.cast_one,
    Rat.cast_ofNat] at hl
  refine ⟨hr.1, hr.2, abs_le.mpr ?_⟩
  constructor <;> linarith only [hl.1, hl.2]

/-- For rational `0 ≤ t ≤ 100` and `1 ≤ n ≤ 128`, the rounded power built from the precise
shared logarithm differs from `n^(-(1/2+it))` by at most `31/10000000000`. The proof combines
the kernel-checked logarithm interval and the rounded exponential error. -/
theorem norm_endpoint_precise_term (t : ℚ) (ht0 : 0 ≤ t) (ht : t ≤ 100) (n : ℕ)
    (hn : n ∈ Finset.Icc (1 : ℕ) 128) :
    ‖(n : ℂ) ^ (-((((1 / 2 : ℝ) : ℂ) + ((t : ℝ) : ℂ) * Complex.I))) -
          Analysis.rationalComplexCast (endpointPowerApprox t (endpointPreciseLog n))‖ ≤
      (31 / 10000000000 : ℝ) := by
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
  have hc := endpoint_precise_log_sound n (endpoint_precise_log_checks n hn)
  have h1 :=
    norm_cpow_log_approx s hs0 n (Finset.mem_Icc.mp hn).1 (endpointPreciseLog n) hc.1 hc.2.2
  have h2 := norm_endpoint_power_approx t (endpointPreciseLog n) ht0 ht hc.1 hc.2.1
  change
    ‖(n : ℂ) ^ (-s) - Analysis.rationalComplexCast (endpointPowerApprox t (endpointPreciseLog n))‖ ≤
      _
  have h :=
    norm_sub_le_norm_sub_add_norm_sub ((n : ℂ) ^ (-s))
      (Complex.exp ((-s) * (endpointPreciseLog n : ℂ)))
      (Analysis.rationalComplexCast (endpointPowerApprox t (endpointPreciseLog n)))
  linarith only [h, h1, h2, hs]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
