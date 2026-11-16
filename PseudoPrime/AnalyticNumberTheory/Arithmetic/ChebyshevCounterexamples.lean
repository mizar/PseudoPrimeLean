/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Exact lower-endpoint counterexamples for normalized Chebyshev psi errors

Integer least-common-multiple comparisons certify the points 1422.99 and 16.99.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- An integer power comparison bounds `psi n` from above without a prime table.
Taking logarithms and dividing by sixteen gives the bound used at the two small endpoints. -/
private theorem psi_upper_of_power {n k : ℕ}
    (h : Nat.lcmUpto n ^ 16 ≤ 2 ^ k) :
    Chebyshev.psi n ≤ k * Real.log 2 / 16 := by
  have hp : (0 : ℝ) < Nat.lcmUpto n := by exact_mod_cast Nat.lcmUpto_pos n
  have hc : (Nat.lcmUpto n : ℝ) ^ 16 ≤ (2 : ℝ) ^ k := by exact_mod_cast h
  have hl := Real.log_le_log (pow_pos hp 16) hc
  rw [Real.log_pow, Real.log_pow, ← Chebyshev.psi_eq_log_lcmUpto] at hl
  norm_num only [Nat.cast_ofNat] at hl
  linarith only [hl]

/-- At `x = 1422.99`, the normalized Chebyshev ψ error is strictly greater than `4 / 5`.
The proof uses a kernel-checked least-common-multiple bound and rational bounds on log and sqrt. -/
theorem psi_error_lower_counterexample :
    |Chebyshev.psi (142299 / 100) - 142299 / 100| / Real.sqrt (142299 / 100) > (4 / 5 : ℝ) := by
  have hc : Nat.lcmUpto 1422 ^ 16 ≤ 2 ^ 32148 := by decide +kernel
  have hp := psi_upper_of_power hc
  have hf : ⌊(142299 / 100 : ℝ)⌋₊ = 1422 := by
    norm_num only [Nat.floor_eq_iff (by norm_num only : (0 : ℝ) ≤ 142299 / 100), and_self]
  have he := Chebyshev.psi_eq_psi_coe_floor (142299 / 100)
  rw [hf] at he
  have hs : Real.sqrt (142299 / 100) < (3773 / 100 : ℝ) :=
    (Real.sqrt_lt (by norm_num only) (by norm_num only)).2 (by norm_num only)
  apply (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num only))).2
  have ha := neg_le_abs (Chebyshev.psi (142299 / 100) - 142299 / 100)
  norm_num only [Nat.cast_ofNat] at hp he
  rw [he] at ha ⊢
  linarith only [hp, hs, ha, Real.log_two_lt_d9]

/-- At `x = 16.99`, the normalized Chebyshev ψ error exceeds `81 / 100`.
The proof uses a kernel-checked least-common-multiple bound and rational bounds on log and sqrt. -/
theorem psi_error_81_lower_counterexample :
    |Chebyshev.psi (1699 / 100) - 1699 / 100| / Real.sqrt (1699 / 100) > (81 / 100 : ℝ) := by
  have hc : Nat.lcmUpto 16 ^ 16 ≤ 2 ^ 312 := by decide +kernel
  have hp := psi_upper_of_power hc
  have hf : ⌊(1699 / 100 : ℝ)⌋₊ = 16 := by
    norm_num only [Nat.floor_eq_iff (by norm_num only : (0 : ℝ) ≤ 1699 / 100), and_self]
  have he := Chebyshev.psi_eq_psi_coe_floor (1699 / 100)
  rw [hf] at he
  have hs : Real.sqrt (1699 / 100) < (413 / 100 : ℝ) :=
    (Real.sqrt_lt (by norm_num only) (by norm_num only)).2 (by norm_num only)
  apply (lt_div_iff₀ (Real.sqrt_pos.2 (by norm_num only))).2
  have ha := neg_le_abs (Chebyshev.psi (1699 / 100) - 1699 / 100)
  norm_num only [Nat.cast_ofNat] at hp he
  rw [he] at ha ⊢
  linarith only [hp, hs, ha, Real.log_two_lt_d9]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
