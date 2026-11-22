/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLinearExtension
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ChebyshevLcmBounds

/-! # Integer certificates for linear Chebyshev bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A power-of-two upper bound for the least common multiple through `b` bounds `psi b`.
The integer budget `70k ≤ 111a` then gives the endpoint condition for the `111/100` cell. -/
theorem psi_le_111_of_lcm_bound {a b k : ℕ} (hlcm : Nat.lcmUpto b ≤ 2 ^ k)
    (hbudget : 70 * k ≤ 111 * a) : Chebyshev.psi b ≤ (111 / 100 : ℝ) * a := by
  rw [Chebyshev.psi_eq_log_lcmUpto]
  have hl : (0 : ℝ) < Nat.lcmUpto b := by exact_mod_cast Nat.lcmUpto_pos b
  have hpow : (Nat.lcmUpto b : ℝ) ≤ (2 : ℝ) ^ k := by exact_mod_cast hlcm
  have hlog := Real.log_le_log hl hpow
  rw [Real.log_pow] at hlog
  have hk :=
    mul_le_mul_of_nonneg_left (le_of_lt Real.log_two_lt_d9) (Nat.cast_nonneg k : (0 : ℝ) ≤ k)
  have hb : (70 : ℝ) * k ≤ 111 * a := by exact_mod_cast hbudget
  linarith only [hlog, hk, hb]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
