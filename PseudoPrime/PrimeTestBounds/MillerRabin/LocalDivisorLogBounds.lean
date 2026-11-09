/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Logarithmic bounds for local divisors -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A positive local modulus q with q²≤10^9*n has log(q) at most
(log(n)+9log(10))/2. Apply logarithmic monotonicity and product identities.
This transfers a local arithmetic size bound into the analytic cutoff. -/
theorem local_log_le_of_square_le {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    Real.log q ≤ (Real.log n + 9 * Real.log 10) / 2 := by
  have h :=
    Real.log_le_log (sq_pos_of_pos (Nat.cast_pos.mpr hq : (0 : ℝ) < q))
      (by exact_mod_cast hsize : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 9 * n)
  rw [Real.log_pow,
    Real.log_mul (pow_ne_zero 9 (by norm_num only : (10 : ℝ) ≠ 0)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
