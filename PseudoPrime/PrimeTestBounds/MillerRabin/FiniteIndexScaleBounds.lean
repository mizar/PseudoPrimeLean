/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalDecimalScale
public import PseudoPrime.LLS.DecimalLogBounds
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-! # Fixed decimal thresholds for finite-index classification -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A logarithmic scale of 250 already places n above the cube of the
10^9 finite-index threshold. -/
theorem pow10_27_le_of_log_ge_250 {n : ℕ} [NeZero n] (hL : 250 ≤ Real.log n) : 10 ^ 27 ≤ n := by
  by_contra hnot
  have hsmall : n < 10 ^ 27 := Nat.lt_of_not_ge hnot
  have hcast : (n : ℝ) < (10 : ℝ) ^ 27 := by exact_mod_cast hsmall
  have hlogsmall := Real.log_lt_log (Nat.cast_pos.mpr (NeZero.pos n)) hcast
  have hlog27 : Real.log ((10 : ℝ) ^ 27) < 250 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [log_ten_lt_seven_thirds]
  exact (not_lt_of_ge hL) (hlogsmall.trans hlog27)

/-- A logarithmic scale of 240 already places n above the cube of the
10^9 finite-index threshold. -/
theorem pow10_27_le_of_log_ge_240 {n : ℕ} [NeZero n] (hL : 240 ≤ Real.log n) : 10 ^ 27 ≤ n := by
  by_contra hnot
  have hsmall : n < 10 ^ 27 := Nat.lt_of_not_ge hnot
  have hcast : (n : ℝ) < (10 : ℝ) ^ 27 := by exact_mod_cast hsmall
  have hlogsmall := Real.log_lt_log (Nat.cast_pos.mpr (NeZero.pos n)) hcast
  have hlog27 : Real.log ((10 : ℝ) ^ 27) < 240 := by
    rw [Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    nlinarith only [log_ten_lt_seven_thirds]
  exact (not_lt_of_ge hL) (hlogsmall.trans hlog27)

end PseudoPrime.PrimeTestBounds.MillerRabin
