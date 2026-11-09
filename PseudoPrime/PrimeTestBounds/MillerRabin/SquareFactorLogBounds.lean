/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Logarithmic bounds for square-divisor count stages -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If the logarithm of the input is at most twice the logarithm of `W`,
a prime-square divisor has base at most `W`. Monotonicity of logarithms
transfers the input bound to the prime factor. -/
theorem square_factor_le_of_log_bound {n p W : ℕ} (hn : 1 < n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hW : 0 < W) (hlog : Real.log n ≤ 2 * Real.log W) : p ≤ W := by
  have hpow : p ^ 2 ≤ n := Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv
  have hl := Real.log_le_log (Nat.cast_pos.mpr (pow_pos hp.pos 2)) (Nat.cast_le.mpr hpow)
  rw [Nat.cast_pow, Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hpW : Real.log (p : ℝ) ≤ Real.log (W : ℝ) := by linarith only [hl, hlog]
  exact_mod_cast (Real.log_le_log_iff (Nat.cast_pos.mpr hp.pos) (Nat.cast_pos.mpr hW)).mp hpW

/-- An integer at least `W` has a square whose logarithm exceeds the
scaled budget when twice the logarithm of `W` does. -/
theorem square_factor_budget_of_log {p W H : ℕ} (hW : 0 < W) (hbig : W ≤ p)
    (hlow : (H : ℝ) / 10 < 2 * Real.log W) : (H : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have hl := Real.log_le_log (Nat.cast_pos.mpr hW) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [hl, hlow]

end PseudoPrime.PrimeTestBounds.MillerRabin
