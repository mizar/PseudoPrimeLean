/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalDivisorLogBounds
public import PseudoPrime.LLS.DecimalLogBounds

/-! # Coefficient 0.282924 for MR local divisor moduli

At n≥10^142, a local modulus with q²≤10^9*n has its old LLS envelope
max(3000,log(q)²) strictly below (282924/1000000)log(n)².
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A nonnegative logarithmic shift at most (9/142)L gives the strict
quarter-square coefficient 282924/1000000. Compare squares with (151/142)L and use
the exact positive rational gap. This absorbs the finite-index logarithmic shift. -/
theorem local_shift_quarter_lt {L A : ℝ} (hL : 0 < L) (hA : 0 ≤ A) (hAL : A ≤ (9 / 142 : ℝ) * L) :
    (L + A) ^ 2 / 4 < (282924 / 1000000 : ℝ) * L ^ 2 := by
  have hb : L + A ≤ (151 / 142 : ℝ) * L := by linarith only [hAL]
  have hs := mul_self_le_mul_self (add_nonneg hL.le hA) hb
  have hpos := sq_pos_of_pos hL
  nlinarith only [hs, hpos]

/-- At log scale at least 326, the coefficient 282924/1000000 envelope exceeds 3000.
Compare squares at the endpoint. This covers small local moduli by prime divisors. -/
theorem local_small_modulus_floor_lt {L : ℝ} (hL : 326 ≤ L) :
    (3000 : ℝ) < (282924 / 1000000 : ℝ) * L ^ 2 := by
  have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 326) hL 2
  nlinarith only [hs]

/-- The decimal cutoff 10^142 absorbs both 3000 and the shifted quarter-square.
Retain the exact log(10) factor to bound the relative shift by 9/142.
This is the finite-index local coefficient certificate. -/
theorem local_shifted_envelope_lt_of_decimal {n : ℕ} (hn : 10 ^ 142 ≤ n) :
    max 3000 (((Real.log n + 9 * Real.log 10) ^ 2) / 4) <
      (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 := by
  have hl := LLS.log_ge_of_pow10_le hn
  norm_num only [Nat.cast_ofNat] at hl
  have hL : 326 ≤ Real.log n := by linarith only [hl]
  have hlog :=
    Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 10) 142)
      (by exact_mod_cast hn : (10 : ℝ) ^ 142 ≤ n)
  rw [Real.log_pow] at hlog
  norm_num only [Nat.cast_ofNat] at hlog
  have hAL : 9 * Real.log 10 ≤ (9 / 142 : ℝ) * Real.log n := by
    have h := mul_le_mul_of_nonneg_left hlog (by norm_num only : (0 : ℝ) ≤ 9 / 142)
    nlinarith only [h]
  apply max_lt
  · exact local_small_modulus_floor_lt hL
  · exact
      local_shift_quarter_lt ((by norm_num only : (0 : ℝ) < 326).trans_le hL)
        (mul_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 10))) hAL

/-- For n≥10^142 and positive q with q²≤10^9*n, the old LLS local
envelope is strictly below (282924/1000000)log(n)². Square the nonnegative local log
and use the certified shifted envelope. This feeds the local subgroup MR witness. -/
theorem local_envelope_lt_of_square_le {n q : ℕ} (hn : 10 ^ 142 ≤ n) (hq : 0 < q)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    max 3000 ((Real.log q) ^ 2) < (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 := by
  have hnpos : 0 < n := lt_of_lt_of_le (pow_pos (by decide : (0 : ℕ) < 10) 142) hn
  have hlog := local_log_le_of_square_le hnpos hq hsize
  have hs := mul_self_le_mul_self (Real.log_natCast_nonneg q) hlog
  have hbound : (Real.log q) ^ 2 ≤ (Real.log n + 9 * Real.log 10) ^ 2 / 4 := by nlinarith only [hs]
  exact (max_le_max (le_refl 3000) hbound).trans_lt (local_shifted_envelope_lt_of_decimal hn)

end PseudoPrime.PrimeTestBounds.MillerRabin
