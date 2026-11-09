/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalDecimalScale
public import PseudoPrime.LLS.DecimalLogBounds

/-! # Local logarithmic cutoff at scale 25000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A local subgroup with the stated size bound has its logarithmic cutoff below any
quadratic coefficient at least (5313/10000)^2 from scale 25000. Bound the logarithm
of the subgroup modulus and absorb both its additive term and the fixed cutoff. -/
theorem local_log_sq_le_of_size {n q : ℕ} (hn : 0 < n) (hq : 0 < q) (hsize : q ^ 2 ≤ 10 ^ 12 * n)
    (hL : (25000 : ℝ) ≤ Real.log n) {C : ℝ} (hC : (5313 / 10000 : ℝ) ^ 2 ≤ C) :
    max (3000 : ℝ) (Real.log q ^ 2) ≤ C * Real.log n ^ 2 := by
  have hR : (q : ℝ) ^ 2 ≤ (10 : ℝ) ^ 12 * n := by exact_mod_cast hsize
  have hl := Real.log_le_log (pow_pos (Nat.cast_pos.mpr hq) 2) hR
  rw [Real.log_pow, Real.log_mul (pow_ne_zero _ (by norm_num only)) (Nat.cast_pos.mpr hn).ne',
    Real.log_pow] at hl
  norm_num only [Nat.cast_ofNat] at hl
  have hLp : 0 < Real.log n := by linarith only [hL]
  have hcap : Real.log q ≤ (5313 / 10000 : ℝ) * Real.log n := by
    nlinarith only [hl, log_ten_lt_seven_thirds, hL]
  have hp : 0 ≤ (5313 / 10000 : ℝ) * Real.log n := mul_nonneg (by norm_num only) hLp.le
  have hs := (sq_le_sq₀ (Real.log_natCast_nonneg q) hp).mpr hcap
  have hsq := mul_le_mul_of_nonneg_right hC (sq_nonneg (Real.log n))
  have hbase : (1 / 4 : ℝ) ≤ C := by nlinarith only [hC]
  have hc := mul_le_mul_of_nonneg_right hbase (sq_nonneg (Real.log n))
  apply max_le
  · nlinarith only [hc, hL]
  · nlinarith only [hs, hsq]

end PseudoPrime.PrimeTestBounds.MillerRabin
