/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.LogGrid

/-! # Real logarithm bounds from the binary grid and its residual -/

public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint

/-- The quadratic lower and linear upper polynomial enclose the nonnegative residual log. -/
theorem residual_log {z : ℝ} (hz : 0 ≤ z) :
    z * (2 - z) / 2 ≤ Real.log (1 + z) ∧ Real.log (1 + z) ≤ z := by
  constructor
  · apply le_trans ?_ (Real.le_log_one_add_of_nonneg hz)
    apply (le_div_iff₀ (show 0 < z + 2 by linarith only [hz])).2
    nlinarith only [mul_nonneg (sq_nonneg z) hz]
  · have h := Real.log_le_sub_one_of_pos (show 0 < 1 + z by linarith only [hz])
    linarith only [h]

/-- Given a binary exponent, grid index and nonnegative residual whose product is the input,
combine the certified grid intervals with the residual bounds to enclose its logarithm. -/
theorem grid_decomp {p z : ℝ} {k i : ℕ} (hi : i < 32) (hz : 0 ≤ z)
    (hp : p = 2 ^ k * ((32 + (i : ℝ)) / 32) * (1 + z)) :
    (k * ((gridTicks 32).1 / (scale : ℝ)) + (gridTicks i).1 / scale + z * (2 - z) / 2 ≤
        Real.log p) ∧
      (Real.log p ≤ k * ((gridTicks 32).2 / (scale : ℝ)) + (gridTicks i).2 / scale + z) := by
  have hg := gridTicks_sound (Nat.lt_trans hi (by decide : 32 < 33))
  have ht := gridTicks_sound (by decide : 32 < 33)
  have htwo : ((32 + ((32 : ℕ) : ℝ)) / 32) = 2 := by norm_num only [Nat.cast_ofNat]
  have hbase : 0 < (32 + (i : ℝ)) / 32 :=
    div_pos (add_pos_of_pos_of_nonneg (by norm_num only) (Nat.cast_nonneg i)) (by norm_num only)
  have hone : 0 < 1 + z := by linarith only [hz]
  rw [hp, Real.log_mul (mul_pos (pow_pos (by norm_num only : (0 : ℝ) < 2) k) hbase).ne' hone.ne',
    Real.log_mul (pow_pos (by norm_num only : (0 : ℝ) < 2) k).ne' hbase.ne', Real.log_pow]
  rw [htwo] at ht
  exact
    ⟨add_le_add (add_le_add (mul_le_mul_of_nonneg_left ht.1 (Nat.cast_nonneg k)) hg.1)
        (residual_log hz).1,
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left ht.2 (Nat.cast_nonneg k)) hg.2)
        (residual_log hz).2⟩

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint
