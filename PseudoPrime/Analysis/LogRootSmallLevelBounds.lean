/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Small-level comparisons for logarithmically corrected radii -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: 0<L<=8 and c>=21/5.
Claim: the root L-2*log(L)+c is at least L, hence its square is at least L^2.
Proof: use log(L)<=log(8) and the certified logarithm of two.
Role: attach small-modulus witnesses to several improved logarithmic radii. -/
theorem logRoot_sq_ge_log_sq_of_small_level {L c : ℝ} (hL : 0 < L) (hL8 : L ≤ 8)
    (hc : (21 / 5 : ℝ) ≤ c) : L ^ 2 ≤ (L - 2 * Real.log L + c) ^ 2 := by
  have hu := Real.log_le_log hL hL8
  rw [show (8 : ℝ) = 2 ^ 3 by norm_num only, Real.log_pow] at hu
  norm_num only [Nat.cast_ofNat] at hu
  have hroot : L ≤ L - 2 * Real.log L + c := by linarith only [hu, Real.log_two_lt_d9, hc]
  exact (sq_le_sq₀ hL.le (hL.le.trans hroot)).mpr hroot

/-- Input: a positive modulus below 1120. Claim: log(q)<=8.
Proof: compare q with 2048=2^11 and use the certified logarithm of two.
Role: supply the finite-to-analytic radius comparison. -/
theorem log_level_le_eight_of_lt1120 {q : ℕ} (hq : 0 < q) (hQ : q < 1120) : Real.log q ≤ 8 := by
  have hq2 : (q : ℝ) ≤ 2048 :=
    Nat.cast_le.mpr (Nat.le_trans (Nat.le_of_lt hQ) (by norm_num only : 1120 ≤ 2048))
  have h := Real.log_le_log (Nat.cast_pos.mpr hq) hq2
  rw [show (2048 : ℝ) = 2 ^ 11 by norm_num only, Real.log_pow] at h
  norm_num only [Nat.cast_ofNat] at h
  linarith only [h, Real.log_two_lt_d9]

/-- Input: a positive logarithmic level and a nonnegative correction constant.
Claim: L-2*log(L)+c is positive.
Proof: apply the logarithm tangent at two and the certified upper bound for log(2).
Role: compare squared radii without assuming a large-modulus entrance. -/
theorem logarithmicRoot_pos {L c : ℝ} (hL : 0 < L) (hc : 0 ≤ c) : 0 < L - 2 * Real.log L + c := by
  have h := Real.log_le_sub_one_of_pos (div_pos hL (by norm_num only : (0 : ℝ) < 2))
  rw [Real.log_div hL.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at h
  linarith only [h, Real.log_two_lt_d9, hc]

/-- Input: a positive level and correction constants 0<=c<d.
Claim: the squared logarithmic radius is strictly smaller with c.
Proof: both roots are positive and their difference is d-c.
Role: express constant improvements uniformly over the whole positive level range. -/
theorem logarithmicRoot_sq_strictMono_constant {L c d : ℝ} (hL : 0 < L) (hc : 0 ≤ c) (hcd : c < d) :
    (L - 2 * Real.log L + c) ^ 2 < (L - 2 * Real.log L + d) ^ 2 := by
  have hp := logarithmicRoot_pos hL hc
  exact (sq_lt_sq₀ hp.le (by linarith only [hp, hcd])).mpr (by linarith only [hcd])

end PseudoPrime.Analysis
