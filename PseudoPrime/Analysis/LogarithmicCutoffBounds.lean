/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RealLog
public import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Bounds for the logarithmic cutoff root L−2log(L)+5 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The real cutoff root L−2log(L)+5.
For L≥8 it is positive and its square is admissible for the weighted comparison.
It provides the refined Part 2 and Miller–Rabin search cutoff. -/
noncomputable def logarithmicCutoffRoot (L : ℝ) : ℝ :=
  L - 2 * Real.log L + 5

/-- For L≥8 the logarithmic cutoff root exceeds eight.
Use the logarithm tangent at eight and a certified bound for log(2).
This places its square within the analytic comparison range x≥64. -/
theorem eight_lt_logarithmicCutoffRoot {L : ℝ} (hL : 8 ≤ L) : 8 < logarithmicCutoffRoot L := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hL
  have ht := log_le_log_add_sub_div (a := (8 : ℝ)) (y := L) (by norm_num only) hL0
  have h8 : Real.log (8 : ℝ) ≤ (21 / 10 : ℝ) := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat] at ⊢
    linarith only [Real.log_two_lt_d9]
  unfold logarithmicCutoffRoot
  linarith only [ht, h8, hL]

/-- For L≥8 the cutoff root is at least 15L/16.
Use the logarithm tangent at 32. This controls the ratio between the level logarithm and cutoff. -/
theorem fifteen_sixteenths_mul_le_logarithmicCutoffRoot {L : ℝ} (hL : 8 ≤ L) :
    (15 / 16 : ℝ) * L ≤ logarithmicCutoffRoot L := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hL
  have ht := log_le_log_add_sub_div (a := (32 : ℝ)) (y := L) (by norm_num only) hL0
  have h32 : Real.log (32 : ℝ) ≤ (7 / 2 : ℝ) := by
    rw [show (32 : ℝ) = 2 ^ (5 : ℕ) by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat] at ⊢
    linarith only [Real.log_two_lt_d9]
  unfold logarithmicCutoffRoot
  linarith only [ht, h32]

/-- For L≥8, with t the cutoff root, L≤t+2log(t)−73/15.
Apply a logarithm tangent at t and the bound t≥15L/16.
This is the affine level bound used to prove the refined weighted comparison has a strict gap. -/
theorem le_logarithmicCutoffRoot_add_log {L : ℝ} (hL : 8 ≤ L) :
    L ≤ logarithmicCutoffRoot L + 2 * Real.log (logarithmicCutoffRoot L) - 73 / 15 := by
  have hL0 : 0 < L := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 8) hL
  have ht0 : 0 < logarithmicCutoffRoot L :=
    lt_trans (by norm_num only : (0 : ℝ) < 8) (eight_lt_logarithmicCutoffRoot hL)
  have hratio := fifteen_sixteenths_mul_le_logarithmicCutoffRoot hL
  have ht := log_le_log_add_sub_div (a := logarithmicCutoffRoot L) (y := L) ht0 hL0
  have hd : (L - logarithmicCutoffRoot L) / logarithmicCutoffRoot L ≤ (1 / 15 : ℝ) :=
    (div_le_iff₀ ht0).mpr (by linarith only [hratio])
  have hlog : Real.log L ≤ Real.log (logarithmicCutoffRoot L) + 1 / 15 := by linarith only [ht, hd]
  have he : L = logarithmicCutoffRoot L + 2 * Real.log L - 5 := by
    unfold logarithmicCutoffRoot
    ring
  linarith only [he, hlog]

end PseudoPrime.Analysis
