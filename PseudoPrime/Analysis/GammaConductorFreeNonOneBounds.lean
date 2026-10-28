/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeAdaptiveBounds
public import PseudoPrime.LLS.GammaNonOneAdaptiveWitnessBounds
public import PseudoPrime.LLS.GammaNonOneProfileWitnessBounds
public import PseudoPrime.LLS.GammaRefinedTailErrorBounds

/-! # Non-one quadratic Gamma witnesses from logarithmic scale 30000 -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For a positive anchor a, suppose log a ≤ b a and 1 ≤ b a.
Then log L ≤ b L for all L ≥ a. Apply the logarithm tangent at L/a,
and use the slope condition beyond the anchor. The real parameters
allow the same lemma to verify logarithmic error budgets at other scales. -/
theorem log_le_mul_of_anchor {a b L : ℝ} (ha : 0 < a) (hL : a ≤ L) (hlog : Real.log a ≤ b * a)
    (hslope : 1 ≤ b * a) : Real.log L ≤ b * L := by
  have hL0 := ha.trans_le hL
  have ht := Real.log_le_sub_one_of_pos (div_pos hL0 ha)
  rw [Real.log_div hL0.ne' ha.ne'] at ht
  have hcancel : a * (L / a) = L := mul_div_cancel₀ _ ha.ne'
  have hprod := mul_nonneg (sub_nonneg.mpr hslope) (sub_nonneg.mpr hL)
  nlinarith only [ht, hcancel, hlog, hprod, ha]

/-- For every L ≥ 30000, log L ≤ L/2800. Compare the anchor with 2^15,
use the certified log two upper bound, then apply the real-anchor tangent lemma.
This controls the non-one cutoff logarithm on a full half-line. -/
theorem conductor_free_nonOne_log_bound {L : ℝ} (hL : 30000 ≤ L) : Real.log L ≤ L / 2800 := by
  have hanchor :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 30000) (by norm_num only : (30000 : ℝ) ≤ 2 ^ 15)
  rw [Real.log_pow] at hanchor
  norm_num only [Nat.cast_ofNat] at hanchor
  have h :=
    log_le_mul_of_anchor (a := 30000) (b := 1 / 2800) (by norm_num only) hL
      (by linarith only [hanchor, Real.log_two_lt_d9]) (by norm_num only)
  simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using h

/-- At scale x=(32/99)L² with L ≥ 30000, the cutoff logarithm is at most L/1400.
Compare the coefficient-four-fifths cutoff with L² and apply the log anchor.
This supplies common bounds for the principal, ramp and prime-two errors. -/
theorem conductor_free_nonOne_cutoff_log {L : ℝ} (hL : 30000 ≤ L) :
    Real.log (((32 / 99 : ℝ) * L ^ 2) * (99 / 40)) ≤ L / 1400 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :=
    Real.log_le_log
      (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 32 / 99) (sq_pos_of_pos hL0))
        (by norm_num only : (0 : ℝ) < 99 / 40))
      (show ((32 / 99 : ℝ) * L ^ 2) * (99 / 40) ≤ L ^ 2 by nlinarith only [sq_nonneg L])
  rw [Real.log_pow] at hc
  norm_num only [Nat.cast_ofNat] at hc
  linarith only [hc, conductor_free_nonOne_log_bound hL]

end PseudoPrime.Analysis
