/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.Analysis.RealLog

/-! # Part 2 cutoff from the precise reciprocal loss -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The root L-2 log L+2279/500 for reciprocal loss 789/500.
Its square is the new prime cutoff. The definition shares the analytic
radius between character and primality-test consumers. -/
noncomputable def reciprocalPart2CutoffRoot (L : ℝ) : ℝ :=
  L - 2 * Real.log L + 2279 / 500

/-- Every level at least 1120 lies above logarithmic entrance 175527/25000.
Certify the endpoint by a short rational Taylor interval and use monotonicity.
This supplies an analytic half-line without enumerating moduli. -/
theorem log_level_ge_reciprocalPart2_entrance {q : ℕ} (hq : 1120 ≤ q) :
    (175527 / 25000 : ℝ) ≤ Real.log q := by
  have hc : rationalLogIntervalCheck 1120 10 10 (175527 / 25000) (703 / 100) = true := by
    decide +kernel
  have h := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h.trans (Real.log_le_log (by norm_num only) (by exact_mod_cast hq))

/-- Above the rational logarithmic entrance, the reciprocal-cost root
exceeds 15/2 and its square is at least 59. Retain a logarithm tangent at
the endpoint and certify its logarithm. These are the two cutoff conditions
needed by the parameterized character comparison. -/
theorem reciprocalPart2Root_height_and_cutoff {L : ℝ} (hL : (175527 / 25000 : ℝ) ≤ L) :
    (15 / 2 : ℝ) < reciprocalPart2CutoffRoot L ∧ 59 ≤ (reciprocalPart2CutoffRoot L) ^ 2 := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc :
    rationalLogIntervalCheck (175527 / 25000) 3 12 (194 / 100) (974459 / 500000) = true := by
    decide +kernel
  have h := (rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have ht := log_le_log_add_sub_div (a := (175527 / 25000 : ℝ)) (y := L) (by norm_num only) hL0
  have hb : (19203 / 2500 : ℝ) ≤ reciprocalPart2CutoffRoot L := by
    unfold reciprocalPart2CutoffRoot
    linarith only [ht, h, hL]
  constructor
  · linarith only [hb]
  · nlinarith only [hb]

/-- At every level at least 18000, the new radius squared is strictly
less than the squared logarithm. Two short log certificates place log log q
above 57/25, while the radius stays positive by its entrance bound.
This proves the strict comparison on the entire half-line. -/
theorem reciprocalPart2Root_sq_lt_log_sq_of_18000_le {q : ℕ} (hq : 18000 ≤ q) :
    (reciprocalPart2CutoffRoot (Real.log q)) ^ 2 < (Real.log q) ^ 2 := by
  have hc : rationalLogIntervalCheck 18000 14 10 (979 / 100) (98 / 10) = true := by decide +kernel
  have hL := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hL
  have hLq : (979 / 100 : ℝ) ≤ Real.log q :=
    hL.trans (Real.log_le_log (by norm_num only) (by exact_mod_cast hq))
  have hd : rationalLogIntervalCheck (979 / 100) 3 12 (57 / 25) (229 / 100) = true := by
    decide +kernel
  have hlog := (rationalLogIntervalCheck_sound hd).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hlogq := hlog.trans (Real.log_le_log (by norm_num only) hLq)
  have hlow : (175527 / 25000 : ℝ) ≤ Real.log q := by linarith only [hLq]
  have ht := (reciprocalPart2Root_height_and_cutoff hlow).1
  unfold reciprocalPart2CutoffRoot at *
  nlinarith only [ht, hlogq]

end PseudoPrime.Analysis
