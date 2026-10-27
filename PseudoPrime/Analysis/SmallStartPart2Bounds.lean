/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SharperPart2CutoffBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Smaller analytic entrance for the precise Part 2 radius -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Above the rational logarithmic entrance 14803/2000, the precise
Part 2 root exceeds eight. Certify the logarithm at the entrance and use
its tangent to extend the lower bound to the whole half-line. -/
theorem eight_lt_sharperPart2Root_of_log_entrance {L : ℝ} (hL : (14803 / 2000 : ℝ) ≤ L) :
    8 < sharperPart2CutoffRoot L := by
  have hL0 : 0 < L := by linarith only [hL]
  have hc : rationalLogIntervalCheck (14803 / 2000) 3 10 2 (20017 / 10000) = true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have ht := log_le_log_add_sub_div (a := (14803 / 2000 : ℝ)) (y := L) (by norm_num only) hL0
  unfold sharperPart2CutoffRoot
  linarith only [ht, hl, hL]

/-- Every level q at least 1639 lies above the rational logarithmic
entrance. A ten-term rational Taylor certificate and logarithm monotonicity
prove this uniformly without enumerating moduli. -/
theorem log_level_ge_precisePart2_entrance {q : ℕ} (hq : 1639 ≤ q) :
    (14803 / 2000 : ℝ) ≤ Real.log q := by
  have hc : rationalLogIntervalCheck 1639 11 10 (14803 / 2000) (741 / 100) = true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  exact hl.trans (Real.log_le_log (by norm_num only) (by exact_mod_cast hq))

/-- Above the rational logarithmic entrance, the precise root satisfies
the coupled level bound. Use the generic tangent identity and the root
height theorem. This keeps the true modulus in the analytic comparison. -/
theorem sharperPart2Root_coupled_of_log_entrance {L : ℝ} (hL : (14803 / 2000 : ℝ) ≤ L) :
    let t := sharperPart2CutoffRoot L;
    (t - 2) * L ≤ (t - 2) * t + t * (2 * Real.log t - 2301 / 500) := by
  exact
    logarithmicCutoffRoot_coupled_level_bound (by linarith only [hL])
      ((by norm_num only : (0 : ℝ) < 8).trans (eight_lt_sharperPart2Root_of_log_entrance hL)) rfl

/-- At level 1638, the precise Part 2 root is strictly below eight.
Two short rational logarithm certificates bound both nested logarithms.
Thus extending this exact radius below the new entrance requires estimates
beyond the current x at least 64 comparison interface. -/
theorem sharperPart2Root_log_1638_lt_eight : sharperPart2CutoffRoot (Real.log (1638 : ℝ)) < 8 := by
  have hq : rationalLogIntervalCheck 1638 11 10 (740123 / 100000) (185031 / 25000) = true := by
    decide +kernel
  have hqlog := rationalLogIntervalCheck_sound hq
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hqlog
  have hc :
    rationalLogIntervalCheck (740123 / 100000) 3 10 (50041 / 25000) (200165 / 100000) = true := by
    decide +kernel
  have hl := (rationalLogIntervalCheck_sound hc).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl
  have hm := Real.log_le_log (by norm_num only : (0 : ℝ) < 740123 / 100000) hqlog.1
  unfold sharperPart2CutoffRoot
  linarith only [hqlog.2, hl, hm]

end PseudoPrime.Analysis
