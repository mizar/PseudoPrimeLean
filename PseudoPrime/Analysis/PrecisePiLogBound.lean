/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # Rational lower bound 2096/1831 for log pi -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The twelve-term rational logarithm interval at 3.141592 lies above
2096/1831 and below 114473/100000. The kernel checks exact rational arithmetic;
the generic Taylor theorem supplies the analytic meaning of the interval.
This is the short numerical input to the lower bound for log pi. -/
theorem rational_log_pi_lower_interval :
    rationalLogIntervalCheck (392699 / 125000) 2 12 (2096 / 1831) (114473 / 100000) = true := by
  decide +kernel

/-- The rational number 2096/1831 is at most log pi.
Combine the certified logarithm interval at 3.141592 with mathlib's strict
lower bound for pi and monotonicity of log. No floating-point assumption
or extra axiom is used; this precision can be retained in conductor estimates. -/
theorem log_pi_ge_2096_div_1831 : (2096 / 1831 : ℝ) ≤ Real.log Real.pi := by
  have h := (rationalLogIntervalCheck_sound rational_log_pi_lower_interval).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : (392699 / 125000 : ℝ) ≤ Real.pi := by
    convert Real.pi_gt_d6.le using 1
    norm_num only
  exact h.trans (Real.log_le_log (by norm_num only) hpi)

end PseudoPrime.Analysis
