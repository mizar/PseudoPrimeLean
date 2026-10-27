/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRefinedTailGeometry
public import PseudoPrime.Analysis.GammaFinitePrefixCutoff

/-! # Geometry of logarithmic profiles on the full certified input range -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- For L at least 100 log ten and c at least ten, the variable-shift
profile scale dominates the fixed shift-ten scale. Compare the positive
shifted roots before squaring. This is valid throughout the compact range. -/
theorem gamma_profile_scale_ge_refined {L c : ℝ} (hL : 100 * Real.log 10 ≤ L) (hc : 10 ≤ c) :
    gammaRefinedScale L ≤ gammaTailProfileScale L c := by
  have ht : 0 ≤ L + 2 * Real.log L + 10 := by
    linarith only [gamma_refined_log_lower hL, gamma_refined_log_log_lower hL]
  have htc : L + 2 * Real.log L + 10 ≤ L + 2 * Real.log L + c := by linarith only [hc]
  have hs := (sq_le_sq₀ ht (ht.trans htc)).mpr htc
  exact mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 32 / 99)

/-- Every variable-shift profile with c at least ten has scale at least
20000 on the certified logarithmic range. Transfer the fixed-scale lower
bound by profile monotonicity to discharge the local analytic assumptions. -/
theorem gamma_profile_scale_ge_twenty_thousand {L c : ℝ} (hL : 100 * Real.log 10 ≤ L)
    (hc : 10 ≤ c) : (20000 : ℝ) ≤ gammaTailProfileScale L c := by
  exact (gamma_refined_scale_ge_twenty_thousand hL).trans (gamma_profile_scale_ge_refined hL hc)

/-- The exact profile cutoff is four fifths of the shifted logarithm
squared. Rational algebra identifies the cutoff for an independent shift. -/
theorem gamma_profile_scale_cutoff (L c : ℝ) :
    (99 / 40 : ℝ) * gammaTailProfileScale L c = (4 / 5 : ℝ) * (L + 2 * Real.log L + c) ^ 2 := by
  dsimp only [gammaTailProfileScale]
  ring

/-- Every shift at least ten covers prefix 50000 on the certified
logarithmic range. Use the fixed prefix coverage and scale monotonicity.
This keeps the numerical prefix independent of the chosen profile. -/
theorem gamma_profile_cutoff_ge_fifty_thousand {L c : ℝ} (hL : 100 * Real.log 10 ≤ L)
    (hc : 10 ≤ c) : (50000 : ℝ) ≤ (99 / 40 : ℝ) * gammaTailProfileScale L c := by
  exact
    (gamma_refined_cutoff_ge_fifty_thousand hL).trans
      (mul_le_mul_of_nonneg_left (gamma_profile_scale_ge_refined hL hc)
        (by norm_num only : (0 : ℝ) ≤ 99 / 40))

end PseudoPrime.Analysis
