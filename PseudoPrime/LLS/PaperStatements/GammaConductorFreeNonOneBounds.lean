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
public import PseudoPrime.Analysis.GammaConductorFreeNonOneBounds

/-! # Non-one quadratic Gamma witnesses from logarithmic scale 30000 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- If L ≥ 30000, x ≥ 1, sqrt x ≥ 9L/16 and log(99x/40) ≤ L/1400,
then the conductor-free left, principal, ramp and dyadic allowances are at most
1/100, 3/20, 7 and 1/100 respectively. Clear positive denominators and use
the existing power-decay comparison. The scale is otherwise arbitrary. -/
theorem conductor_free_nonOne_error_budgets {L x : ℝ} (hL : 30000 ≤ L) (hx : 1 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hlog : Real.log (x * (99 / 40 : ℝ)) ≤ L / 1400) :
    43 * x ^ (-9 / 16 : ℝ) ≤ 1 / 100 ∧
      (Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) / Real.sqrt x ≤
        3 / 20 ∧
      ((135 / 20 : ℝ) * Real.sqrt x +
            86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20)) /
          Real.sqrt x ≤
        7 ∧
      (Real.log ((99 / 40 : ℝ) * x) + Real.log 2) / Real.sqrt x ≤ 1 / 100 := by
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hlx : Real.log x ≤ Real.log (x * (99 / 40 : ℝ)) :=
    Real.log_le_log hx0 (by nlinarith only [hx])
  have hdecay :=
    rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 1) (by norm_num only)
      (by
        norm_num only; exact hx)
  simp only [one_mul] at hdecay
  have hleft := mul_le_mul_of_nonneg_left hdecay (by norm_num only : (0 : ℝ) ≤ 43)
  have hleft' : 43 * (1 / Real.sqrt x) ≤ (1 / 100 : ℝ) := by
    rw [mul_one_div, div_le_iff₀ hs]
    linarith only [hroot, hL]
  refine ⟨hleft.trans hleft', ?_, ?_, ?_⟩
  · rw [div_le_iff₀ hs]
    linarith only [hlx, hlog, hroot, hL]
  · rw [div_le_iff₀ hs]
    linarith only [hlog, hroot, hL]
  · rw [mul_comm (99 / 40 : ℝ), div_le_iff₀ hs]
    linarith only [hlog, hroot, hL, Real.log_two_lt_d9]

end PseudoPrime.LLS.PaperStatements
