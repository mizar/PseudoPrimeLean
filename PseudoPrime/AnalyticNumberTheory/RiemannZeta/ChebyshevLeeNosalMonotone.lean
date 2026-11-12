/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.Real.Pi.Bounds

/-! # Monotonicity of the Lee–Nosal error envelope -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The function `t - log t` is nondecreasing for `t ≥ 1`. -/
private theorem sub_log_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    a - Real.log a ≤ b - Real.log b := by
  have ha0 : 0 < a := zero_lt_one.trans_le ha
  have hb0 : 0 < b := ha0.trans_le hab
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hlog
  have hprod := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hab)
  have hdiv : b / a ≤ b - a + 1 := by
    apply (div_le_iff₀ ha0).2
    nlinarith only [hprod]
  linarith only [hlog, hdiv]

/-- The Lee–Nosal error envelope is nondecreasing for arguments at least `exp 1`.
This transfers a certified endpoint lower bound to every point to its right. -/
theorem lee_nosal_envelope_mono {x y : ℝ} (hx : Real.exp 1 ≤ x) (hxy : x ≤ y) :
    Real.sqrt x * (Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi)) ≤
      Real.sqrt y * (Real.log y * (Real.log y - Real.log (Real.log y)) / (8 * Real.pi)) := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlx : 1 ≤ Real.log x := (Real.le_log_iff_exp_le hx0).2 hx
  have hlog0 : 0 ≤ Real.log x := (show (0 : ℝ) ≤ 1 by norm_num only).trans hlx
  have hlog := Real.log_le_log hx0 hxy
  have hgap := sub_log_mono hlx hlog
  have hgap0 : 0 ≤ Real.log x - Real.log (Real.log x) := by
    have h := Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hlx)
    linarith only [h]
  have hprod := mul_le_mul hlog hgap hgap0 (hlog0.trans hlog)
  have hpi : 0 ≤ 8 * Real.pi := by nlinarith only [Real.pi_pos]
  have hdiv := div_le_div_of_nonneg_right hprod hpi
  have hfactor : 0 ≤ Real.log x * (Real.log x - Real.log (Real.log x)) / (8 * Real.pi) :=
    div_nonneg (mul_nonneg hlog0 hgap0) hpi
  exact mul_le_mul (Real.sqrt_le_sqrt hxy) hdiv hfactor (Real.sqrt_nonneg y)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
