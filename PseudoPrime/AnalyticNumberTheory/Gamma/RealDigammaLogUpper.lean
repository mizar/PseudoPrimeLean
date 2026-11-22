/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.Gamma.UniformDigamma
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! # A signed real digamma bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- For positive `a`, the logarithmic increment from `a` to `a + 1` is at most `1 / a`.
Apply the tangent-line bound for the logarithm to `(a + 1) / a`.
This supplies the sign of each term in the real digamma error series. -/
theorem log_succ_sub_log_le {a : ℝ} (ha : 0 < a) : Real.log (a + 1) - Real.log a ≤ 1 / a := by
  have h := Real.log_le_sub_one_of_pos (div_pos (add_pos ha zero_lt_one) ha)
  rw [Real.log_div (ne_of_gt (add_pos ha zero_lt_one)) (ne_of_gt ha)] at h
  have he : (a + 1) / a - 1 = 1 / a := by
    rw [add_div, div_self (ne_of_gt ha)]
    ring
  linarith only [h, he]

/-- At a real point `x ≥ 1/2`, every term of the digamma logarithm error series
has nonpositive real part. The logarithmic tangent bound controls its increment.
This sign is used to bound the completed Dirichlet gamma factor. -/
private theorem digammaLogError_re_nonpos {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (digammaLogError (x : ℂ) n).re ≤ 0 := by
  have ha : 0 < x + n := add_pos_of_pos_of_nonneg hx (Nat.cast_nonneg n)
  have hlog := log_succ_sub_log_le ha
  dsimp only [digammaLogError]
  simp only [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add,
    ← Complex.ofReal_div, ← Complex.ofReal_sub, ← Complex.ofReal_log (le_of_lt ha),
    ← Complex.ofReal_log (le_of_lt (add_pos ha zero_lt_one)), Complex.ofReal_re]
  linarith only [hlog]

/-- For every real `x ≥ 1/2`, the real digamma value is at most `log x`.
The summable increment series for digamma minus log has nonpositive terms.
This signed inequality controls the gamma factor in Dirichlet zero-tail bounds. -/
theorem real_digamma_le_log {x : ℝ} (hx : 1 / 2 ≤ x) :
    (Complex.digamma (x : ℂ)).re ≤ Real.log x := by
  have hx0 : 0 < x := lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 1 / 2) hx
  have hs : (1 / 2 : ℝ) ≤ (x : ℂ).re := by simpa only [Complex.ofReal_re] using hx
  have h := digamma_sub_log_eq_tsum_digammaLogError hs
  have hsum := congrArg Complex.reCLM h
  rw [Complex.reCLM.map_tsum (summable_digammaLogError hs)] at hsum
  have ht : (∑' n : ℕ, (digammaLogError (x : ℂ) n).re) ≤ 0 :=
    tsum_nonpos (digammaLogError_re_nonpos hx0)
  simp only [Complex.reCLM_apply, Complex.sub_re, ← Complex.ofReal_log hx0.le,
    Complex.ofReal_re] at hsum
  linarith only [hsum, ht]

end PseudoPrime.AnalyticNumberTheory.Gamma
