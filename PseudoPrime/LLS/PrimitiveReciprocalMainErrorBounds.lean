/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.Analysis.ElementaryBounds
import PseudoPrime.Analysis.LogarithmicRatios
import PseudoPrime.Analysis.LogarithmicMainTerms
import PseudoPrime.Analysis.RealLog
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-!
# Odd/even parity main-error numerical bounds

Pure numerical (character-free) content: the two "main error" functions appearing in the odd/even
`r₀ + r₁` closed forms (`PrimitiveResidueClosedForms.lean` (O),
`PrimitiveEvenResidueClosedForm.lean` (E)) are `≤ -1/4` once `x ≥ 64`. This isolates the
elementary real-analysis content (an explicit Euler–Mascheroni-constant lower bound, and
monotonicity of `(log x + 1)/x`) away from the contour machinery.
-/

namespace PseudoPrime.LLS

/--
Input/assumptions: `x ≥ 64`.
Conclusion: `PseudoPrime.Analysis.primitiveReciprocalOddMainError x ≤ -1/4`.
Content: `1/x ≤ 1/64` and `1 - 1/x ≥ 63/64`; combined with `γ > 27/50`
(`Analysis.twenty_seven_fiftieths_lt_eulerMascheroniConstant`) and `log 2 < 7/10`
(`Real.log_two_lt_d9`),
`-(γ/2)(1-1/x) + log2/x ≤ -(1/2)(27/50)(63/64) + (7/10)(1/64) = -1631/6400 < -1/4`.
Role: the odd half of the reciprocal main-error estimate.
-/
theorem llsPrimitiveReciprocalOddMainError_le_neg_quarter {x : ℝ} (hx : 64 ≤ x) :
    Analysis.primitiveReciprocalOddMainError x ≤ -(1 / 4 : ℝ) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hinv_le : 1 / x ≤ 1 / 64 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hx
  have hinv_nn : (0 : ℝ) ≤ 1 / x := by positivity
  have h1mx_ge : (63 / 64 : ℝ) ≤ 1 - 1 / x := by linarith
  have h1mx_nn : (0 : ℝ) ≤ 1 - 1 / x := by linarith
  have hγ := Analysis.twenty_seven_fiftieths_lt_eulerMascheroniConstant
  have hlog2 := Real.log_two_lt_d9
  have hterm1 : (27 / 50 : ℝ) * (1 - 1 / x) ≤ Real.eulerMascheroniConstant * (1 - 1 / x) :=
    mul_le_mul_of_nonneg_right hγ.le h1mx_nn
  have hterm2 : (27 / 100 : ℝ) * (63 / 64) ≤ (27 / 100 : ℝ) * (1 - 1 / x) :=
    mul_le_mul_of_nonneg_left h1mx_ge (by norm_num only)
  have hterm3 : Real.log 2 / x ≤ (0.6931471808 : ℝ) * (1 / 64) := by
    rw [div_eq_mul_inv, ← one_div]
    exact mul_le_mul hlog2.le hinv_le (by positivity) (by norm_num only)
  unfold Analysis.primitiveReciprocalOddMainError
  nlinarith [hterm1, hterm2, hterm3]

/--
Input/assumptions: `x ≥ 64`.
Conclusion: `PseudoPrime.Analysis.primitiveReciprocalEvenMainError x ≤ -1/4`.
Content: `(log x + 1)/x ≤ (2 log x + 1)/x = Analysis.logLinearRatio x ≤ Analysis.logLinearRatio 64`
(`Analysis.strictAntiOn_logLinearRatio`, using `log x ≥ 0`); `Analysis.logLinearRatio 64 = (12 log
2 + 1)/64`;
combined with `γ > 1/2` (`Real.one_half_lt_eulerMascheroniConstant`) and `log 2 > 1/2`
(`Real.log_two_gt_d9`), the sum is `≤ -log2 - (1/4)(63/64) + (12 log2+1)/64 < -1/4` (ample margin,
no sharp numerics needed).
Role: the even half of the reciprocal main-error estimate.
-/
theorem llsPrimitiveReciprocalEvenMainError_le_neg_quarter {x : ℝ} (hx : 64 ≤ x) :
    Analysis.primitiveReciprocalEvenMainError x ≤ -(1 / 4 : ℝ) := by
  have hxpos : (0 : ℝ) < x := by linarith
  have hlogx_nn : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hratio_le : (Real.log x + 1) / x ≤ Analysis.logLinearRatio x := by
    unfold Analysis.logLinearRatio
    apply div_le_div_of_nonneg_right _ hxpos.le
    linarith
  have hratio_anti :
    Analysis.logLinearRatio x ≤ Analysis.logLinearRatio 64 :=
    Analysis.strictAntiOn_logLinearRatio.antitoneOn
      (by
        simp only [Set.mem_Ici]; norm_num only)
      (by
        simp only [Set.mem_Ici]; linarith)
      hx
  have hratio64 : Analysis.logLinearRatio 64 = (12 * Real.log 2 + 1) / 64 := by
    unfold Analysis.logLinearRatio
    rw [show (64 : ℝ) = 2 ^ 6 from by norm_num only, Real.log_pow]
    norm_num only
    ring
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hlog2 := Real.log_two_gt_d9
  have hinv_le : 1 / x ≤ 1 / 64 := by
    apply div_le_div_of_nonneg_left (by norm_num only) (by norm_num only) hx
  have h1mx_ge : (63 / 64 : ℝ) ≤ 1 - 1 / x := by linarith
  have h1mx_nn : (0 : ℝ) ≤ 1 - 1 / x := by linarith
  have hterm1 : (1 / 4 : ℝ) * (63 / 64) ≤ (Real.eulerMascheroniConstant / 2) * (1 - 1 / x) := by
    have hstep1 : (1 / 2 : ℝ) * (1 - 1 / x) ≤ Real.eulerMascheroniConstant * (1 - 1 / x) :=
      mul_le_mul_of_nonneg_right hγ.le h1mx_nn
    have hstep2 : (1 / 4 : ℝ) * (63 / 64) ≤ (1 / 4 : ℝ) * (1 - 1 / x) :=
      mul_le_mul_of_nonneg_left h1mx_ge (by norm_num only)
    linarith
  have hratio_full : (Real.log x + 1) / x ≤ (12 * Real.log 2 + 1) / 64 := by
    rw [← hratio64]; exact hratio_le.trans hratio_anti
  unfold Analysis.primitiveReciprocalEvenMainError
  nlinarith [hterm1, hratio_full, hlog2]

end PseudoPrime.LLS
