/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.Analysis.ElementaryBounds
import PseudoPrime.Analysis.LogarithmicMainTerms
import PseudoPrime.LLS.PrimitiveReciprocalMainErrorBounds

/-!
# Odd/even parity main-error numerical bounds for the log kernel

Pure numerical (character-free) content: the two "main error" functions appearing in the odd/even
`s = 0` log-kernel residue closed forms
(`PrimitiveLogResidueClosedForms.lean`,
`DirichletLFunction.re_deriv_dirichletLogMellinZeroRegularization_zero_of_odd_raw`,
`DirichletLFunction.re_iteratedDeriv_two_dirichletLogEvenZeroRegularization_zero_div_two_raw`) are
`≤ -11/4` once
`x ≥ 64`. Mirrors `PrimitiveReciprocalMainErrorBounds.lean`'s odd/even numerical bounds, but odd
and even are *not* proved by a shared argument here: odd's margin is tight (`≈ 0.02`) and needs a
sharper rational bound on `γ`, `log 2`, `π`; even's margin is ample and closes from coarse bounds.
-/

namespace PseudoPrime.LLS

/--
Input/assumptions: `x ≥ 64`.
Conclusion: `PseudoPrime.Analysis.primitiveLogOddMainError x ≤ -11/4`.
Content: `log x ≥ 6 log 2 > 4158/1000` (`Analysis.six_mul_log_two_le_log_of_sixty_four_le`,
`Real.log_two_gt_d9`); `log 2 + γ/2 > 963/1000` (`Real.log_two_gt_d9`,
`Analysis.twenty_seven_fiftieths_lt_eulerMascheroniConstant`); their product exceeds `4.004`, while
`π²/8 < 3.1416²/8 < 1.235` (`Real.pi_lt_d4`), giving `E₁⁺(x) < 1.235 - 4.004 < -11/4`.
Role: the odd half of the log-kernel main-error estimate.
-/
theorem llsPrimitiveLogOddMainError_le_neg_eleven_fourths {x : ℝ} (hx : 64 ≤ x) :
    Analysis.primitiveLogOddMainError x ≤ -(11 / 4 : ℝ) := by
  have hlogx : (6 * Real.log 2 : ℝ) ≤ Real.log x :=
    Analysis.six_mul_log_two_le_log_of_sixty_four_le hx
  have hlog2 := Real.log_two_gt_d9
  have hγ := Analysis.twenty_seven_fiftieths_lt_eulerMascheroniConstant
  have hpi := Real.pi_lt_d4
  have hpinn : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hpisq : Real.pi ^ 2 ≤ (3.1416 : ℝ) ^ 2 := by nlinarith
  have hlogx_pos : (0 : ℝ) ≤ 6 * Real.log 2 := by linarith
  have hterm1 :
    (963 / 1000 : ℝ) * (4158 / 1000) ≤
      (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x := by
    have hcoef : (963 / 1000 : ℝ) ≤ Real.log 2 + Real.eulerMascheroniConstant / 2 := by linarith
    have hxbound : (4158 / 1000 : ℝ) ≤ Real.log x := by linarith
    have hcoef_nn : (0 : ℝ) ≤ (963 / 1000 : ℝ) := by norm_num only
    calc
      (963 / 1000 : ℝ) * (4158 / 1000) ≤
          (Real.log 2 + Real.eulerMascheroniConstant / 2) * (4158 / 1000) :=
        mul_le_mul_of_nonneg_right hcoef (by norm_num only)
      _ ≤ (Real.log 2 + Real.eulerMascheroniConstant / 2) * Real.log x :=
        mul_le_mul_of_nonneg_left hxbound (by linarith)
  unfold Analysis.primitiveLogOddMainError
  nlinarith [hpisq, hterm1]

/--
Input/assumptions: `x ≥ 64`.
Conclusion: `PseudoPrime.Analysis.primitiveLogEvenMainError x ≤ -11/4`.
Content: `log x ≥ 6 log 2 > 4` (`Analysis.six_mul_log_two_le_log_of_sixty_four_le`,
`Real.log_two_gt_d9`);
`γ > 1/2` (`Real.one_half_lt_eulerMascheroniConstant`); `π < 4` (`Real.pi_lt_four`); ample margin
gives `π²/24 ≤ 2/3`, `(γ/2) log x ≥ 1`, `(1/2)(log x)² ≥ 8`, so `E₀⁺(x) ≤ 2/3 - 1 - 8 < -11/4`.
Role: the even half of the log-kernel main-error estimate.
-/
theorem llsPrimitiveLogEvenMainError_le_neg_eleven_fourths {x : ℝ} (hx : 64 ≤ x) :
    Analysis.primitiveLogEvenMainError x ≤ -(11 / 4 : ℝ) := by
  have hlogx : (6 * Real.log 2 : ℝ) ≤ Real.log x :=
    Analysis.six_mul_log_two_le_log_of_sixty_four_le hx
  have hlog2 := Real.log_two_gt_d9
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have hpi := Real.pi_lt_four
  have hpinn : (0 : ℝ) ≤ Real.pi := Real.pi_pos.le
  have hpisq : Real.pi ^ 2 ≤ (4 : ℝ) ^ 2 := by nlinarith
  have hlogx4 : (4 : ℝ) ≤ Real.log x := by linarith
  have hlogx_nn : (0 : ℝ) ≤ Real.log x := by linarith
  have hterm1 : (1 : ℝ) ≤ (Real.eulerMascheroniConstant / 2) * Real.log x := by
    have h1 : (1 / 4 : ℝ) * 4 ≤ (Real.eulerMascheroniConstant / 2) * Real.log x := by
      calc
        (1 / 4 : ℝ) * 4 ≤ (Real.eulerMascheroniConstant / 2) * 4 :=
          mul_le_mul_of_nonneg_right (by linarith) (by norm_num only)
        _ ≤ (Real.eulerMascheroniConstant / 2) * Real.log x :=
          mul_le_mul_of_nonneg_left hlogx4 (by linarith)
    linarith
  have hterm2 : (8 : ℝ) ≤ (1 / 2) * Real.log x ^ 2 := by
    have h1 : (4 : ℝ) * 4 ≤ Real.log x * Real.log x := by nlinarith
    nlinarith
  unfold Analysis.primitiveLogEvenMainError
  nlinarith [hpisq, hterm1, hterm2]

end PseudoPrime.LLS
