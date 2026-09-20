import PseudoPrime.Analysis.RealLog
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-! # General analytic bounds and auxiliary constructions -/

namespace PseudoPrime.Analysis

/--
Input/assumptions: none.
Conclusion: `27 / 50 < γ` (the Euler–Mascheroni constant).
Content: `Real.eulerMascheroniSeq 16 < γ` (mathlib); `eulerMascheroniSeq 16 = harmonic 16 -
log 17`, `harmonic 16 = 2436559/720720` (rational arithmetic); `log 17 ≤ log 16 + 1/16 = 4 log 2 +
1/16` (`log_le_log_add_sub_div` at `a := 16`, `Real.log_pow`); combined with `Real.log_two_lt_d9`.
Role: the sharper Euler–Mascheroni lower bound needed for the odd main-error bound (`γ > 1/2`
alone is too weak).
-/
theorem twenty_seven_fiftieths_lt_eulerMascheroniConstant :
    (27 / 50 : ℝ) < Real.eulerMascheroniConstant := by
  have hseq := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant 16
  have hlog17 :=
    log_le_log_add_sub_div (a := (16 : ℝ)) (y := 17) (by norm_num only) (by norm_num only)
  have hlog16eq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 from by norm_num only, Real.log_pow]
    norm_num only
  rw [hlog16eq] at hlog17
  have hseq16 : Real.eulerMascheroniSeq 16 = (harmonic 16 : ℝ) - Real.log 17 := by
    rw [Real.eulerMascheroniSeq]
    norm_num only
  have hH16 : (harmonic 16 : ℝ) = 2436559 / 720720 := by
    norm_num only [harmonic, Finset.sum_range_succ]
  rw [hseq16, hH16] at hseq
  nlinarith [hseq, hlog17, Real.log_two_lt_d9]

/--
Input/assumptions: `x ≥ 64`.
Conclusion: `6 * log 2 ≤ log x`.
Content: `64 = 2 ^ 6` (`Real.log_pow`) and `Real.log` monotone.
Role: the common `log x` lower bound feeding both parity's log-kernel main-error bounds.
-/
theorem six_mul_log_two_le_log_of_sixty_four_le {x : ℝ} (hx : 64 ≤ x) :
    6 * Real.log 2 ≤ Real.log x := by
  have h64 : Real.log (64 : ℝ) = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 from by norm_num only, Real.log_pow]
    norm_num only
  rw [← h64]
  exact Real.log_le_log (by norm_num only) hx

/-- A radius at least `8` has square at least `64`; this avoids repeated nonlinear arithmetic. -/
lemma sq_ge_64_of_ge_8 {y : ℝ} (hy : 8 ≤ y) : (64 : ℝ) ≤ y ^ 2 := by
  have hsq := mul_self_le_mul_self (show (0 : ℝ) ≤ 8 by norm_num only) hy
  calc
    (64 : ℝ) = 8 * 8 := by norm_num only
    _ ≤ y * y := hsq
    _ = y ^ 2 := by ring

end PseudoPrime.Analysis
