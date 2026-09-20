/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.Analysis.RealLog
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.Tactic

/-! # General bounds and arithmetic certificates -/

namespace PseudoPrime.Analysis

/--
Input/assumptions: a positive anchor `a`, an endpoint `b ≥ a`, and
`a ≤ y ≤ b`, together with a real lower certificate `L < log a`.
Conclusion: a chord-style lower certificate for `log y`.
Content: apply `Real.le_log_one_add_of_nonneg` to `y/a - 1`; the elementary
fraction comparison uses only the interval product `(y-a)(b-y) ≥ 0`.
Role: produces affine logarithmic lower bounds on compact positive intervals.
-/
theorem log_gt_affine_of_anchor {a b y L : ℝ} (ha : 0 < a) (hab : a ≤ b) (hay : a ≤ y) (hyb : y ≤ b)
    (hL : L < Real.log a) : L + 2 / (a + b) * (y - a) < Real.log y := by
  have hy0 : 0 < y := by linarith only [ha, hay]
  have hfactor : a * (y / a) = y := by field_simp
  rw [← hfactor]
  have hlogmul : Real.log (a * (y / a)) = Real.log a + Real.log (y / a) := by
    rw [Real.log_mul (ne_of_gt ha) (by positivity)]
  rw [hlogmul]
  have hratio : 1 ≤ y / a := (le_div_iff₀ ha).2 (by linarith only [hay])
  have hx : 0 ≤ y / a - 1 := by linarith only [hratio]
  have hla := Real.le_log_one_add_of_nonneg hx
  have hla' : 2 * (y / a - 1) / ((y / a - 1) + 2) ≤ Real.log (y / a) := by
    convert hla using 1
    all_goals ring_nf
  have hden : 0 < (y / a - 1) + 2 := by linarith only [hx]
  have hfrac : 2 / (a + b) * (y - a) ≤ 2 * (y / a - 1) / ((y / a - 1) + 2) := by
    apply (le_div_iff₀ hden).2
    have haab : 0 < a + b := by linarith
    field_simp [ne_of_gt ha, ne_of_gt haab]
    nlinarith only [mul_nonneg (by linarith : 0 ≤ y - a) (by linarith : 0 ≤ b - y)]
  rw [hfactor]
  linarith only [hL, hla', hfrac]

/-- The logarithmic saving from replacing `π` by `4` is strictly positive. -/
theorem log_four_sub_log_pi_pos : 0 < Real.log 4 - Real.log Real.pi := by
  have h := Real.strictMonoOn_log Real.pi_pos (by norm_num only [Set.mem_Ioi]) Real.pi_lt_four
  rw [Real.log_four_eq] at h ⊢
  linarith

/-- A strict lower bound `24/100 < log 4 - log π`, obtained from rational bounds for `π`
and logarithms of `2` and `3`. -/
theorem log_four_sub_log_pi_gt_twenty_four : (24 : ℝ) / 100 < Real.log 4 - Real.log Real.pi := by
  have hlog4 : (138629 : ℝ) / 100000 < Real.log 4 := by
    rw [Real.log_four_eq]
    linarith only [Real.log_two_gt_d9]
  have hpi : Real.pi < (31416 : ℝ) / 10000 := by
    have h := Real.pi_lt_d4
    norm_num only at h ⊢
    exact h
  have hxpos : 0 < Real.pi / 3 - 1 := by linarith only [Real.pi_gt_three]
  have hlogadd := Real.log_le_sub_one_of_pos (x := 1 + (Real.pi / 3 - 1)) (by linarith)
  have hlogdiv : Real.log (Real.pi / 3) = Real.log Real.pi - Real.log 3 := by
    rw [Real.log_div (by positivity) (by norm_num only)]
  have hlogone : Real.log (1 + (Real.pi / 3 - 1)) = Real.log (Real.pi / 3) := by
    congr 1
    ring
  rw [hlogone, hlogdiv] at hlogadd
  nlinarith only [hlog4, hlogadd, hpi, Real.log_three_lt_d9]

/-- At every level `q ≥ 3000`, the natural logarithm of `q` is strictly greater than `8`. -/
theorem eight_lt_log_level {q : ℕ} (hq : 3000 ≤ q) : (8 : ℝ) < Real.log q := by
  have hexp : Real.exp 8 < (3000 : ℝ) := by
    rw [show (8 : ℝ) = (8 : ℕ) * 1 by norm_num only, Real.exp_nat_mul]
    calc
      Real.exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 := by
        gcongr
        exact Real.exp_one_lt_d9
      _ < 3000 := by norm_num only
  apply (Real.lt_log_iff_exp_lt (by positivity)).mpr
  exact hexp.trans_le (by exact_mod_cast hq)

/-- On `[12, ∞)`, `log 2` is at most twice `log y`. -/
theorem log_two_le_two_mul_log {y : ℝ} (hy : 12 ≤ y) : Real.log 2 ≤ 2 * Real.log y := by
  have hlog : Real.log 2 ≤ Real.log y := by exact Real.log_le_log (by norm_num only) (by linarith)
  have hnonneg : 0 ≤ Real.log y := Real.log_nonneg (by linarith)
  linarith

/-- A rational upper certificate for `log 12`, obtained from the bounds for `log 2` and `log 3`. -/
theorem log_twelve_le : Real.log 12 ≤ (248491 : ℝ) / 100000 := by
  have hlogTwo := Real.log_two_lt_d9
  have hlogThree := Real.log_three_lt_d9
  rw [show (12 : ℝ) = 3 * 4 by norm_num only, Real.log_mul (by norm_num only) (by norm_num only),
    Real.log_four_eq]
  norm_num only at hlogTwo hlogThree ⊢
  linarith

/-- The rational lower bound `247/100 < log 12`, from `12 = 3 * 4`. -/
theorem log_twelve_gt : (247 : ℝ) / 100 < Real.log 12 := by
  rw [show (12 : ℝ) = 3 * 4 by norm_num only, Real.log_mul (by norm_num only) (by norm_num only),
    Real.log_four_eq]
  have h2 := Real.log_two_gt_d9
  have h3 := Real.log_three_gt_d9
  norm_num only at h2 h3 ⊢
  linarith

/-- The bound `247/100 < log y` for every `y ≥ 12`, by monotonicity of `log`. -/
theorem log_ge_twelve_lower {y : ℝ} (hy : 12 ≤ y) : (247 : ℝ) / 100 < Real.log y := by
  have hlog :=
    Real.strictMonoOn_log.monotoneOn (by norm_num only : (0 : ℝ) < 12) (by linarith : (0 : ℝ) < y)
      hy
  exact log_twelve_gt.trans_le hlog

/-- A rational upper certificate for `log 13`, propagated from the tangent at `12`. -/
theorem log_thirteen_le : Real.log 13 ≤ (256825 : ℝ) / 100000 := by
  have htangent :=
    log_le_log_add_sub_div (a := (12 : ℝ)) (y := 13) (by norm_num only) (by norm_num only)
  norm_num only at htangent ⊢
  linarith only [htangent, log_twelve_le]

/-- A rational upper certificate for `log 14`, propagated from the tangent at `13`. -/
theorem log_fourteen_le : Real.log 14 ≤ (264518 : ℝ) / 100000 := by
  have htangent :=
    log_le_log_add_sub_div (a := (13 : ℝ)) (y := 14) (by norm_num only) (by norm_num only)
  norm_num only at htangent ⊢
  linarith only [htangent, log_thirteen_le]

/-- A rational upper certificate for `log 15`, propagated from the tangent at `14`. -/
theorem log_fifteen_le : Real.log 15 ≤ (271661 : ℝ) / 100000 := by
  have htangent :=
    log_le_log_add_sub_div (a := (14 : ℝ)) (y := 15) (by norm_num only) (by norm_num only)
  norm_num only at htangent ⊢
  linarith only [htangent, log_fourteen_le]

/-- A rational upper certificate for the logarithm of `2π`. -/
theorem log_two_mul_pi_lt : Real.log (2 * Real.pi) < (1839 / 1000 : ℝ) := by
  have htangent :=
    log_le_log_add_sub_div (a := (3 : ℝ)) (y := Real.pi) (by norm_num only) Real.pi_pos
  have hlogTwo := Real.log_two_lt_d9
  have hlogThree := Real.log_three_lt_d9
  rw [Real.log_mul (by norm_num only) Real.pi_ne_zero]
  nlinarith only [htangent, hlogTwo, hlogThree, Real.pi_lt_d4]

end PseudoPrime.Analysis
