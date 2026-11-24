/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SincMomentDerivatives
public import PseudoPrime.Analysis.SimpsonQuadrature
import all PseudoPrime.Analysis.SincMomentDerivatives
import all PseudoPrime.Analysis.SineMajorant
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-! # Uniform Simpson error for the two fixed kernel moments -/

public section

namespace PseudoPrime.Analysis

/-- Uniform majorant for the nth derivative of the weight, given a lower endpoint
a and a bound J on the absolute logarithm. -/
def momentWeightBound (n : ℕ) (s t a J : ℚ) : ℚ :=
  (n + 1).factorial * (|s| * J + |t| + |s| * |momentLogShift n|) / a ^ (n + 2)

/-- Rational fourth derivative budget on one cell. -/
def momentCellBound (s t a J : ℚ) : ℚ :=
  ∑ i ∈ Finset.range 5,
    (Nat.choose 4 i : ℚ) * sincMomentAmplitude i * momentWeightBound (4 - i) s t a J

private theorem weight_le (n : ℕ) (s t a J : ℚ) {x : ℝ} (ha : 0 < (a : ℝ)) (hx : (a : ℝ) ≤ x)
    (hJ : |Real.log x| ≤ (J : ℝ)) :
    |momentWeightTerm n s t x| ≤ (momentWeightBound n s t a J : ℝ) := by
  have h1 := abs_sub ((s : ℝ) * Real.log x + t) ((s : ℝ) * (momentLogShift n : ℝ))
  have h2 := abs_add_le ((s : ℝ) * Real.log x) (t : ℝ)
  rw [abs_mul] at h1 h2
  have h3 := mul_le_mul_of_nonneg_left hJ (abs_nonneg (s : ℝ))
  have h4 :=
    mul_le_mul_of_nonneg_left
      (by linarith only [h1, h2, h3] :
        |(s : ℝ) * Real.log x + t - s * (momentLogShift n : ℝ)| ≤
          |(s : ℝ)| * J + |(t : ℝ)| + |(s : ℝ)| * |(momentLogShift n : ℝ)|)
      (Nat.cast_nonneg (α := ℝ) (n + 1).factorial)
  simp only [momentWeightTerm, momentWeightBound, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
    one_pow, one_mul, abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (n + 1).factorial),
    abs_of_pos (ha.trans_le hx), Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_abs,
    Rat.cast_pow, Rat.cast_natCast]
  exact
    div_le_div₀ ((mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _)).trans h4) h4 (pow_pos ha _)
      (pow_le_pow_left₀ ha.le hx _)

/-- The computed rational budget bounds the fourth derivative at every point above
the left endpoint where the given logarithm enclosure holds. -/
theorem sincMoment_cell_fourth_le (s t a J : ℚ) {x : ℝ} (ha : 0 < (a : ℝ)) (hx : (a : ℝ) ≤ x)
    (hJ : |Real.log x| ≤ (J : ℝ)) :
    |iteratedDeriv 4 (sincMomentNumerator * momentWeightTerm 0 s t) x| ≤
      (momentCellBound s t a J : ℝ) := by
  apply (sincMoment_fourth_le _ _ (ha.trans_le hx)).trans
  simp only [momentCellBound, Rat.cast_sum, Rat.cast_mul, Rat.cast_natCast]
  apply Finset.sum_le_sum
  intro i _
  have hA : 0 ≤ (sincMomentAmplitude i : ℝ) :=
    (abs_nonneg _).trans (abs_iteratedDeriv_sincNumerator i x)
  exact mul_le_mul_of_nonneg_left (weight_le _ s t a J ha hx hJ) (mul_nonneg (Nat.cast_nonneg _) hA)

/-- For either moment the integral over a positive cell is bounded by three sampled
values and the rational fourth derivative budget. Monotonicity of log reduces its
absolute bound to the two endpoint comparisons. -/
theorem sincMoment_simpson_cell (s t a b J : ℚ) (ha : 0 < (a : ℝ)) (hab : (a : ℝ) < b)
    (hl : -(J : ℝ) ≤ Real.log (a : ℝ)) (hr : Real.log (b : ℝ) ≤ (J : ℝ)) :
    let f := sincMomentNumerator * momentWeightTerm 0 (s : ℝ) (t : ℝ)
    (∫ x in (a : ℝ)..(b : ℝ), f x) ≤
      ((b : ℝ) - a) / 6 * (f a + 4 * f (((a : ℝ) + b) / 2) + f b) +
        ((b : ℝ) - a) ^ 5 * (momentCellBound s t a J : ℝ) / 2880 := by
  let f := sincMomentNumerator * momentWeightTerm 0 (s : ℝ) (t : ℝ)
  have hpos {x : ℝ} (hx : x ∈ Set.Icc (a : ℝ) b) := ha.trans_le hx.1
  have han (n : ℕ) {x : ℝ} (hx : 0 < x) : AnalyticAt ℝ (iteratedDeriv n f) x := by
    induction n with
    | zero =>
      rw [iteratedDeriv_zero]
      unfold f sincMomentNumerator sineMajorant momentWeightTerm
      have hlog := analyticAt_log hx
      fun_prop (disch :=
        first
        | exact hx.ne'
        | exact pow_ne_zero _ hx.ne')
    | succ n ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv
  have hd (n : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (a : ℝ) b) :
    HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f x) x := by
    rw [iteratedDeriv_succ]
    exact (han n (hpos hx)).differentiableAt.hasDerivAt
  apply
    integral_le_simpson hab (fun x hx ↦ by simpa only [iteratedDeriv_zero] using hd 0 x hx) (hd 1)
      (hd 2) (hd 3)
  intro x hx
  have hlog :=
    abs_le.mpr ⟨hl.trans (Real.log_le_log ha hx.1), (Real.log_le_log (hpos hx) hx.2).trans hr⟩
  exact (abs_le.mp (sincMoment_cell_fourth_le s t a J ha hx.1 hlog)).1

end PseudoPrime.Analysis
