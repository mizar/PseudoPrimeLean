/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogHalfExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogOriginValues
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFunctionalEquation

/-! # Explicit remainder and actual zero-phase witness criterion -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under primitive GRH, compute the real origin-residue difference for an
even character at positive x. The derivative constant cancels between scales. -/
theorem log_origin_half_even_re_eq {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (he : χ.Even) {x : ℝ} (hx : 0 < x) :
    (dirichletLogResidueAt hne x 0 - dirichletLogResidueAt hne (x / 2) 0).re =
      (|primitiveBRe χ| + Real.log N / 2 - (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 -
            Real.log x) *
          Real.log 2 +
        (Real.log 2) ^ 2 / 2 := by
  rw [log_residue_zero_even_eq hp hne he hx,
    log_residue_zero_even_eq hp hne he (div_pos hx (by norm_num only : (0 : ℝ) < 2)),
    Real.log_div hx.ne' (by norm_num only : (2 : ℝ) ≠ 0)]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log hN hGRH hp hne hinv]
  ring

/-- Under primitive GRH, compute the real origin-residue difference for an
odd character at positive x. The result is independent of x. -/
theorem log_origin_half_odd_re_eq {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    (ho : χ.Odd) {x : ℝ} (hx : 0 < x) :
    (dirichletLogResidueAt hne x 0 - dirichletLogResidueAt hne (x / 2) 0).re =
      (|primitiveBRe χ| + Real.log N / 2 -
          (Real.log Real.pi / 2 + Real.log 2 + Real.eulerMascheroniConstant / 2)) *
        Real.log 2 := by
  rw [log_residue_zero_odd_eq hp hne ho hx,
    log_residue_zero_odd_eq hp hne ho (div_pos hx (by norm_num only : (0 : ℝ) < 2)),
    Real.log_div hx.ne' (by norm_num only : (2 : ℝ) ≠ 0)]
  simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero]
  rw [completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log hN hGRH hp hne hinv]
  ring

/-- Under primitive GRH and x≥1, bound the real origin difference in terms
of the completed zero mass and log(N). Discard only nonpositive parity corrections. -/
theorem log_origin_half_re_le {N : ℕ} [NeZero N] (hN : 2 ≤ N) {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1)
    {x : ℝ} (hx : 1 ≤ x) :
    (dirichletLogResidueAt hne x 0 - dirichletLogResidueAt hne (x / 2) 0).re ≤
      (|primitiveBRe χ| + Real.log N / 2) * Real.log 2 + (Real.log 2) ^ 2 / 2 := by
  have hx0 := zero_lt_one.trans_le hx
  have hl0 := Real.log_nonneg hx
  have h20 := Real.log_nonneg (by norm_num only : (1 : ℝ) ≤ 2)
  have hp0 : 0 ≤ Real.log Real.pi :=
    Real.log_nonneg (by linarith only [Real.pi_gt_three] : 1 ≤ Real.pi)
  have hg0 := Real.one_half_lt_eulerMascheroniConstant
  rcases χ.even_or_odd with he | ho
  · rw [log_origin_half_even_re_eq hN hGRH hp hne hinv he hx0]
    have hm :=
      mul_nonneg
        (show 0 ≤ (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 + Real.log x by
          linarith only [hp0, hg0, hl0])
        h20
    nlinarith only [hm]
  · rw [log_origin_half_odd_re_eq hN hGRH hp hne hinv ho hx0]
    have hm :=
      mul_nonneg
        (show 0 ≤ Real.log Real.pi / 2 + Real.log 2 + Real.eulerMascheroniConstant / 2 by
          linarith only [hp0, hg0, h20])
        h20
    nlinarith only [hm, sq_nonneg (Real.log 2)]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
