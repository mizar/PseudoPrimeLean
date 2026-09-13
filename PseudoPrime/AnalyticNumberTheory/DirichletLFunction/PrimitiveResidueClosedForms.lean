/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveMultiplicityBridge
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.OddZeroLogDeriv
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveFarLeftHorizontalBound

/-!
# the residue evaluation (start): closed forms for the `s = 1` and odd `s = 0` residues

The Mellin-pole regularizations collapse to plain `L'/L` values once the Mellin power factor is
evaluated: at `s = 1`, `x^{s-1} = x^0 = 1`; at `s = 0` (odd character, simple pole), `x^{s-1} =
x^{-1}`. This file records both closed forms, the first building block toward the odd `r₀ + r₁`
exact formula (the residue evaluation).
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `N ≥ 1`, `χ ≠ 1`, `x : ℝ`.
Conclusion: `DirichletLFunction.dirichletReciprocalResidueAt hne x 1 = -logDeriv (LFunction χ) 1`.
Content: unfold `DirichletLFunction.dirichletReciprocalResidueAt_one` and
`DirichletLFunction.dirichletReciprocalOneRegularization`;
the Mellin factor `x^{1-1} = x^0 = 1` and the denominator `s = 1` disappear, leaving exactly
`-logDeriv (LFunction χ) 1`.
Role: the `s = 1` half of the residue closed form, common to both parities.
-/
theorem dirichletReciprocalResidueAt_one_eq_neg_logDeriv {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (x : ℝ) :
    dirichletReciprocalResidueAt hne x 1 =
      -logDeriv (DirichletCharacter.LFunction χ) 1 := by
  rw [dirichletReciprocalResidueAt_one,
    dirichletReciprocalOneRegularization,
    logDeriv_apply]
  simp only [sub_self, Complex.cpow_zero, mul_one, div_one]

/--
Input/assumptions: `N ≥ 1`, `χ ≠ 1` odd, `x > 0`.
Conclusion: `DirichletLFunction.dirichletReciprocalResidueAt hne x 0 = (1 / x : ℂ) * logDeriv
(LFunction χ) 0`.
Content: unfold `DirichletLFunction.dirichletReciprocalResidueAt_zero_of_odd` and
`DirichletLFunction.dirichletReciprocalMellinZeroRegularization`; the Mellin factor `x^{0-1} =
x^{-1} = 1/x`
(`Complex.cpow_neg_one`, via `x ≠ 0`) and the denominator `0 - 1 = -1` combine with the leading
`-1` to leave `(1/x) · logDeriv (LFunction χ) 0`.
Role: the odd `s = 0` half of the residue closed form.
-/
theorem dirichletReciprocalResidueAt_zero_of_odd_eq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) (hodd : χ.Odd) :
    dirichletReciprocalResidueAt hne x 0 =
      (1 / x : ℂ) * logDeriv (DirichletCharacter.LFunction χ) 0 := by
  rw [dirichletReciprocalResidueAt_zero_of_odd
      hne x hodd,
    dirichletReciprocalMellinZeroRegularization,
    logDeriv_apply]
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hpow : (x : ℂ) ^ ((0 : ℂ) - 1) = (x : ℂ)⁻¹ := by rw [zero_sub, Complex.cpow_neg_one]
  rw [hpow]
  field_simp
  ring

/-! ### the residue evaluation (odd): the exact `r₀ + r₁` closed form -/

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial odd mod `N`, GRH, `χ⁻¹ ≠ 1`, `x > 0`.
Conclusion:
`Re (r₀ + r₁) = (1/2)(1 - 1/x)(log N - log π) - (1 + 1/x)|Re B(χ)| - (γ/2)(1 - 1/x) + (log 2)/x`.
Content: `r₀ = x⁻¹ L'/L(0)`, `r₁ = -L'/L(1)` (the two closed forms above); the regular-point
completed-to-ordinary bridge
(`DirichletLFunction.logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular`,
fed by
`LFunction_ne_zero_of_one_le_re`/
`DirichletLFunction.gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat`-type
regularity at `0, 1`) expresses `L'/L = F'/F - Γ_χ'/Γ_χ` at both points; substitute (F0), (F1),
(G0), (G1) and simplify.
Role: supplies the odd endpoint sum with `log N - log π` written separately.
-/
theorem re_add_dirichletReciprocalResidues_zero_one_of_odd_raw {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hodd : χ.Odd) {x : ℝ}
    (hx : 0 < x) :
    (dirichletReciprocalResidueAt hne x 0 +
          dirichletReciprocalResidueAt hne x
            1).re =
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
          (1 + 1 / x) * |primitiveBRe χ| -
          (Real.eulerMascheroniConstant / 2) * (1 - 1 / x) +
        (Real.log 2) / x := by
  have hr0 :=
    dirichletReciprocalResidueAt_zero_of_odd_eq
      hne hx hodd
  have hr1 :=
    dirichletReciprocalResidueAt_one_eq_neg_logDeriv
      hne x
  have hΓ0ne : DirichletCharacter.gammaFactor χ 0 ≠ 0 :=
    gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat
      hodd
      (by
        intro m hm
        have him := congrArg Complex.re hm
        simp only [zero_add] at him
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
          div_self_mul_self', Complex.neg_re, Complex.natCast_re] at him
        linarith)
  have hΓ1ne : DirichletCharacter.gammaFactor χ 1 ≠ 0 :=
    gammaFactor_ne_zero_of_odd_of_half_ne_neg_nat
      hodd
      (by
        intro m hm
        have him := congrArg Complex.re hm
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        simp only [add_self_div_two, Complex.one_re, Complex.neg_re, Complex.natCast_re] at him
        linarith)
  have hdΓ0 : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) 0 :=
    differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat
      hodd
      (by
        intro m hm
        have him := congrArg Complex.re hm
        simp only [zero_add] at him
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
          div_self_mul_self', Complex.neg_re, Complex.natCast_re] at him
        linarith)
  have hdΓ1 : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) 1 :=
    differentiableAt_gammaFactor_of_odd_of_half_ne_neg_nat
      hodd
      (by
        intro m hm
        have him := congrArg Complex.re hm
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        simp only [add_self_div_two, Complex.one_re, Complex.neg_re, Complex.natCast_re] at him
        linarith)
  have hF0ne :=
    dirichletCompletedLFunction_zero_ne_zero_of_primitive
      hprimitive hne
  have hF1ne : DirichletCharacter.completedLFunction χ 1 ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hne
      (le_refl 1)
  have hbridge0 :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular
      hne hF0ne hΓ0ne hdΓ0
  have hbridge1 :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular
      hne hF1ne hΓ1ne hdΓ1
  have hL0re :
    (logDeriv (DirichletCharacter.LFunction χ) 0).re =
      (logDeriv (DirichletCharacter.completedLFunction χ) 0).re -
        (logDeriv (DirichletCharacter.gammaFactor χ) 0).re := by
    rw [hbridge0]
    simp only [Complex.sub_re]
  have hL1re :
    (logDeriv (DirichletCharacter.LFunction χ) 1).re =
      (logDeriv (DirichletCharacter.completedLFunction χ) 1).re -
        (logDeriv (DirichletCharacter.gammaFactor χ) 1).re := by
    rw [hbridge1]
    simp only [Complex.sub_re]
  have hL0final :
    (logDeriv (DirichletCharacter.LFunction χ) 0).re =
      (-|primitiveBRe χ| -
          (1 / 2) * Real.log N) -
        (-Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2 - Real.log 2) := by
    rw [hL0re,
      completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log_of_grh
        hN2 hGRH hprimitive hne hinv,
      logDeriv_gammaFactor_zero_re_of_odd hodd]
  have hL1final :
    (logDeriv (DirichletCharacter.LFunction χ) 1).re =
      (|primitiveBRe χ| -
          (1 / 2) * Real.log N) -
        (-Real.log Real.pi / 2 - Real.eulerMascheroniConstant / 2) := by
    rw [hL1re,
      completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log_of_grh
        hN2 hGRH hprimitive hne hinv,
      logDeriv_gammaFactor_one_re_of_odd hodd]
  rw [hr0, hr1]
  simp only [Complex.add_re, Complex.neg_re]
  have hmulre :
    ((1 / x : ℂ) * logDeriv (DirichletCharacter.LFunction χ) 0).re =
      (1 / x) * (logDeriv (DirichletCharacter.LFunction χ) 0).re := by
    rw [show (1 / x : ℂ) = ((1 / x : ℝ) : ℂ) from by
        push_cast; ring,
      Complex.re_ofReal_mul]
  rw [hmulre, hL0final, hL1final]
  ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
