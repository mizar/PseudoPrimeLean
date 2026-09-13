/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveEvenZeroLocalFactor
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveResidueClosedForms

/-!
# The sum of reciprocal-kernel residues at zero and one for an even character

For a primitive nontrivial even character, combine the canonical local factor at zero from
`PrimitiveEvenZeroLocalFactor` with the completed-L-function endpoint identities and gamma-factor
special values from `PrimitiveResidueClosedForms`. Under GRH this expresses the real part of the
sum in terms of the modulus, the real Hadamard constant, and the positive real parameter `x`.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: `N ≥ 2`, `χ` primitive nontrivial even mod `N`, GRH, `χ⁻¹ ≠ 1`,
`x > 0`.
Conclusion:
`Re (r₀ + r₁) = (1/2)(1 - 1/x)(log N - log π) - (1 + 1/x)|Re B(χ)| - log 2 - (γ/2)(1 - 1/x) +
(log x + 1)/x`.
Proof: `dirichletReciprocalResidueAt_zero_of_primitive_even_eq` identifies `r₀` with the derivative
of the canonical regularization; `deriv_dirichletReciprocalEvenZeroRegularization_zero` and
`logDeriv_dirichletEvenZeroLocalFactor_zero` evaluate it. At one, the completed-to-ordinary
logarithmic-derivative identity evaluates `r₁ = -L'/L(1)`. Substitute the completed-L-function
endpoint real parts and the even gamma-factor value, then collect terms.
Role: supplies the even-character endpoint contribution to the reciprocal-kernel residue sum.
-/
theorem re_add_dirichletReciprocalResidues_zero_one_of_even_raw {N : ℕ} [NeZero N] (hN2 : 2 ≤ N)
    {χ : DirichletCharacter ℂ N}
    (hGRH : GRH.GeneralizedRiemannHypothesis)
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (heven : χ.Even) {x : ℝ}
    (hx : 0 < x) :
    (dirichletReciprocalResidueAt hne x 0 +
          dirichletReciprocalResidueAt hne x
            1).re =
      (1 / 2) * (1 - 1 / x) * (Real.log N - Real.log Real.pi) -
          (1 + 1 / x) * |primitiveBRe χ| -
          Real.log 2 -
          (Real.eulerMascheroniConstant / 2) * (1 - 1 / x) +
        (Real.log x + 1) / x := by
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  -- r₀ via the canonical local factor and (ER)
  have hr0eq :=
    dirichletReciprocalResidueAt_zero_of_primitive_even_eq
      hprimitive hne heven x
  obtain ⟨hGanalytic, hG0⟩ :=
    analyticAt_and_ne_zero_dirichletEvenZeroLocalFactor
      hprimitive hne
  have hER :=
    deriv_dirichletReciprocalEvenZeroRegularization_zero
      hx 1 hGanalytic hG0
  have hG0logDeriv :=
    logDeriv_dirichletEvenZeroLocalFactor_zero
      hprimitive hne
  rw [hG0logDeriv] at hER
  rw [hER] at hr0eq
  have hr0re :
    (dirichletReciprocalResidueAt hne x 0).re =
      (1 / x) *
        ((logDeriv (DirichletCharacter.completedLFunction χ) 0).re +
          (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 +
          Real.log x +
          1) := by
    rw [hr0eq]
    have hmulre :
      ((1 / x : ℂ) *
            (logDeriv (DirichletCharacter.completedLFunction χ) 0 +
              (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 +
              (1 : ℕ) * (Complex.log (x : ℂ) + 1))).re =
        (1 / x) *
          ((logDeriv (DirichletCharacter.completedLFunction χ) 0).re +
            (Real.log Real.pi + Real.eulerMascheroniConstant) / 2 +
            Real.log x +
            1) := by
      have hconst_eq :
        (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 +
            (1 : ℕ) * (Complex.log (x : ℂ) + 1) =
          (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 + Real.log x + 1 : ℝ) : ℂ) := by
        rw [← Complex.ofReal_log Real.pi_nonneg, ← Complex.ofReal_log hx.le]
        push_cast
        ring
      rw [show
          logDeriv (DirichletCharacter.completedLFunction χ) 0 +
              (Complex.log (Real.pi : ℂ) + (Real.eulerMascheroniConstant : ℂ)) / 2 +
              (1 : ℕ) * (Complex.log (x : ℂ) + 1) =
            logDeriv (DirichletCharacter.completedLFunction χ) 0 +
              (((Real.log Real.pi + Real.eulerMascheroniConstant) / 2 + Real.log x + 1 : ℝ) : ℂ)
          from by
          rw [← hconst_eq]; ring,
        show (1 / x : ℂ) = ((1 / x : ℝ) : ℂ) from by
          push_cast; ring,
        Complex.re_ofReal_mul, Complex.add_re, Complex.ofReal_re]
      ring
    rw [hmulre]
  -- r₁ via the regular-point bridge
  have hΓ1ne : DirichletCharacter.gammaFactor χ 1 ≠ 0 :=
    gammaFactor_ne_zero_of_even_of_half_ne_neg_nat
      heven
      (by
        intro m hm
        have him := congrArg Complex.re hm
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
          div_self_mul_self', Complex.neg_re, Complex.natCast_re] at him;
        linarith)
  have hdΓ1 : DifferentiableAt ℂ (DirichletCharacter.gammaFactor χ) 1 :=
    differentiableAt_gammaFactor_of_even_of_half_ne_neg_nat
      heven
      (by
        intro m hm
        have him := congrArg Complex.re hm
        have hmnn : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
        simp only [one_div, Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat,
          div_self_mul_self', Complex.neg_re, Complex.natCast_re] at him;
        linarith)
  have hF1ne : DirichletCharacter.completedLFunction χ 1 ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hne
      (le_refl 1)
  have hbridge1 :=
    logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular
      hne hF1ne hΓ1ne hdΓ1
  have hr1 :=
    dirichletReciprocalResidueAt_one_eq_neg_logDeriv
      hne x
  have hr1re :
    (dirichletReciprocalResidueAt hne x 1).re =
      -((logDeriv (DirichletCharacter.completedLFunction χ) 1).re -
          (logDeriv (DirichletCharacter.gammaFactor χ) 1).re) := by
    rw [hr1, hbridge1]
    simp only [neg_sub, Complex.sub_re]
  -- assemble
  have hF0re :=
    completedLFunction_logDeriv_zero_re_eq_neg_abs_BRe_sub_half_log_of_grh
      hN2 hGRH hprimitive hne hinv
  have hF1re :=
    completedLFunction_logDeriv_one_re_eq_abs_BRe_sub_half_log_of_grh
      hN2 hGRH hprimitive hne hinv
  have hG1re :=
    logDeriv_gammaFactor_one_re_of_even heven
  rw [Complex.add_re, hr0re, hr1re, hF0re, hF1re, hG1re]
  ring

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
