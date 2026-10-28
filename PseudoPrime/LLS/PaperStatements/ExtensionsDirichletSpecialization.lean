/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.PaperStatements
public import PseudoPrime.LLS.Extensions.ArithmeticCoefficients
public import PseudoPrime.LLS.DirichletExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.General.AnalyticMultiplicity
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import PseudoPrime.LLS.Extensions.GeneralLFunction.DirichletSpecialization2

/-!
# Arithmetic specialization of general L-function data to Dirichlet characters

Degree-one data, finite sums, gamma endpoints and completed-zero multiplicities are compared.
The identities transfer arithmetic sums, RH and zero mass without requiring general admissibility.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For `x ≥ 1`, the real part of the character logarithmic L-value sum is at most
its unsigned counterpart. The extension's degree-one norm comparison supplies the bound.
This is the arithmetic upper-bound input to Theorem 1.5. -/
theorem characterLogLValueSum_re_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {x : ℝ}
    (hx : 1 ≤ x) : (characterLogLValueSum χ x).re ≤ logLValueSum x := by
  exact (Complex.re_le_norm _).trans (norm_characterLogLValueSum_le χ hx)

/-- For a primitive character of modulus at least three under individual RH and `x ≥ 2`,
the general logarithmic formula gives the parity-dependent formula of Lemma 2.5.
The general formula, admissibility of the degree-one data, and its mass identity are
explicit premises. Transport RH, substitute the arithmetic sum, gamma endpoint and mass,
and rearrange the two bounded errors. This is the specialization interface used by the
mass-free and admissibility-free versions. -/
theorem characterLogLValue_formula_of_general (hformula : Extensions.lls_propL1_general) {q : ℕ}
    [NeZero q] (χ : DirichletCharacter ℂ q) (hq : 3 ≤ q) (hp : χ.IsPrimitive)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hf : (Extensions.GeneralLFunction.ofDirichletCharacter χ).IsAdmissible)
    (hMass :
      (Extensions.GeneralLFunction.ofDirichletCharacter χ).zeroMass =
        2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ|)
    {x : ℝ} (hx : 2 ≤ x) :
    ∃ θ₁ θ₂ : ℝ,
      |θ₁| ≤ 1 ∧
        |θ₂| ≤ 1 ∧
        Real.log ‖χ.LFunction 1‖ =
          (characterLogLValueSum χ x).re +
                (1 / Real.log x) *
                  (Real.log ((q : ℝ) / Real.pi) / 2 +
                    (if χ (-1) = 1 then -2 * Real.log 2 - Real.eulerMascheroniConstant
                      else -Real.eulerMascheroniConstant) /
                      2) -
              (1 / Real.log x + 2 * θ₁ / (Real.sqrt x * (Real.log x) ^ 2)) *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            2 * θ₂ / (x * (Real.log x) ^ 2) := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hRHf := Extensions.GeneralLFunction.ofDirichletCharacter_riemannHypothesis χ hp hne hRH
  obtain ⟨θ₁, θ₂, hθ₁, hθ₂, he⟩ :=
    (hformula (Extensions.GeneralLFunction.ofDirichletCharacter χ) hf hRHf).2 x hx
  rw [Extensions.GeneralLFunction.ofDirichletCharacter_logValueSum,
    Extensions.GeneralLFunction.ofDirichletCharacter_gammaLogDerivativeAtOne, hMass] at he
  simp only [Extensions.GeneralLFunction.ofDirichletCharacter, Nat.cast_one, mul_one] at he
  refine ⟨θ₁, θ₂, hθ₁, hθ₂, ?_⟩
  convert he using 1
  ring

/-- For a primitive character of modulus at least three under individual RH and `x ≥ 2`,
assume the general logarithmic formula and admissibility of its degree-one data.
Identify zero mass as twice the absolute real Hadamard constant using this character's RH,
then apply the specialization formula. The mass identity is derived rather than assumed;
the remaining premises are the formula and admissibility. -/
theorem characterLogLValue_formula_of_general_of_admissible
    (hformula : Extensions.lls_propL1_general) {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hf : (Extensions.GeneralLFunction.ofDirichletCharacter χ).IsAdmissible) {x : ℝ} (hx : 2 ≤ x) :
    ∃ θ₁ θ₂ : ℝ,
      |θ₁| ≤ 1 ∧
        |θ₂| ≤ 1 ∧
        Real.log ‖χ.LFunction 1‖ =
          (characterLogLValueSum χ x).re +
                (1 / Real.log x) *
                  (Real.log ((q : ℝ) / Real.pi) / 2 +
                    (if χ (-1) = 1 then -2 * Real.log 2 - Real.eulerMascheroniConstant
                      else -Real.eulerMascheroniConstant) /
                      2) -
              (1 / Real.log x + 2 * θ₁ / (Real.sqrt x * (Real.log x) ^ 2)) *
                |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| +
            2 * θ₂ / (x * (Real.log x) ^ 2) := by
  have hne := primitiveCharacter_ne_one_of_three_le hq hp
  have hMass :=
    Extensions.GeneralLFunction.ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe_of_dirichletRH χ
      (Nat.le_trans (by norm_num only : 2 ≤ 3) hq) hp hne hRH
  exact characterLogLValue_formula_of_general hformula χ hq hp hRH hf hMass hx

/-- The general logarithmic formula implies Lemma 2.5 when degree-one primitive
character data at modulus at least three is assumed admissible. Introduce the parameters
of the numbered statement and use the mass-free specialization under individual RH.
This packages the implication with the admissibility premise explicit. -/
theorem lls_lemma25_of_general (hformula : Extensions.lls_propL1_general)
    (hadmissible :
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
        3 ≤ q → χ.IsPrimitive → (Extensions.GeneralLFunction.ofDirichletCharacter χ).IsAdmissible) :
    lls_lemma25 := by
  intro q _ χ hq hp hRH x hx
  exact
    characterLogLValue_formula_of_general_of_admissible hformula χ hq hp hRH (hadmissible q χ hq hp)
      hx

end PseudoPrime.LLS.PaperStatements
