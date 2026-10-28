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
public import PseudoPrime.LLS.PaperStatements.DirichletSpecialization

/-!
# Arithmetic specialization of general L-function data to Dirichlet characters

Degree-one data, finite sums, gamma endpoints and completed-zero multiplicities are compared.
The identities transfer arithmetic sums, RH and zero mass without requiring general admissibility.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions.GeneralLFunction

/-- The real digamma value at one half is the even-character endpoint constant.
Take real parts of the complex special value and convert the logarithm of two.
This supplies the gamma term in the degree-one logarithmic formula. -/
private theorem digamma_one_half_re :
    (Complex.digamma (1 / 2)).re = -2 * Real.log 2 - Real.eulerMascheroniConstant := by
  rw [Complex.digamma_one_half]
  simp only [Complex.sub_re, Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
    Complex.re_ofNat, Complex.im_ofNat, neg_zero, zero_mul, sub_zero]
  rw [show (Complex.log (2 : ℂ)).re = Real.log 2 from Complex.log_ofReal_re 2]

/-- The gamma endpoint of degree-one character data equals the parity constant in Lemma 2.5.
The singleton gamma sum reduces to digamma at one half or one; no RH or primitivity is needed.
This identifies the deterministic term of the generalized logarithmic formula. -/
theorem ofDirichletCharacter_gammaLogDerivativeAtOne {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    (ofDirichletCharacter χ).gammaLogDerivativeAtOne =
      Real.log ((q : ℝ) / Real.pi) / 2 +
        (if χ (-1) = 1 then -2 * Real.log 2 - Real.eulerMascheroniConstant
          else -Real.eulerMascheroniConstant) /
          2 := by
  change
    Real.log ((q : ℝ) / Real.pi ^ 1) / 2 +
        (∑ _j : Fin 1, (Complex.digamma ((1 + if χ (-1) = 1 then 0 else 1) / 2)).re) / 2 =
      _
  rw [Fin.sum_univ_one, pow_one]
  split_ifs with h
  · rw [add_zero, digamma_one_half_re]
  · norm_num only [Complex.digamma_one, Complex.neg_re, Complex.ofReal_re]

/-- The conductor and parity normalization never vanish, for any nonzero modulus.
Nonzero complex powers and positivity of the square root of pi prove the claim.
Consequently normalization preserves the completed-zero set. -/
private theorem completionScale_ne_zero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    (q : ℂ) ^ (s / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ)) ≠ 0 := by
  apply mul_ne_zero (Complex.cpow_ne_zero_iff.mpr (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q))))
  split_ifs with h
  · exact one_ne_zero
  · exact Complex.ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.mpr Real.pi_pos))

/-- The normalized completion vanishes exactly at the character's completed zeros.
Cancel the nonzero conductor and parity factor. This transports RH and reindexes zero mass. -/
theorem ofDirichletCharacter_completed_eq_zero_iff {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (s : ℂ) : (ofDirichletCharacter χ).completed s = 0 ↔ χ.completedLFunction s = 0 := by
  change
    ((q : ℂ) ^ (s / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))) *
          χ.completedLFunction s =
        0 ↔
      _
  rw [mul_eq_zero]
  exact or_iff_right (completionScale_ne_zero χ s)

/-- Individual RH of a primitive nontrivial character gives RH of its degree-one data.
Normalization preserves zeros, and reflection excludes trivial completed zeros.
This uses the precise hypothesis of Lemma 2.5 rather than global Dirichlet GRH. -/
theorem ofDirichletCharacter_riemannHypothesis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) :
    (ofDirichletCharacter χ).RiemannHypothesis := by
  intro ρ
  exact
    AnalyticNumberTheory.DirichletLFunction.completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp
      (inv_ne_one.mpr hne) ((ofDirichletCharacter_completed_eq_zero_iff χ ρ).mp ρ.property)

/-- The normalization factor is entire, since its complex-power base is nonzero.
Differentiate the exponent and multiply by the constant parity factor.
Analyticity of this unit is needed to compare completed-zero multiplicities. -/
private theorem differentiable_completionScale {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    Differentiable ℂ
      (fun z : ℂ ↦ (q : ℂ) ^ (z / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))) := by
  exact
    ((differentiable_id.div_const 2).const_cpow
          (Or.inl (Nat.cast_ne_zero.mpr (NeZero.ne q)))).mul_const
      _

/-- For a nontrivial character, normalization preserves analytic multiplicity at every point.
Its factor is an analytic unit of order zero, so additivity of order gives the equality.
This identifies the actual multiplicities used in the generalized zero mass. -/
theorem ofDirichletCharacter_analyticOrderNatAt_completed {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderNatAt (ofDirichletCharacter χ).completed s =
      analyticOrderNatAt χ.completedLFunction s := by
  change
    analyticOrderNatAt
        ((fun z : ℂ ↦ (q : ℂ) ^ (z / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))) *
          χ.completedLFunction)
        s =
      _
  have ho :
    analyticOrderAt
        (fun z : ℂ ↦ (q : ℂ) ^ (z / 2) * (if χ (-1) = 1 then 1 else (Real.sqrt Real.pi : ℂ))) s =
      0 :=
    analyticOrderAt_eq_zero.mpr (Or.inr (completionScale_ne_zero χ s))
  unfold analyticOrderNatAt
  rw [analyticOrderAt_mul ((differentiable_completionScale χ).analyticAt s)
      ((DirichletCharacter.differentiable_completedLFunction hne).analyticAt s),
    ho, zero_add]

/-- For a nontrivial character, the normalized zero mass is the original completed-zero sum.
Reindex by the unchanged zero set and use equality of analytic multiplicities.
This is the subtype form of the mass needed to specialize the generalized formula. -/
theorem ofDirichletCharacter_zeroMass_eq_subtype_tsum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    (ofDirichletCharacter χ).zeroMass =
      ∑' ρ : { z : ℂ // χ.completedLFunction z = 0 },
        (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 := by
  let e : (ofDirichletCharacter χ).Zero ≃ { z : ℂ // χ.completedLFunction z = 0 } :=
    Equiv.subtypeEquivProp (funext fun z ↦ propext (ofDirichletCharacter_completed_eq_zero_iff χ z))
  rw [← e.tsum_eq (fun ρ ↦ (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2)]
  apply tsum_congr
  intro ρ
  change
    (analyticOrderNatAt (ofDirichletCharacter χ).completed (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2 =
      (analyticOrderNatAt χ.completedLFunction (ρ : ℂ) : ℝ) / ‖(ρ : ℂ)‖ ^ 2
  rw [ofDirichletCharacter_analyticOrderNatAt_completed χ hne]

/-- The normalized mass equals the divisor-weighted mass of the character's completed function.
Extend the zero-subtype sum by zero, convert analytic order to divisor multiplicity,
and identify squared norm with `Complex.normSq`. This connects the general mass to `primitiveBRe`.
Only nontriviality is needed; the equality does not assume RH or convergence. -/
theorem ofDirichletCharacter_zeroMass_eq_divisor_tsum {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1) :
    (ofDirichletCharacter χ).zeroMass =
      ∑' z : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ z : ℝ) / Complex.normSq z := by
  rw [ofDirichletCharacter_zeroMass_eq_subtype_tsum χ hne]
  exact
    AnalyticNumberTheory.General.tsum_zeroMultiplicity_eq_divisor
      (DirichletCharacter.differentiable_completedLFunction hne)

open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character of modulus at least two under its individual RH,
the degree-one zero mass equals `2 * |primitiveBRe χ|`. Convert the normalized mass to the
completed function's divisor sum and apply the single-character mass identity.
This supplies the zero-mass substitution in Lemma 2.5 without RH for other characters. -/
theorem ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe_of_dirichletRH {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ) :
    (ofDirichletCharacter χ).zeroMass =
      2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  rw [ofDirichletCharacter_zeroMass_eq_divisor_tsum χ hne]
  exact tsum_divisor_inv_normSq_eq_two_mul_abs_BRe_of_dirichletRH hq hRH hp hne (inv_ne_one.mpr hne)

/-- Under GRH, the degree-one mass is twice the absolute real Hadamard constant.
The modulus is at least two and the character is primitive and nontrivial.
Use the divisor-mass identity after normalization. This supplies the mass term for Theorem 1.5. -/
theorem ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hq : 2 ≤ q) (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (ofDirichletCharacter χ).zeroMass =
      2 * |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| := by
  exact ofDirichletCharacter_zeroMass_eq_two_mul_abs_BRe_of_dirichletRH χ hq hp hne (hGRH q χ hp)

end PseudoPrime.LLS.Extensions.GeneralLFunction
