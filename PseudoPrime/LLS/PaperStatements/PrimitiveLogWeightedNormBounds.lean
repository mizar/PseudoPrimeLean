/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.DirichletExplicitFormula
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimitiveComparison

/-! # Norm bounds for primitive logarithmic character sums

Retain the complex logarithmic derivative at zero when taking the norm of the
explicit formula. This gives equation (4.4), rather than only a real-part estimate.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Two complex errors of norm at most one give `2u+2` at a nonnegative scale `u`.
Use multiplicativity of the norm and its triangle inequality. This bounds the zero
contribution in the logarithmic explicit formula. -/
private theorem norm_two_theta_mul_add_le {θ₁ θ₂ : ℂ} {u : ℝ} (hu : 0 ≤ u) (hθ₁ : ‖θ₁‖ ≤ 1)
    (hθ₂ : ‖θ₂‖ ≤ 1) : ‖2 * θ₁ * (u : ℂ) + 2 * θ₂‖ ≤ 2 * u + 2 := by
  have h := norm_add_le (2 * θ₁ * (u : ℂ)) (2 * θ₂)
  simp only [norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hu] at h
  nlinarith only [h, hθ₁, hθ₂, hu]

/-- For a primitive character of modulus at least three, GRH bounds the norm of
its logarithmic weighted sum at every cutoff above one. The terms are the zero
mass, the norm of the completed logarithmic derivative at zero times log cutoff,
and the absolute conductor-parity correction. Take norms in Lemma 2.2's complex
formula. This is the estimate in equation (4.4) used for coset bounds. -/
theorem norm_characterLogWeightedSum_le_explicit {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hq : 3 ≤ q) (hp : χ.IsPrimitive) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| * (2 * Real.sqrt x + 2) +
        ‖logDeriv (xi χ) 0‖ * Real.log x +
        |Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + logCorrection χ x| := by
  obtain ⟨θ₁, θ₂, hθ₁, hθ₂, he⟩ := characterLogWeightedSum_complex_formula hq hp hGRH hx
  rw [he]
  have hb := norm_two_theta_mul_add_le (Real.sqrt_nonneg x) hθ₁ hθ₂
  have hm :
    ‖((|AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| : ℝ) : ℂ) *
          (2 * θ₁ * (Real.sqrt x : ℂ) + 2 * θ₂)‖ ≤
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| * (2 * Real.sqrt x + 2) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have ht :=
    (norm_add_le
          (((|AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ| : ℝ) : ℂ) *
              (2 * θ₁ * (Real.sqrt x : ℂ) + 2 * θ₂) -
            logDeriv (xi χ) 0 * (Real.log x : ℂ))
          ((Real.log ((q : ℝ) / Real.pi) * Real.log x / 2 + logCorrection χ x : ℝ) : ℂ)).trans
      (add_le_add (norm_sub_le _ _) (le_refl _))
  simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_abs,
    abs_of_pos (Real.log_pos hx)] at ht hm
  linarith only [ht, hm]

/-- For a character of conductor at least three and cutoff above one, GRH bounds
its logarithmic sum by the primitive explicit estimate plus the common-factor error.
The latter is one half the number of distinct prime factors of the level-conductor
quotient times the squared logarithm. Combine the primitive norm estimate with the
level-change norm bound. This gives equations (4.4) and (4.5) for imprimitive data. -/
theorem norm_characterLogWeightedSum_le_primitive_explicit {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hq : 3 ≤ χ.conductor)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    ‖AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ‖ ≤
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| *
          (2 * Real.sqrt x + 2) +
        ‖logDeriv (xi χ.primitiveCharacter) 0‖ * Real.log x +
        |Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 +
            logCorrection χ.primitiveCharacter x| +
        (1 / 2 : ℝ) * (q / χ.conductor).primeFactors.card * (Real.log x) ^ 2 := by
  have h :=
    norm_add_le
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ -
        AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.primitiveCharacter)
      (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.primitiveCharacter)
  rw [sub_add_cancel] at h
  have he :=
    AnalyticNumberTheory.Arithmetic.norm_characterLogWeightedSum_sub_primitive_le x χ
      (zero_lt_one.trans hx)
  have hp :=
    norm_characterLogWeightedSum_le_explicit hq
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hGRH hx
  linarith only [h, he, hp]

end PseudoPrime.LLS.PaperStatements
