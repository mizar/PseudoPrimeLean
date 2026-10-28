/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteZeroMass
public import PseudoPrime.LLS.TriangularArchimedeanBounds
public import PseudoPrime.LLS.PaperStatements.TriangularSignedZeroMass2

/-! # Signed arithmetic formula for triangular absolute zero mass

Keep the character and inverse-character arithmetic sums on the left.
Only the two gamma integrals remain in addition to the conductor.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data of modulus at least two and nonprincipal
inverse, the scale-one arithmetic sums for the character and its inverse plus
the absolute zero mass equal 36 log(q) plus the two gamma integrals.
Reflect the ordinary Euler integral and retain both signed arithmetic sums.
This is the entry point for cancellation across a finite character family. -/
theorem triangular18_absoluteMass_signed_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let G := fun ψ : DirichletCharacter ℂ q ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
    (∑' n : ℕ, K.summand χ 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
        ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      36 * Complex.log q + G χ + G χ⁻¹ := by
  have he := triangular18_absoluteMass_conductor_formula hq hGRH hp hne hinv
  dsimp only at he ⊢
  rw [triangular_weightedResidue_pole_eq_zero, add_zero, triangular18_reflectedIntegral_eq_right,
    triangular18_completed_rightIntegral_eq_arithmetic_add_gamma hinv] at he
  linear_combination he

end PseudoPrime.LLS.PaperStatements
