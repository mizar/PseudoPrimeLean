/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteZeroMass
public import PseudoPrime.LLS.TriangularArchimedeanBounds
public import PseudoPrime.LLS.PaperStatements.TriangularSignedZeroMass3

/-! # Signed arithmetic formula for triangular absolute zero mass

Keep the character and inverse-character arithmetic sums on the left.
Only the two gamma integrals remain in addition to the conductor.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a finite family of primitive nonprincipal GRH characters of the same
modulus, sum the signed absolute-mass formulas before taking any norms.
The cardinality multiplies the exact conductor term; arithmetic and gamma terms
retain their signs. This is the finite-family interface for improved zero budgets. -/
theorem triangular18_sum_absoluteMass_signed_formula {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    (S : Finset (DirichletCharacter ℂ q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : ∀ (χ : DirichletCharacter ℂ q), χ ∈ S → χ.IsPrimitive)
    (hne : ∀ (χ : DirichletCharacter ℂ q), χ ∈ S → χ ≠ 1)
    (hinv : ∀ (χ : DirichletCharacter ℂ q), χ ∈ S → χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let G := fun ψ : DirichletCharacter ℂ q ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
    (∑ χ ∈ S,
        ((∑' n : ℕ, K.summand (χ : DirichletCharacter ℂ q) 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
          ((∑' ρ : ℂ, ‖K.kernelZeroTerm (q := q) χ ρ‖ : ℝ) : ℂ))) =
      (S.card : ℂ) * (36 * Complex.log q) + ∑ χ ∈ S, (G χ + G χ⁻¹) := by
  dsimp only
  calc
    _ = ∑ χ ∈ S, (36 * Complex.log q + _ + _) :=
      Finset.sum_congr rfl
        (fun χ hχ ↦
          triangular18_absoluteMass_signed_formula hq hGRH (hp χ hχ) (hne χ hχ) (hinv χ hχ))
    _ = _ := by simp only [add_assoc, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]

end PseudoPrime.LLS.PaperStatements
