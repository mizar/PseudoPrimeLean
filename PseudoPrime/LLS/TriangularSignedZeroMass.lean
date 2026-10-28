/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularFiniteZeroMass
public import PseudoPrime.LLS.TriangularArchimedeanBounds
public import PseudoPrime.LLS.PaperStatements.TriangularSignedZeroMass4

/-! # Signed arithmetic formula for triangular absolute zero mass

Keep the character and inverse-character arithmetic sums on the left.
Only the two gamma integrals remain in addition to the conductor.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data, the alpha-18 absolute zero mass is
at most 36 log(q) minus the character and inverse arithmetic real parts plus
110000. Shift each gamma integral to the central line and retain the signs
of both scale-one sums. This supplies a sharper signed comparison budget. -/
theorem triangular18_absoluteMass_le_signed_arithmetic {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤
      36 * Real.log q - (∑' n : ℕ, K.summand χ 1 n).re - (∑' n : ℕ, K.summand χ⁻¹ 1 n).re +
        110000 := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let G := fun ψ : DirichletCharacter ℂ q ↦
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
          K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t))
  have hg (ψ : DirichletCharacter ℂ q) : (G ψ).re ≤ 55000 := by
    have hn :=
      triangular18_gammaIntegral_norm_le_uniform ψ (b := 9 / 16) (x := 1) (by norm_num only)
        (by norm_num only) (le_refl _)
    simp only [Complex.ofReal_one, Complex.one_cpow, mul_one] at hn
    exact (Complex.re_le_norm (G ψ)).trans hn
  have he := triangular18_absoluteMass_signed_formula hq hGRH hp hne hinv
  change
    (∑' n : ℕ, K.summand χ 1 n) + (∑' n : ℕ, K.summand χ⁻¹ 1 n) +
        ((∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ : ℝ) : ℂ) =
      36 * Complex.log q + G χ + G χ⁻¹ at he
  rw [← Complex.natCast_log, ← Complex.ofReal_ofNat 36, ← Complex.ofReal_mul] at he
  have hr := congrArg Complex.re he
  simp only [Complex.add_re, Complex.ofReal_re] at hr
  change (∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖) ≤ _
  linarith only [hr, hg χ, hg χ⁻¹]

end PseudoPrime.LLS.PaperStatements
