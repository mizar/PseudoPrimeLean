/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularGammaPositiveScale
public import PseudoPrime.LLS.TriangularDualScaleFormula

/-!
# Central Gamma form of the triangular dual-scale identity

Move both right-line Gamma integrals to the imaginary line at their positive scales.
The explicit weight series can then evaluate both terms without a scale restriction.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data and scale at least one, the dual-scale arithmetic
and oscillating zero sums equal the conductor profile plus the two central Gamma
integrals. Apply the positive-scale line shift at the scale and its inverse to the exact
dual-scale identity. This exposes both terms to the explicit reciprocal-weight series. -/
theorem triangular18_dual_scale_signed_formula_central {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let G := fun (ψ : DirichletCharacter ℂ q) (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor (Complex.I * t + 1 / 2) *
            (K.function (Complex.I * t) * (y : ℂ) ^ (Complex.I * t)))
    (∑' n : ℕ, K.summand χ x n) + (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n) +
        (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) =
      Complex.log q * (triangularKernelProfile 18 x : ℂ) + G χ x + G χ⁻¹ x⁻¹ := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hx0 := zero_lt_one.trans_le hx
  have h := triangular18_dual_scale_signed_formula hq hGRH hp hne hinv hx
  dsimp only at h ⊢
  have hshift (ψ : DirichletCharacter ℂ q) {y : ℝ} (hy : 0 < y) :=
    MellinKernel.gammaIntegral_eq_central_of_pos K ψ (b := 9 / 16) (by norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) hy
  rw [hshift χ hx0, hshift χ⁻¹ (inv_pos.mpr hx0)] at h
  exact h

/-- For primitive nonprincipal GRH data and scale at least one, the dual-scale identity
has two explicit convergent Gamma weight series and no unevaluated Gamma integrals.
Choose the parity bases for the character and its inverse, then evaluate both central
terms. This is the exact interface for signed numerical bounds in the target range. -/
theorem triangular18_dual_scale_signed_formula_weight_series {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    ∃ β γ : ℝ,
      1 / 4 ≤ β ∧
        β ≤ 1 ∧
          1 / 4 ≤ γ ∧
            γ ≤ 1 ∧
              let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
              (∑' n : ℕ, K.summand χ x n) + (∑' n : ℕ, K.summand χ⁻¹ x⁻¹ n) +
                  (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ) =
                Complex.log q * (triangularKernelProfile 18 x : ℂ) +
                  (((-Complex.log Real.pi + Complex.digamma (β : ℂ)) / 2) *
                      (triangularKernelProfile 18 x : ℂ) +
                    (1 / 2 : ℂ) * ∑' n : ℕ, triangularGammaReciprocalTerm 18 (β + n) x) +
                  (((-Complex.log Real.pi + Complex.digamma (γ : ℂ)) / 2) *
                      (triangularKernelProfile 18 x⁻¹ : ℂ) +
                    (1 / 2 : ℂ) * ∑' n : ℕ, triangularGammaReciprocalTerm 18 (γ + n) x⁻¹) := by
  obtain ⟨β, hβ, hβ1, hg⟩ := triangular_central_gammaIntegral_eq_weight_series χ
  obtain ⟨γ, hγ, hγ1, hgi⟩ := triangular_central_gammaIntegral_eq_weight_series χ⁻¹
  refine ⟨β, γ, hβ, hβ1, hγ, hγ1, ?_⟩
  have h := triangular18_dual_scale_signed_formula_central hq hGRH hp hne hinv hx
  dsimp only at h ⊢
  simp only [triangularMellinKernel] at h
  rw [hg 18 x (by norm_num only) (zero_lt_one.trans_le hx),
    hgi 18 x⁻¹ (by norm_num only) (inv_pos.mpr (zero_lt_one.trans_le hx))] at h
  exact h

end PseudoPrime.LLS.PaperStatements
