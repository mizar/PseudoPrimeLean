/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleGammaZeroMass
public import PseudoPrime.AnalyticNumberTheory.Gamma.SignedGammaIntervalBounds
public import PseudoPrime.AnalyticNumberTheory.Gamma.TwoPoleGammaSignedConstant

/-! # Signed Gamma-factor corrections for the two-pole zero-mass bound -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For every Dirichlet character and positive real sigma at most 5/4, the
Gamma-factor real logarithmic derivative is at most -3/4. Treat the even and odd
shifts using the common GammaReal interval. No RH or primitivity is needed. -/
theorem re_logDeriv_gammaFactor_le_neg_three_fourths {q : ℕ} (χ : DirichletCharacter ℂ q) {σ : ℝ}
    (hσ : 0 < σ) (hu : σ ≤ 5 / 4) : (logDeriv χ.gammaFactor (σ : ℂ)).re ≤ -(3 / 4 : ℝ) := by
  have hf : (1 : DirichletCharacter ℂ 1).gammaFactor = Complex.Gammaℝ := by
    funext z
    exact principal_modulus_one_even.gammaFactor_def z
  rcases logDeriv_gammaFactor_eq_one_or_one_shift χ (show 0 < (σ : ℂ).re from hσ) with h | h
  · rw [h, hf]
    exact Gamma.re_logDeriv_GammaReal_le_neg_three_fourths hσ (by linarith only [hu])
  · rw [h, hf]
    rw [show (σ : ℂ) + 1 = ((σ + 1 : ℝ) : ℂ) from (Complex.ofReal_add σ 1).symm]
    exact
      Gamma.re_logDeriv_GammaReal_le_neg_three_fourths (by linarith only [hσ])
        (by linarith only [hu])

/-- For every character, the signed two-pole Gamma remainder is at most 523/100.
Retain the negative first Gamma derivative and use the other certified Gamma and
principal Euler bounds. This improves the conductor-independent zero-mass constant. -/
theorem twoPoleGammaConstant_le_signed {q : ℕ} (χ : DirichletCharacter ℂ q) :
    twoPoleGammaConstant χ ≤ 523 / 100 := by
  have hA :=
    re_logDeriv_gammaFactor_le_neg_three_fourths χ (by norm_num only : (0 : ℝ) < 5 / 4)
      (le_refl (5 / 4 : ℝ))
  have hB := (abs_le.mp (abs_re_gammaFactor_eleven_fourths_le χ)).1
  have hZ := re_principal_logDeriv_nonpos (σ := 11 / 4) (by norm_num only)
  have hP :=
    (abs_le.mp
        ((Complex.abs_re_le_norm
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((5 / 4 : ℝ) : ℂ))).trans
          norm_principal_logDeriv_five_fourths_le_four)).1
  dsimp only [twoPoleGammaConstant]
  linarith only [hA, hB, hZ, hP]

/-- For every even character, the signed two-pole Gamma remainder is at most
112/25. Use the stronger even Gamma bound at the first node while preserving the
other signs. This supplies the sharper constant for positive quadratic inputs. -/
theorem twoPoleGammaConstant_le_signed_of_even {q : ℕ} (χ : DirichletCharacter ℂ q)
    (heven : χ.Even) : twoPoleGammaConstant χ ≤ 112 / 25 := by
  have hf : χ.gammaFactor = Complex.Gammaℝ := funext (fun z ↦ heven.gammaFactor_def z)
  have hA : (logDeriv χ.gammaFactor ((5 / 4 : ℝ) : ℂ)).re ≤ -(5 / 4 : ℝ) := by
    rw [hf]
    exact Gamma.re_logDeriv_GammaReal_le_neg_five_fourths (by norm_num only) (le_refl _)
  have hB := (abs_le.mp (abs_re_gammaFactor_eleven_fourths_le χ)).1
  have hZ := re_principal_logDeriv_nonpos (σ := 11 / 4) (by norm_num only)
  have hP :=
    (abs_le.mp
        ((Complex.abs_re_le_norm
              (logDeriv (1 : DirichletCharacter ℂ 1).LFunction ((5 / 4 : ℝ) : ℂ))).trans
          norm_principal_logDeriv_five_fourths_le_four)).1
  dsimp only [twoPoleGammaConstant]
  linarith only [hA, hB, hZ, hP]

/-- For primitive nonprincipal individual-RH data and any certified upper C on
the two-pole Gamma constant, the Gamma zero mass converges and is at most half
the conductor logarithm plus C minus both retained Euler prefixes. Insert C only
after the signed Poisson comparison, preserving it for arithmetic consumers. -/
theorem gamma_zeroMass_le_twoPole_of_constant {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {C : ℝ} (hC : twoPoleGammaConstant χ ≤ C) (A B : Finset ℕ) :
    Summable
        (fun ρ : ℂ ↦
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ∧
      (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖Complex.Gamma ρ‖) ≤
        Real.log q / 2 + C - (∑ n ∈ A, realPairedEulerTerm χ (5 / 4) n) -
          (3 / 4 : ℝ) * (∑ n ∈ B, Real.log n * realPairedEulerTerm χ (11 / 4) n) := by
  have h := gamma_zeroMass_le_twoPole_retained_prefixes hq hRH hp hne hinv A B
  exact ⟨h.1, by linarith only [h.2, hC]⟩

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
