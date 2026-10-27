/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.RealPairedEuler
public import PseudoPrime.Analysis.GammaPairedEulerMass

/-! # Signed resolvent identities retaining the nonnegative paired Euler mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under individual RH and primitive nonprincipal conductor data, the
actual resolvent zero mass plus the nonnegative paired Euler mass equals
the exact conductor and Gamma contributions plus the untwisted common mass.
The real-axis derivative cancellation is preserved as an equality. -/
theorem gammaResolvent_zeroMass_add_pairedEuler_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        (∑' m : ℕ, Analysis.gammaPairedEulerTerm χ m) =
      (11783423 / 25000000 : ℝ) * Real.log q +
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        ∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m := by
  rw [gammaResolvent_zeroMass_eq_signed_euler hq hRH hp hne hinv, add_assoc,
    Analysis.gamma_signed_euler_add_paired_eq_total χ]

/-- The signed finite-node pair of real logarithmic derivatives equals
the nonnegative common paired Euler mass. Combine all signed coefficients
before using positivity of H; negative coefficients are retained exactly. -/
theorem gammaResolvent_neg_real_derivative_pair_eq_pairedEuler {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    -(Analysis.gammaResolventCoefficients.map
              (fun ab ↦
                (ab.2 : ℝ) *
                  (logDeriv (1 : DirichletCharacter ℂ 1).LFunction
                      (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum -
        (Analysis.gammaResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      ∑' m : ℕ, Analysis.gammaPairedEulerTerm χ m := by
  rw [gammaResolvent_signed_ordinary_eq_euler _, gammaResolvent_signed_ordinary_eq_euler χ]
  simp only [MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), Complex.one_re, neg_mul,
    one_mul, tsum_neg, neg_neg]
  have h := Analysis.gamma_signed_euler_add_paired_eq_total χ
  simp only [neg_mul, tsum_neg] at h
  linarith only [h]

/-- Under the same primitive RH hypotheses, the resolvent zero mass plus
the unretained nonnegative paired tail equals the original signed prefix
budget exactly. Keep the complementary prime-power gain on the left rather
than discard it. Subsequent local conductor absorption can use this stronger identity. -/
theorem gammaResolvent_zeroMass_add_pairedTail_eq_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (B : Finset ℕ) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gammaResolventMajorant ρ.im) +
        Analysis.gammaPairedEulerTail χ B =
      (11783423 / 25000000 : ℝ) * Real.log q +
            (Analysis.gammaResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gammaResolventMangoldtWeight m) -
          2 * (∑ m ∈ B, Analysis.gammaResolventMangoldtWeight m) +
        ∑ m ∈ B, (1 - (χ m).re) * Analysis.gammaResolventMangoldtWeight m := by
  have hz := gammaResolvent_zeroMass_add_pairedEuler_eq hq hRH hp hne hinv
  have hB := Analysis.gammaPairedEuler_prefix_eq_gain_sub_deficit χ B
  dsimp only [Analysis.gammaPairedEulerTail]
  linarith only [hz, hB]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
