/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianSignedEulerIdentity
public import PseudoPrime.Analysis.GaussianPairedEulerMass

/-! # Gaussian zero mass retaining nonnegative paired Euler tails -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Under individual RH and primitive nonprincipal conductor data, the
actual resolvent zero mass plus the nonnegative paired Euler mass equals
the exact conductor and Gamma contributions plus the untwisted common mass.
The real-axis derivative cancellation is preserved as an equality. -/
theorem gaussianResolvent_zeroMass_add_pairedEuler_eq {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gaussianResolventMajorant ρ.im) +
        (∑' m : ℕ, Analysis.gaussianPairedEulerTerm χ m) =
      (20115621 / 50000000 : ℝ) * Real.log q +
        (Analysis.gaussianResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
        ∑' m : ℕ, Analysis.gaussianResolventMangoldtWeight m := by
  rw [gaussianResolvent_zeroMass_eq_signed_euler hq hRH hp hne hinv, add_assoc,
    Analysis.gaussian_signed_euler_add_paired_eq_total χ]

/-- The signed finite-node pair of real logarithmic derivatives equals
the nonnegative common paired Euler mass. Combine all signed coefficients
before using positivity of H; negative coefficients are retained exactly. -/
theorem gaussianResolvent_neg_real_derivative_pair_eq_pairedEuler {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) :
    -(Analysis.gaussianResolventCoefficients.map
              (fun ab ↦
                (ab.2 : ℝ) *
                  (logDeriv (1 : DirichletCharacter ℂ 1).LFunction
                      (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum -
        (Analysis.gaussianResolventCoefficients.map
            (fun ab ↦
              (ab.2 : ℝ) * (logDeriv χ.LFunction (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum =
      ∑' m : ℕ, Analysis.gaussianPairedEulerTerm χ m := by
  rw [gaussianResolvent_signed_ordinary_eq_euler _, gaussianResolvent_signed_ordinary_eq_euler χ]
  simp only [MulChar.one_apply (isUnit_of_subsingleton (_ : ZMod 1)), Complex.one_re, neg_mul,
    one_mul, tsum_neg, neg_neg]
  have h := Analysis.gaussian_signed_euler_add_paired_eq_total χ
  simp only [neg_mul, tsum_neg] at h
  linarith only [h]

/-- Under the same primitive RH hypotheses, the resolvent zero mass plus
the unretained nonnegative paired tail equals the original signed prefix
budget exactly. Keep the complementary prime-power gain on the left rather
than discard it. Subsequent local conductor absorption can use this stronger identity. -/
theorem gaussianResolvent_zeroMass_add_pairedTail_eq_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (B : Finset ℕ) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            Analysis.gaussianResolventMajorant ρ.im) +
        Analysis.gaussianPairedEulerTail χ B =
      (20115621 / 50000000 : ℝ) * Real.log q +
            (Analysis.gaussianResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gaussianResolventMangoldtWeight m) -
          2 * (∑ m ∈ B, Analysis.gaussianResolventMangoldtWeight m) +
        ∑ m ∈ B, (1 - (χ m).re) * Analysis.gaussianResolventMangoldtWeight m := by
  have hz := gaussianResolvent_zeroMass_add_pairedEuler_eq hq hRH hp hne hinv
  have hB := Analysis.gaussianPairedEuler_prefix_eq_gain_sub_deficit χ B
  dsimp only [Analysis.gaussianPairedEulerTail]
  linarith only [hz, hB]

/-- Under primitive nonprincipal individual RH, the actual Gaussian norm mass
is bounded by the signed resolvent mass. This comparison retains the exact
Euler budget instead of substituting the coarse additive constant. -/
theorem gaussian_zeroMass_le_signed_resolvent {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) :
    (∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) ≤
      ∑' ρ : ℂ,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          Analysis.gaussianResolventMajorant ρ.im := by
  have hK :=
    Analysis.norm_gaussianGammaFunction_le_gaussianResolvent_of_grid
      Analysis.gaussianResolvent_grid_lower
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
  have hn (ρ : ℂ) : (0 : ℝ) ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) := by
    exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ
  have hb (ρ : ℂ) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖ ≤
      (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
        Analysis.gaussianResolventMajorant ρ.im := by
    by_cases hD : MeromorphicOn.divisor χ.completedLFunction Set.univ ρ = 0
    · simp only [hD, Int.cast_zero, zero_mul, le_refl]
    · have hr :=
        completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
          (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
      have he : ρ - 1 / 2 = Complex.I * (ρ.im : ℂ) := by
        calc
          ρ - 1 / 2 = (ρ.re : ℂ) + (ρ.im : ℂ) * Complex.I - 1 / 2 := by rw [Complex.re_add_im]
          _ = _ := by
            rw [hr]
            norm_num only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat]
            ring
      exact mul_le_mul_of_nonneg_left (by simpa only [he] using hK ρ.im) (hn ρ)
  have hg := summable_completed_gaussianResolvent_terms hq hRH hp hne hinv
  have hsum := hg.of_nonneg_of_le (fun ρ ↦ mul_nonneg (hn ρ) (norm_nonneg _)) hb
  exact hsum.tsum_le_tsum hb hg

/-- The actual Gaussian norm mass plus the nonnegative unretained Euler tail
obeys the exact signed prefix budget. No absolute-coefficient error allowance
is introduced; later quantitative bounds may retain every positive prime-power gain. -/
theorem gaussian_zeroMass_add_pairedTail_le_prefix {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : GRH.DirichletRiemannHypothesis χ) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (B : Finset ℕ) :
    (∑' ρ : ℂ,
          (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
            ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖) +
        Analysis.gaussianPairedEulerTail χ B ≤
      (20115621 / 50000000 : ℝ) * Real.log q +
            (Analysis.gaussianResolventCoefficients.map
                (fun ab ↦
                  (ab.2 : ℝ) * (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + (ab.1 : ℝ)) : ℂ)).re)).sum +
            (∑' m : ℕ, Analysis.gaussianResolventMangoldtWeight m) -
          2 * (∑ m ∈ B, Analysis.gaussianResolventMangoldtWeight m) +
        ∑ m ∈ B, (1 - (χ m).re) * Analysis.gaussianResolventMangoldtWeight m := by
  have h := gaussian_zeroMass_le_signed_resolvent hq hRH hp hne hinv
  have he := gaussianResolvent_zeroMass_add_pairedTail_eq_prefix hq hRH hp hne hinv B
  linarith only [h, he]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
