/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleEulerTriple
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GaussianPrincipalEulerBudget

/-! Joint Gaussian Euler and zero-mass comparison for three characters. -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The character-weighted common Gaussian Euler series is absolutely summable. -/
theorem gaussian_character_euler_summable {q : ℕ} (χ : DirichletCharacter ℂ q) :
    Summable (fun n : ℕ ↦ (χ n).re * Analysis.gaussianResolventMangoldtWeight n) := by
  have h :=
    Analysis.summable_gaussian_signed_euler (fun n ↦ (χ n).re)
      (fun n ↦ (Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))
  simpa only [neg_mul, neg_neg] using h.neg

/-- Three character values satisfying the common sign condition retain a fourfold Euler prefix. -/
theorem gaussian_three_euler_prefix {p q r : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (s : Finset ℕ)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp :
      ∀ n ∈ s,
        Analysis.gaussianResolventMangoldtWeight n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    4 * (∑ n ∈ s, Analysis.gaussianResolventMangoldtWeight n) ≤
      (∑' n : ℕ, Analysis.gaussianResolventMangoldtWeight n) +
        (∑' n : ℕ, (a n).re * Analysis.gaussianResolventMangoldtWeight n) +
        (∑' n : ℕ, (b n).re * Analysis.gaussianResolventMangoldtWeight n) +
        (∑' n : ℕ, (c n).re * Analysis.gaussianResolventMangoldtWeight n) := by
  have hsA := gaussian_character_euler_summable a
  have hsB := gaussian_character_euler_summable b
  have hsC := gaussian_character_euler_summable c
  have h :=
    (Analysis.summable_gaussianResolventMangoldtWeight.add ((hsA.add hsB).add hsC)).sum_le_tsum s
      (fun n _ ↦ by
        have hw := Analysis.gaussianResolventMangoldtWeight_nonneg n
        have hsign := mul_le_mul_of_nonneg_right (ht n) hw
        nlinarith only [hsign])
  have he :
    (∑ n ∈ s,
        (Analysis.gaussianResolventMangoldtWeight n +
          ((a n).re * Analysis.gaussianResolventMangoldtWeight n +
            (b n).re * Analysis.gaussianResolventMangoldtWeight n +
            (c n).re * Analysis.gaussianResolventMangoldtWeight n))) =
      4 * (∑ n ∈ s, Analysis.gaussianResolventMangoldtWeight n) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    by_cases hz : Analysis.gaussianResolventMangoldtWeight n = 0
    · simp only [hz, add_zero, mul_zero]
    · have hsign :=
        congrArg (fun z : ℝ ↦ z * Analysis.gaussianResolventMangoldtWeight n) (hp n hn hz)
      nlinarith only [hsign]
  rw [he,
    Summable.tsum_add Analysis.summable_gaussianResolventMangoldtWeight ((hsA.add hsB).add hsC),
    Summable.tsum_add (hsA.add hsB) hsC, Summable.tsum_add hsA hsB] at h
  linarith only [h]

/-- The actual Gaussian kernel norm summed over completed zeros with multiplicity. -/
noncomputable def gaussianActualZeroMass {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : ℝ :=
  ∑' ρ : ℂ,
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      ‖Analysis.gaussianGammaFunction (ρ - 1 / 2)‖

/-- Under GRH, three even characters share one universal Euler cost and a fourfold prefix gain. -/
theorem gaussian_three_mass_even {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) (hP : 2 ≤ p) (hQ : 2 ≤ q) (hR : 2 ≤ r)
    (hpA : a.IsPrimitive) (hpB : b.IsPrimitive) (hpC : c.IsPrimitive) (hnA : a ≠ 1) (hnB : b ≠ 1)
    (hnC : c ≠ 1) (hiA : a⁻¹ ≠ 1) (hiB : b⁻¹ ≠ 1) (hiC : c⁻¹ ≠ 1) (heA : a.Even) (heB : b.Even)
    (heC : c.Even) (s : Finset ℕ) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re)
    (hp :
      ∀ n ∈ s,
        Analysis.gaussianResolventMangoldtWeight n ≠ 0 → (a n).re + (b n).re + (c n).re = 3) :
    gaussianActualZeroMass a + gaussianActualZeroMass b + gaussianActualZeroMass c <
      (20115621 / 50000000 : ℝ) * (Real.log p + Real.log q + Real.log r) + 683 / 50 - 108 / 25 -
        4 * ∑ n ∈ s, Analysis.gaussianResolventMangoldtWeight n := by
  have hma :=
    AnalyticNumberTheory.DirichletLFunction.gaussianNormMass_le_resolvent_RH hP (hGRH p a hpA) hpA
      hnA hiA
  have hmb :=
    AnalyticNumberTheory.DirichletLFunction.gaussianNormMass_le_resolvent_RH hQ (hGRH q b hpB) hpB
      hnB hiB
  have hmc :=
    AnalyticNumberTheory.DirichletLFunction.gaussianNormMass_le_resolvent_RH hR (hGRH r c hpC) hpC
      hnC hiC
  have hea :=
    AnalyticNumberTheory.DirichletLFunction.gaussianMass_eq_signedEuler_RH hP (hGRH p a hpA) hpA hnA
      hiA
  have heb :=
    AnalyticNumberTheory.DirichletLFunction.gaussianMass_eq_signedEuler_RH hQ (hGRH q b hpB) hpB hnB
      hiB
  have hec :=
    AnalyticNumberTheory.DirichletLFunction.gaussianMass_eq_signedEuler_RH hR (hGRH r c hpC) hpC hnC
      hiC
  have hga := AnalyticNumberTheory.DirichletLFunction.gaussianResolvent_gammaFactor_0_le heA
  have hgb := AnalyticNumberTheory.DirichletLFunction.gaussianResolvent_gammaFactor_0_le heB
  have hgc := AnalyticNumberTheory.DirichletLFunction.gaussianResolvent_gammaFactor_0_le heC
  have he :=
    AnalyticNumberTheory.DirichletLFunction.gaussianEuler_lt_principalBudget_RH hGRH.riemann
  have hpref := gaussian_three_euler_prefix a b c s ht hp
  simp only [neg_mul, tsum_neg] at hea heb hec
  dsimp only [gaussianActualZeroMass]
  linarith only [hma, hmb, hmc, hea, heb, hec, hga, hgb, hgc, he, hpref]

end PseudoPrime.PrimeTestBounds.MillerRabin
