/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.Euler16CertifiedBounds
public import PseudoPrime.LLS.ReciprocalGapTwoShiftBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ReciprocalGapCertifiedEuler

/-! # Certified scalar Euler caps in a fixed two-shift witness criterion -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The two-shift separation budget at h=7/10,r=1/5,c=77/100, with certified Euler
caps 3.194,4.481,0.970. The modulus, radius and two finite supports remain variable.
This removes Euler-cap premises while retaining the Gamma values and positive prefixes. -/
noncomputable def reciprocalGapCertifiedSeparation (q : ℕ) (x : ℝ) (B₀ B₁ : Finset ℕ) : ℝ :=
  (100 / 77) *
      (Real.log q / 2 + reciprocalGapOddGammaUpper (127 / 100) + 1597 / 500 -
        2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (127 / 100 : ℝ)) +
    (reciprocalGapPrefixPoleBudget (7 / 10) (1 / 5) q x (4481 / 1000)
        (reciprocalGapOddGammaUpper (6 / 5)) B₁ +
      reciprocalGapRealAxisBudget (7 / 10) q x (97 / 100) (reciprocalGapEvenGammaLower (17 / 10)) +
      reciprocalGapSignedGammaBudget (7 / 10) x)

/-- For primitive nonprincipal GRH data at q>=2, x>=1 and finite supports below x,
the certified scalar budget being below the principal sum produces a non-one prime witness.
Apply the two-shift criterion with three kernel-certified Euler caps and rational parameters.
Values zero are allowed; a negative-value witness needs additional common-factor control. -/
theorem exists_prime_not_one_of_reciprocalGap_certified_separation {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ : Finset ℕ)
    (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (hgap :
      reciprocalGapCertifiedSeparation q x B₀ B₁ <
        (reciprocalGapCharacterSum (7 / 10) (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  refine
    exists_prime_not_one_of_reciprocalGap_two_shift_prefix (h := 7 / 10) (r := 1 / 5) (c :=
      77 / 100) (by norm_num only) (by norm_num only) hq hGRH hp hne hinv (by norm_num only)
      (by norm_num only) hx B₀ B₁ hB₀ hB₁ (1597 / 500) (4481 / 1000) (97 / 100) ?_ ?_ ?_ ?_
  · exact
      AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_hundredTwentySeven_hundredths_certified
        (by norm_num only)
  · exact
      AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_six_fifths_certified (by norm_num only)
  · exact
      AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_seventeen_tenths_certified
        (by norm_num only)
  · norm_num only [reciprocalGapCertifiedSeparation] at hgap ⊢
    exact hgap

end PseudoPrime.LLS.PaperStatements
