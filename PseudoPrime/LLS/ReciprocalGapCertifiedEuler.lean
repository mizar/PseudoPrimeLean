/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.Euler16CertifiedBounds
public import PseudoPrime.LLS.ReciprocalGapTwoShiftBounds

/-! # Certified scalar Euler caps in a fixed two-shift witness criterion -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For every character and height, the certified Euler cap bounds the logarithmic
 derivative norm throughout the indicated right half-plane. Use absolute convergence
 and the unconditional sixteen-term Euler certificate; no GRH is needed. -/
theorem norm_logDeriv_le_six_fifths_certified {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : (6 / 5 : ℝ) ≤ σ) (t : ℝ) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤ (4481 / 1000 : ℝ) := by
  have hn :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ
      ((by norm_num only : (1 : ℝ) < 6 / 5).trans_le hσ) t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_le_six_fifths_certified hσ)

/-- For every character and height, the certified Euler cap bounds the logarithmic
 derivative norm throughout the indicated right half-plane. Use absolute convergence
 and the unconditional sixteen-term Euler certificate; no GRH is needed. -/
theorem norm_logDeriv_le_hundredTwentySeven_hundredths_certified {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {σ : ℝ} (hσ : (127 / 100 : ℝ) ≤ σ) (t : ℝ) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤ (1597 / 500 : ℝ) := by
  have hn :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ
      ((by norm_num only : (1 : ℝ) < 127 / 100).trans_le hσ) t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_le_hundredTwentySeven_hundredths_certified hσ)

/-- For every character and height, the certified Euler cap bounds the logarithmic
 derivative norm throughout the indicated right half-plane. Use absolute convergence
 and the unconditional sixteen-term Euler certificate; no GRH is needed. -/
theorem norm_logDeriv_le_seventeen_tenths_certified {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {σ : ℝ} (hσ : (17 / 10 : ℝ) ≤ σ) (t : ℝ) :
    ‖logDeriv χ.LFunction ((σ : ℂ) + t * Complex.I)‖ ≤ (97 / 100 : ℝ) := by
  have hn :=
    norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum χ
      ((by norm_num only : (1 : ℝ) < 17 / 10).trans_le hσ) t
  simp only [neg_div, norm_neg] at hn
  exact hn.trans (Arithmetic.tsum_vonMangoldt_le_seventeen_tenths_certified hσ)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction

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
