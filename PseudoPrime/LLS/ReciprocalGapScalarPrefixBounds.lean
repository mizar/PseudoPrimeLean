/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapCoprimeWitness

/-! # Scalar positive-prefix inputs for reciprocal-gap analytic bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The first-pole real budget with arbitrary retained positive-prefix lower bound K.
The Euler and Gamma inputs are M,G, with positive h,r,x required by later comparisons.
This separates analytic comparison from how arithmetic prefix savings are certified. -/
noncomputable def reciprocalGapScalarPoleBudget (h r : ℝ) (q : ℕ) (x M G K : ℝ) : ℝ :=
  (1 / (h * Real.sqrt x)) * ((1 + r) * Real.log q + (1 + 2 * r) * (G + M - K))

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data and h,r,x>0, a lower bound K on any
finite positive character prefix bounds the pole by the scalar-prefix budget.
Compare at 1+r, weaken by the prefix lower certificate and evaluate the pole exactly.
No prime-triviality or support-cutoff assumptions are needed for this analytic lemma. -/
theorem reciprocalGap_pole_re_le_scalar_prefix {h r x : ℝ} (hh : 0 < h) (hr : 0 < r) (hx : 0 < x)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (B : Finset ℕ)
    {M G K : ℝ} (hM : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M)
    (hG : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G)
    (hK : K ≤ ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) :
    (MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)).re ≤
      reciprocalGapScalarPoleBudget h r q x M G K := by
  have hpi := DirichletCharacter.isPrimitive_inv hp
  have hni : χ⁻¹⁻¹ ≠ 1 := by simpa only [inv_inv] using hne
  have hc :=
    completedLogDeriv_endpoint_le_positive_prefix hq (hGRH q χ⁻¹ hpi) hpi hinv hni hr B hM hG
  simp only [DirichletCharacter.inv_apply_eq_conj, Complex.conj_re] at hc
  have hsub :=
    mul_le_mul_of_nonneg_left (sub_le_sub_left hK (G + M))
      (show 0 ≤ 1 + 2 * r by linarith only [hr])
  have hcap := hc.trans (add_le_add (le_refl _) hsub)
  have hm :=
    mul_le_mul_of_nonneg_left hcap (div_nonneg zero_le_one (mul_pos hh (Real.sqrt_pos.mpr hx)).le)
  rw [reciprocalGap_poleResidue_eq_realAxis hh hp hne hinv hx, ← Complex.natCast_log]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, zero_mul,
    sub_zero]
  unfold reciprocalGapScalarPoleBudget
  nlinarith only [hm]

/-- For primitive nonprincipal GRH data and h,r>0,x>=1, a certified lower scalar
prefix bounds the full completed remainder by the scalar pole, signed left and Gamma
budgets. Combine their three real contributions without prime-triviality assumptions. -/
theorem reciprocalGap_remainder_re_le_scalar_prefix {h r : ℝ} (hh : 0 < h) (hr : 0 < r) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B : Finset ℕ) {M₁ G₁ M₂ G₂ K : ℝ}
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hG₁ : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hG₂ : G₂ ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re)
    (hK : K ≤ ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) :
    (reciprocalGapCompletedRemainder h hh χ x).re ≤
      reciprocalGapScalarPoleBudget h r q x M₁ G₁ K + reciprocalGapRealAxisBudget h q x M₂ G₂ +
        reciprocalGapSignedGammaBudget h x := by
  have hx0 := zero_lt_one.trans_le hx
  have hΓ := reciprocalGap_remainder_gamma_re_le_signed_budget hh hx χ
  have hP := reciprocalGap_pole_re_le_scalar_prefix hh hr hx0 hq hp hne hinv hGRH B hM₁ hG₁ hK
  have hL := reciprocalGap_leftIntegral_re_eq_realAxis hh hp hne hinv hx
  have hV := reciprocalGapRealAxisLeftValue_le_budget hh hx0 hinv hM₂ hG₂
  rw [← hL] at hV
  simp only [Complex.sub_re] at hΓ
  linarith only [hΓ, hP, hV]

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data and admissible h,r,c,x, two arbitrary lower
bounds for positive character prefixes and certified Euler/Gamma inputs bound the real
character sum. Weaken each positive prefix with the correct subtraction sign. -/
theorem reciprocalGapCharacterSum_re_le_scalar_prefix {h r c : ℝ} (hh : 0 < h) (hr : 0 < r) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B₀ B₁ : Finset ℕ) (M₀ G₀ M₁ G₁ M₂ G₂ K₀ K₁ : ℝ)
    (hM₀ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤ M₀)
    (hG₀ : (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re ≤ G₀)
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hG₁ : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hG₂ : G₂ ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re)
    (hK₀ : K₀ ≤ ∑ n ∈ B₀, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c))
    (hK₁ : K₁ ≤ ∑ n ∈ B₁, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) :
    (reciprocalGapCharacterSum h χ x).re ≤
      (1 / c) * (Real.log q / 2 + G₀ + M₀ - K₀) +
        (reciprocalGapScalarPoleBudget h r q x M₁ G₁ K₁ + reciprocalGapRealAxisBudget h q x M₂ G₂ +
          reciprocalGapSignedGammaBudget h x) := by
  have hR :=
    reciprocalGap_remainder_re_le_scalar_prefix hh hr hq hGRH hp hne hinv hx B₁ hM₁ hG₁ hM₂ hG₂ hK₁
  have hU := reciprocalGapCharacterSum_re_le_positive_prefix hh hq hGRH hp hne hinv hc hbound hx B₀
  have hE := add_le_add (add_le_add (le_refl (Real.log q / 2)) hG₀) hM₀
  have hZ :=
    mul_le_mul_of_nonneg_left (sub_le_sub hE hK₀)
      (div_nonneg zero_le_one (lt_trans (by norm_num only : (0 : ℝ) < 1 / 2) hc).le)
  exact hU.trans (add_le_add hZ hR)

/-- The fixed h=7/10,r=1/5,c=77/100 budget with certified rational Euler/Gamma
inputs and two arbitrary positive-prefix lower scalars K0,K1. The modulus and radius vary.
This isolates all finite arithmetic savings from the analytic upper-bound expression. -/
noncomputable def reciprocalGapScalarRationalSeparation (q : ℕ) (x K₀ K₁ : ℝ) : ℝ :=
  (100 / 77) * (Real.log q / 2 + (-(759 / 1000)) + 1597 / 500 - K₀) +
    (reciprocalGapScalarPoleBudget (7 / 10) (1 / 5) q x (4481 / 1000) (-(784 / 1000)) K₁ +
      reciprocalGapRealAxisBudget (7 / 10) q x (97 / 100) (-(1001 / 1000)) +
      reciprocalGapSignedGammaBudget (7 / 10) x)

/-- For primitive nonprincipal GRH data at q>=2,x>=1, any two certified lower scalars
for the indicated positive prefixes bound the real character sum by the fixed rational
separation budget. Supply all six Euler/Gamma endpoints internally from proved certificates. -/
theorem reciprocalGapCharacterSum_re_le_scalar_rational {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x K₀ K₁ : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ : Finset ℕ)
    (hK₀ :
      K₀ ≤ ∑ n ∈ B₀, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (127 / 100 : ℝ))
    (hK₁ :
      K₁ ≤ ∑ n ∈ B₁, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (6 / 5 : ℝ)) :
    (reciprocalGapCharacterSum (7 / 10) χ x).re ≤
      reciprocalGapScalarRationalSeparation q x K₀ K₁ := by
  have H :
    (reciprocalGapCharacterSum (7 / 10) χ x).re ≤
      (1 / (77 / 100 : ℝ)) * (Real.log q / 2 + (-(759 / 1000)) + 1597 / 500 - K₀) +
        (reciprocalGapScalarPoleBudget (7 / 10) (1 / 5) q x (4481 / 1000) (-(784 / 1000)) K₁ +
          reciprocalGapRealAxisBudget (7 / 10) q x (97 / 100) (-(1001 / 1000)) +
          reciprocalGapSignedGammaBudget (7 / 10) x) := by
    refine
      reciprocalGapCharacterSum_re_le_scalar_prefix (h := 7 / 10) (r := 1 / 5) (c := 77 / 100)
        (by norm_num only) (by norm_num only) hq hGRH hp hne hinv (by norm_num only)
        (by norm_num only) hx B₀ B₁ (1597 / 500) (-(759 / 1000)) (4481 / 1000) (-(784 / 1000))
        (97 / 100) (-(1001 / 1000)) K₀ K₁ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_hundredTwentySeven_hundredths_certified
          (by norm_num only)
    · have hg :=
        (reciprocalGapGamma_re_le_odd (by norm_num only : (0 : ℝ) < 127 / 100) χ).trans
          reciprocalGapOddGammaUpper_at_127_div_100
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hg ⊢
      exact hg
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_six_fifths_certified (by norm_num only)
    · have hg :=
        (reciprocalGapGamma_re_le_odd (by norm_num only : (0 : ℝ) < 6 / 5) χ⁻¹).trans
          reciprocalGapOddGammaUpper_at_six_fifths
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hg ⊢
      exact hg
    · exact
        AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_seventeen_tenths_certified
          (by norm_num only)
    · have hg :=
        reciprocalGapEvenGammaLower_at_seventeen_tenths.trans
          (reciprocalGapEvenGammaLower_le (by norm_num only : (0 : ℝ) < 17 / 10) χ⁻¹)
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one] at hg ⊢
      exact hg
    · norm_num only
      exact hK₀
    · norm_num only
      exact hK₁
  norm_num only [reciprocalGapScalarRationalSeparation] at H ⊢
  exact H

end PseudoPrime.LLS.PaperStatements
