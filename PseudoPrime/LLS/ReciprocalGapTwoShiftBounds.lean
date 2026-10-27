/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapPoleLeft
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.CompletedEndpointPoissonComparison

/-! # Independent endpoint shifts with retained positive Euler prefixes -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The first-pole real budget with independent endpoint shift r and retained untwisted
Mangoldt prefix B. It is ((1+r)*log(q)+(1+2r)*(G+M-2*prefix(B,1+r)))/(h*sqrt(x)).
Operations are totalized; later lemmas supply Euler/Gamma caps and prime triviality.
This separates the endpoint comparison parameter from the Mellin pole gap h. -/
noncomputable def reciprocalGapPrefixPoleBudget (h r : ℝ) (q : ℕ) (x M G : ℝ) (B : Finset ℕ) : ℝ :=
  (1 / (h * Real.sqrt x)) *
    ((1 + r) * Real.log q +
      (1 + 2 * r) * (G + M - 2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)))

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data at modulus at least two, h,r,x>0 and prime
triviality through x, the real first-pole residue is bounded by the retained prefix
budget for any finite B below x and certified Euler/Gamma caps M,G at 1+r.
Compare the inverse character's endpoint through Poisson kernels, preserve the positive
Euler prefix, use inverse conjugation and evaluate the residue exactly. -/
theorem reciprocalGap_pole_re_le_positive_prefix {h r x : ℝ} (hh : 0 < h) (hr : 0 < r) (hx : 0 < x)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (B : Finset ℕ)
    (hB : ∀ n ∈ B, (n : ℝ) ≤ x) (htriv : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1) {M G : ℝ}
    (hM : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M)
    (hG : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G) :
    (MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)).re ≤
      reciprocalGapPrefixPoleBudget h r q x M G B := by
  have hpi := DirichletCharacter.isPrimitive_inv hp
  have hni : χ⁻¹⁻¹ ≠ 1 := by simpa only [inv_inv] using hne
  have hc :=
    completedLogDeriv_endpoint_le_positive_prefix hq (hGRH q χ⁻¹ hpi) hpi hinv hni hr B hM hG
  simp only [DirichletCharacter.inv_apply_eq_conj, Complex.conj_re] at hc
  have hpre :=
    AnalyticNumberTheory.Arithmetic.character_positive_mangoldt_prefix_eq_twice χ B
      (fun n ↦ ((n : ℝ) ^ (1 + r))⁻¹) hB htriv
  have he :
    (∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) =
      2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r) := by
    simpa only [div_eq_mul_inv] using hpre
  rw [he] at hc
  have hm :=
    mul_le_mul_of_nonneg_left hc (div_nonneg zero_le_one (mul_pos hh (Real.sqrt_pos.mpr hx)).le)
  rw [reciprocalGap_poleResidue_eq_realAxis hh hp hne hinv hx, ← Complex.natCast_log]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, zero_mul,
    sub_zero]
  unfold reciprocalGapPrefixPoleBudget
  nlinarith only [hm]

/-- For primitive nonprincipal GRH data, h,r>0, x>=1 and prime triviality through x,
the real completed remainder is bounded by the prefix pole budget at shift r,
the signed left budget at gap h and the signed Gamma budget. Euler and Gamma caps
at both shifts remain arbitrary certified inputs. Combine the three real contributions. -/
theorem reciprocalGap_remainder_re_le_two_shift_prefix {h r : ℝ} (hh : 0 < h) (hr : 0 < r) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B : Finset ℕ) (hB : ∀ n ∈ B, (n : ℝ) ≤ x)
    (htriv : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1) {M₁ G₁ M₂ G₂ : ℝ}
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hG₁ : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hG₂ : G₂ ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re) :
    (reciprocalGapCompletedRemainder h hh χ x).re ≤
      reciprocalGapPrefixPoleBudget h r q x M₁ G₁ B + reciprocalGapRealAxisBudget h q x M₂ G₂ +
        reciprocalGapSignedGammaBudget h x := by
  have hx0 := zero_lt_one.trans_le hx
  have hΓ := reciprocalGap_remainder_gamma_re_le_signed_budget hh hx χ
  have hP :=
    reciprocalGap_pole_re_le_positive_prefix hh hr hx0 hq hp hne hinv hGRH B hB htriv hM₁ hG₁
  have hL := reciprocalGap_leftIntegral_re_eq_realAxis hh hp hne hinv hx
  have hV := reciprocalGapRealAxisLeftValue_le_budget hh hx0 hinv hM₂ hG₂
  rw [← hL] at hV
  simp only [Complex.sub_re] at hΓ
  linarith only [hΓ, hP, hV]

/-- For primitive nonprincipal GRH data at modulus at least two, admissible h,c, independent
positive endpoint shift r, x>=1 and two finite index sets below x, the explicit scalar
separation with three certified Euler caps produces a non-one prime witness.
Assume prime triviality, retain untwisted positive prefixes at both comparison points,
and bound Gamma factors uniformly by the two parity endpoints. No input-range certificate
or concrete numerical cutoff is built into this generic criterion. -/
theorem exists_prime_not_one_of_reciprocalGap_two_shift_prefix {h r c : ℝ} (hh : 0 < h) (hr : 0 < r)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B₀ B₁ : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (M₀ M₁ M₂ : ℝ) (hM₀ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤ M₀)
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + reciprocalGapOddGammaUpper (1 / 2 + c) + M₀ -
              2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (reciprocalGapPrefixPoleBudget h r q x M₁ (reciprocalGapOddGammaUpper (1 + r)) B₁ +
            reciprocalGapRealAxisBudget h q x M₂ (reciprocalGapEvenGammaLower (1 + h)) +
            reciprocalGapSignedGammaBudget h x) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  by_contra hn
  have htriv : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hpP hpx
    by_contra hχ
    exact hn ⟨p, hpP, hpx, hχ⟩
  have hR :=
    reciprocalGap_remainder_re_le_two_shift_prefix hh hr hq hGRH hp hne hinv hx B₁ hB₁ htriv hM₁
      (reciprocalGapGamma_re_le_odd (by linarith only [hr]) χ⁻¹) hM₂
      (reciprocalGapEvenGammaLower_le (by linarith only [hh]) χ⁻¹)
  have hpre :=
    AnalyticNumberTheory.Arithmetic.character_positive_mangoldt_prefix_eq_twice χ B₀
      (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹) hB₀ htriv
  have he :
    (∑ n ∈ B₀, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) =
      2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c) := by
    simpa only [div_eq_mul_inv] using hpre
  have hγ := reciprocalGapGamma_re_le_odd (show 0 < (1 / 2 : ℝ) + c by linarith only [hc]) χ
  rw [Complex.ofReal_add] at hγ
  have hc0 : 0 < c := lt_trans (by norm_num only : (0 : ℝ) < 1 / 2) hc
  apply hn
  apply exists_prime_not_one_of_reciprocalGap_separation hh hq hGRH hp hne hinv hc hbound hx B₀
  rw [he]
  have hE :
    (1 / c) *
        (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
            (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
          2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤
      (1 / c) *
        (Real.log q / 2 + reciprocalGapOddGammaUpper (1 / 2 + c) + M₀ -
          2 * ∑ n ∈ B₀, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hγ, hM₀]) (div_nonneg zero_le_one hc0.le)
  exact (add_le_add hE hR).trans_lt hgap

end PseudoPrime.LLS.PaperStatements
