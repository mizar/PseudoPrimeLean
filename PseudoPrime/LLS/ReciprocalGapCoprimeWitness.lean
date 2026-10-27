/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterCoprimeTriviality
public import PseudoPrime.LLS.ReciprocalGapCoprimeArithmetic

/-! # Reciprocal-gap bounds retaining coprime prime-power prefixes -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The first-pole budget with one full positive Mangoldt prefix and one additional
coprime prefix. Inputs h,r,q,x,M,G,B are totalized. The bound theorem requires
positive h,r,x and prime triviality only on primes coprime to q. -/
noncomputable def reciprocalGapCoprimePoleBudget (h r : ℝ) (q : ℕ) (x M G : ℝ) (B : Finset ℕ) : ℝ :=
  (1 / (h * Real.sqrt x)) *
    ((1 + r) * Real.log q +
      (1 + 2 * r) *
        (G + M -
          AnalyticNumberTheory.Arithmetic.coprimePositiveMangoldtPrefix q B
            (fun n ↦ ((n : ℝ) ^ (1 + r))⁻¹)))

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data, positive h,r,x and coprime prime triviality,
the first-pole residue is bounded by the coprime retained-prefix budget.
Use horizontal Poisson comparison and the exact full-plus-coprime prefix identity.
Ramified primes retain their zero character values. -/
theorem reciprocalGap_pole_re_le_coprime_prefix {h r x : ℝ} (hh : 0 < h) (hr : 0 < r) (hx : 0 < x)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1)
    (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (B : Finset ℕ)
    (hB : ∀ n ∈ B, (n : ℝ) ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p q → χ p = 1) {M G : ℝ}
    (hM : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M)
    (hG : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G) :
    (MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)).re ≤
      reciprocalGapCoprimePoleBudget h r q x M G B := by
  have hpi := DirichletCharacter.isPrimitive_inv hp
  have hni : χ⁻¹⁻¹ ≠ 1 := by simpa only [inv_inv] using hne
  have hc :=
    completedLogDeriv_endpoint_le_positive_prefix hq (hGRH q χ⁻¹ hpi) hpi hinv hni hr B hM hG
  simp only [DirichletCharacter.inv_apply_eq_conj, Complex.conj_re] at hc
  have hpre :=
    AnalyticNumberTheory.Arithmetic.character_positive_mangoldt_prefix_eq_coprime χ B
      (fun n ↦ ((n : ℝ) ^ (1 + r))⁻¹) hB hsmall
  have he :
    (∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) =
      AnalyticNumberTheory.Arithmetic.coprimePositiveMangoldtPrefix q B
        (fun n ↦ ((n : ℝ) ^ (1 + r))⁻¹) := by
    simpa only [div_eq_mul_inv] using hpre
  rw [he] at hc
  have hm :=
    mul_le_mul_of_nonneg_left hc (div_nonneg zero_le_one (mul_pos hh (Real.sqrt_pos.mpr hx)).le)
  rw [reciprocalGap_poleResidue_eq_realAxis hh hp hne hinv hx, ← Complex.natCast_log]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, zero_mul,
    sub_zero]
  unfold reciprocalGapCoprimePoleBudget
  nlinarith only [hm]

/-- For primitive nonprincipal GRH data, h,r>0,x>=1 and coprime prime triviality,
the completed remainder is bounded by the coprime pole, signed left and Gamma budgets.
Combine the three real contributions using arbitrary certified Euler and Gamma inputs. -/
theorem reciprocalGap_remainder_re_le_coprime_prefix {h r : ℝ} (hh : 0 < h) (hr : 0 < r) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B : Finset ℕ) (hB : ∀ n ∈ B, (n : ℝ) ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p q → χ p = 1) {M₁ G₁ M₂ G₂ : ℝ}
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hG₁ : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hG₂ : G₂ ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re) :
    (reciprocalGapCompletedRemainder h hh χ x).re ≤
      reciprocalGapCoprimePoleBudget h r q x M₁ G₁ B + reciprocalGapRealAxisBudget h q x M₂ G₂ +
        reciprocalGapSignedGammaBudget h x := by
  have hx0 := zero_lt_one.trans_le hx
  have hΓ := reciprocalGap_remainder_gamma_re_le_signed_budget hh hx χ
  have hP :=
    reciprocalGap_pole_re_le_coprime_prefix hh hr hx0 hq hp hne hinv hGRH B hB hsmall hM₁ hG₁
  have hL := reciprocalGap_leftIntegral_re_eq_realAxis hh hp hne hinv hx
  have hV := reciprocalGapRealAxisLeftValue_le_budget hh hx0 hinv hM₂ hG₂
  rw [← hL] at hV
  simp only [Complex.sub_re] at hΓ
  linarith only [hΓ, hP, hV]

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal GRH data and admissible positive kernel parameters,
separation against a selected unit-supported principal sum gives a coprime prime
where the character is not one. Retain the exact full-plus-coprime positive prefixes
under witness nonexistence and compare the selected character lower sum.
The six Euler and Gamma inputs remain arbitrary certified scalar bounds. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_separation {h r c : ℝ} (hh : 0 < h)
    (hr : 0 < r) {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n q) (M₀ G₀ M₁ G₁ M₂ G₂ : ℝ)
    (hM₀ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤ M₀)
    (hG₀ : (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re ≤ G₀)
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hG₁ : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hG₂ : G₂ ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + G₀ + M₀ -
              AnalyticNumberTheory.Arithmetic.coprimePositiveMangoldtPrefix q B₀
                (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹)) +
          (reciprocalGapCoprimePoleBudget h r q x M₁ G₁ B₁ +
            reciprocalGapRealAxisBudget h q x M₂ G₂ +
            reciprocalGapSignedGammaBudget h x) <
        ∑ n ∈ B, reciprocalGapPrincipalWeight h x n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p q ∧ χ p ≠ 1 := by
  by_contra hn
  have hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p q → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have hR :=
    reciprocalGap_remainder_re_le_coprime_prefix hh hr hq hGRH hp hne hinv hx B₁ hB₁ hsmall hM₁ hG₁
      hM₂ hG₂
  have hpre :=
    AnalyticNumberTheory.Arithmetic.character_positive_mangoldt_prefix_eq_coprime χ B₀
      (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹) hB₀ hsmall
  have he :
    (∑ n ∈ B₀, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) =
      AnalyticNumberTheory.Arithmetic.coprimePositiveMangoldtPrefix q B₀
        (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹) := by
    simpa only [div_eq_mul_inv] using hpre
  have hU := reciprocalGapCharacterSum_re_le_positive_prefix hh hq hGRH hp hne hinv hc hbound hx B₀
  rw [he] at hU
  have hZ :=
    mul_le_mul_of_nonneg_left
      (show
        Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
              (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
            AnalyticNumberTheory.Arithmetic.coprimePositiveMangoldtPrefix q B₀
              (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹) ≤
          Real.log q / 2 + G₀ + M₀ -
            AnalyticNumberTheory.Arithmetic.coprimePositiveMangoldtPrefix q B₀
              (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹)
        by linarith only [hG₀, hM₀])
      (div_nonneg zero_le_one (lt_trans (by norm_num only : (0 : ℝ) < 1 / 2) hc).le)
  have hupper := hU.trans (add_le_add hZ hR)
  have hlower :=
    sum_reciprocalGapPrincipalWeight_le_of_coprime_trivial hh.le (zero_lt_one.trans_le hx) χ hsmall
      B hB hcop
  exact (not_lt_of_ge (hlower.trans hupper)) hgap

/-- The fixed h=7/10,r=1/5,c=77/100 separation budget with certified rational
Euler and Gamma inputs, retaining one full and one coprime prefix at each comparison.
The modulus, radius and finite supports remain variable. All operations are totalized. -/
noncomputable def reciprocalGapCoprimeRationalSeparation (q : ℕ) (x : ℝ) (B₀ B₁ : Finset ℕ) : ℝ :=
  (100 / 77) *
      (Real.log q / 2 + (-(759 / 1000)) + 1597 / 500 -
        AnalyticNumberTheory.Arithmetic.coprimePositiveMangoldtPrefix q B₀
          (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹)) +
    (reciprocalGapCoprimePoleBudget (7 / 10) (1 / 5) q x (4481 / 1000) (-(784 / 1000)) B₁ +
      reciprocalGapRealAxisBudget (7 / 10) q x (97 / 100) (-(1001 / 1000)) +
      reciprocalGapSignedGammaBudget (7 / 10) x)

/-- For primitive nonprincipal GRH data, q>=2,x>=1 and supports below x,
the fixed rational separation against a selected unit-supported sum produces a
coprime prime where the character is not one. Supply all Euler and Gamma bounds
from the kernel-certified scalar lemmas. The conclusion excludes character value zero. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_rational_separation {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ)
    (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ n ∈ B, Nat.Coprime n q)
    (hgap :
      reciprocalGapCoprimeRationalSeparation q x B₀ B₁ <
        ∑ n ∈ B, reciprocalGapPrincipalWeight (7 / 10) x n) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p q ∧ χ p ≠ 1 := by
  refine
    exists_prime_coprime_not_one_of_reciprocalGap_separation (h := 7 / 10) (r := 1 / 5) (c :=
      77 / 100) (by norm_num only) (by norm_num only) hq hGRH hp hne hinv (by norm_num only)
      (by norm_num only) hx B₀ B₁ B hB₀ hB₁ hB hcop (1597 / 500) (-(759 / 1000)) (4481 / 1000)
      (-(784 / 1000)) (97 / 100) (-(1001 / 1000)) ?_ ?_ ?_ ?_ ?_ ?_ ?_
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
  · norm_num only [reciprocalGapCoprimeRationalSeparation] at hgap ⊢
    exact hgap

/-- For primitive nonprincipal GRH data and a selected unit-supported finite lower
certificate, rational separation produces a coprime non-one prime witness below x.
Compare certified lower endpoints with the selected weights, then apply the fixed-gap
coprime witness theorem. The finite supports remain independently selectable. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_coprime_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ)
    (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ n ∈ B, Nat.Coprime n q) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapCoprimeRationalSeparation q x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p q ∧ χ p ≠ 1 := by
  apply
    exists_prime_coprime_not_one_of_reciprocalGap_rational_separation hq hGRH hp hne hinv hx B₀ B₁ B
      hB₀ hB₁ hB hcop
  exact
    hgap.trans_le
      (sum_lower_le_reciprocalGap_selectedWeight (by norm_num only : (0 : ℝ) ≤ 7 / 10) B lo u hlo hu
        hu1)

/-- For a primitive nonprincipal quadratic character under GRH, the selected coprime
lower certificate produces a prime p<=x with chi(p)=-1. Quadraticity identifies the
inverse with the character and excludes zero on the coprime witness.
The prime two is allowed; this is not yet an odd-prime Jacobi bound for arbitrary input n. -/
theorem exists_prime_neg_one_of_reciprocalGap_coprime_lower {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n q) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapCoprimeRationalSeparation q x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p q ∧ χ p = -1 := by
  have hinv : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_coprime_lower hq hGRH hp hne hinv hx B₀ B₁ B hB₀
      hB₁ hB hcop lo u hlo hu hu1 hgap
  exact
    ⟨p, hprime, hpx, hpc,
      AnalyticNumberTheory.Arithmetic.quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad
        hpc hv⟩

end PseudoPrime.LLS.PaperStatements
