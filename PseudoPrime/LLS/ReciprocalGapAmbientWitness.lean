/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapScalarPrefixBounds
public import PseudoPrime.LLS.ReciprocalGapAmbientArithmetic

/-! # Ambient exclusions and odd negative prime witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The certified scalar separation budget with ambient positive prefixes at 127/100
and 6/5, plus the exact extra-nonunit principal-weight cost. The character level q and
exclusion modulus N are separate inputs; later theorems assume q divides N.
This retains the cost of excluding two and primes lost during primitive normalization. -/
noncomputable def reciprocalGapAmbientRationalSeparation (q N : ℕ) (x : ℝ) (B₀ B₁ : Finset ℕ) : ℝ :=
  reciprocalGapScalarRationalSeparation q x
      (AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix q N B₀
        (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹))
      (AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix q N B₁
        (fun n ↦ ((n : ℝ) ^ (6 / 5 : ℝ))⁻¹)) +
    reciprocalGapAdditionalNonunitWeight (7 / 10) q N x

/-- For primitive nonprincipal GRH data, q>=2 dividing N, radius x>=1 and finite
supports, ambient separation against a selected N-coprime lower certificate yields
an N-coprime non-one prime witness below x. Under witness nonexistence, bound positive
prefixes from below and subtract precisely the extra nonunit cost from the main sum. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_ambient_lower {q N : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hqN : q ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ)
    (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapAmbientRationalSeparation q N x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have hK₀ :=
    AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix_le_character hqN χ B₀
      (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹) hB₀
      (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsmall
  have hK₁ :=
    AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix_le_character hqN χ B₁
      (fun n ↦ ((n : ℝ) ^ (6 / 5 : ℝ))⁻¹) hB₁
      (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsmall
  simp only [← div_eq_mul_inv] at hK₀ hK₁
  have hU := reciprocalGapCharacterSum_re_le_scalar_rational hq hGRH hp hne hinv hx B₀ B₁ hK₀ hK₁
  have hL :=
    selected_reciprocalGap_lower_sub_loss_le_character hqN (by norm_num only : (0 : ℝ) ≤ 7 / 10)
      (zero_lt_one.trans_le hx) χ hsmall B hB hcop lo u hlo hu hu1
  unfold reciprocalGapAmbientRationalSeparation at hgap
  linarith only [hL, hU, hgap]

/-- For a primitive nonprincipal quadratic character under GRH, assume q divides N
and two divides N. Ambient separation against the selected lower certificate yields
an odd N-coprime prime p<=x with chi(p)=-1. Coprimality excludes two and zero character
values. The exact extra-exclusion budget is retained in the separation premise. -/
theorem exists_odd_prime_neg_one_of_reciprocalGap_ambient_lower {q N : ℕ} [NeZero q] (hq : 2 ≤ q)
    (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ)
    (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapAmbientRationalSeparation q N x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hinv : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_ambient_lower hq hqN hGRH hp hne hinv hx B₀ B₁ B
      hB₀ hB₁ hB hcop lo u hlo hu hu1 hgap
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      AnalyticNumberTheory.Arithmetic.quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad
        (hpc.of_dvd_right hqN) hv⟩

end PseudoPrime.LLS.PaperStatements
