/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapCoupledScalarBounds
public import PseudoPrime.LLS.ReciprocalGapAmbientArithmetic

/-! # Variable-gap coprime and odd negative witnesses with coupled conductor terms -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Variable-gap coupled scalar budget with ambient positive prefixes and the exact
additional-nonunit principal-weight cost. Inputs h,r,c,kappa, six Euler/Gamma endpoints,
q,N,x and two finite supports are totalized. Witness theorems supply the analytic and
support hypotheses. This keeps conductor cancellation compatible with prime exclusions. -/
noncomputable def reciprocalGapCoupledAmbientSeparation (h r c κ : ℝ) (q N : ℕ)
    (x M₀ G₀ M₁ G₁ M₂ G₂ : ℝ) (B₀ B₁ : Finset ℕ) : ℝ :=
  reciprocalGapCoupledScalarSeparation h r c κ q x M₀ G₀ M₁ G₁ M₂ G₂
      (AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix q N B₀
        (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹))
      (AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix q N B₁
        (fun n ↦ ((n : ℝ) ^ (1 + r))⁻¹)) +
    reciprocalGapAdditionalNonunitWeight h q N x

/-- For primitive nonprincipal GRH data at q>=2 dividing N, x>=1, positive h,r,
the zero-comparison constraint and r<=kappa*h, ambient coupled separation against
a finite selected lower certificate produces an N-coprime non-one prime below x.
Use witness nonexistence to bound both positive prefixes and the principal sum.
The Euler/Gamma endpoints remain explicit, rather than fixed numerical constants. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_coupled_ambient {h r c κ : ℝ} (hh : 0 < h)
    (hr : 0 < r) {q N : ℕ} [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2)
    (hκ : r ≤ κ * h) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x)
    (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N)
    (M₀ G₀ M₁ G₁ M₂ G₂ : ℝ)
    (hM₀ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤ M₀)
    (hG₀ : (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re ≤ G₀)
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hG₁ : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hG₂ : G₂ ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapCoupledAmbientSeparation h r c κ q N x M₀ G₀ M₁ G₁ M₂ G₂ B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have hK₀ :=
    AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix_le_character hqN χ B₀
      (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹) hB₀
      (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsmall
  have hK₁ :=
    AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix_le_character hqN χ B₁
      (fun n ↦ ((n : ℝ) ^ (1 + r))⁻¹) hB₁
      (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsmall
  simp only [← div_eq_mul_inv] at hK₀ hK₁
  have hU :=
    reciprocalGapCharacterSum_re_le_coupled_scalar hh hr hq hGRH hp hne hinv hc hbound hκ hx B₀ B₁
      M₀ G₀ M₁ G₁ M₂ G₂ _ _ hM₀ hG₀ hM₁ hG₁ hM₂ hG₂ hK₀ hK₁
  have hL :=
    selected_reciprocalGap_lower_sub_loss_le_character hqN hh.le (zero_lt_one.trans_le hx) χ hsmall
      B hB hcop lo u hlo hu hu1
  unfold reciprocalGapCoupledAmbientSeparation at hgap
  linarith only [hL, hU, hgap]

/-- Under the same variable-gap analytic and finite-certificate conditions, a
primitive nonprincipal quadratic character and 2 dividing N yield an odd N-coprime
prime below x with value minus one. Obtain the coprime non-one witness, rule out two,
and use the quadratic value classification. Even parity is not assumed. -/
theorem exists_odd_prime_neg_one_of_reciprocalGap_coupled_ambient {h r c κ : ℝ} (hh : 0 < h)
    (hr : 0 < r) {q N : ℕ} [NeZero q] (hq : 2 ≤ q) (hqN : q ∣ N) (hN2 : 2 ∣ N)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) (hc : (1 / 2 : ℝ) < c)
    (hbound : c ^ 2 ≤ 1 / 4 + h / 2) (hκ : r ≤ κ * h) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ B : Finset ℕ)
    (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x) (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ n ∈ B, Nat.Coprime n N) (M₀ G₀ M₁ G₁ M₂ G₂ : ℝ)
    (hM₀ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤ M₀)
    (hG₀ : (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re ≤ G₀)
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hG₁ : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hG₂ : G₂ ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapCoupledAmbientSeparation h r c κ q N x M₀ G₀ M₁ G₁ M₂ G₂ B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hi : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_coupled_ambient hh hr hq hqN hGRH hp hne hi hc
      hbound hκ hx B₀ B₁ B hB₀ hB₁ hB hcop M₀ G₀ M₁ G₁ M₂ G₂ hM₀ hG₀ hM₁ hG₁ hM₂ hG₂ lo u hlo hu hu1
      hgap
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      AnalyticNumberTheory.Arithmetic.quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad
        (hpc.of_dvd_right hqN) hv⟩

end PseudoPrime.LLS.PaperStatements
