/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaSmallScaleLocalBounds

/-! # Parametric actual local budgets and conductor absorption -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: scale x and dyadic allowance delta. Fields certify a positive scale, nonnegative
allowance, actual odd-prime square losses and the two dyadic branches.
Invariant: every positive-power prefix and modulus satisfies these local comparisons.
Role: separate finite-scale analysis from conductor absorption and witness extraction. -/
structure GammaLocalBudgetCertificate (x δ : ℝ) : Prop where
  /-- The scale is at least one, as required by the signed local-series estimates. -/
  scale_ge_one : 1 ≤ x
  /-- The common additive dyadic allowance is nonnegative. -/
  allowance_nonneg : 0 ≤ δ
  /-- Every actual minus-one odd-prime prefix fits its square-part logarithmic budget. -/
  odd_prime_cost :
    ∀ {f : ℕ} (χ : DirichletCharacter ℂ f) (p : ℕ),
      p.Prime →
        3 ≤ p →
        ∀ K : Finset ℕ,
          χ p = -1 →
            gammaActualPrimeLocalCost χ p K x ≤ Real.log p * (2 * (11783423 / 25000000 : ℝ))
  /-- Every minus-one dyadic prefix fits the reserved log-four budget plus delta. -/
  dyadic_minus_cost :
    ∀ {f : ℕ} (χ : DirichletCharacter ℂ f) (K : Finset ℕ),
      χ 2 = -1 → gammaActualPrimeLocalCost χ 2 K x - (11783423 / 25000000 : ℝ) * Real.log 4 ≤ δ
  /-- Every zero-valued dyadic prefix fits delta. -/
  dyadic_zero_cost :
    ∀ {f : ℕ} (χ : DirichletCharacter ℂ f) (K : Finset ℕ),
      χ 2 = 0 → gammaActualPrimeLocalCost χ 2 K x ≤ δ

/-- Input: an odd input, selected minus-one prime factors and a local certificate.
Claim: their actual local losses are bounded by twice the conductor coefficient times log weight.
Proof: sum the certified pointwise comparisons. Role: avoid a fixed analytic scale gate. -/
theorem gamma_actual_square_sum_of_local_certificate {n f : ℕ} (hn : Odd n) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x δ : ℝ} (cert : GammaLocalBudgetCertificate x δ) :
    (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (∑ p ∈ S, Real.log p) * (2 * (11783423 / 25000000 : ℝ)) := by
  have hpoint :
    (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      ∑ p ∈ S, Real.log p * (2 * (11783423 / 25000000 : ℝ)) := by
    apply Finset.sum_le_sum
    intro p hp
    have hprime := Nat.prime_of_mem_primeFactors (hS hp)
    have hpne : p ≠ 2 := fun he ↦ hn.not_two_dvd_nat (he ▸ Nat.dvd_of_mem_primeFactors (hS hp))
    have hp3 : 3 ≤ p := Nat.succ_le_iff.mpr (lt_of_le_of_ne hprime.two_le (Ne.symm hpne))
    exact cert.odd_prime_cost χ p hprime hp3 (K p) (hχ p hp)
  simpa only [Finset.sum_mul] using hpoint

/-- Input: n=f*t^2, positive factors, selected minus-one primes and a local certificate.
Claim: actual square losses fit the conductor gap from f to n.
Proof: combine the certified sum with the exact omitted-prime logarithmic budget.
Role: reserve log four for the odd-conductor dyadic branch. -/
theorem gamma_actual_odd_square_of_local_certificate {n t f : ℕ} (hn : n = f * t ^ 2) (hodd : Odd n)
    (hf : 0 < f) (ht : 0 < t) (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f)
    (hχ : ∀ p ∈ S, χ p = -1) (K : ℕ → Finset ℕ) {x δ : ℝ} (cert : GammaLocalBudgetCertificate x δ) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log n := by
  have hs := gamma_actual_square_sum_of_local_certificate hodd S hS χ hχ K cert
  have hg :=
    gamma_odd_conductor_square_log_budget hn hf ht S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hs, hw]

/-- Input: n=d*t^2 with d dividing f<=4d, selected primes and a local certificate.
Claim: actual square losses fit the conductor gap from f to 4n.
Proof: combine the certified sum with the square-only logarithmic gap.
Role: support the even-conductor branch at arbitrary certified scales. -/
theorem gamma_actual_square_of_local_certificate {n d t f : ℕ} (hn : n = d * t ^ 2) (hodd : Odd n)
    (hd : 0 < d) (ht : 0 < t) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d) (S : Finset ℕ)
    (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (K : ℕ → Finset ℕ) {x δ : ℝ} (cert : GammaLocalBudgetCertificate x δ) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) := by
  have hs := gamma_actual_square_sum_of_local_certificate hodd S hS χ hχ K cert
  have hg :=
    gamma_square_only_prime_log_gap_budget hn hd ht hf hdf hfd S hS
      (fun p hp ↦
        gamma_minus_one_prime_not_dvd_modulus χ (Nat.prime_of_mem_primeFactors (hS hp)) (hχ p hp))
  have hw := mul_le_mul_of_nonneg_left hg (by norm_num only : (0 : ℝ) ≤ 11783423 / 25000000)
  nlinarith only [hs, hw]

/-- Input: a local certificate and local value one or minus one at two.
Claim: the actual dyadic cost minus the log-four budget is at most delta.
Proof: use nonpositivity in the one branch and the certificate otherwise.
Role: combine dyadic losses without introducing an artificial scale threshold. -/
theorem gamma_dyadic_adjusted_of_local_certificate {f : ℕ} (χ : DirichletCharacter ℂ f)
    (K : Finset ℕ) {x δ : ℝ} (cert : GammaLocalBudgetCertificate x δ) (hχ2 : χ 2 = 1 ∨ χ 2 = -1) :
    gammaActualPrimeLocalCost χ 2 K x - (11783423 / 25000000 : ℝ) * Real.log 4 ≤ δ := by
  rcases hχ2 with h2 | h2
  · have hc :=
      gamma_actual_one_prime_cost_nonpos χ Nat.prime_two (by simpa only [Nat.cast_ofNat] using h2) K
        (zero_lt_one.trans_le cert.scale_ge_one)
    have hl : 0 ≤ (11783423 / 25000000 : ℝ) * Real.log 4 :=
      mul_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only))
    linarith only [hc, hl, cert.allowance_nonneg]
  · exact cert.dyadic_minus_cost χ K h2

/-- Input: positive odd-conductor square decomposition, selected primes and a local certificate.
Claim: square and dyadic losses together fit the 4n conductor budget plus delta.
Proof: add the square absorption and adjusted dyadic bound.
Role: provide a reusable odd-conductor comparison for arithmetic bridges. -/
theorem gamma_actual_odd_square_dyadic_of_local_certificate {n t f : ℕ} (hn : n = f * t ^ 2)
    (hodd : Odd n) (hf : 0 < f) (ht : 0 < t) (S : Finset ℕ) (hS : S ⊆ n.primeFactors)
    (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1) (hχ2 : χ 2 = 1 ∨ χ 2 = -1)
    (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x δ : ℝ} (cert : GammaLocalBudgetCertificate x δ) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) +
        gammaActualPrimeLocalCost χ 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + δ := by
  have hs := gamma_actual_odd_square_of_local_certificate hn hodd hf ht S hS χ hχ K cert
  have hd := gamma_dyadic_adjusted_of_local_certificate χ K2 cert hχ2
  rw [Real.log_mul (by norm_num only : (4 : ℝ) ≠ 0) (Nat.cast_pos.mpr hodd.pos).ne']
  linarith only [hs, hd]

/-- Input: a square decomposition, a zero dyadic value and a local certificate.
Claim: square and dyadic losses fit the 4n conductor budget plus delta.
Proof: add square absorption and the certified zero-branch cost.
Role: provide the corresponding even-conductor comparison. -/
theorem gamma_actual_square_dyadic_of_local_certificate {n d t f : ℕ} (hn : n = d * t ^ 2)
    (hodd : Odd n) (hd : 0 < d) (ht : 0 < t) (hf : 0 < f) (hdf : d ∣ f) (hfd : f ≤ 4 * d)
    (S : Finset ℕ) (hS : S ⊆ n.primeFactors) (χ : DirichletCharacter ℂ f) (hχ : ∀ p ∈ S, χ p = -1)
    (hχ2 : χ 2 = 0) (K : ℕ → Finset ℕ) (K2 : Finset ℕ) {x δ : ℝ}
    (cert : GammaLocalBudgetCertificate x δ) :
    (11783423 / 25000000 : ℝ) * Real.log f + (∑ p ∈ S, gammaActualPrimeLocalCost χ p (K p) x) +
        gammaActualPrimeLocalCost χ 2 K2 x ≤
      (11783423 / 25000000 : ℝ) * Real.log (4 * (n : ℝ)) + δ := by
  have hs := gamma_actual_square_of_local_certificate hn hodd hd ht hf hdf hfd S hS χ hχ K cert
  have ht := cert.dyadic_zero_cost χ K2 hχ2
  linarith only [hs, ht]

end PseudoPrime.Analysis
