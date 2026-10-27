/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CommonFactorSeries

/-! # Signed common-factor prime-power reindexing -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- A function vanishing outside prime powers and on level units has support
in the injective parametrization by level primes and positive exponents.
Prime-power uniqueness supplies the support needed for signed infinite reindexing. -/
theorem commonFactorPrimePowerIndex_support_of_vanishing (f : ℕ → ℝ) {q : ℕ} (hq : q ≠ 0)
    (hprime : ∀ n, ¬IsPrimePow n → f n = 0) (hunit : ∀ n, Nat.Coprime n q → f n = 0) :
    Function.support f ⊆ Set.range (commonFactorPrimePowerIndex q) := by
  intro n hn
  have hnp : IsPrimePow n := of_not_not (fun h ↦ hn (hprime n h))
  have hnc : ¬Nat.Coprime n q := fun h ↦ hn (hunit n h)
  obtain ⟨p, k, hp, hk, he⟩ := (isPrimePow_nat_iff n).mp hnp
  obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  have hd : p ∣ q := of_not_not (fun h ↦ hnc (he ▸ (hp.coprime_iff_not_dvd.mpr h).pow_left k))
  refine ⟨(⟨p, Nat.mem_primeFactors.mpr ⟨hp, hd, hq⟩⟩, j), ?_⟩
  exact (congrArg (fun r : ℕ ↦ p ^ r) hj).symm.trans he

/-- For a summable real function supported on nonunit prime powers at nonzero level,
its whole series equals the finite level-prime sum of positive-power series.
Use support reindexing and absolute summability for the product-index exchange.
This transfers signed Mangoldt corrections without taking termwise absolute values. -/
theorem tsum_common_factor_eq_sum_prime_powers (f : ℕ → ℝ) {q : ℕ} (hq : q ≠ 0) (hf : Summable f)
    (hprime : ∀ n, ¬IsPrimePow n → f n = 0) (hunit : ∀ n, Nat.Coprime n q → f n = 0) :
    (∑' n : ℕ, f n) = ∑ p ∈ q.primeFactors, ∑' k : ℕ, f (p ^ (k + 1)) := by
  have hi := commonFactorPrimePowerIndex_injective q
  have hs := commonFactorPrimePowerIndex_support_of_vanishing f hq hprime hunit
  have hcomp := hf.comp_injective hi
  rw [← hi.tsum_eq hs]
  change Summable (fun z ↦ f (commonFactorPrimePowerIndex q z)) at hcomp
  rw [hcomp.tsum_prod, tsum_fintype]
  exact Finset.sum_coe_sort q.primeFactors (fun p ↦ ∑' k : ℕ, f (p ^ (k + 1)))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
