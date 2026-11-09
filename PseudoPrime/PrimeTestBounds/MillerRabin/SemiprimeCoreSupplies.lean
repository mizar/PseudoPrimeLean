/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113Table
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount

/-! # Semiprime witnesses from certified prime supplies -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The checked supply through 113 yields semiprime witnesses for budgets
through 358 whenever the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed113 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 358)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed113Row6.getD budget 0 : ℝ)) (hB : (113 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH primeSeed113Primes
      primeSeed113Weights 113 budget 358 primeSeed113Weight 10 (by norm_num only)
      primeSeed113_labels.1 (fun r hr ↦ (primeSeed113_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed113_prime_supply r hr).2) primeSeed113_labels.2.2
      primeSeed113_weight_bounds primeSeed113_labels.2.1 hN primeSeed113Row6
      ([primeSeed113Row5, primeSeed113Row4, primeSeed113Row3, primeSeed113Row2, primeSeed113Row1,
          primeSeed89Row358] ++
        primeSeed89Tail358)
      primeSeed113_checked hD hB hlocal

/-- A checked weighted-count lower bound through 373 yields semiprime
witnesses when its logarithmic count and local envelope meet the target. -/
theorem exists_prime_reject_semiprime_seed373 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 500)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed373Row14.getD budget 0 : ℝ)) (hB : (373 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_lower hn ho hp hq hpq hprod hGRH primeSeed373Primes
      primeSeed373Weights 373 budget primeSeed373Weight 10 (by norm_num only) primeSeed373_labels.1
      (fun r hr ↦ (primeSeed373_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed373_prime_supply r hr).2) primeSeed373_labels.2.2
      primeSeed373_weight_bounds primeSeed373_labels.2.1 primeSeed373Row14
      (primeSeed373_count_lower budget hN) hD hB hlocal

/-- The grouped count through 1849 gives a semiprime witness when its
logarithmic lower count and local envelope fit the requested bound. -/
theorem exists_prime_reject_semiprime_seed1849 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (A k : ℕ) (hA : A ≤ 500)
    {D X : ℝ} (hD : D ≤ Real.log ((Nat.choose (209 + k) k * primeSeed373Row14.getD A 0 : ℕ) : ℝ))
    (hB : (1849 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max (((A + k * 76 : ℕ) : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed1849Primes
      primeSeed1849Weights 1849 (A + k * 76) primeSeed1849Weight 10 (by norm_num only)
      primeSeed1849_labels.1 (fun r hr ↦ (primeSeed1849_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed1849_prime_supply r hr).2) primeSeed1849_labels.2.2
      primeSeed1849_weight_bounds primeSeed1849_labels.2.1
      (Nat.choose (209 + k) k * primeSeed373Row14.getD A 0) (primeSeed1849_group_lower A k hA) hD hB
      hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
