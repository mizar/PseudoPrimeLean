/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed113Supply
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed373
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed1849Count

/-! # Semiprime witnesses from numerical count lower bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a numerical lower bound for the weighted count through 113
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed113 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed113Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (113 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed113Primes
      primeSeed113Weights 113 budget primeSeed113Weight 10 (by norm_num only) primeSeed113_labels.1
      (fun r hr ↦ (primeSeed113_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed113_prime_supply r hr).2) primeSeed113_labels.2.2
      primeSeed113_weight_bounds primeSeed113_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, a numerical lower bound for the weighted count through 373
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed373 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed373Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (373 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed373Primes
      primeSeed373Weights 373 budget primeSeed373Weight 10 (by norm_num only) primeSeed373_labels.1
      (fun r hr ↦ (primeSeed373_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed373_prime_supply r hr).2) primeSeed373_labels.2.2
      primeSeed373_weight_bounds primeSeed373_labels.2.1 C hcount hD hB hlocal

/-- A lower bound for the supply through 373 gives a grouped semiprime witness
through 1849 after adding 209 labels of weight 76. -/
theorem exists_prime_reject_semiprime_seed1849 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (A k C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed373Weights A) {D X : ℝ}
    (hD : D ≤ Real.log ((Nat.choose (209 + k) k * C : ℕ) : ℝ)) (hB : (1849 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max (((A + k * 76 : ℕ) : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed1849Primes
      primeSeed1849Weights 1849 (A + k * 76) primeSeed1849Weight 10 (by norm_num only)
      primeSeed1849_labels.1 (fun r hr ↦ (primeSeed1849_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed1849_prime_supply r hr).2) primeSeed1849_labels.2.2
      primeSeed1849_weight_bounds primeSeed1849_labels.2.1 (Nat.choose (209 + k) k * C)
      (primeSeed1849_group_lower A k C hcount) hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
