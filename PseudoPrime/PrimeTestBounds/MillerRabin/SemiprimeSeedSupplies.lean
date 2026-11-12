/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeCoreSupplies
public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeFirstSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Weight
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61Weight
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Data
import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Weight

/-! # Semiprime witnesses from numerical count bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a numerical lower bound for the weighted count through 199
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed199 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed199Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (199 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed199Primes
      primeSeed199Weights 199 budget primeSeed199Weight 10 (by norm_num only) primeSeed199_labels.1
      (fun r hr ↦ (primeSeed199_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed199_prime_supply r hr).2) primeSeed199_labels.2.2
      primeSeed199_weight_bounds primeSeed199_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, a numerical lower bound for the weighted count through 281
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed281 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed281Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (281 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed281Primes
      primeSeed281Weights 281 budget primeSeed281Weight 10 (by norm_num only) primeSeed281_labels.1
      (fun r hr ↦ (primeSeed281_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed281_prime_supply r hr).2) primeSeed281_labels.2.2
      primeSeed281_weight_bounds primeSeed281_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, a numerical lower bound for the weighted count through 89
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed89_358 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed89Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed89Primes
      primeSeed89Weights 89 budget primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, a numerical lower bound for the weighted count through 89
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed89_282 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed89Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed89Primes
      primeSeed89Weights 89 budget primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, a numerical lower bound for the weighted count through 89
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed89_197 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed89Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed89Primes
      primeSeed89Weights 89 budget primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, a numerical lower bound for the weighted count through 89
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed89 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed89Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed89Primes
      primeSeed89Weights 89 budget primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, a numerical lower bound for the weighted count through 61
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed61 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed61Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (61 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed61Primes
      primeSeed61Weights 61 budget primeSeed61Weight 10 (by norm_num only) primeSeed61_labels.1
      (fun r hr ↦ (primeSeed61_prime_supply r hr).1) (fun r hr ↦ (primeSeed61_prime_supply r hr).2)
      primeSeed61_labels.2.2 primeSeed61_weight_bounds primeSeed61_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, a numerical lower bound for the weighted count through 43
yields a semiprime witness when the cutoff and local envelope fit. -/
theorem exists_prime_reject_semiprime_seed43 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed43Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (43 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_count_lower hn ho hp hq hpq hprod hGRH primeSeed43Primes
      primeSeed43Weights 43 budget primeSeed43Weight 10 (by norm_num only) primeSeed43_labels.1
      (fun r hr ↦ (primeSeed43_prime_supply r hr).1) (fun r hr ↦ (primeSeed43_prime_supply r hr).2)
      primeSeed43_labels.2.2 primeSeed43_weight_bounds primeSeed43_labels.2.1 C hcount hD hB hlocal

/-- Under GRH, any numerical lower bound for the first weighted supply
can be used to obtain a semiprime witness when the envelope fits. -/
theorem exists_prime_reject_supply58 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget C : ℕ)
    (hcount : C ≤ weightedPrimeCount id primeSeed19Weights budget) {D X : ℝ}
    (hD : D ≤ Real.log (C : ℝ)) (hB : (19 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact exists_prime_reject_first_supply hn ho hp hq hpq hprod hGRH budget C hcount hD hB hlocal

end PseudoPrime.PrimeTestBounds.MillerRabin
