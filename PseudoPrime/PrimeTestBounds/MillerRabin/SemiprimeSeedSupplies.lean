/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeCoreSupplies
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed199Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeLower
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed281Count
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count197
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count282
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count358
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeTable
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed61
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19Count58

/-! # Semiprime witnesses from certified prime supplies -/

@[expose] public section

set_option maxRecDepth 32768

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked weighted-count lower bound through 199 yields semiprime
witnesses when its logarithmic count and local envelope meet the target. -/
theorem exists_prime_reject_semiprime_seed199 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 450)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed199Row16.getD budget 0 : ℝ)) (hB : (199 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_lower hn ho hp hq hpq hprod hGRH primeSeed199Primes
      primeSeed199Weights 199 budget primeSeed199Weight 10 (by norm_num only) primeSeed199_labels.1
      (fun r hr ↦ (primeSeed199_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed199_prime_supply r hr).2) primeSeed199_labels.2.2
      primeSeed199_weight_bounds primeSeed199_labels.2.1 primeSeed199Row16
      (primeSeed199_count_lower budget hN) hD hB hlocal

/-- A checked weighted-count lower bound through 281 yields semiprime
witnesses when its logarithmic count and local envelope meet the target. -/
theorem exists_prime_reject_semiprime_seed281 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 550)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed281Row14.getD budget 0 : ℝ)) (hB : (281 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_lower hn ho hp hq hpq hprod hGRH primeSeed281Primes
      primeSeed281Weights 281 budget primeSeed281Weight 10 (by norm_num only) primeSeed281_labels.1
      (fun r hr ↦ (primeSeed281_prime_supply r hr).1)
      (fun r hr ↦ (primeSeed281_prime_supply r hr).2) primeSeed281_labels.2.2
      primeSeed281_weight_bounds primeSeed281_labels.2.1 primeSeed281Row14
      (primeSeed281_count_lower budget hN) hD hB hlocal

/-- The checked supply through 89 yields semiprime witnesses for budgets
through 358 whenever the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed89_358 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 358)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed89Row358.getD budget 0 : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH primeSeed89Primes
      primeSeed89Weights 89 budget 358 primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 hN primeSeed89Row358
      primeSeed89Tail358 primeSeed89_checked358 hD hB hlocal

/-- The checked supply through 89 yields semiprime witnesses for budgets
through 282 whenever the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed89_282 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 282)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed89Row282.getD budget 0 : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH primeSeed89Primes
      primeSeed89Weights 89 budget 282 primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 hN primeSeed89Row282
      primeSeed89Tail282 primeSeed89_checked282 hD hB hlocal

/-- The checked supply through 89 yields semiprime witnesses for budgets
through 197 whenever the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed89_197 {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 197)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed89Row197.getD budget 0 : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH primeSeed89Primes
      primeSeed89Weights 89 budget 197 primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 hN primeSeed89Row197
      primeSeed89Tail197 primeSeed89_checked197 hD hB hlocal

/-- Under GRH, the checked supply through 89 transfers any certified budget
through 110 to a rejecting semiprime witness when the local envelope fits. -/
theorem exists_prime_reject_semiprime_seed89 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 110)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed89Row.getD budget 0 : ℝ)) (hB : (89 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH primeSeed89Primes
      primeSeed89Weights 89 budget 110 primeSeed89Weight 10 (by norm_num only) primeSeed89_labels.1
      (fun r hr ↦ (primeSeed89_prime_supply r hr).1) (fun r hr ↦ (primeSeed89_prime_supply r hr).2)
      primeSeed89_labels.2.2 primeSeed89_weight_bounds primeSeed89_labels.2.1 hN primeSeed89Row
      primeSeed89Tail primeSeed89_checked hD hB hlocal

/-- Under GRH, the checked prime supply through 61 yields a semiprime witness
at every budget through 96 when the count and local-envelope conditions hold. -/
theorem exists_prime_reject_semiprime_seed61 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 96)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed61Row.getD budget 0 : ℝ)) (hB : (61 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH primeSeed61Primes
      primeSeed61Weights 61 budget 96 primeSeed61Weight 10 (by norm_num only) primeSeed61_labels.1
      (fun r hr ↦ (primeSeed61_prime_supply r hr).1) (fun r hr ↦ (primeSeed61_prime_supply r hr).2)
      primeSeed61_labels.2.2 primeSeed61_weight_bounds primeSeed61_labels.2.1 hN primeSeed61Row
      primeSeed61Tail primeSeed61_checked hD hB hlocal

/-- Under GRH, the checked supply through 43 yields a distinct-semiprime
witness at any budget through 77 when the count and local envelope fit the
target. The generic table theorem transfers the count directly to the kernel. -/
theorem exists_prime_reject_semiprime_seed43 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ) (hN : budget ≤ 77)
    {D X : ℝ} (hD : D ≤ Real.log (primeSeed43Row.getD budget 0 : ℝ)) (hB : (43 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  exact
    exists_prime_reject_semiprime_table hn ho hp hq hpq hprod hGRH primeSeed43Primes
      primeSeed43Weights 43 budget 77 primeSeed43Weight 10 (by norm_num only) primeSeed43_labels.1
      (fun r hr ↦ (primeSeed43_prime_supply r hr).1) (fun r hr ↦ (primeSeed43_prime_supply r hr).2)
      primeSeed43_labels.2.2 primeSeed43_weight_bounds primeSeed43_labels.2.1 hN primeSeed43Row
      primeSeed43Tail primeSeed43_checked hD hB hlocal

set_option maxHeartbeats 4000000 in
-- The finite family is expanded during elaboration.
/-- Under GRH, the extended weighted table supplies a semiprime witness for
any budget through 58 when the logarithmic and local bounds hold. -/
theorem exists_prime_reject_supply58 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ)
    (hbudget : budget ≤ 58) {D X : ℝ} (hD : D ≤ Real.log (primeSeed19Row58.getD budget 0 : ℝ))
    (hB : (19 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := primeSeed19Primes.toFinset
  let w := primeSeed19Weight
  let F := weightedPrimeFamily S w budget
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (prime_seed19_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
    (prime_seed19_prime_supply r (List.mem_toFinset.mp hr)).2
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    prime_seed19_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ primeSeed19_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w budget hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ budget := fun T hT ↦
    ((mem_weightedPrimeFamily S w budget hwpos T).mp hT).2
  have hc : F.card = primeSeed19Row58.getD budget 0 := primeSeed19_family58 budget hbudget
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 19 budget w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl (hc ▸ hD) hB hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
