/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19Count53
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeWitness

/-! # Shared weighted semiprime candidate for the first supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 4000000 in
-- The complete finite multiset family is expanded during elaboration.
/-- Under GRH, the eight-prime supply and its checked table give a semiprime
witness whenever the supplied logarithmic count and local-envelope bounds
fit `X`. Any budget through 53 can reuse the same certificate. -/
theorem exists_prime_reject_first_supply {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ)
    (hbudget : budget ≤ 53) {D X : ℝ} (hD : D ≤ Real.log (primeSeed19Row53.getD budget 0 : ℝ))
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
  have hc : F.card = primeSeed19Row53.getD budget 0 := primeSeed19_family53 budget hbudget
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 19 budget w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl (hc ▸ hD) hB hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
