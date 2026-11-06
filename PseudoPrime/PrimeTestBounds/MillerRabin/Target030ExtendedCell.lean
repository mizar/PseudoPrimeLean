/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030ExtendedCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030FirstSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeWitness

/-! # Shared weighted semiprime candidate for the first supply -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational radius covering both local-scale alternatives bounds the local
envelope by the 0.30 target throughout a closed logarithmic interval. Squaring
uses nonnegativity of the scale and its lower endpoint. -/
theorem local_envelope_le_03_interval {n : ℕ} {lo hi A D R : ℝ} (hlo : 0 ≤ lo)
    (hL : lo ≤ Real.log n) (hU : Real.log n ≤ hi) (hA0 : 0 ≤ A) (hA : A ≤ R) (hRD : hi - D ≤ R)
    (hr : R ^ 2 ≤ (3 / 10 : ℝ) * lo ^ 2) :
    localFullEnvelope (max A (Real.log n - D)) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
  have hs : max A (Real.log n - D) ≤ R := max_le hA (by linarith only [hU, hRD])
  have hs0 : 0 ≤ max A (Real.log n - D) := hA0.trans (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hs0 hs
  have hLsq := mul_self_le_mul_self hlo hL
  exact (min_le_left _ _).trans ((min_le_left _ _).trans (by nlinarith only [hsquare, hLsq, hr]))

set_option maxHeartbeats 4000000 in
-- The complete finite multiset family is expanded during elaboration.
/-- Under GRH, the eight-prime supply and its checked table give a semiprime
witness whenever the supplied logarithmic count and local-envelope bounds
fit `X`. Any budget through 53 can reuse the same certificate. -/
theorem exists_prime_reject_first_supply {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (budget : ℕ)
    (hbudget : budget ≤ 53) {D X : ℝ} (hD : D ≤ Real.log (target030ExtendedRow.getD budget 0 : ℝ))
    (hB : (19 : ℝ) ≤ X)
    (hlocal : localFullEnvelope (max ((budget : ℝ) / 10) (Real.log n - D)) ≤ X) :
    ∃ r : ℕ, r.Prime ∧ (r : ℝ) ≤ X ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target030FirstPrimes.toFinset
  let w := target030FirstWeight
  let F := weightedPrimeFamily S w budget
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (target030_first_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
    (target030_first_prime_supply r (List.mem_toFinset.mp hr)).2
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    target030_first_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target030First_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w budget hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ budget := fun T hT ↦
    ((mem_weightedPrimeFamily S w budget hwpos T).mp hT).2
  have hc : F.card = target030ExtendedRow.getD budget 0 :=
    target030Extended_family_card budget hbudget
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 19 budget w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl (hc ▸ hD) hB hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
