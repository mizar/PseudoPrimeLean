/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030FirstSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeWitness

/-! # First semiprime interval for the 0.30 target -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 4000000 in
-- The finite family and its checked table require additional elaboration steps.
/-- Under GRH, a product of distinct odd primes with logarithm in `[8, 8.37]`
has a rejecting prime within the coefficient-0.30 cutoff. The eight-prime
weighted count is 54, and the local or counting alternative covers the cell. -/
theorem exists_prime_reject_03_first_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 837 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target030FirstPrimes.toFinset
  let w := target030FirstWeight
  let F := weightedPrimeFamily S w 43
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (target030_first_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
    (target030_first_prime_supply r (List.mem_toFinset.mp hr)).2
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    target030_first_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target030First_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w 43 hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ 43 := fun T hT ↦
    ((mem_weightedPrimeFamily S w 43 hwpos T).mp hT).2
  have hc : F.card = 54 := target030First_family_card
  have hlog54 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 54 6 32 (3988984 / 1000000) 4 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog54
  have hD : (498623 / 125000 : ℝ) ≤ Real.log (F.card : ℝ) := by
    rw [hc]
    exact hlog54
  have hs : max (43 / 10 : ℝ) (Real.log n - 498623 / 125000) ≤ 43815 / 10000 := by
    apply max_le
    · norm_num only
    · linarith only [hU]
  have hs0 : 0 ≤ max (43 / 10 : ℝ) (Real.log n - 498623 / 125000) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hs0 hs
  have htarget : (43815 / 10000 : ℝ) ^ 2 ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  have hlocal :
    localFullEnvelope (max (43 / 10 : ℝ) (Real.log n - 498623 / 125000)) ≤
      (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
    exact (min_le_left _ _).trans ((min_le_left _ _).trans (by nlinarith only [hsquare, htarget]))
  have hB : (19 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 19 43 w 10
      (by norm_num only) hsub hprime hbound hw hcost (by norm_num only) hD hB hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
