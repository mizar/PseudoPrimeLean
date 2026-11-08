/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SharpCount

/-! # Sharpened nine-prime semiprime interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 4000000 in
-- Elaborating the finite weighted family requires additional heartbeats.
/-- Under GRH, a semiprime of logarithmic scale between 10.16 and 10.2 has
 a 0.28 rejecting prime. The sharpened weighted supply contains 122 products. -/
theorem target028_semiprime_sharp53 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (254 / 25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 51 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028NinePrimes.toFinset
  let w := target028SharpWeight
  let F := weightedPrimeFamily S w 53
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (target028Sharp_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 23 := fun r hr ↦
    (target028Sharp_supply r (List.mem_toFinset.mp hr)).2.1
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    (target028Sharp_supply r (List.mem_toFinset.mp hr)).2.2
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Sharp_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w 53 hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ 53 := fun T hT ↦
    ((mem_weightedPrimeFamily S w 53 hwpos T).mp hT).2
  have hc : F.card = 122 := target028Sharp_card
  have hD : (4804 / 1000 : ℝ) ≤ Real.log (122 : ℝ) := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 122 7 32 (4804 / 1000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  have hDF : (4804 / 1000 : ℝ) ≤ Real.log (F.card : ℝ) := by
    rw [hc]; exact hD
  have hs : max (53 / 10 : ℝ) (Real.log n - 4804 / 1000) ≤ (52915 / 100000 : ℝ) * Real.log n := by
    apply max_le <;> linarith only [hL, hU]
  have hs0 : 0 ≤ max (53 / 10 : ℝ) (Real.log n - 4804 / 1000) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hs0 hs
  have hlocal :
    localFullEnvelope (max (53 / 10 : ℝ) (Real.log n - 4804 / 1000)) ≤
      (7 / 25 : ℝ) * (Real.log n) ^ 2 := by
    exact
      (min_le_left _ _).trans
        ((min_le_left _ _).trans (by nlinarith only [hsquare, sq_nonneg (Real.log n)]))
  have hB : (23 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 23 53 w 10
      (by norm_num only) hsub hprime hbound hw hcost (by norm_num only) hDF hB hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
