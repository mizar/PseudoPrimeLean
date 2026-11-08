/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SevenSupply
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareLog10

/-! # Eight-prime weighted semiprime witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 4000000 in
-- Elaborating the finite weighted family requires additional heartbeats.
/-- Under GRH, a semiprime has a 0.28 witness whenever the given weighted
budget and certified family count fit the linear local cutoff. This transfers
any checked row of the eight-prime table to a semiprime interval. -/
theorem target028_eight_supply_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (83 / 10 : ℝ) ≤ Real.log n)
    (H : ℕ) (hH : H ≤ 58) (D : ℝ) (hD : D ≤ Real.log (target030SquareRow.getD H 0 : ℝ))
    (hbudget : (H : ℝ) / 10 ≤ (52915 / 100000 : ℝ) * Real.log n)
    (hmargin : (1 - 52915 / 100000 : ℝ) * Real.log n ≤ D) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target030FirstPrimes.toFinset
  let w := target030FirstWeight
  let F := weightedPrimeFamily S w H
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (target030_first_prime_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
    (target030_first_prime_supply r (List.mem_toFinset.mp hr)).2
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    target030_first_weight_bounds r (List.mem_toFinset.mp hr)
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target030First_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ H := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).2
  have hc : F.card = target030SquareRow.getD H 0 := target030Square_family_card H hH
  have hDF : D ≤ Real.log (F.card : ℝ) := by
    rw [hc]; exact hD
  have hs : max ((H : ℝ) / 10) (Real.log n - D) ≤ (52915 / 100000 : ℝ) * Real.log n := by
    apply max_le hbudget
    linarith only [hmargin]
  have hs0 : 0 ≤ max ((H : ℝ) / 10) (Real.log n - D) :=
    le_trans (div_nonneg (Nat.cast_nonneg H) (by norm_num only)) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hs0 hs
  have hlocal :
    localFullEnvelope (max ((H : ℝ) / 10) (Real.log n - D)) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by
    exact
      (min_le_left _ _).trans
        ((min_le_left _ _).trans (by nlinarith only [hsquare, sq_nonneg (Real.log n)]))
  have hB : (19 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 19 H w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl hDF hB hlocal hGRH

/-- Under GRH, the eight-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_eight_cell46 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (883 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 179 / 20) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_eight_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 46
      (by decide) (4219 / 1000)
  · change (4219 / 1000 : ℝ) ≤ Real.log (68 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 68 7 32 (4219 / 1000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the eight-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_eight_cell47 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (179 / 20 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 91 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_eight_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 47
      (by decide) (429 / 100)
  · change (429 / 100 : ℝ) ≤ Real.log (73 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 73 7 32 (429 / 100) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the eight-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_eight_cell48 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (91 / 10 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 233 / 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_eight_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 48
      (by decide) (2197 / 500)
  · change (2197 / 500 : ℝ) ≤ Real.log (81 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 81 7 32 (2197 / 500) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the eight-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_eight_cell49 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (233 / 25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 943 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_eight_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 49
      (by decide) (2221 / 500)
  · change (2221 / 500 : ℝ) ≤ Real.log (85 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 85 7 32 (2221 / 500) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
