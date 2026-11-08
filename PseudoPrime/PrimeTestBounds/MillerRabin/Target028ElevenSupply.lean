/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ElevenCount

/-! # Eleven-prime semiprime witness cells -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

-- The constructor-name linter times out while reducing this finite-family proof.
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 8000000 in
-- Elaborating the eleven-prime weighted family requires additional heartbeats.
/-- Under GRH, a semiprime has a 0.28 witness whenever the given weighted
budget and certified family count fit the linear local cutoff. This transfers
any checked row of the eleven-prime table to a semiprime interval. -/
theorem target028_eleven_supply_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (269 / 25 : ℝ) ≤ Real.log n) (H : ℕ) (hH : H ≤ 66) (D : ℝ)
    (hD : D ≤ Real.log (target028ElevenRow.getD H 0 : ℝ))
    (hbudget : (H : ℝ) / 10 ≤ (52915 / 100000 : ℝ) * Real.log n)
    (hmargin : (1 - 52915 / 100000 : ℝ) * Real.log n ≤ D) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028ElevenPrimes.toFinset
  let w := target028ElevenWeight
  let F := weightedPrimeFamily S w H
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (target028Eleven_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 31 := fun r hr ↦
    (target028Eleven_supply r (List.mem_toFinset.mp hr)).2.1
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    (target028Eleven_supply r (List.mem_toFinset.mp hr)).2.2
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Eleven_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ H := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).2
  have hc : F.card = target028ElevenRow.getD H 0 := target028Eleven_card H hH
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
  have hB : (31 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 31 H w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl hDF hB hlocal hGRH

/-- The eleven-prime product family certifies a semiprime witness on this interval. -/
theorem target028_eleven_cell56 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (269 / 25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 543 / 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_eleven_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 56
      (by decide) (1023 / 200)
  · change (1023 / 200 : ℝ) ≤ Real.log (167 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 167 8 32 (1023 / 200) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The eleven-prime product family certifies a semiprime witness on this interval. -/
theorem target028_eleven_cell57 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (543 / 50 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1101 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_eleven_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 57
      (by decide) (2593 / 500)
  · change (2593 / 500 : ℝ) ≤ Real.log (179 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 179 8 32 (2593 / 500) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The eleven-prime product family certifies a semiprime witness on this interval. -/
theorem target028_eleven_cell58 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1101 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1117 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_eleven_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 58
      (by decide) (5261 / 1000)
  · change (5261 / 1000 : ℝ) ≤ Real.log (193 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 193 8 32 (5261 / 1000) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- The eleven-prime product family certifies a semiprime witness on this interval. -/
theorem target028_eleven_cell59 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1117 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1133 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_eleven_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 59
      (by decide) (667 / 125)
  · change (667 / 125 : ℝ) ≤ Real.log (208 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 208 8 32 (667 / 125) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    norm_num only
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
