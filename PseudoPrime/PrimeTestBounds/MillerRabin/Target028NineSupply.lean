/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028NineCount

/-! # Nine-prime weighted semiprime witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 4000000 in
-- Elaborating the finite weighted family requires additional heartbeats.
/-- Under GRH, a semiprime has a 0.28 witness whenever the given weighted
budget and certified family count fit the linear local cutoff. This transfers
any checked row of the nine-prime table to a semiprime interval. -/
theorem target028_nine_supply_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (47 / 5 : ℝ) ≤ Real.log n)
    (H : ℕ) (hH : H ≤ 58) (D : ℝ) (hD : D ≤ Real.log (target028NineRow.getD H 0 : ℝ))
    (hbudget : (H : ℝ) / 10 ≤ (52915 / 100000 : ℝ) * Real.log n)
    (hmargin : (1 - 52915 / 100000 : ℝ) * Real.log n ≤ D) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028NinePrimes.toFinset
  let w := target028NineWeight
  let F := weightedPrimeFamily S w H
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (target028Nine_supply r (List.mem_toFinset.mp hr)).1
  have hbound : ∀ r ∈ S, r ≤ 23 := fun r hr ↦ (target028Nine_supply r (List.mem_toFinset.mp hr)).2.1
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    (target028Nine_supply r (List.mem_toFinset.mp hr)).2.2
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Nine_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ H := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).2
  have hc : F.card = target028NineRow.getD H 0 := target028Nine_family_card H hH
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
  have hB : (23 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 23 H w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl hDF hB hlocal hGRH

/-- Under GRH, the nine-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_nine_cell49 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (47 / 5 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 191 / 20) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_nine_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 49
      (by decide) (4499 / 1000)
  · change (4499 / 1000 : ℝ) ≤ Real.log (90 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 90 7 32 (4499 / 1000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the nine-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_nine_cell50 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (191 / 20 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 971 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_nine_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 50
      (by decide) (2287 / 500)
  · change (2287 / 500 : ℝ) ≤ Real.log (97 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 97 7 32 (2287 / 500) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the nine-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_nine_cell51 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (971 / 100 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 247 / 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_nine_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 51
      (by decide) (4653 / 1000)
  · change (4653 / 1000 : ℝ) ≤ Real.log (105 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 105 7 32 (4653 / 1000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the nine-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_nine_cell52 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (247 / 25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 201 / 20) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_nine_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 52
      (by decide) (592 / 125)
  · change (592 / 125 : ℝ) ≤ Real.log (114 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 114 7 32 (592 / 125) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the nine-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_nine_cell53 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (201 / 20 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 254 / 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_nine_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 53
      (by decide) (4787 / 1000)
  · change (4787 / 1000 : ℝ) ≤ Real.log (120 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 120 7 32 (4787 / 1000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- A square divisor of an input with logarithm at most 10.2 has base at most
171. A rational logarithm certificate bounds the input by 171 squared. -/
theorem target028_square_factor_le171 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (51 / 5 : ℝ)) : p ≤ 171 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 29241 15 32 (51 / 5) 11 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 29241 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (29241 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 29241)).mp
        hlog
  have hpsq : p ^ 2 ≤ 29241 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- Budget 58/10 lies below the logarithm of the square of every integer
greater than 23. A rational logarithm bound for 24 gives a strict margin. -/
theorem target028_square_budget58 {p : ℕ} (hp : 23 < p) :
    (58 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h24 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 24 5 32 3 4 = true from by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at h24
  have hp24 : 24 ≤ p := Nat.succ_le_of_lt hp
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 24) (Nat.cast_le.mpr hp24)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h24, hl]

set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- An odd input divisible by a prime square has a 0.28 rejecting prime when
its logarithm lies between 9.4 and 10.2. A small divisor rejects directly;
otherwise 171 weighted products exceed the local square kernel. -/
theorem exists_prime_reject_028_square_through1016 {n p : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hdiv : p ^ 2 ∣ n) (hL : (47 / 5 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 51 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hB : (23 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 23
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · let S := target028NinePrimes.toFinset
    let w := target028NineWeight
    let F := weightedPrimeFamily S w 58
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 23 := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).2.1
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).2.2
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Nine_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 58 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 58 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 58 hwpos T).mp hT).2
    have hc : F.card = 171 := by
      have h := target028Nine_family_card 58 (by decide)
      change F.card = 171 at h
      exact h
    have hp171 := target028_square_factor_le171 hn hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp171
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 23 58 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (target028_square_budget58 (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
