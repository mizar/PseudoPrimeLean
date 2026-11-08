/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028SquareFirst

/-! # Reusable seven-prime weighted witness -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 4000000 in
-- Elaborating the finite weighted family requires additional heartbeats.
/-- Under GRH, a semiprime has a 0.28 witness whenever the given weighted
budget and certified family count fit the linear local cutoff. This transfers
any checked row of the seven-prime table to a semiprime interval. -/
theorem target028_seven_supply_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (H : ℕ) (hH : H ≤ 57) (D : ℝ) (hD : D ≤ Real.log (target028FirstRow.getD H 0 : ℝ))
    (hbudget : (H : ℝ) / 10 ≤ (52915 / 100000 : ℝ) * Real.log n)
    (hmargin : (1 - 52915 / 100000 : ℝ) * Real.log n ≤ D) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028FirstPrimes.toFinset
  let w := target030FirstWeight
  let F := weightedPrimeFamily S w H
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (target030_first_prime_supply r (List.mem_of_mem_take (List.mem_toFinset.mp hr))).1
  have hbound : ∀ r ∈ S, r ≤ 17 := by
    intro r hr
    have hm : r ∈ target028FirstPrimes := List.mem_toFinset.mp hr
    simp only [target028FirstPrimes, target030FirstPrimes, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h <;> subst r <;> decide
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    target030_first_weight_bounds r (List.mem_of_mem_take (List.mem_toFinset.mp hr))
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028First_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ H := fun T hT ↦
    ((mem_weightedPrimeFamily S w H hwpos T).mp hT).2
  have hc : F.card = target028FirstRow.getD H 0 := target028First_family_card_at H hH
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
  have hB : (17 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 17 H w 10
      (by norm_num only) hsub hprime hbound hw hcost le_rfl hDF hB hlocal hGRH

/-- Under GRH, the seven-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_semiprime_cell44 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (417 / 50 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 427 / 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_seven_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 44
      (by decide) (161 / 40)
  · change (161 / 40 : ℝ) ≤ Real.log (56 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 56 6 32 (161 / 40) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the seven-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_semiprime_cell45 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (427 / 50 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1739 / 200) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_seven_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 45
      (by decide) (40943 / 10000)
  · change (40943 / 10000 : ℝ) ≤ Real.log (60 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 60 6 32 (40943 / 10000) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- Under GRH, the seven-prime table supplies a 0.28 witness on this
semiprime interval. A rational logarithm certificate controls the family count. -/
theorem target028_semiprime_cell46 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1739 / 200 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 883 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  apply
    target028_seven_supply_semiprime hn ho hp hq hpq hprod hGRH (by linarith only [hL]) 46
      (by decide) (2079 / 500)
  · change (2079 / 500 : ℝ) ≤ Real.log (64 : ℝ)
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 64 6 32 (2079 / 500) 5 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
    exact h
  · norm_num only [Nat.cast_ofNat]
    linarith only [hL]
  · linarith only [hU]

/-- A prime-square divisor of an input with logarithm at most 9.7 has base
at most 133. The logarithm certificate bounds the input by 133 squared. -/
theorem target028_square_factor_le133 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (97 / 10 : ℝ)) : p ≤ 133 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 17689 15 32 (97 / 10) 10 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 17689 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (17689 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 17689)).mp
        hlog
  have hpsq : p ^ 2 ≤ 17689 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- Budget 57/10 lies below the logarithm of the square of every integer
greater than 17. A rational lower bound for log 18 supplies the strict margin. -/
theorem target028_square_budget57 {p : ℕ} (hp : 17 < p) :
    (57 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h18 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 18 5 32 (72 / 25) 3 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h18
  have hp18 : 18 ≤ p := Nat.succ_le_of_lt hp
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 18) (Nat.cast_le.mpr hp18)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h18, hl]

set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- An odd input divisible by a prime square has a 0.28 rejecting prime when
its logarithm lies between 8 and 9.7. A small divisor rejects directly;
otherwise 133 weighted products exceed the local square kernel. -/
theorem exists_prime_reject_028_square_through97 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 97 / 10) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hB : (17 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 17
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · let S := target028FirstPrimes.toFinset
    let w := target030FirstWeight
    let F := weightedPrimeFamily S w 57
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target030_first_prime_supply r (List.mem_of_mem_take (List.mem_toFinset.mp hr))).1
    have hbound : ∀ r ∈ S, r ≤ 17 := by
      intro r hr
      have hm : r ∈ target028FirstPrimes := List.mem_toFinset.mp hr
      simp only [target028FirstPrimes, target030FirstPrimes, List.take_succ_cons, List.take_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h | h <;> subst r <;> decide
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      target030_first_weight_bounds r (List.mem_of_mem_take (List.mem_toFinset.mp hr))
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦
      target028First_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 57 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 57 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 57 hwpos T).mp hT).2
    have hc : F.card = 133 := by
      have h := target028First_family_card_at 57 (by decide)
      change F.card = 133 at h
      exact h
    have hp133 := target028_square_factor_le133 hn hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp133
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 17 57 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (target028_square_budget57 (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
