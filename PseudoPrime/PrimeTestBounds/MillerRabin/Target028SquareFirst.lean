/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorSmall
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeWitness

/-! # Initial weighted square-factor certificate for coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first seven prime labels are the primes at most 17. Their weights are
inherited from the certified first supply. -/
def target028FirstPrimes : List ℕ :=
  primeSeed19Primes.take 7

/-- The logarithmic weights of the first seven supplied prime labels. -/
def target028FirstWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26, 30]

/-- The cumulative weighted-product count for the first seven primes. -/
def target028FirstRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    18, 21, 22, 24, 26, 29, 30, 33, 36, 38, 41, 45, 49, 51, 56, 60, 64, 68, 75, 79, 84, 91, 98, 103,
    110, 119, 125, 133]

/-- Tail rows certify the cumulative weighted-product recurrence. -/
def target028FirstTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9,
      10, 10, 11, 12, 13, 13, 15, 15, 16, 17, 19, 20, 21, 23, 24, 26, 27, 30, 30, 33, 35, 38, 39,
      42, 44, 46, 49],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 6,
      6, 6, 6, 7, 7, 7, 8, 8, 8, 9, 10, 10, 11, 12, 12, 13, 14, 15, 15, 17, 18, 19, 19, 21, 21, 22,
      23],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 6, 6, 7, 7, 8, 8, 9, 9, 11, 11, 12, 12, 13, 13, 14, 14],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the weighted recurrence up to budget 57. -/
theorem target028First_checked :
    weightedPrimeTableCheck 57 target028FirstWeights (target028FirstRow :: target028FirstTail) =
      true := by
  decide +kernel

/-- The seven prime labels are distinct and match the certified weights. -/
theorem target028First_labels :
    target028FirstPrimes.Nodup ∧
      target028FirstPrimes.map primeSeed19Weight = target028FirstWeights ∧
      ∀ p ∈ target028FirstPrimes, 0 < primeSeed19Weight p := by
  decide +kernel

/-- There are exactly 64 weighted prime multisets within budget 46. The
checked recurrence transfers to the family of actual prime labels. -/
theorem target028First_family_card :
    (weightedPrimeFamily target028FirstPrimes.toFinset primeSeed19Weight 46).card = 64 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed19Weight 46 target028FirstPrimes
          target028FirstWeights target028First_labels.1 target028First_labels.2.2
          target028First_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 57 target028FirstWeights target028FirstRow target028FirstTail
          target028First_checked 46 (by decide)).symm)
  change (weightedPrimeFamily target028FirstPrimes.toFinset primeSeed19Weight 46).card = 64 at h
  exact h

/-- There are exactly 49 weighted prime multisets within budget 42. This
smaller budget supplies the first semiprime interval. -/
theorem target028First_family_card42 :
    (weightedPrimeFamily target028FirstPrimes.toFinset primeSeed19Weight 42).card = 49 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed19Weight 42 target028FirstPrimes
          target028FirstWeights target028First_labels.1 target028First_labels.2.2
          target028First_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 57 target028FirstWeights target028FirstRow target028FirstTail
          target028First_checked 42 (by decide)).symm)
  change (weightedPrimeFamily target028FirstPrimes.toFinset primeSeed19Weight 42).card = 49 at h
  exact h

/-- There are exactly 51 weighted prime multisets within budget 43. This
smaller budget supplies the first semiprime interval. -/
theorem target028First_family_card43 :
    (weightedPrimeFamily target028FirstPrimes.toFinset primeSeed19Weight 43).card = 51 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed19Weight 43 target028FirstPrimes
          target028FirstWeights target028First_labels.1 target028First_labels.2.2
          target028First_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 57 target028FirstWeights target028FirstRow target028FirstTail
          target028First_checked 43 (by decide)).symm)
  change (weightedPrimeFamily target028FirstPrimes.toFinset primeSeed19Weight 43).card = 51 at h
  exact h

/-- The checked table gives the weighted family count at every budget up to
57. This interface supplies the subsequent square and semiprime cells. -/
theorem target028First_family_card_at (H : ℕ) (hH : H ≤ 57) :
    (weightedPrimeFamily target028FirstPrimes.toFinset primeSeed19Weight H).card =
      target028FirstRow.getD H 0 :=
  (weightedPrimeCount_weights_eq_card primeSeed19Weight H target028FirstPrimes target028FirstWeights
        target028First_labels.1 target028First_labels.2.2 target028First_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 57 target028FirstWeights target028FirstRow target028FirstTail
        target028First_checked H hH).symm)

/-- The budget 46/10 is strictly below the logarithm of the square of any
integer greater than 17. A rational lower bound for log 18 gives the margin. -/
theorem target028_square_budget {p : ℕ} (hp : 17 < p) :
    (46 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h18 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 18 5 32 (14 / 5) 3 = true from by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h18
  have hp18 : 18 ≤ p := Nat.succ_le_of_lt hp
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 18) (Nat.cast_le.mpr hp18)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h18, hl]

set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- An odd input divisible by a prime square has a 0.28 rejecting prime when
its logarithm lies between 8 and 8.3. A small divisor rejects directly;
otherwise 64 weighted products exceed the local square kernel. -/
theorem exists_prime_reject_028_square_first {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 83 / 10) :
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
    let w := primeSeed19Weight
    let F := weightedPrimeFamily S w 46
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (prime_seed19_prime_supply r (List.mem_of_mem_take (List.mem_toFinset.mp hr))).1
    have hbound : ∀ r ∈ S, r ≤ 17 := by
      intro r hr
      have hm : r ∈ target028FirstPrimes := List.mem_toFinset.mp hr
      simp only [target028FirstPrimes, primeSeed19Primes, List.take_succ_cons, List.take_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h | h <;> subst r <;> decide
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      prime_seed19_weight_bounds r (List.mem_of_mem_take (List.mem_toFinset.mp hr))
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦
      target028First_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 46 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 46 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 46 hwpos T).mp hT).2
    have hc : F.card = 64 := target028First_family_card
    have hp64 := square_factor_le_64 hn hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp64
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 17 46 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (target028_square_budget (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- Under GRH, a product of two distinct odd primes has a 0.28 rejecting prime
when its logarithm lies between 8 and 8.26. The 49 weighted products give the
counting alternative and a linear radius bounds the local alternative. -/
theorem exists_prime_reject_028_semiprime_first {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 413 / 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028FirstPrimes.toFinset
  let w := primeSeed19Weight
  let F := weightedPrimeFamily S w 42
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (prime_seed19_prime_supply r (List.mem_of_mem_take (List.mem_toFinset.mp hr))).1
  have hbound : ∀ r ∈ S, r ≤ 17 := by
    intro r hr
    have hm : r ∈ target028FirstPrimes := List.mem_toFinset.mp hr
    simp only [target028FirstPrimes, primeSeed19Primes, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h <;> subst r <;> decide
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    prime_seed19_weight_bounds r (List.mem_of_mem_take (List.mem_toFinset.mp hr))
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028First_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w 42 hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ 42 := fun T hT ↦
    ((mem_weightedPrimeFamily S w 42 hwpos T).mp hT).2
  have hc : F.card = 49 := target028First_family_card42
  have hlog49 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 49 6 32 (389 / 100) 4 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog49
  have hD : (389 / 100 : ℝ) ≤ Real.log (F.card : ℝ) := by
    rw [hc]
    exact hlog49
  have hs : max (42 / 10 : ℝ) (Real.log n - 389 / 100) ≤ (52915 / 100000 : ℝ) * Real.log n := by
    apply max_le <;> linarith only [hL, hU]
  have hs0 : 0 ≤ max (42 / 10 : ℝ) (Real.log n - 389 / 100) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hs0 hs
  have hlocal :
    localFullEnvelope (max (42 / 10 : ℝ) (Real.log n - 389 / 100)) ≤
      (7 / 25 : ℝ) * (Real.log n) ^ 2 := by
    exact
      (min_le_left _ _).trans
        ((min_le_left _ _).trans (by nlinarith only [hsquare, sq_nonneg (Real.log n)]))
  have hB : (17 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 17 42 w 10
      (by norm_num only) hsub hprime hbound hw hcost (by norm_num only) hD hB hlocal hGRH

set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- Under GRH, a product of two distinct odd primes has a 0.28 rejecting prime
when its logarithm lies between 8.26 and 8.34. The 51 weighted products give the
counting alternative and a linear radius bounds the local alternative. -/
theorem exists_prime_reject_028_semiprime_second {n p q : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q) (hprod : n = p * q)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (413 / 50 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 417 / 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let S := target028FirstPrimes.toFinset
  let w := primeSeed19Weight
  let F := weightedPrimeFamily S w 43
  have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
    (prime_seed19_prime_supply r (List.mem_of_mem_take (List.mem_toFinset.mp hr))).1
  have hbound : ∀ r ∈ S, r ≤ 17 := by
    intro r hr
    have hm : r ∈ target028FirstPrimes := List.mem_toFinset.mp hr
    simp only [target028FirstPrimes, primeSeed19Primes, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with h | h | h | h | h | h | h <;> subst r <;> decide
  have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
    prime_seed19_weight_bounds r (List.mem_of_mem_take (List.mem_toFinset.mp hr))
  have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028First_labels.2.2 r (List.mem_toFinset.mp hr)
  have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
    ((mem_weightedPrimeFamily S w 43 hwpos T).mp hT).1
  have hcost : ∀ T ∈ F, (T.map w).sum ≤ 43 := fun T hT ↦
    ((mem_weightedPrimeFamily S w 43 hwpos T).mp hT).2
  have hc : F.card = 51 := target028First_family_card43
  have hlog51 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 51 6 32 (393 / 100) 4 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog51
  have hD : (393 / 100 : ℝ) ≤ Real.log (F.card : ℝ) := by
    rw [hc]
    exact hlog51
  have hs : max (43 / 10 : ℝ) (Real.log n - 393 / 100) ≤ (52915 / 100000 : ℝ) * Real.log n := by
    apply max_le <;> linarith only [hL, hU]
  have hs0 : 0 ≤ max (43 / 10 : ℝ) (Real.log n - 393 / 100) :=
    le_trans (by norm_num only) (le_max_left _ _)
  have hsquare := mul_self_le_mul_self hs0 hs
  have hlocal :
    localFullEnvelope (max (43 / 10 : ℝ) (Real.log n - 393 / 100)) ≤
      (7 / 25 : ℝ) * (Real.log n) ^ 2 := by
    exact
      (min_le_left _ _).trans
        ((min_le_left _ _).trans (by nlinarith only [hsquare, sq_nonneg (Real.log n)]))
  have hB : (17 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  exact
    exists_prime_reject_semiprime_weighted_cell hn ho hp hq hpq hprod S F 17 43 w 10
      (by norm_num only) hsub hprime hbound hw hcost (by norm_num only) hD hB hlocal hGRH

end PseudoPrime.PrimeTestBounds.MillerRabin
