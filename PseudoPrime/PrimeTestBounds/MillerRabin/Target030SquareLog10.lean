/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareExtended

/-! # Weighted square-factor certificate up to logarithmic scale 10.059 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Cumulative counts for the eight-prime supply through budget 58. -/
def target030SquareRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    19, 22, 23, 25, 27, 30, 31, 35, 38, 40, 43, 48, 52, 54, 60, 64, 68, 73, 81, 85, 91, 99, 107,
    112, 121, 131, 138, 147, 158]

/-- Remaining cumulative-count rows for the weighted supply through budget 58. -/
def target030SquareTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 10,
      11, 11, 12, 13, 14, 14, 16, 16, 17, 18, 21, 22, 23, 25, 26, 28, 30, 33, 33, 37, 39, 43, 44,
      48, 50, 53, 56, 59],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 7,
      7, 7, 7, 8, 8, 8, 9, 9, 9, 10, 11, 11, 12, 13, 13, 14, 16, 17, 17, 20, 21, 22, 22, 25, 25, 27,
      28, 29],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 6,
      6, 6, 6, 6, 6, 6, 6, 6, 6, 7, 7, 7, 7, 8, 8, 9, 9, 10, 10, 13, 13, 14, 14, 16, 16, 18, 18,
      18],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 5,
      5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 6, 6, 7, 7, 8, 8, 10, 10, 12, 12, 12],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 7, 7, 7],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- The finite table satisfies the weighted-count recurrence through budget 58. -/
theorem target030Square_checked :
    weightedPrimeTableCheck 58 target030FirstWeights (target030SquareRow :: target030SquareTail) =
      true := by
  decide +kernel

/-- The checked row gives the exact weighted-family count for every budget
through 58, by transfer from the table recurrence to the prime labels. -/
theorem target030Square_family_card (H : ℕ) (hH : H ≤ 58) :
    (weightedPrimeFamily target030FirstPrimes.toFinset target030FirstWeight H).card =
      target030SquareRow.getD H 0 :=
  (weightedPrimeCount_weights_eq_card target030FirstWeight H target030FirstPrimes
        target030FirstWeights target030First_labels.1 target030First_labels.2.2
        target030First_labels.2.1).symm.trans
    ((weightedPrimeTableCheck_sound 58 target030FirstWeights target030SquareRow target030SquareTail
        target030Square_checked H hH).symm)

/-- The weighted product family contains exactly 158 elements at budget 58. -/
theorem target030Square_card :
    (weightedPrimeFamily target030FirstPrimes.toFinset target030FirstWeight 58).card = 158 := by
  have h :=
    (weightedPrimeCount_weights_eq_card target030FirstWeight 58 target030FirstPrimes
          target030FirstWeights target030First_labels.1 target030First_labels.2.2
          target030First_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 58 target030FirstWeights target030SquareRow
          target030SquareTail target030Square_checked 58 (by decide)).symm)
  change (weightedPrimeFamily target030FirstPrimes.toFinset target030FirstWeight 58).card = 158 at h
  exact h

/-- A prime square dividing an input of logarithm at most 10.059 has base at most 157. -/
theorem square_factor_le_157 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (10059 / 1000 : ℝ)) : p ≤ 157 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 24649 15 32 (10059 / 1000) 11 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 24649 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (24649 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 24649)).mp
        hlog
  have hpsq : p ^ 2 ≤ 24649 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The budget 58/10 is below the logarithm of the square of any integer above 19. -/
theorem square_factor_budget_58 {p : ℕ} (hbig : 19 < p) :
    (58 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h20 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 20 5 32 (291 / 100) 3 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h20
  have hp20 : 20 ≤ p := Nat.succ_le_of_lt hbig
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 20) (Nat.cast_le.mpr hp20)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h20, hl]

set_option maxHeartbeats 4000000 in
-- Elaborating the finite weighted family requires additional heartbeats.
/-- Every odd input with a prime-square divisor has a 0.30 rejecting prime on
`[8, 10.059]`. Small factors reject directly; otherwise the certified weighted
family exceeds the local Fermat kernel. -/
theorem exists_prime_reject_03_square_log10 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 10059 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hB : (19 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 19
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · let S := target030FirstPrimes.toFinset
    let w := target030FirstWeight
    let F := weightedPrimeFamily S w 58
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target030_first_prime_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
      (target030_first_prime_supply r (List.mem_toFinset.mp hr)).2
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      target030_first_weight_bounds r (List.mem_toFinset.mp hr)
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦
      target030First_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 58 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 58 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 58 hwpos T).mp hT).2
    have hc : F.card = 158 := target030Square_card
    have hp157 := square_factor_le_157 hn hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le (hp157.trans (by decide))
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 19 58 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (square_factor_budget_58 (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
