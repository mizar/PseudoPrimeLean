/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedSemiprimeWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformLow

/-! # Initial square-factor certificate for coefficient one quarter -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The six primes at most 13, used as distinct labels for weighted products. -/
def quarterFirstPrimes : List ℕ :=
  primeSeed19Primes.take 6

/-- Positive logarithm weights for the six-prime supply, scaled by ten. -/
def quarterFirstWeights : List ℕ :=
  [7, 11, 17, 20, 24, 26]

/-- The complete cumulative count row through budget 49. -/
def quarterFirstRow : Array ℕ :=
  #[1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 4, 4, 4, 5, 6, 6, 7, 8, 9, 9, 11, 12, 13, 14, 16, 17,
    17, 20, 21, 23, 25, 28, 29, 31, 34, 36, 39, 42, 46, 48, 52, 56, 60, 63, 69, 73]

/-- Suffix rows certify the weighted-product recurrence. -/
def quarterFirstTail : List (Array ℕ) :=
  [#[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 3, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 8, 9,
      9, 10, 11, 12, 12, 14, 14, 15, 16, 17, 18, 19, 21, 22, 24, 24, 27, 27],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 3, 3, 3, 3, 4, 4, 5, 5, 5, 5, 5,
      5, 5, 5, 6, 6, 6, 7, 7, 7, 8, 9, 9, 10, 11, 11, 12, 12, 13, 13],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 4, 4, 4, 4, 4,
      4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5, 6, 6, 7, 7, 8, 8],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 3, 3, 3,
      3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 4, 4],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2,
      2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
    #[1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
      1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]]

set_option maxRecDepth 8192 in
/-- Kernel-check the recurrence for the six-prime count through budget 49. -/
theorem quarterFirst_checked :
    weightedPrimeTableCheck 49 quarterFirstWeights (quarterFirstRow :: quarterFirstTail) =
      true := by
  decide +kernel

/-- The supplied prime labels are distinct and have the recorded positive weights. -/
theorem quarterFirst_labels :
    quarterFirstPrimes.Nodup ∧
      quarterFirstPrimes.map primeSeed19Weight = quarterFirstWeights ∧
      ∀ p ∈ quarterFirstPrimes, 0 < primeSeed19Weight p := by
  decide +kernel

/-- The six-prime weighted family has 69 products through budget 48.
The checked recurrence transfers to the actual multiset family. -/
theorem quarterFirst_family_card :
    (weightedPrimeFamily quarterFirstPrimes.toFinset primeSeed19Weight 48).card = 69 := by
  have h :=
    (weightedPrimeCount_weights_eq_card primeSeed19Weight 48 quarterFirstPrimes quarterFirstWeights
          quarterFirst_labels.1 quarterFirst_labels.2.2 quarterFirst_labels.2.1).symm.trans
      ((weightedPrimeTableCheck_sound 49 quarterFirstWeights quarterFirstRow quarterFirstTail
          quarterFirst_checked 48 (by decide)).symm)
  change (weightedPrimeFamily quarterFirstPrimes.toFinset primeSeed19Weight 48).card = 69 at h
  exact h

/-- The weighted budget `48/10` lies below the logarithm of `p²` for every
natural `p > 13`. A certified lower bound for `log 14` supplies the margin. -/
theorem quarter_first_square_budget {p : ℕ} (hp : 13 < p) :
    (48 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h14 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 14 4 32 (5 / 2) 3 = true from by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h14
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 14)
      (show (14 : ℝ) ≤ p by exact_mod_cast Nat.succ_le_of_lt hp)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h14, hl]

/-- If a prime square divides an input of logarithmic scale at most 8.45,
its prime factor is at most 69. An exact logarithm certificate bounds the
input by `69²`, after which divisibility gives the factor bound. -/
theorem quarter_first_square_factor_le {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (169 / 20 : ℝ)) : p ≤ 69 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4761 13 32 (169 / 20) 9 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 4761 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (4761 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 4761)).mp
        hlog
  have hpsq : p ^ 2 ≤ 4761 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- An odd input divisible by a prime square has a rejecting prime within
the one-quarter bound when `8 ≤ log n ≤ 8.45`. A small divisor is a witness;
otherwise 69 weighted products exceed the local square kernel. -/
theorem exists_prime_reject_quarter_square_first {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 169 / 20) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hB : (13 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 13
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · let S := quarterFirstPrimes.toFinset
    let w := primeSeed19Weight
    let F := weightedPrimeFamily S w 48
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (prime_seed19_prime_supply r (List.mem_of_mem_take (List.mem_toFinset.mp hr))).1
    have hbound : ∀ r ∈ S, r ≤ 13 := by
      intro r hr
      have hm : r ∈ quarterFirstPrimes := List.mem_toFinset.mp hr
      simp only [quarterFirstPrimes, primeSeed19Primes, List.take_succ_cons, List.take_zero,
        List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with h | h | h | h | h | h <;> subst r <;> decide
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      prime_seed19_weight_bounds r (List.mem_of_mem_take (List.mem_toFinset.mp hr))
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ quarterFirst_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 48 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 48 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 48 hwpos T).mp hT).2
    have hc : F.card = 69 := quarterFirst_family_card
    have hp69 := quarter_first_square_factor_le hn hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp69
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 13 48 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (quarter_first_square_budget (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
