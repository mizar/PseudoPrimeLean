/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterSquareSecond
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNineCount90

/-! # Extended square-factor certificate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 800000 in
-- The weighted nine-prime family exceeds the default heartbeat limit.
/-- A prime square divisor at most 2292 supplies a quarter-square rejecting prime
when the input logarithm is at least 9.6. The preceding factor bound and a
checked family of signed weighted products cover the two factor ranges. -/
theorem quarter_square_factor_le2292 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (48 / 5 : ℝ) ≤ Real.log n) (hp2292 : p ≤ 2292) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hp390 : p ≤ 390
  · exact quarter_square_factor_le390 hn ho hp hdiv hL hp390
  · have hp391 : 391 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hp390)
    have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
    have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
    have hB : (23 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
    let S := target028NinePrimes.toFinset
    let w := target028NineWeight
    let F := weightedPrimeFamily S w 90
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 23 := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).2.1
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).2.2
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Nine_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 90 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 90 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 90 hwpos T).mp hT).2
    have hc : F.card = 1146 := by
      have h := quarter_nine90_family_card 90 (by decide)
      change F.card = 1146 at h
      exact h
    have hcount : p - 1 < 2 * F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp2292
    have h391 :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 391 9 32 (59 / 10) 6 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h391
    have hlogp := Real.log_le_log (by norm_num only : (0 : ℝ) < 391) (Nat.cast_le.mpr hp391)
    have hbudget : Real.log 2 + (90 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_two_lt_d9, h391, hlogp]
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_signed hn ho hp hp2 (by decide : 0 < 2) hdiv S F 23 90 w 10
        (by norm_num only) hsub hprime hbound hw hcost hbudget hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- A prime square divisor on logarithmic scales 9.6 through 15.47 supplies a
quarter-square rejecting prime. Factors through 390 use the preceding cell;
the remaining factors use a separately checked family of 1146 products. -/
theorem quarter_square_third {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hL : (48 / 5 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1547 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 5253264 22 64 (1547 / 100) 16 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 5253264 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (5253264 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 5253264)).mp
        hlog
  have hpsq : p ^ 2 ≤ 5253264 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  have hp2292 : p ≤ 2292 := by nlinarith only [hpsq]
  exact quarter_square_factor_le2292 hn ho hp hdiv hL hp2292

end PseudoPrime.PrimeTestBounds.MillerRabin
