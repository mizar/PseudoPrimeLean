/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SignedPrimeProductTransfer
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNineCount

/-! # Signed-product square-factor cell -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

set_option maxHeartbeats 800000 in
-- The nine-prime family exceeds the default heartbeat limit during elaboration.
/-- For logarithmic scale at least 9.6, a prime square factor at most 390
gives a quarter-square rejecting prime. The 195 weighted products and their
negatives exceed the local Fermat kernel when the factor exceeds 23. -/
theorem quarter_square_factor_le390 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (48 / 5 : ℝ) ≤ Real.log n) (hp390 : p ≤ 390) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hB : (23 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 23
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · have hp29 : 29 ≤ p := by
      by_contra h
      have hnp : ∀ k ∈ Finset.Icc 24 28, ¬Nat.Prime k := by decide +kernel
      exact
        hnp p
          (Finset.mem_Icc.mpr
            ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge hpSmall), Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h)⟩)
          hp
    let S := target028NinePrimes.toFinset
    let w := target028NineWeight
    let F := weightedPrimeFamily S w 60
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 23 := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).2.1
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      (target028Nine_supply r (List.mem_toFinset.mp hr)).2.2
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Nine_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 60 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 60 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 60 hwpos T).mp hT).2
    have hc : F.card = 195 := by
      have h := quarter_nine_family_card 60 (by decide)
      change F.card = 195 at h
      exact h
    have hcount : p - 1 < 2 * F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp390
    have h29 :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 29 5 32 (336 / 100) 4 = true from by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div] at h29
    have hlogp := Real.log_le_log (by norm_num only : (0 : ℝ) < 29) (Nat.cast_le.mpr hp29)
    have hbudget : Real.log 2 + (60 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
      norm_num only [Nat.cast_ofNat]
      linarith only [Real.log_two_lt_d9, h29, hlogp]
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_signed hn ho hp hp2 (by decide : 0 < 2) hdiv S F 23 60 w 10
        (by norm_num only) hsub hprime hbound hw hcost hbudget hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- A prime square divisor of an odd input with logarithm between 9.6 and
11.93 yields a quarter-square rejecting prime. A rational logarithm
certificate bounds the square factor, and the preceding result supplies it. -/
theorem quarter_square_second {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hL : (48 / 5 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 1193 / 100) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 152100 17 64 (1193 / 100) 12 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 152100 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (152100 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 152100)).mp
        hlog
  have hpsq : p ^ 2 ≤ 152100 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  have hp390 : p ≤ 390 := by nlinarith only [hpsq]
  exact quarter_square_factor_le390 hn ho hp hdiv hL hp390

end PseudoPrime.PrimeTestBounds.MillerRabin
