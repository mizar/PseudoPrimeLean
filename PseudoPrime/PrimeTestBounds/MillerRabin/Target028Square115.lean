/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028TenSquare

/-! # Extended ten-prime square-factor range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A square divisor of an input of logarithmic scale at most 11.5 has base
at most 316. A rational logarithm certificate bounds the input by 316 squared. -/
theorem target028_square_factor_le316_wide {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (23 / 2 : ℝ)) : p ≤ 316 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 99856 17 32 (23 / 2) 12 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnle : n ≤ 99856 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (99856 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 99856)).mp
        hlog
  have hpsq : p ^ 2 ≤ 99856 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

-- The constructor-name linter times out while reducing this finite-family proof.
set_option linter.constructorNameAsVariable false in
set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- An odd input divisible by a prime square has a 0.28 rejecting prime when
its logarithm lies between 10.2 and 11.5. A small divisor rejects directly;
otherwise 316 weighted products exceed the local square kernel. -/
theorem exists_prime_reject_028_square_through115 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (51 / 5 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 23 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hB : (29 : ℝ) ≤ (7 / 25 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 29
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · let S := target028TenPrimes.toFinset
    let w := target028TenWeight
    let F := weightedPrimeFamily S w 66
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦ (target028Ten_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 29 := fun r hr ↦
      (target028Ten_supply r (List.mem_toFinset.mp hr)).2.1
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      (target028Ten_supply r (List.mem_toFinset.mp hr)).2.2
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ target028Ten_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 66 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 66 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 66 hwpos T).mp hT).2
    have hc : F.card = 316 := by
      have h := target028Ten_card 66 (by decide)
      change F.card = 316 at h
      exact h
    have hp316 := target028_square_factor_le316_wide hn hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp316
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 29 66 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (target028_square_budget66 (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
