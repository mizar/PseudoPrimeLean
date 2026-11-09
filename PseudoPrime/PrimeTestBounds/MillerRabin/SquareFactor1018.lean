/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed19Count58
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductFamilyTransfer

/-! # Unconditional square-factor witness at logarithmic scale 10.18 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime whose square divides an input of logarithm at most 10.18 is at most
157. The rational logarithm certificate bounds the square below 163 squared,
and primality excludes the remaining integers above 157. -/
theorem square_factor_le_157_at_1018 {n p : ℕ} (hn : 1 < n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (509 / 50 : ℝ)) : p ≤ 157 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 26569 15 32 (10181 / 1000) 11 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnlt : n < 26569 := by
    have hlog : Real.log (n : ℝ) < Real.log (26569 : ℝ) := by linarith only [hU, hcert]
    exact_mod_cast
      (Real.log_lt_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 26569)).mp
        hlog
  have hpsq : p ^ 2 < 26569 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans_lt hnlt
  have hp162 : p ≤ 162 := by nlinarith only [hpsq]
  by_contra h
  have hlower : 158 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
  interval_cases p <;> norm_num only [Nat.prime_def_lt] at hp

set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- Any odd input divisible by a prime square has a 0.30 rejecting prime for
logarithm from 8 through 10.18. The 158-element weighted family exceeds the
local kernel when the prime factor itself is too large. -/
theorem exists_prime_reject_03_square_1018 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 509 / 50) :
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
  · let S := primeSeed19Primes.toFinset
    let w := primeSeed19Weight
    let F := weightedPrimeFamily S w 58
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (prime_seed19_prime_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
      (prime_seed19_prime_supply r (List.mem_toFinset.mp hr)).2
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      prime_seed19_weight_bounds r (List.mem_toFinset.mp hr)
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦ primeSeed19_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 58 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 58 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 58 hwpos T).mp hT).2
    have hc : F.card = 158 := primeSeed19_card58
    have hp157 := square_factor_le_157_at_1018 hn hp hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le (hp157.trans (by decide))
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 19 58 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (square_factor_budget_58 (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
