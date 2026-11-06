/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030ExtendedCell

/-! # Extended weighted square-factor interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If `p²` divides a positive input with logarithm at most 9.4, then
`p ≤ 112`. A rational lower certificate for `log 12544` bounds the input and
the divisibility relation bounds the square. -/
theorem square_factor_le_112 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (47 / 5 : ℝ)) : p ≤ 112 := by
  have h12544 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 12544 14 32 (47 / 5) 10 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h12544
  have hnle : n ≤ 12544 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (12544 : ℝ) := hU.trans h12544
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 12544)).mp
        hlog
  have hpsq : p ^ 2 ≤ 12544 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The budget `53/10` is below the logarithm of `p²` whenever `p > 19`.
The certified lower bound for `log 20` and logarithm monotonicity supply the
strict product-size condition for the extended weighted square-factor cell. -/
theorem square_factor_budget_53 {p : ℕ} (hbig : 19 < p) :
    (53 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h20 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 20 5 32 (29 / 10) 3 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h20
  have hp20 : 20 ≤ p := Nat.succ_le_of_lt hbig
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 20) (Nat.cast_le.mpr hp20)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h20, hl]

set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- Any odd input divisible by a prime square has a 0.30 rejecting prime
for `8 ≤ log n ≤ 9.4`. A small factor itself rejects; otherwise the checked
112-element weighted family exceeds the local Fermat kernel modulo `p²`. -/
theorem exists_prime_reject_03_square_extended {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 47 / 5) :
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
    let F := weightedPrimeFamily S w 53
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target030_first_prime_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
      (target030_first_prime_supply r (List.mem_toFinset.mp hr)).2
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      target030_first_weight_bounds r (List.mem_toFinset.mp hr)
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦
      target030First_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 53 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 53 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 53 hwpos T).mp hT).2
    have hc : F.card = 112 := target030Extended_family_card 53 (by decide)
    have hp112 := square_factor_le_112 hn hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp112
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 19 53 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (square_factor_budget_53 (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
