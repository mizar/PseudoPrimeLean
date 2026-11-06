/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030ExtendedCell

/-! # First weighted square-factor interval -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If `p²` divides a positive input with logarithm at most 8.3, then
`p ≤ 64`. A rational lower certificate for `log 4096` bounds the input and
the divisibility relation bounds the square. -/
theorem square_factor_le_64 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (83 / 10 : ℝ)) : p ≤ 64 := by
  have h4096 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 4096 12 32 (83 / 10) 9 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h4096
  have hnle : n ≤ 4096 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (4096 : ℝ) := hU.trans h4096
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 4096)).mp
        hlog
  have hpsq : p ^ 2 ≤ 4096 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The budget `45/10` is below the logarithm of `p²` whenever `p > 19`.
The certified lower bound for `log 20` and logarithm monotonicity supply the
strict product-size condition for the first weighted square-factor cell. -/
theorem square_factor_budget_45 {p : ℕ} (hbig : 19 < p) :
    (45 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
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
for `8 ≤ log n ≤ 8.3`. A small factor itself rejects; otherwise the checked
64-element weighted family exceeds the local Fermat kernel modulo `p²`. -/
theorem exists_prime_reject_03_square_first {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 83 / 10) :
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
    let F := weightedPrimeFamily S w 45
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target030_first_prime_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
      (target030_first_prime_supply r (List.mem_toFinset.mp hr)).2
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      target030_first_weight_bounds r (List.mem_toFinset.mp hr)
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦
      target030First_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 45 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 45 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 45 hwpos T).mp hT).2
    have hc : F.card = 64 := target030Extended_family_card 45 (by decide)
    have hp64 := square_factor_le_64 hn hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hp64
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 19 45 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (square_factor_budget_45 (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
