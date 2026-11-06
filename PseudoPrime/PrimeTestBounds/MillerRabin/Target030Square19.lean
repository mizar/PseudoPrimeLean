/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed43Count133
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareGap
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimePowerTable

/-! # Two-stage weighted square-divisor coverage through scale 19 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor of an input with logarithm at most 19 has base at
most 19639. The rational logarithm certificate bounds the input by its square. -/
theorem square_factor_le_19639 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (19 : ℝ)) : p ≤ 19639 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 385690321 29 32 19 21 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hnle : n ≤ 385690321 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (385690321 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 385690321)).mp
        hlog
  have hpsq : p ^ 2 ≤ 385690321 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The square of an integer at least 810 has logarithm strictly above the
second-stage budget 133/10, by a rational lower bound for `log 810`. -/
theorem square_factor_budget_133 {p : ℕ} (hbig : 810 ≤ p) :
    (133 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h810 :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 810 10 32 (669 / 100) 7 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h810
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 810) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h810, hl]

set_option maxRecDepth 8192 in
/-- The second-stage weighted table gives a rejecting prime at most 43 for a
prime-square divisor of base at most 19639 when its logarithm exceeds the
budget. The table count is 19639 and the original-input kernel has size below it. -/
theorem exists_prime_reject_square_seed43_133 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hbound : p ≤ 19639)
    (hbudget : (133 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 43 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hcount : p - 1 < target030Seed43Row133.getD 133 0 := by
    change p - 1 < 19639
    exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hbound
  exact
    exists_prime_reject_prime_pow_table hn ho hp hp2 (by decide : 0 < 2) hdiv target030Seed43Primes
      target030Seed43Weights 43 133 133 target030Seed43Weight 10 (by norm_num only)
      target030Seed43_labels.1 (fun r hr ↦ (target030Seed43_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed43_prime_supply r hr).2) target030Seed43_labels.2.2
      target030Seed43_weight_bounds target030Seed43_labels.2.1 (by decide) target030Seed43Row133
      target030Seed43Tail133 target030Seed43Table133_checked hbudget hcount

/-- A prime-square divisor gives a 0.30 witness on `[13.04, 19]`. Small prime
factors reject directly; the two weighted budgets cover the remaining factors. -/
theorem exists_prime_reject_03_square_19 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (326 / 25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 19) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hB : (43 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 43
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · by_cases hpMedium : p ≤ 809
    · obtain ⟨r, hr, hb, hf⟩ :=
        exists_prime_reject_square_seed43 hn ho hp hdiv hpMedium
          (square_factor_budget_77 (prime_ge_47_of_gt_43 hp (Nat.lt_of_not_ge hpSmall)))
      exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
    · have hp810 : 810 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hpMedium)
      obtain ⟨r, hr, hb, hf⟩ :=
        exists_prime_reject_square_seed43_133 hn ho hp hdiv (square_factor_le_19639 hn hdiv hU)
          (square_factor_budget_133 hp810)
      exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- Under RH, every odd input with a prime-square divisor and logarithm in
`[8, 19]` has a 0.30 rejecting prime. The two-stage weighted bound extends the
previously certified initial range. -/
theorem exists_prime_reject_03_square_8_to_19 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 19) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h : Real.log n ≤ 326 / 25
  · exact exists_prime_reject_03_square_8_to_1304 hn ho hp hdiv hRH hL h
  · exact exists_prime_reject_03_square_19 hn ho hp hdiv (le_of_not_ge h) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
