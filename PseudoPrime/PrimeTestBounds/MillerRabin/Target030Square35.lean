/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Square28
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed89Count282

/-! # Square-divisor coverage through logarithmic scale 35 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor at logarithmic scale at most 35 has base at most
59789534, by a rational logarithm certificate. -/
theorem square_factor_le_59789534 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (35 : ℝ)) : p ≤ 59789534 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3574788375937156 52 32 35 37 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hnle : n ≤ 3574788375937156 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (3574788375937156 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 3574788375937156)).mp
        hlog
  have hpsq : p ^ 2 ≤ 3574788375937156 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

/-- The square of an integer at least 1372509 exceeds budget 282/10
logarithmically, by a rational logarithm lower bound. -/
theorem square_factor_budget_282 {p : ℕ} (hbig : 1372509 ≤ p) :
    (282 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1372509 21 32 (1413 / 100) 15 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 1372509) (Nat.cast_le.mpr hbig)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  linarith only [h, hl]

set_option maxRecDepth 32768 in
/-- The checked prime supply through 89 gives a rejecting prime when its
budget is below the square-divisor logarithm and its count exceeds the kernel. -/
theorem exists_prime_reject_square_seed89_282 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hbound : p ≤ 59789534)
    (hbudget : (282 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 89 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hcount : p - 1 < target030Seed89Row282.getD 282 0 := by
    change p - 1 < 59789534
    exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hbound
  exact
    exists_prime_reject_prime_pow_table hn ho hp hp2 (by decide : 0 < 2) hdiv target030Seed89Primes
      target030Seed89Weights 89 282 282 target030Seed89Weight 10 (by norm_num only)
      target030Seed89_labels.1 (fun r hr ↦ (target030Seed89_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed89_prime_supply r hr).2) target030Seed89_labels.2.2
      target030Seed89_weight_bounds target030Seed89_labels.2.1 (by decide) target030Seed89Row282
      target030Seed89Tail282 target030Seed89_checked282 hbudget hcount

/-- Under RH, a prime-square divisor yields a 0.30 rejecting prime throughout
`[8, 35]`, using the previously checked budgets and the extended count. -/
theorem exists_prime_reject_03_square_8_to_35 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 35) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h28 : Real.log n ≤ 28
  · exact exists_prime_reject_03_square_8_to_28 hn ho hp hdiv hRH hL h28
  · have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
    have hB : (89 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by nlinarith only [h28]
    by_cases hsmall : p ≤ 43
    · exact
        ⟨p, hp, (Nat.cast_le.mpr hsmall).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB),
          PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
    · by_cases hmedium : p ≤ 809
      · obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed43 hn ho hp hdiv hmedium
            (square_factor_budget_77 (prime_ge_47_of_gt_43 hp (Nat.lt_of_not_ge hsmall)))
        exact ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB), hf⟩
      · by_cases hnext : p ≤ 19639
        · have hp810 : 810 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hmedium)
          obtain ⟨r, hr, hb, hf⟩ :=
            exists_prime_reject_square_seed43_133 hn ho hp hdiv hnext
              (square_factor_budget_133 hp810)
          exact
            ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB), hf⟩
        · by_cases hthird : p ≤ 1372508
          · have hp19640 : 19640 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hnext)
            obtain ⟨r, hr, hb, hf⟩ :=
              exists_prime_reject_square_seed89_197 hn ho hp hdiv hthird
                (square_factor_budget_197 hp19640)
            exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
          · have hbig : 1372509 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hthird)
            obtain ⟨r, hr, hb, hf⟩ :=
              exists_prime_reject_square_seed89_282 hn ho hp hdiv
                (square_factor_le_59789534 hn hdiv hU) (square_factor_budget_282 hbig)
            exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
