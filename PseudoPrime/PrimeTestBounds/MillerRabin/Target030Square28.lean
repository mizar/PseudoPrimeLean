/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Square25
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Seed89Count197

/-! # Square-divisor coverage through logarithmic scale 28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor at logarithmic scale at most 28 has base at most
1372508, by a rational logarithm certificate. -/
theorem square_factor_le_1372508 {n p : ℕ} (hn : 1 < n) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (28 : ℝ)) : p ≤ 1372508 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1883778210064 41 32 28 30 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hcert
  have hnle : n ≤ 1883778210064 := by
    have hlog : Real.log (n : ℝ) ≤ Real.log (1883778210064 : ℝ) := hU.trans hcert
    exact_mod_cast
      (Real.log_le_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 1883778210064)).mp
        hlog
  have hpsq : p ^ 2 ≤ 1883778210064 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans hnle
  nlinarith only [hpsq]

set_option maxRecDepth 16384 in
/-- The checked 89-prime supply gives a rejecting prime when the square
divisor lies within its count bound and exceeds the budget logarithmically. -/
theorem exists_prime_reject_square_seed89_197 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hbound : p ≤ 1372508)
    (hbudget : (197 : ℝ) / 10 < Real.log ((p ^ 2 : ℕ) : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 89 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hcount : p - 1 < target030Seed89Row197.getD 197 0 := by
    change p - 1 < 1372508
    exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le hbound
  exact
    exists_prime_reject_prime_pow_table hn ho hp hp2 (by decide : 0 < 2) hdiv target030Seed89Primes
      target030Seed89Weights 89 197 197 target030Seed89Weight 10 (by norm_num only)
      target030Seed89_labels.1 (fun r hr ↦ (target030Seed89_prime_supply r hr).1)
      (fun r hr ↦ (target030Seed89_prime_supply r hr).2) target030Seed89_labels.2.2
      target030Seed89_weight_bounds target030Seed89_labels.2.1 (by decide) target030Seed89Row197
      target030Seed89Tail197 target030Seed89_checked197 hbudget hcount

/-- Under RH, a prime-square divisor yields a 0.30 rejecting prime throughout
`[8, 28]`, using the prior stages and the extended weighted count. -/
theorem exists_prime_reject_03_square_8_to_28 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 28) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h25 : Real.log n ≤ 25
  · exact exists_prime_reject_03_square_8_to_25 hn ho hp hdiv hRH hL h25
  · have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
    have hB : (89 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by nlinarith only [h25]
    by_cases hpSmall : p ≤ 43
    · exact
        ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans (le_trans (by norm_num only : (43 : ℝ) ≤ 89) hB),
          PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
    · by_cases hpMedium : p ≤ 809
      · obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed43 hn ho hp hdiv hpMedium
            (square_factor_budget_77 (prime_ge_47_of_gt_43 hp (Nat.lt_of_not_ge hpSmall)))
        exact ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB), hf⟩
      · by_cases hpNext : p ≤ 19639
        · have hp810 : 810 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hpMedium)
          obtain ⟨r, hr, hb, hf⟩ :=
            exists_prime_reject_square_seed43_133 hn ho hp hdiv hpNext
              (square_factor_budget_133 hp810)
          exact
            ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB), hf⟩
        · have hp19640 : 19640 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hpNext)
          obtain ⟨r, hr, hb, hf⟩ :=
            exists_prime_reject_square_seed89_197 hn ho hp hdiv
              (square_factor_le_1372508 hn hdiv hU) (square_factor_budget_197 hp19640)
          exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
