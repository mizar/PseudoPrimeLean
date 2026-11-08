/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Square25
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Square28

/-! # Coefficient 0.28 for square divisors through scale 25 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd input with a prime-square divisor and logarithm in `[13, 25]`,
the three existing weighted-count stages find a rejecting prime at most 43.
The lower endpoint makes that fixed prime bound fit the coefficient 0.28. -/
theorem exists_prime_reject_028_square_13_25 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (13 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hB : (43 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 43
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · by_cases hpMedium : p ≤ 809
    · obtain ⟨r, hr, hb, hf⟩ :=
        exists_prime_reject_square_seed43 hn ho hp hdiv hpMedium
          (square_factor_budget_77 (prime_ge_47_of_gt_43 hp (Nat.lt_of_not_ge hpSmall)))
      exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
    · by_cases hpNext : p ≤ 19639
      · have hp810 : 810 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hpMedium)
        obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed43_133 hn ho hp hdiv hpNext
            (square_factor_budget_133 hp810)
        exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
      · have hp19640 : 19640 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hpNext)
        obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed43_197 hn ho hp hdiv (square_factor_le_335463 hn hdiv hU)
            (square_factor_budget_197 hp19640)
        exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- For logarithmic scale between 25 and 28, the table through 89 extends the
three smaller weighted-count stages. Each selected prime fits the 0.28 bound. -/
theorem exists_prime_reject_028_square_25_28 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 28) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hB : (89 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
  have h43 : (43 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := (by norm_num only : (43 : ℝ) ≤ 89).trans hB
  by_cases hpSmall : p ≤ 43
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans h43,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · by_cases hpMedium : p ≤ 809
    · obtain ⟨r, hr, hb, hf⟩ :=
        exists_prime_reject_square_seed43 hn ho hp hdiv hpMedium
          (square_factor_budget_77 (prime_ge_47_of_gt_43 hp (Nat.lt_of_not_ge hpSmall)))
      exact ⟨r, hr, (Nat.cast_le.mpr hb).trans h43, hf⟩
    · by_cases hpNext : p ≤ 19639
      · have hp810 : 810 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hpMedium)
        obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed43_133 hn ho hp hdiv hpNext
            (square_factor_budget_133 hp810)
        exact ⟨r, hr, (Nat.cast_le.mpr hb).trans h43, hf⟩
      · have hp19640 : 19640 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hpNext)
        obtain ⟨r, hr, hb, hf⟩ :=
          exists_prime_reject_square_seed89_197 hn ho hp hdiv (square_factor_le_1372508 hn hdiv hU)
            (square_factor_budget_197 hp19640)
        exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
