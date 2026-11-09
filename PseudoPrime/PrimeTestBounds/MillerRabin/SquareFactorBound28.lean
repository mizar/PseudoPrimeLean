/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorBound25
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count197
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage197

/-! # Square-divisor coverage through logarithmic scale 28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

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
