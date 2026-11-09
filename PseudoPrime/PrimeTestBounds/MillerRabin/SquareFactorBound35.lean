/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorBound28
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed89Count282
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage282

/-! # Square-divisor coverage through logarithmic scale 35 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

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
