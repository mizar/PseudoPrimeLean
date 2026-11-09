/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorBound394
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountExtend
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorBoundMiddle
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage414

/-! # Square-divisor coverage through logarithmic scale 80.5 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under RH, every odd input with a prime-square divisor has a 0.30
rejecting prime through logarithmic scale 42.5. -/
theorem exists_prime_reject_03_square_8_to_425 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 85 / 2) :
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
          · by_cases hfourth : p ≤ 59789534
            · have hbig : 1372509 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hthird)
              obtain ⟨r, hr, hb, hf⟩ :=
                exists_prime_reject_square_seed89_282 hn ho hp hdiv hfourth
                  (square_factor_budget_282 hbig)
              exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
            · by_cases hfifth : p ≤ 1054033525
              · have hbig : 59789535 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hfourth)
                obtain ⟨r, hr, hb, hf⟩ :=
                  exists_prime_reject_square_seed89_358 hn ho hp hdiv hfifth
                    (square_factor_budget_358 hbig)
                exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩
              · have hbig : 1054033526 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge hfifth)
                obtain ⟨r, hr, hb, hf⟩ :=
                  exists_prime_reject_square_seed89_414 hn ho hp hdiv
                    (square_factor_le_2087485596 hn hdiv hU) (square_factor_budget_414 hbig)
                exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- Under RH, the extended count and three existing coverage rows yield a
0.30 rejecting prime for a square divisor throughout `[8, 80.5]`. -/
theorem exists_prime_reject_03_square_8_to_805 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 161 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h : Real.log n ≤ 85 / 2
  · exact exists_prime_reject_03_square_8_to_425 hn ho hp hdiv hRH hL h
  · exact exists_prime_reject_03_square_mid hn ho hp hdiv hRH (le_of_not_ge h) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
