/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage414
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed43Stage197
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage197
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage282
import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed89Stage358

/-! # Bounded square factors for coefficient 0.28 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For logarithm at least 28, the checked supply through 89 handles a square
factor with base at most 2087485596 within the coefficient 0.28 cutoff. -/
theorem exists_prime_reject_028_square_small_factor {n p : ℕ} (hn : 1 < n) (ho : Odd n)
    (hp : p.Prime) (hdiv : p ^ 2 ∣ n) (hL : (28 : ℝ) ≤ Real.log n) (hpC : p ≤ 2087485596) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hB : (89 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
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
          exists_prime_reject_square_seed43_133 hn ho hp hdiv hnext (square_factor_budget_133 hp810)
        exact ⟨r, hr, (Nat.cast_le.mpr hb).trans ((by norm_num only : (43 : ℝ) ≤ 89).trans hB), hf⟩
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
                exists_prime_reject_square_seed89_414 hn ho hp hdiv hpC
                  (square_factor_budget_414 hbig)
              exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
