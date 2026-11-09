/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeSeed43Count197
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorBound19
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed43Stage197

/-! # Three-stage weighted square-divisor coverage through scale 25 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor gives a 0.30 witness on `[13.04, 25]`. Small prime
factors reject directly; three checked weighted budgets cover the rest. -/
theorem exists_prime_reject_03_square_25 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (326 / 25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hB : (43 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by nlinarith only [hL]
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

/-- Under RH, every odd input with a prime-square divisor and logarithm in
`[8, 25]` has a 0.30 rejecting prime. The three-stage weighted bound extends
the previously certified initial range. -/
theorem exists_prime_reject_03_square_8_to_25 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h : Real.log n ≤ 326 / 25
  · exact exists_prime_reject_03_square_8_to_1304 hn ho hp hdiv hRH hL h
  · exact exists_prime_reject_03_square_25 hn ho hp hdiv (le_of_not_ge h) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
