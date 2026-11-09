/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorBoundCoverage
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedCountWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareSeed43Bounds

/-! # Weighted square-divisor bridge near logarithmic scale 13 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime-square divisor gives a 0.30 witness on `[13.04, 13.3]`. Prime
factors at most 43 reject directly; larger factors use the 809-product table. -/
theorem exists_prime_reject_03_square_gap {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (326 / 25 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 133 / 10) :
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
  · obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_square_seed43 hn ho hp hdiv (square_factor_le_809 hn hdiv hU)
        (square_factor_budget_77 (prime_ge_47_of_gt_43 hp (Nat.lt_of_not_ge hpSmall)))
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- Under RH, the checked cutoff-53 row gives a 0.30 witness for an odd input
with a prime-square divisor on `[13.3, 14.4]`. -/
theorem exists_prime_reject_03_square_144 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (133 / 10 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 72 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let d : SquareCoverageData :=
    ⟨53, 3988984046563 / 500000000000, 7218909707617 / 500000000000, 6, [15, 5, 8, 13, 16, 11]⟩
  have hd : d ∈ squareCoverages := List.mem_of_getElem? (show squareCoverages[6]? = some d by rfl)
  apply
    squareCoverage_divisor_03 hn ho hp hdiv hRH d hd (lo := (133 / 10 : ℝ)) (hi := 72 / 5)
      (by norm_num only) hL hU
  all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, every odd input with a prime-square divisor and logarithm in
`[8, 14.4]` has a 0.30 rejecting prime. The weighted bridge connects the
initial coverage to the checked cutoff-53 row. -/
theorem exists_prime_reject_03_square_8_to_144 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 72 / 5) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ 326 / 25
  · exact exists_prime_reject_03_square_8_to_1304 hn ho hp hdiv hRH hL h1
  · by_cases h2 : Real.log n ≤ 133 / 10
    · exact exists_prime_reject_03_square_gap hn ho hp hdiv (le_of_not_ge h1) h2
    · exact exists_prime_reject_03_square_144 hn ho hp hdiv hRH (le_of_not_ge h2) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
