/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareDivisorCoverage
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareCoverageRows
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Low1018

/-! # Square-divisor coverage for the 0.30 target -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked square-coverage row gives a 0.30 witness for an odd input with a
prime-square divisor when its target covers the logarithmic interval and its
prime cutoff fits the coefficient budget at the left endpoint. -/
theorem squareCoverage_divisor_03 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (d : SquareCoverageData) (hd : d ∈ squareCoverages)
    {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hL : lo ≤ Real.log n) (hU : Real.log n ≤ hi)
    (htarget : hi ≤ (d.target : ℝ)) (hbudget : (d.bound : ℝ) ≤ (3 / 10 : ℝ) * lo ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcheck : d.check = true := List.all_eq_true.mp squareCoverages_checked d hd
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  obtain ⟨r, hr, hB, hf⟩ :=
    squareCoverage_sound_divisor hn ho hp hp2 hdiv hRH d hcheck (hU.trans htarget)
  have hB' : (r : ℝ) ≤ d.bound := by exact_mod_cast hB
  have hsq := pow_le_pow_left₀ hlo0 hL 2
  exact ⟨r, hr, (hB'.trans hbudget).trans (mul_le_mul_of_nonneg_left hsq (by norm_num only)), hf⟩

/-- Under RH, the existing checked square-coverage rows give a 0.30 witness
for a prime-square divisor on `[10.18, 13.04]`. Three overlapping rows cover
the interval and their cutoffs satisfy the coefficient budget. -/
theorem exists_prime_reject_03_square_1304 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (509 / 50 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 326 / 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ (113 / 10 : ℝ)
  · let d : SquareCoverageData :=
      ⟨29, 3401197381661 / 500000000000, 5655991810819 / 500000000000, 5, [7, 3, 5, 8]⟩
    have hd : d ∈ squareCoverages := List.mem_of_getElem? (show squareCoverages[3]? = some d by rfl)
    apply
      squareCoverage_divisor_03 hn ho hp hdiv hRH d hd (lo := (509 / 50 : ℝ)) (hi := 113 / 10)
        (by norm_num only) hL h1
    all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]
  · by_cases h2 : Real.log n ≤ (62 / 5 : ℝ)
    · let d : SquareCoverageData :=
        ⟨31, 1732867951399 / 250000000000, 6204557762567 / 500000000000, 6, [9, 3, 5, 8, 10, 6]⟩
      have hd : d ∈ squareCoverages :=
        List.mem_of_getElem? (show squareCoverages[4]? = some d by rfl)
      apply
        squareCoverage_divisor_03 hn ho hp hdiv hRH d hd (lo := (113 / 10 : ℝ)) (hi := 62 / 5)
          (by norm_num only) (le_of_not_ge h1) h2
      all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]
    · let d : SquareCoverageData :=
        ⟨43, 3784189633917 / 500000000000, 652209279817 / 50000000000, 6, [12, 5, 8, 13]⟩
      have hd : d ∈ squareCoverages :=
        List.mem_of_getElem? (show squareCoverages[5]? = some d by rfl)
      apply
        squareCoverage_divisor_03 hn ho hp hdiv hRH d hd (lo := (62 / 5 : ℝ)) (hi := 326 / 25)
          (by norm_num only) (le_of_not_ge h2) hU
      all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]

/-- Under RH, every odd input with a prime-square divisor and logarithm in
`[8, 13.04]` has a 0.30 rejecting prime. The initial weighted certificate and
the transferred coverage rows meet at 10.18. -/
theorem exists_prime_reject_03_square_8_to_1304 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 326 / 25) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h : Real.log n ≤ 509 / 50
  · exact exists_prime_reject_03_square_1018 hn ho hp hdiv hL h
  · exact exists_prime_reject_03_square_1304 hn ho hp hdiv hRH (le_of_not_ge h) hU

end PseudoPrime.PrimeTestBounds.MillerRabin
