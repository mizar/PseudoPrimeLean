/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareDivisorCoverage
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareCoverageRows

/-! # Coefficient 0.28 for square divisors through logarithmic scale 13 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A checked square-coverage row gives a 0.28 witness when its target covers
the logarithmic interval and its cutoff fits the left endpoint. The existing
chain theorem applies to the original input and its square divisor. -/
theorem squareCoverage_divisor_028 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (d : SquareCoverageData) (hd : d ∈ squareCoverages)
    {lo hi : ℝ} (hlo0 : 0 ≤ lo) (hL : lo ≤ Real.log n) (hU : Real.log n ≤ hi)
    (htarget : hi ≤ (d.target : ℝ)) (hbudget : (d.bound : ℝ) ≤ (7 / 25 : ℝ) * lo ^ 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hcheck : d.check = true := List.all_eq_true.mp squareCoverages_checked d hd
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  obtain ⟨r, hr, hB, hf⟩ :=
    squareCoverage_sound_divisor hn ho hp hp2 hdiv hRH d hcheck (hU.trans htarget)
  have hB' : (r : ℝ) ≤ d.bound := by exact_mod_cast hB
  have hsq := pow_le_pow_left₀ hlo0 hL 2
  exact ⟨r, hr, (hB'.trans hbudget).trans (mul_le_mul_of_nonneg_left hsq (by norm_num only)), hf⟩

/-- Under RH, an odd input with a prime-square divisor and logarithm between
11.33 and 13 has a 0.28 rejecting prime. Two previously checked coverage rows
overlap at 12.4 and their cutoffs fit the target at the left endpoints. -/
theorem exists_prime_reject_028_square_1133_13 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (1133 / 100 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 13) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h1 : Real.log n ≤ (62 / 5 : ℝ)
  · let d : SquareCoverageData :=
      ⟨31, 1732867951399 / 250000000000, 6204557762567 / 500000000000, 6, [9, 3, 5, 8, 10, 6]⟩
    have hd : d ∈ squareCoverages := List.mem_of_getElem? (show squareCoverages[4]? = some d by rfl)
    apply
      squareCoverage_divisor_028 hn ho hp hdiv hRH d hd (lo := (1133 / 100 : ℝ)) (hi := 62 / 5)
        (by norm_num only) hL h1
    all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]
  · let d : SquareCoverageData :=
      ⟨43, 3784189633917 / 500000000000, 652209279817 / 50000000000, 6, [12, 5, 8, 13]⟩
    have hd : d ∈ squareCoverages := List.mem_of_getElem? (show squareCoverages[5]? = some d by rfl)
    apply
      squareCoverage_divisor_028 hn ho hp hdiv hRH d hd (lo := (62 / 5 : ℝ)) (hi := 13)
        (by norm_num only) (le_of_not_ge h1) hU
    all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]

/-- The certified cutoff-1103 row covers the square-divisor case for
logarithmic scale from 63 to 80.5 under RH, within the 0.28 cutoff. -/
theorem exists_prime_reject_028_square_63_805 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hRH : RiemannHypothesis) (hL : (63 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 161 / 2) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let d : SquareCoverageData :=
    ⟨1103, 1751673806709 / 125000000000, 5033898982571 / 62500000000, 11,
      [161, 110, 97, 163, 164, 165, 166, 167, 158, 168, 159, 169, 145, 160, 170]⟩
  have hd : d ∈ squareCoverages := List.mem_of_getElem? (show squareCoverages[29]? = some d by rfl)
  apply
    squareCoverage_divisor_028 hn ho hp hdiv hRH d hd (lo := (63 : ℝ)) (hi := 161 / 2)
      (by norm_num only) hL hU
  all_goals norm_num only [d, Rat.cast_div, Rat.cast_ofNat]

end PseudoPrime.PrimeTestBounds.MillerRabin
