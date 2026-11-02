/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsFirstSemiprimeCell
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsLowSemiprimeData

/-! # Closed interval coverage for low semiprime inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every odd semiprime in the large-factor branch with `8.3 ≤ log n ≤ 50` has an MR rejecting prime
within the four-ninths bound. Split at the ten common endpoints and
apply the certified repeated-product cell on each closed subinterval. -/
theorem exists_prime_witness_low_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : (83 / 10 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 50) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h01 : Real.log n ≤ ((2499 / 250) : ℝ)
  · exact exists_prime_witness_first_semiprime_cell hn ho hp hq hq2 hprod hlo h01 hqLarge
  have hlo02 : ((2499 / 250) : ℝ) ≤ Real.log n := (lt_of_not_ge h01).le
  by_cases h02 : Real.log n ≤ ((12021 / 1000) : ℝ)
  · exact semiprime_low_cell_02 hn ho hp hq hq2 hprod hlo02 h02 hqLarge
  have hlo03 : ((12021 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h02).le
  by_cases h03 : Real.log n ≤ ((15091 / 1000) : ℝ)
  · exact semiprime_low_cell_03 hn ho hp hq hq2 hprod hlo03 h03 hqLarge
  have hlo04 : ((15091 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h03).le
  by_cases h04 : Real.log n ≤ ((4451 / 250) : ℝ)
  · exact semiprime_low_cell_04 hn ho hp hq hq2 hprod hlo04 h04 hqLarge
  have hlo05 : ((4451 / 250) : ℝ) ≤ Real.log n := (lt_of_not_ge h04).le
  by_cases h05 : Real.log n ≤ ((20113 / 1000) : ℝ)
  · exact semiprime_low_cell_05 hn ho hp hq hq2 hprod hlo05 h05 hqLarge
  have hlo06 : ((20113 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h05).le
  by_cases h06 : Real.log n ≤ ((23589 / 1000) : ℝ)
  · exact semiprime_low_cell_06 hn ho hp hq hq2 hprod hlo06 h06 hqLarge
  have hlo07 : ((23589 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h06).le
  by_cases h07 : Real.log n ≤ ((717 / 25) : ℝ)
  · exact semiprime_low_cell_07 hn ho hp hq hq2 hprod hlo07 h07 hqLarge
  have hlo08 : ((717 / 25) : ℝ) ≤ Real.log n := (lt_of_not_ge h07).le
  by_cases h08 : Real.log n ≤ ((834 / 25) : ℝ)
  · exact semiprime_low_cell_08 hn ho hp hq hq2 hprod hlo08 h08 hqLarge
  have hlo09 : ((834 / 25) : ℝ) ≤ Real.log n := (lt_of_not_ge h08).le
  by_cases h09 : Real.log n ≤ ((9771 / 250) : ℝ)
  · exact semiprime_low_cell_09 hn ho hp hq hq2 hprod hlo09 h09 hqLarge
  have hlo10 : ((9771 / 250) : ℝ) ≤ Real.log n := (lt_of_not_ge h09).le
  by_cases h10 : Real.log n ≤ ((48357 / 1000) : ℝ)
  · exact semiprime_low_cell_10 hn ho hp hq hq2 hprod hlo10 h10 hqLarge
  have hlo11 : ((48357 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h10).le
  exact semiprime_low_cell_11 hn ho hp hq hq2 hprod hlo11 hhi hqLarge

end PseudoPrime.PrimeTestBounds.MillerRabin
