/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsFirstSquareCell
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsSecondSquareCell
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsLowSquareData
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsLastLowSquareCell

/-! # Closed interval coverage for low square inputs -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every odd prime square with `8.3 ≤ log n ≤ 56` has an MR rejecting prime
within the four-ninths bound. Split at the seventeen common endpoints and
apply the certified repeated-product cell on each closed subinterval. -/
theorem exists_prime_witness_low_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hlo : (83 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 56) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h01 : Real.log n ≤ ((8861 / 1000) : ℝ)
  · exact exists_prime_witness_first_square_cell hn ho hp hp2 hpow hlo h01
  have hlo02 : ((8861 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h01).le
  by_cases h02 : Real.log n ≤ ((10211 / 1000) : ℝ)
  · exact exists_prime_witness_second_square_cell hn ho hp hp2 hpow hlo02 h02
  have hlo03 : ((10211 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h02).le
  by_cases h03 : Real.log n ≤ ((11311 / 1000) : ℝ)
  · exact square_low_cell_03 hn ho hp hp2 hpow hlo03 h03
  have hlo04 : ((11311 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h03).le
  by_cases h04 : Real.log n ≤ ((3261 / 250) : ℝ)
  · exact square_low_cell_04 hn ho hp hp2 hpow hlo04 h04
  have hlo05 : ((3261 / 250) : ℝ) ≤ Real.log n := (lt_of_not_ge h04).le
  by_cases h05 : Real.log n ≤ ((609 / 40) : ℝ)
  · exact square_low_cell_05 hn ho hp hp2 hpow hlo05 h05
  have hlo06 : ((609 / 40) : ℝ) ≤ Real.log n := (lt_of_not_ge h05).le
  by_cases h06 : Real.log n ≤ ((16617 / 1000) : ℝ)
  · exact square_low_cell_06 hn ho hp hp2 hpow hlo06 h06
  have hlo07 : ((16617 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h06).le
  by_cases h07 : Real.log n ≤ ((3559 / 200) : ℝ)
  · exact square_low_cell_07 hn ho hp hp2 hpow hlo07 h07
  have hlo08 : ((3559 / 200) : ℝ) ≤ Real.log n := (lt_of_not_ge h07).le
  by_cases h08 : Real.log n ≤ ((3909 / 200) : ℝ)
  · exact square_low_cell_08 hn ho hp hp2 hpow hlo08 h08
  have hlo09 : ((3909 / 200) : ℝ) ≤ Real.log n := (lt_of_not_ge h08).le
  by_cases h09 : Real.log n ≤ ((21967 / 1000) : ℝ)
  · exact square_low_cell_09 hn ho hp hp2 hpow hlo09 h09
  have hlo10 : ((21967 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h09).le
  by_cases h10 : Real.log n ≤ ((24857 / 1000) : ℝ)
  · exact square_low_cell_10 hn ho hp hp2 hpow hlo10 h10
  have hlo11 : ((24857 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h10).le
  by_cases h11 : Real.log n ≤ ((13263 / 500) : ℝ)
  · exact square_low_cell_11 hn ho hp hp2 hpow hlo11 h11
  have hlo12 : ((13263 / 500) : ℝ) ≤ Real.log n := (lt_of_not_ge h11).le
  by_cases h12 : Real.log n ≤ ((29339 / 1000) : ℝ)
  · exact square_low_cell_12 hn ho hp hp2 hpow hlo12 h12
  have hlo13 : ((29339 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h12).le
  by_cases h13 : Real.log n ≤ ((33463 / 1000) : ℝ)
  · exact square_low_cell_13 hn ho hp hp2 hpow hlo13 h13
  have hlo14 : ((33463 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h13).le
  by_cases h14 : Real.log n ≤ ((36171 / 1000) : ℝ)
  · exact square_low_cell_14 hn ho hp hp2 hpow hlo14 h14
  have hlo15 : ((36171 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h14).le
  by_cases h15 : Real.log n ≤ ((39937 / 1000) : ℝ)
  · exact square_low_cell_15 hn ho hp hp2 hpow hlo15 h15
  have hlo16 : ((39937 / 1000) : ℝ) ≤ Real.log n := (lt_of_not_ge h15).le
  by_cases h16 : Real.log n ≤ ((11301 / 250) : ℝ)
  · exact square_low_cell_16 hn ho hp hp2 hpow hlo16 h16
  have hlo17 : ((11301 / 250) : ℝ) ≤ Real.log n := (lt_of_not_ge h16).le
  by_cases h17 : Real.log n ≤ ((9971 / 200) : ℝ)
  · exact square_low_cell_17 hn ho hp hp2 hpow hlo17 h17
  have hlo18 : ((9971 / 200) : ℝ) ≤ Real.log n := (lt_of_not_ge h17).le
  exact exists_prime_witness_last_low_square hn ho hp hp2 hpow hlo18 hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
