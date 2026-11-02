/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsAnalyticCells01
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsAnalyticCells02
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsAnalyticCells03
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsAnalyticCells04
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsAnalyticCells05
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsAnalyticCells06
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsAnalyticCells07

/-! # Analytic closed-cell coverage for four-ninths witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- RH and the checked overlapping analytic cells cover the square
branch through `log n = 1024`, including every shared endpoint. -/
theorem exists_prime_witness_analytic_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : (56 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 1024) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h01 : Real.log n ≤ ((1418 / 25) : ℝ)
  · exact analytic_cell_01_square hn ho hp hp2 hpow hRH hlo h01
  have hlo02 : ((1416 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h01).le
    linarith only [h]
  by_cases h02 : Real.log n ≤ ((579 / 10) : ℝ)
  · exact analytic_cell_02_square hn ho hp hp2 hpow hRH hlo02 h02
  have hlo03 : ((289 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h02).le
    linarith only [h]
  by_cases h03 : Real.log n ≤ ((6013 / 100) : ℝ)
  · exact analytic_cell_03_square hn ho hp hp2 hpow hRH hlo03 h03
  have hlo04 : ((6003 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h03).le
    linarith only [h]
  by_cases h04 : Real.log n ≤ ((3117 / 50) : ℝ)
  · exact analytic_cell_04_square hn ho hp hp2 hpow hRH hlo04 h04
  have hlo05 : ((1556 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h04).le
    linarith only [h]
  by_cases h05 : Real.log n ≤ ((6343 / 100) : ℝ)
  · exact analytic_cell_05_square hn ho hp hp2 hpow hRH hlo05 h05
  have hlo06 : ((6333 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h05).le
    linarith only [h]
  by_cases h06 : Real.log n ≤ ((3199 / 50) : ℝ)
  · exact analytic_cell_06_square hn ho hp hp2 hpow hRH hlo06 h06
  have hlo07 : ((6391 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h06).le
    linarith only [h]
  by_cases h07 : Real.log n ≤ ((6421 / 100) : ℝ)
  · exact analytic_cell_07_square hn ho hp hp2 hpow hRH hlo07 h07
  have hlo08 : ((3209 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h07).le
    linarith only [h]
  by_cases h08 : Real.log n ≤ ((6437 / 100) : ℝ)
  · exact analytic_cell_08_square hn ho hp hp2 hpow hRH hlo08 h08
  have hlo09 : ((1287 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h08).le
    linarith only [h]
  by_cases h09 : Real.log n ≤ ((6457 / 100) : ℝ)
  · exact analytic_cell_09_square hn ho hp hp2 hpow hRH hlo09 h09
  have hlo10 : ((3227 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h09).le
    linarith only [h]
  by_cases h10 : Real.log n ≤ ((6493 / 100) : ℝ)
  · exact analytic_cell_10_square hn ho hp hp2 hpow hRH hlo10 h10
  have hlo11 : ((6489 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h10).le
    linarith only [h]
  by_cases h11 : Real.log n ≤ ((6551 / 100) : ℝ)
  · exact analytic_cell_11_square hn ho hp hp2 hpow hRH hlo11 h11
  have hlo12 : ((1636 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h11).le
    linarith only [h]
  by_cases h12 : Real.log n ≤ ((6661 / 100) : ℝ)
  · exact analytic_cell_12_square hn ho hp hp2 hpow hRH hlo12 h12
  have hlo13 : ((6651 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h12).le
    linarith only [h]
  by_cases h13 : Real.log n ≤ ((3427 / 50) : ℝ)
  · exact analytic_cell_13_square hn ho hp hp2 hpow hRH hlo13 h13
  have hlo14 : ((1711 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h13).le
    linarith only [h]
  by_cases h14 : Real.log n ≤ ((7219 / 100) : ℝ)
  · exact analytic_cell_14_square hn ho hp hp2 hpow hRH hlo14 h14
  have hlo15 : ((7209 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h14).le
    linarith only [h]
  by_cases h15 : Real.log n ≤ ((3727 / 50) : ℝ)
  · exact analytic_cell_15_square hn ho hp hp2 hpow hRH hlo15 h15
  have hlo16 : ((1861 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h15).le
    linarith only [h]
  by_cases h16 : Real.log n ≤ ((7561 / 100) : ℝ)
  · exact analytic_cell_16_square hn ho hp hp2 hpow hRH hlo16 h16
  have hlo17 : ((7551 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h16).le
    linarith only [h]
  by_cases h17 : Real.log n ≤ ((3871 / 50) : ℝ)
  · exact analytic_cell_17_square hn ho hp hp2 hpow hRH hlo17 h17
  have hlo18 : ((1933 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h17).le
    linarith only [h]
  by_cases h18 : Real.log n ≤ ((404 / 5) : ℝ)
  · exact analytic_cell_18_square hn ho hp hp2 hpow hRH hlo18 h18
  have hlo19 : ((807 / 10) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h18).le
    linarith only [h]
  by_cases h19 : Real.log n ≤ ((8517 / 100) : ℝ)
  · exact analytic_cell_19_square hn ho hp hp2 hpow hRH hlo19 h19
  have hlo20 : ((8507 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h19).le
    linarith only [h]
  by_cases h20 : Real.log n ≤ ((8713 / 100) : ℝ)
  · exact analytic_cell_20_square hn ho hp hp2 hpow hRH hlo20 h20
  have hlo21 : ((8703 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h20).le
    linarith only [h]
  by_cases h21 : Real.log n ≤ ((2267 / 25) : ℝ)
  · exact analytic_cell_21_square hn ho hp hp2 hpow hRH hlo21 h21
  have hlo22 : ((4529 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h21).le
    linarith only [h]
  by_cases h22 : Real.log n ≤ ((9663 / 100) : ℝ)
  · exact analytic_cell_22_square hn ho hp hp2 hpow hRH hlo22 h22
  have hlo23 : ((9653 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h22).le
    linarith only [h]
  by_cases h23 : Real.log n ≤ ((2502 / 25) : ℝ)
  · exact analytic_cell_23_square hn ho hp hp2 hpow hRH hlo23 h23
  have hlo24 : ((4999 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h23).le
    linarith only [h]
  by_cases h24 : Real.log n ≤ ((213 / 2) : ℝ)
  · exact analytic_cell_24_square hn ho hp hp2 hpow hRH hlo24 h24
  have hlo25 : ((532 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h24).le
    linarith only [h]
  by_cases h25 : Real.log n ≤ ((2768 / 25) : ℝ)
  · exact analytic_cell_25_square hn ho hp hp2 hpow hRH hlo25 h25
  have hlo26 : ((5531 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h25).le
    linarith only [h]
  by_cases h26 : Real.log n ≤ ((5889 / 50) : ℝ)
  · exact analytic_cell_26_square hn ho hp hp2 hpow hRH hlo26 h26
  have hlo27 : ((2942 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h26).le
    linarith only [h]
  by_cases h27 : Real.log n ≤ ((3074 / 25) : ℝ)
  · exact analytic_cell_27_square hn ho hp hp2 hpow hRH hlo27 h27
  have hlo28 : ((6143 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h27).le
    linarith only [h]
  by_cases h28 : Real.log n ≤ ((13191 / 100) : ℝ)
  · exact analytic_cell_28_square hn ho hp hp2 hpow hRH hlo28 h28
  have hlo29 : ((13181 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h28).le
    linarith only [h]
  by_cases h29 : Real.log n ≤ ((699 / 5) : ℝ)
  · exact analytic_cell_29_square hn ho hp hp2 hpow hRH hlo29 h29
  have hlo30 : ((1397 / 10) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h29).le
    linarith only [h]
  by_cases h30 : Real.log n ≤ ((2951 / 20) : ℝ)
  · exact analytic_cell_30_square hn ho hp hp2 hpow hRH hlo30 h30
  have hlo31 : ((2949 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h30).le
    linarith only [h]
  by_cases h31 : Real.log n ≤ ((15873 / 100) : ℝ)
  · exact analytic_cell_31_square hn ho hp hp2 hpow hRH hlo31 h31
  have hlo32 : ((15863 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h31).le
    linarith only [h]
  by_cases h32 : Real.log n ≤ ((17139 / 100) : ℝ)
  · exact analytic_cell_32_square hn ho hp hp2 hpow hRH hlo32 h32
  have hlo33 : ((17129 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h32).le
    linarith only [h]
  by_cases h33 : Real.log n ≤ ((4618 / 25) : ℝ)
  · exact analytic_cell_33_square hn ho hp hp2 hpow hRH hlo33 h33
  have hlo34 : ((9231 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h33).le
    linarith only [h]
  by_cases h34 : Real.log n ≤ ((4959 / 25) : ℝ)
  · exact analytic_cell_34_square hn ho hp hp2 hpow hRH hlo34 h34
  have hlo35 : ((9913 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h34).le
    linarith only [h]
  by_cases h35 : Real.log n ≤ ((1061 / 5) : ℝ)
  · exact analytic_cell_35_square hn ho hp hp2 hpow hRH hlo35 h35
  have hlo36 : ((2121 / 10) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h35).le
    linarith only [h]
  by_cases h36 : Real.log n ≤ ((4523 / 20) : ℝ)
  · exact analytic_cell_36_square hn ho hp hp2 hpow hRH hlo36 h36
  have hlo37 : ((4521 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h36).le
    linarith only [h]
  by_cases h37 : Real.log n ≤ ((24069 / 100) : ℝ)
  · exact analytic_cell_37_square hn ho hp hp2 hpow hRH hlo37 h37
  have hlo38 : ((24059 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h37).le
    linarith only [h]
  by_cases h38 : Real.log n ≤ ((5159 / 20) : ℝ)
  · exact analytic_cell_38_square hn ho hp hp2 hpow hRH hlo38 h38
  have hlo39 : ((5157 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h38).le
    linarith only [h]
  by_cases h39 : Real.log n ≤ ((27923 / 100) : ℝ)
  · exact analytic_cell_39_square hn ho hp hp2 hpow hRH hlo39 h39
  have hlo40 : ((27913 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h39).le
    linarith only [h]
  by_cases h40 : Real.log n ≤ ((29993 / 100) : ℝ)
  · exact analytic_cell_40_square hn ho hp hp2 hpow hRH hlo40 h40
  have hlo41 : ((29983 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h40).le
    linarith only [h]
  by_cases h41 : Real.log n ≤ ((6449 / 20) : ℝ)
  · exact analytic_cell_41_square hn ho hp hp2 hpow hRH hlo41 h41
  have hlo42 : ((6447 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h41).le
    linarith only [h]
  by_cases h42 : Real.log n ≤ ((6993 / 20) : ℝ)
  · exact analytic_cell_42_square hn ho hp hp2 hpow hRH hlo42 h42
  have hlo43 : ((6991 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h42).le
    linarith only [h]
  by_cases h43 : Real.log n ≤ ((9467 / 25) : ℝ)
  · exact analytic_cell_43_square hn ho hp hp2 hpow hRH hlo43 h43
  have hlo44 : ((18929 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h43).le
    linarith only [h]
  by_cases h44 : Real.log n ≤ ((817 / 2) : ℝ)
  · exact analytic_cell_44_square hn ho hp hp2 hpow hRH hlo44 h44
  have hlo45 : ((2042 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h44).le
    linarith only [h]
  by_cases h45 : Real.log n ≤ ((10969 / 25) : ℝ)
  · exact analytic_cell_45_square hn ho hp hp2 hpow hRH hlo45 h45
  have hlo46 : ((21933 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h45).le
    linarith only [h]
  by_cases h46 : Real.log n ≤ ((4719 / 10) : ℝ)
  · exact analytic_cell_46_square hn ho hp hp2 hpow hRH hlo46 h46
  have hlo47 : ((2359 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h46).le
    linarith only [h]
  by_cases h47 : Real.log n ≤ ((51153 / 100) : ℝ)
  · exact analytic_cell_47_square hn ho hp hp2 hpow hRH hlo47 h47
  have hlo48 : ((51143 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h47).le
    linarith only [h]
  by_cases h48 : Real.log n ≤ ((27647 / 50) : ℝ)
  · exact analytic_cell_48_square hn ho hp hp2 hpow hRH hlo48 h48
  have hlo49 : ((13821 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h48).le
    linarith only [h]
  by_cases h49 : Real.log n ≤ ((11937 / 20) : ℝ)
  · exact analytic_cell_49_square hn ho hp hp2 hpow hRH hlo49 h49
  have hlo50 : ((2387 / 4) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h49).le
    linarith only [h]
  by_cases h50 : Real.log n ≤ ((16126 / 25) : ℝ)
  · exact analytic_cell_50_square hn ho hp hp2 hpow hRH hlo50 h50
  have hlo51 : ((32247 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h50).le
    linarith only [h]
  by_cases h51 : Real.log n ≤ ((2787 / 4) : ℝ)
  · exact analytic_cell_51_square hn ho hp hp2 hpow hRH hlo51 h51
  have hlo52 : ((13933 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h51).le
    linarith only [h]
  by_cases h52 : Real.log n ≤ ((75139 / 100) : ℝ)
  · exact analytic_cell_52_square hn ho hp hp2 hpow hRH hlo52 h52
  have hlo53 : ((75129 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h52).le
    linarith only [h]
  by_cases h53 : Real.log n ≤ ((80851 / 100) : ℝ)
  · exact analytic_cell_53_square hn ho hp hp2 hpow hRH hlo53 h53
  have hlo54 : ((80841 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h53).le
    linarith only [h]
  by_cases h54 : Real.log n ≤ ((8719 / 10) : ℝ)
  · exact analytic_cell_54_square hn ho hp hp2 hpow hRH hlo54 h54
  have hlo55 : ((4359 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h54).le
    linarith only [h]
  by_cases h55 : Real.log n ≤ ((93753 / 100) : ℝ)
  · exact analytic_cell_55_square hn ho hp hp2 hpow hRH hlo55 h55
  have hlo56 : ((93743 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h55).le
    linarith only [h]
  by_cases h56 : Real.log n ≤ ((101159 / 100) : ℝ)
  · exact analytic_cell_56_square hn ho hp hp2 hpow hRH hlo56 h56
  have hlo57 : ((101149 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h56).le
    linarith only [h]
  apply analytic_cell_57_square hn ho hp hp2 hpow hRH hlo57 ?_
  linarith only [hhi]

/-- RH and the checked overlapping analytic cells cover the semiprime
branch through `log n = 1024`, including every shared endpoint. -/
theorem exists_prime_witness_analytic_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : (50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 1024)
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases h01 : Real.log n ≤ ((5409 / 100) : ℝ)
  · exact analytic_cell_58_semiprime hn ho hp hq hq2 hprod hRH hlo h01 hqLarge
  have hlo02 : ((5399 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h01).le
    linarith only [h]
  by_cases h02 : Real.log n ≤ ((3059 / 50) : ℝ)
  · exact analytic_cell_59_semiprime hn ho hp hq hq2 hprod hRH hlo02 h02 hqLarge
  have hlo03 : ((6003 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h02).le
    linarith only [h]
  by_cases h03 : Real.log n ≤ ((3117 / 50) : ℝ)
  · exact analytic_cell_04_semiprime hn ho hp hq hq2 hprod hRH hlo03 h03 hqLarge
  have hlo04 : ((1556 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h03).le
    linarith only [h]
  by_cases h04 : Real.log n ≤ ((6343 / 100) : ℝ)
  · exact analytic_cell_05_semiprime hn ho hp hq hq2 hprod hRH hlo04 h04 hqLarge
  have hlo05 : ((6333 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h04).le
    linarith only [h]
  by_cases h05 : Real.log n ≤ ((3199 / 50) : ℝ)
  · exact analytic_cell_06_semiprime hn ho hp hq hq2 hprod hRH hlo05 h05 hqLarge
  have hlo06 : ((6391 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h05).le
    linarith only [h]
  by_cases h06 : Real.log n ≤ ((6421 / 100) : ℝ)
  · exact analytic_cell_07_semiprime hn ho hp hq hq2 hprod hRH hlo06 h06 hqLarge
  have hlo07 : ((3209 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h06).le
    linarith only [h]
  by_cases h07 : Real.log n ≤ ((6437 / 100) : ℝ)
  · exact analytic_cell_08_semiprime hn ho hp hq hq2 hprod hRH hlo07 h07 hqLarge
  have hlo08 : ((1287 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h07).le
    linarith only [h]
  by_cases h08 : Real.log n ≤ ((6457 / 100) : ℝ)
  · exact analytic_cell_09_semiprime hn ho hp hq hq2 hprod hRH hlo08 h08 hqLarge
  have hlo09 : ((3227 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h08).le
    linarith only [h]
  by_cases h09 : Real.log n ≤ ((6493 / 100) : ℝ)
  · exact analytic_cell_10_semiprime hn ho hp hq hq2 hprod hRH hlo09 h09 hqLarge
  have hlo10 : ((6489 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h09).le
    linarith only [h]
  by_cases h10 : Real.log n ≤ ((6551 / 100) : ℝ)
  · exact analytic_cell_11_semiprime hn ho hp hq hq2 hprod hRH hlo10 h10 hqLarge
  have hlo11 : ((1636 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h10).le
    linarith only [h]
  by_cases h11 : Real.log n ≤ ((6661 / 100) : ℝ)
  · exact analytic_cell_12_semiprime hn ho hp hq hq2 hprod hRH hlo11 h11 hqLarge
  have hlo12 : ((6651 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h11).le
    linarith only [h]
  by_cases h12 : Real.log n ≤ ((3427 / 50) : ℝ)
  · exact analytic_cell_13_semiprime hn ho hp hq hq2 hprod hRH hlo12 h12 hqLarge
  have hlo13 : ((1711 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h12).le
    linarith only [h]
  by_cases h13 : Real.log n ≤ ((7219 / 100) : ℝ)
  · exact analytic_cell_14_semiprime hn ho hp hq hq2 hprod hRH hlo13 h13 hqLarge
  have hlo14 : ((7087 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h13).le
    linarith only [h]
  by_cases h14 : Real.log n ≤ ((1599 / 20) : ℝ)
  · exact analytic_cell_60_semiprime hn ho hp hq hq2 hprod hRH hlo14 h14 hqLarge
  have hlo15 : ((1597 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h14).le
    linarith only [h]
  by_cases h15 : Real.log n ≤ ((8861 / 100) : ℝ)
  · exact analytic_cell_61_semiprime hn ho hp hq hq2 hprod hRH hlo15 h15 hqLarge
  have hlo16 : ((8703 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h15).le
    linarith only [h]
  by_cases h16 : Real.log n ≤ ((2267 / 25) : ℝ)
  · exact analytic_cell_21_semiprime hn ho hp hq hq2 hprod hRH hlo16 h16 hqLarge
  have hlo17 : ((4529 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h16).le
    linarith only [h]
  by_cases h17 : Real.log n ≤ ((9663 / 100) : ℝ)
  · exact analytic_cell_22_semiprime hn ho hp hq hq2 hprod hRH hlo17 h17 hqLarge
  have hlo18 : ((9653 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h17).le
    linarith only [h]
  by_cases h18 : Real.log n ≤ ((2502 / 25) : ℝ)
  · exact analytic_cell_23_semiprime hn ho hp hq hq2 hprod hRH hlo18 h18 hqLarge
  have hlo19 : ((4999 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h18).le
    linarith only [h]
  by_cases h19 : Real.log n ≤ ((213 / 2) : ℝ)
  · exact analytic_cell_24_semiprime hn ho hp hq hq2 hprod hRH hlo19 h19 hqLarge
  have hlo20 : ((532 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h19).le
    linarith only [h]
  by_cases h20 : Real.log n ≤ ((2768 / 25) : ℝ)
  · exact analytic_cell_25_semiprime hn ho hp hq hq2 hprod hRH hlo20 h20 hqLarge
  have hlo21 : ((5531 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h20).le
    linarith only [h]
  by_cases h21 : Real.log n ≤ ((5889 / 50) : ℝ)
  · exact analytic_cell_26_semiprime hn ho hp hq hq2 hprod hRH hlo21 h21 hqLarge
  have hlo22 : ((2942 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h21).le
    linarith only [h]
  by_cases h22 : Real.log n ≤ ((3074 / 25) : ℝ)
  · exact analytic_cell_27_semiprime hn ho hp hq hq2 hprod hRH hlo22 h22 hqLarge
  have hlo23 : ((6143 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h22).le
    linarith only [h]
  by_cases h23 : Real.log n ≤ ((13191 / 100) : ℝ)
  · exact analytic_cell_28_semiprime hn ho hp hq hq2 hprod hRH hlo23 h23 hqLarge
  have hlo24 : ((13181 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h23).le
    linarith only [h]
  by_cases h24 : Real.log n ≤ ((699 / 5) : ℝ)
  · exact analytic_cell_29_semiprime hn ho hp hq hq2 hprod hRH hlo24 h24 hqLarge
  have hlo25 : ((1397 / 10) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h24).le
    linarith only [h]
  by_cases h25 : Real.log n ≤ ((2951 / 20) : ℝ)
  · exact analytic_cell_30_semiprime hn ho hp hq hq2 hprod hRH hlo25 h25 hqLarge
  have hlo26 : ((2949 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h25).le
    linarith only [h]
  by_cases h26 : Real.log n ≤ ((15873 / 100) : ℝ)
  · exact analytic_cell_31_semiprime hn ho hp hq hq2 hprod hRH hlo26 h26 hqLarge
  have hlo27 : ((15863 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h26).le
    linarith only [h]
  by_cases h27 : Real.log n ≤ ((17139 / 100) : ℝ)
  · exact analytic_cell_32_semiprime hn ho hp hq hq2 hprod hRH hlo27 h27 hqLarge
  have hlo28 : ((17129 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h27).le
    linarith only [h]
  by_cases h28 : Real.log n ≤ ((4618 / 25) : ℝ)
  · exact analytic_cell_33_semiprime hn ho hp hq hq2 hprod hRH hlo28 h28 hqLarge
  have hlo29 : ((9231 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h28).le
    linarith only [h]
  by_cases h29 : Real.log n ≤ ((4959 / 25) : ℝ)
  · exact analytic_cell_34_semiprime hn ho hp hq hq2 hprod hRH hlo29 h29 hqLarge
  have hlo30 : ((9913 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h29).le
    linarith only [h]
  by_cases h30 : Real.log n ≤ ((1061 / 5) : ℝ)
  · exact analytic_cell_35_semiprime hn ho hp hq hq2 hprod hRH hlo30 h30 hqLarge
  have hlo31 : ((2121 / 10) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h30).le
    linarith only [h]
  by_cases h31 : Real.log n ≤ ((4523 / 20) : ℝ)
  · exact analytic_cell_36_semiprime hn ho hp hq hq2 hprod hRH hlo31 h31 hqLarge
  have hlo32 : ((4521 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h31).le
    linarith only [h]
  by_cases h32 : Real.log n ≤ ((24069 / 100) : ℝ)
  · exact analytic_cell_37_semiprime hn ho hp hq hq2 hprod hRH hlo32 h32 hqLarge
  have hlo33 : ((24059 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h32).le
    linarith only [h]
  by_cases h33 : Real.log n ≤ ((5159 / 20) : ℝ)
  · exact analytic_cell_38_semiprime hn ho hp hq hq2 hprod hRH hlo33 h33 hqLarge
  have hlo34 : ((5157 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h33).le
    linarith only [h]
  by_cases h34 : Real.log n ≤ ((27923 / 100) : ℝ)
  · exact analytic_cell_39_semiprime hn ho hp hq hq2 hprod hRH hlo34 h34 hqLarge
  have hlo35 : ((27913 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h34).le
    linarith only [h]
  by_cases h35 : Real.log n ≤ ((29993 / 100) : ℝ)
  · exact analytic_cell_40_semiprime hn ho hp hq hq2 hprod hRH hlo35 h35 hqLarge
  have hlo36 : ((29983 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h35).le
    linarith only [h]
  by_cases h36 : Real.log n ≤ ((6449 / 20) : ℝ)
  · exact analytic_cell_41_semiprime hn ho hp hq hq2 hprod hRH hlo36 h36 hqLarge
  have hlo37 : ((6447 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h36).le
    linarith only [h]
  by_cases h37 : Real.log n ≤ ((6993 / 20) : ℝ)
  · exact analytic_cell_42_semiprime hn ho hp hq hq2 hprod hRH hlo37 h37 hqLarge
  have hlo38 : ((6991 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h37).le
    linarith only [h]
  by_cases h38 : Real.log n ≤ ((9467 / 25) : ℝ)
  · exact analytic_cell_43_semiprime hn ho hp hq hq2 hprod hRH hlo38 h38 hqLarge
  have hlo39 : ((18929 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h38).le
    linarith only [h]
  by_cases h39 : Real.log n ≤ ((817 / 2) : ℝ)
  · exact analytic_cell_44_semiprime hn ho hp hq hq2 hprod hRH hlo39 h39 hqLarge
  have hlo40 : ((2042 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h39).le
    linarith only [h]
  by_cases h40 : Real.log n ≤ ((10969 / 25) : ℝ)
  · exact analytic_cell_45_semiprime hn ho hp hq hq2 hprod hRH hlo40 h40 hqLarge
  have hlo41 : ((21933 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h40).le
    linarith only [h]
  by_cases h41 : Real.log n ≤ ((4719 / 10) : ℝ)
  · exact analytic_cell_46_semiprime hn ho hp hq hq2 hprod hRH hlo41 h41 hqLarge
  have hlo42 : ((2359 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h41).le
    linarith only [h]
  by_cases h42 : Real.log n ≤ ((51153 / 100) : ℝ)
  · exact analytic_cell_47_semiprime hn ho hp hq hq2 hprod hRH hlo42 h42 hqLarge
  have hlo43 : ((51143 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h42).le
    linarith only [h]
  by_cases h43 : Real.log n ≤ ((27647 / 50) : ℝ)
  · exact analytic_cell_48_semiprime hn ho hp hq hq2 hprod hRH hlo43 h43 hqLarge
  have hlo44 : ((13821 / 25) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h43).le
    linarith only [h]
  by_cases h44 : Real.log n ≤ ((11937 / 20) : ℝ)
  · exact analytic_cell_49_semiprime hn ho hp hq hq2 hprod hRH hlo44 h44 hqLarge
  have hlo45 : ((2387 / 4) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h44).le
    linarith only [h]
  by_cases h45 : Real.log n ≤ ((16126 / 25) : ℝ)
  · exact analytic_cell_50_semiprime hn ho hp hq hq2 hprod hRH hlo45 h45 hqLarge
  have hlo46 : ((32247 / 50) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h45).le
    linarith only [h]
  by_cases h46 : Real.log n ≤ ((2787 / 4) : ℝ)
  · exact analytic_cell_51_semiprime hn ho hp hq hq2 hprod hRH hlo46 h46 hqLarge
  have hlo47 : ((13933 / 20) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h46).le
    linarith only [h]
  by_cases h47 : Real.log n ≤ ((75139 / 100) : ℝ)
  · exact analytic_cell_52_semiprime hn ho hp hq hq2 hprod hRH hlo47 h47 hqLarge
  have hlo48 : ((75129 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h47).le
    linarith only [h]
  by_cases h48 : Real.log n ≤ ((80851 / 100) : ℝ)
  · exact analytic_cell_53_semiprime hn ho hp hq hq2 hprod hRH hlo48 h48 hqLarge
  have hlo49 : ((80841 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h48).le
    linarith only [h]
  by_cases h49 : Real.log n ≤ ((8719 / 10) : ℝ)
  · exact analytic_cell_54_semiprime hn ho hp hq hq2 hprod hRH hlo49 h49 hqLarge
  have hlo50 : ((4359 / 5) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h49).le
    linarith only [h]
  by_cases h50 : Real.log n ≤ ((93753 / 100) : ℝ)
  · exact analytic_cell_55_semiprime hn ho hp hq hq2 hprod hRH hlo50 h50 hqLarge
  have hlo51 : ((93743 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h50).le
    linarith only [h]
  by_cases h51 : Real.log n ≤ ((101159 / 100) : ℝ)
  · exact analytic_cell_56_semiprime hn ho hp hq hq2 hprod hRH hlo51 h51 hqLarge
  have hlo52 : ((101149 / 100) : ℝ) ≤ Real.log n := by
    have h := (lt_of_not_ge h51).le
    linarith only [h]
  apply analytic_cell_57_semiprime hn ho hp hq hq2 hprod hRH hlo52 ?_ hqLarge
  linarith only [hhi]

end PseudoPrime.PrimeTestBounds.MillerRabin
