/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeData
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellChecks

/-! # Low square cells certified by repeated prime products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Low square cell 3: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_03 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((10211 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (11311 / 1000)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 29 5 12 (1683647914343 / 500000000000)
        (3367295831187 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 286 8 12 (5655991808739 / 1000000000000)
        (2827995906371 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((10211 / 1000) : ℚ)) (b := ((11311 / 1000) : ℚ)) (k := 3) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 10 ≤ (29 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 9) (B := 29) (by rw [NumberTheory.primeByIndex_at_9])
    norm_num only at h
    exact h
  have hchoose : 286 ≤ Nat.choose (10 + 3) 3 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 3)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 286) (Nat.cast_le.mpr hchoose)
  have hcount : ((11311 / 1000) : ℝ) < 2 * Real.log (Nat.choose (10 + 3) 3 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 29) (M := 10) (k := 3) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 4: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_04 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((11311 / 1000) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3261 / 250)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 43 6 12 (1880599705007 / 500000000000)
        (235075058403 / 62500000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 680 9 12 (6522092004971 / 1000000000000)
        (815261691363 / 125000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((11311 / 1000) : ℚ)) (b := ((3261 / 250) : ℚ)) (k := 3) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 14 ≤ (43 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 13) (B := 43) (by rw [NumberTheory.primeByIndex_at_13])
    norm_num only at h
    exact h
  have hchoose : 680 ≤ Nat.choose (14 + 3) 3 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 3)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 680) (Nat.cast_le.mpr hchoose)
  have hcount : ((3261 / 250) : ℝ) < 2 * Real.log (Nat.choose (14 + 3) 3 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 43) (M := 14) (k := 3) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 5: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_05 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((3261 / 250) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (609 / 40)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 73 6 12 (2145229719789 / 500000000000)
        (2145229721299 / 500000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 2024 11 12 (7612831027547 / 1000000000000)
        (951603879131 / 125000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((3261 / 250) : ℚ)) (b := ((609 / 40) : ℚ)) (k := 3) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 21 ≤ (73 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 20) (B := 73) (by rw [NumberTheory.primeByIndex_at_20])
    norm_num only at h
    exact h
  have hchoose : 2024 ≤ Nat.choose (21 + 3) 3 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 3)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 2024) (Nat.cast_le.mpr hchoose)
  have hcount : ((609 / 40) : ℝ) < 2 * Real.log (Nat.choose (21 + 3) 3 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 73) (M := 21) (k := 3) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 6: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_06 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((609 / 40) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16617 / 1000)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 103 7 12 (2317364492859 / 500000000000)
        (926945798143 / 200000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 4060 12 12 (2077234562369 / 250000000000)
        (8308938255477 / 1000000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((609 / 40) : ℚ)) (b := ((16617 / 1000) : ℚ)) (k := 3) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 27 ≤ (103 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 26) (B := 103) (by rw [NumberTheory.primeByIndex_at_26])
    norm_num only at h
    exact h
  have hchoose : 4060 ≤ Nat.choose (27 + 3) 3 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 3)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 4060) (Nat.cast_le.mpr hchoose)
  have hcount : ((16617 / 1000) : ℝ) < 2 * Real.log (Nat.choose (27 + 3) 3 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 103) (M := 27) (k := 3) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 7: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_07 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((16617 / 1000) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3559 / 200)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 61 6 12 (4110873862613 / 1000000000000)
        (2055436932807 / 500000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 7315 13 12 (4448841155037 / 500000000000)
        (278052572393 / 31250000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((16617 / 1000) : ℚ)) (b := ((3559 / 200) : ℚ)) (k := 4) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 18 ≤ (61 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 17) (B := 61) (by rw [NumberTheory.primeByIndex_at_17])
    norm_num only at h
    exact h
  have hchoose : 7315 ≤ Nat.choose (18 + 4) 4 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 4)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 7315) (Nat.cast_le.mpr hchoose)
  have hcount : ((3559 / 200) : ℝ) < 2 * Real.log (Nat.choose (18 + 4) 4 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 61) (M := 18) (k := 4) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 8: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_08 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((3559 / 200) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3909 / 200)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 83 6 12 (2209420199977 / 500000000000)
        (883768159747 / 200000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 17550 14 12 (4886404612627 / 500000000000)
        (1954561846451 / 200000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((3559 / 200) : ℚ)) (b := ((3909 / 200) : ℚ)) (k := 4) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 23 ≤ (83 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 22) (B := 83) (by rw [NumberTheory.primeByIndex_at_22])
    norm_num only at h
    exact h
  have hchoose : 17550 ≤ Nat.choose (23 + 4) 4 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 4)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 17550) (Nat.cast_le.mpr hchoose)
  have hcount : ((3909 / 200) : ℝ) < 2 * Real.log (Nat.choose (23 + 4) 4 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 83) (M := 23) (k := 4) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 9: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_09 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((3909 / 200) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21967 / 1000)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 131 7 12 (4875197321381 / 1000000000000)
        (2437598662441 / 500000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 58905 16 12 (34324003911 / 3125000000)
        (5491840629761 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((3909 / 200) : ℚ)) (b := ((21967 / 1000) : ℚ)) (k := 4) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 32 ≤ (131 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 31) (B := 131) (by rw [NumberTheory.primeByIndex_at_31])
    norm_num only at h
    exact h
  have hchoose : 58905 ≤ Nat.choose (32 + 4) 4 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 4)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 58905) (Nat.cast_le.mpr hchoose)
  have hcount : ((21967 / 1000) : ℝ) < 2 * Real.log (Nat.choose (32 + 4) 4 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 131) (M := 32) (k := 4) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 10: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_10 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((21967 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (24857 / 1000)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 211 8 12 (668982266403 / 125000000000)
        (5351858135597 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 249900 18 12 (776801007009 / 62500000000)
        (2485763224229 / 200000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((21967 / 1000) : ℚ)) (b := ((24857 / 1000) : ℚ)) (k := 4) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 47 ≤ (211 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 46) (B := 211) (by rw [NumberTheory.primeByIndex_at_46])
    norm_num only at h
    exact h
  have hchoose : 249900 ≤ Nat.choose (47 + 4) 4 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 4)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 249900) (Nat.cast_le.mpr hchoose)
  have hcount : ((24857 / 1000) : ℝ) < 2 * Real.log (Nat.choose (47 + 4) 4 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 211) (M := 47) (k := 4) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 11: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_11 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((24857 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (13263 / 500)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 139 7 12 (4934473931311 / 1000000000000)
        (1233618483703 / 250000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 575757 19 12 (3315860242681 / 250000000000)
        (530537639209 / 40000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((24857 / 1000) : ℚ)) (b := ((13263 / 500) : ℚ)) (k := 5) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 34 ≤ (139 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 33) (B := 139) (by rw [NumberTheory.primeByIndex_at_33])
    norm_num only at h
    exact h
  have hchoose : 575757 ≤ Nat.choose (34 + 5) 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 575757) (Nat.cast_le.mpr hchoose)
  have hcount : ((13263 / 500) : ℝ) < 2 * Real.log (Nat.choose (34 + 5) 5 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 139) (M := 34) (k := 5) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 12: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_12 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((13263 / 500) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (29339 / 1000)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 199 8 12 (5293304818713 / 1000000000000)
        (5293304831219 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 2349060 21 12 (7334762900319 / 500000000000)
        (7334762905571 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((13263 / 500) : ℚ)) (b := ((29339 / 1000) : ℚ)) (k := 5) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 46 ≤ (199 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 45) (B := 199) (by rw [NumberTheory.primeByIndex_at_45])
    norm_num only at h
    exact h
  have hchoose : 2349060 ≤ Nat.choose (46 + 5) 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 2349060) (Nat.cast_le.mpr hchoose)
  have hcount : ((29339 / 1000) : ℝ) < 2 * Real.log (Nat.choose (46 + 5) 5 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 199) (M := 46) (k := 5) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 13: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_13 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((29339 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (33463 / 1000)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 353 9 12 (2933233859627 / 500000000000)
        (733308556061 / 125000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 18474840 24 12 (1673192035817 / 100000000000)
        (16731920370171 / 1000000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((29339 / 1000) : ℚ)) (b := ((33463 / 1000) : ℚ)) (k := 5) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 71 ≤ (353 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 70) (B := 353) (by rw [NumberTheory.primeByIndex_at_70])
    norm_num only at h
    exact h
  have hchoose : 18474840 ≤ Nat.choose (71 + 5) 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 18474840) (Nat.cast_le.mpr hchoose)
  have hcount : ((33463 / 1000) : ℝ) < 2 * Real.log (Nat.choose (71 + 5) 5 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 353) (M := 71) (k := 5) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 14: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_14 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((33463 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (36171 / 1000)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 491 9 12 (1239288825091 / 200000000000)
        (1549111032489 / 250000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 71523144 26 12 (4521382910209 / 250000000000)
        (18085531653837 / 1000000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((33463 / 1000) : ℚ)) (b := ((36171 / 1000) : ℚ)) (k := 5) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 94 ≤ (491 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 93) (B := 491) (by rw [NumberTheory.primeByIndex_at_93])
    norm_num only at h
    exact h
  have hchoose : 71523144 ≤ Nat.choose (94 + 5) 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 71523144) (Nat.cast_le.mpr hchoose)
  have hcount : ((36171 / 1000) : ℝ) < 2 * Real.log (Nat.choose (94 + 5) 5 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 491) (M := 94) (k := 5) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 15: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_15 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((36171 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (39937 / 1000)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 409 9 12 (150342878817 / 25000000000)
        (3006857579697 / 500000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 470155077 29 12 (1996857314177 / 100000000000)
        (9984286578137 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((36171 / 1000) : ℚ)) (b := ((39937 / 1000) : ℚ)) (k := 6) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 80 ≤ (409 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 79) (B := 409) (by rw [NumberTheory.primeByIndex_at_79])
    norm_num only at h
    exact h
  have hchoose : 470155077 ≤ Nat.choose (80 + 6) 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 470155077) (Nat.cast_le.mpr hchoose)
  have hcount : ((39937 / 1000) : ℝ) < 2 * Real.log (Nat.choose (80 + 6) 6 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 409) (M := 80) (k := 6) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 16: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_16 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((39937 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (11301 / 250)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 701 10 12 (819063433843 / 125000000000)
        (6552508369761 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 6547258432 33 12 (22602312220961 / 1000000000000)
        (2825289032233 / 125000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((39937 / 1000) : ℚ)) (b := ((11301 / 250) : ℚ)) (k := 6) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 126 ≤ (701 : ℕ).primeCounting := by
    have h :=
      primeCount_ge_of_index (i := 125) (B := 701) (by rw [NumberTheory.primeByIndex_at_125])
    norm_num only at h
    exact h
  have hchoose : 6547258432 ≤ Nat.choose (126 + 6) 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 6547258432) (Nat.cast_le.mpr hchoose)
  have hcount : ((11301 / 250) : ℝ) < 2 * Real.log (Nat.choose (126 + 6) 6 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 701) (M := 126) (k := 6) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

/-- Low square cell 17: the rational logarithm and multichoose certificates
give a four-ninths MR witness using the existing indexed-prime supply. -/
theorem square_low_cell_17 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hlo : ((11301 / 250) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (9971 / 200)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 631 9 12 (6447305852311 / 1000000000000)
        (6447305871861 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 66983637864 36 12 (24927714206169 / 1000000000000)
        (2492771422417 / 100000000000) =
      true := by
    decide +kernel
  have h :=
    square_cell_checked_logs (a := ((11301 / 250) : ℚ)) (b := ((9971 / 200) : ℚ)) (k := 7) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 115 ≤ (631 : ℕ).primeCounting := by
    have h :=
      primeCount_ge_of_index (i := 114) (B := 631) (by rw [NumberTheory.primeByIndex_at_114])
    norm_num only at h
    exact h
  have hchoose : 66983637864 ≤ Nat.choose (115 + 7) 7 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 7)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 66983637864) (Nat.cast_le.mpr hchoose)
  have hcount : ((9971 / 200) : ℝ) < 2 * Real.log (Nat.choose (115 + 7) 7 : ℝ) := by
    linarith only [h.2, hl]
  apply
    square_cell_multichoose hn ho hp hp2 hpow (B := 631) (M := 115) (k := 7) (by norm_num only) hpi
      (by norm_num only) hlo hhi h.1 hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
