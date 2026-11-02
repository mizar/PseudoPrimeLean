/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeData
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellChecks

/-! # Low semiprime cells certified by repeated prime products -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Low semiprime cell 2: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_02 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((2499 / 250) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (12021 / 1000)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 23 5 12 (3135494125949 / 1000000000000)
        (627098864033 / 200000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 55 6 12 (4007333183663 / 1000000000000)
        (1001833296671 / 250000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((2499 / 250) : ℚ)) (b := ((12021 / 1000) : ℚ)) (k := 2) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 9 ≤ (23 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 8) (B := 23) (by rw [NumberTheory.primeByIndex_at_8])
    norm_num only at h
    exact h
  have hs : (2 : ℝ) * Real.log 23 ≤ (2 / 3 : ℝ) * (2499 / 250) := by linarith only [h.1]
  have hchoose : 55 ≤ Nat.choose (9 + 2) 2 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 2)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 55) (Nat.cast_le.mpr hchoose)
  have hcount : ((12021 / 1000) : ℝ) / 3 ≤ Real.log (Nat.choose (9 + 2) 2 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 23) (M := 9) (k := 2) (by norm_num only)
      hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 3: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_03 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((12021 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (15091 / 1000)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 53 6 12 (496286488983 / 125000000000)
        (3970291915141 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 153 7 12 (1006087583757 / 200000000000)
        (2515218961891 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((12021 / 1000) : ℚ)) (b := ((15091 / 1000) : ℚ)) (k := 2) hb
      hc (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 16 ≤ (53 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 15) (B := 53) (by rw [NumberTheory.primeByIndex_at_15])
    norm_num only at h
    exact h
  have hs : (2 : ℝ) * Real.log 53 ≤ (2 / 3 : ℝ) * (12021 / 1000) := by linarith only [h.1]
  have hchoose : 153 ≤ Nat.choose (16 + 2) 2 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 2)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 153) (Nat.cast_le.mpr hchoose)
  have hcount : ((15091 / 1000) : ℝ) / 3 ≤ Real.log (Nat.choose (16 + 2) 2 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 53) (M := 16) (k := 2) (by norm_num only)
      hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 4: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_04 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((15091 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (4451 / 250)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 101 7 12 (4615120513103 / 1000000000000)
        (4615120520753 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 378 9 12 (1186978831883 / 200000000000)
        (5934894237141 / 1000000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((15091 / 1000) : ℚ)) (b := ((4451 / 250) : ℚ)) (k := 2) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 26 ≤ (101 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 25) (B := 101) (by rw [NumberTheory.primeByIndex_at_25])
    norm_num only at h
    exact h
  have hs : (2 : ℝ) * Real.log 101 ≤ (2 / 3 : ℝ) * (15091 / 1000) := by linarith only [h.1]
  have hchoose : 378 ≤ Nat.choose (26 + 2) 2 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 2)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 378) (Nat.cast_le.mpr hchoose)
  have hcount : ((4451 / 250) : ℝ) / 3 ≤ Real.log (Nat.choose (26 + 2) 2 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 101) (M := 26) (k := 2)
      (by norm_num only) hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 5: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_05 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((4451 / 250) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (20113 / 1000)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 47 6 12 (3850147558873 / 1000000000000)
        (962536912781 / 250000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 816 10 12 (3352207175601 / 500000000000)
        (3352207179359 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((4451 / 250) : ℚ)) (b := ((20113 / 1000) : ℚ)) (k := 3) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 15 ≤ (47 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 14) (B := 47) (by rw [NumberTheory.primeByIndex_at_14])
    norm_num only at h
    exact h
  have hs : (3 : ℝ) * Real.log 47 ≤ (2 / 3 : ℝ) * (4451 / 250) := by linarith only [h.1]
  have hchoose : 816 ≤ Nat.choose (15 + 3) 3 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 3)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 816) (Nat.cast_le.mpr hchoose)
  have hcount : ((20113 / 1000) : ℝ) / 3 ≤ Real.log (Nat.choose (15 + 3) 3 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 47) (M := 15) (k := 3) (by norm_num only)
      hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 6: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_06 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((20113 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (23589 / 1000)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
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
    Analysis.rationalLogIntervalCheck 2600 11 12 (982908333059 / 125000000000)
        (1965816694613 / 250000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((20113 / 1000) : ℚ)) (b := ((23589 / 1000) : ℚ)) (k := 3) hb
      hc (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 23 ≤ (83 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 22) (B := 83) (by rw [NumberTheory.primeByIndex_at_22])
    norm_num only at h
    exact h
  have hs : (3 : ℝ) * Real.log 83 ≤ (2 / 3 : ℝ) * (20113 / 1000) := by linarith only [h.1]
  have hchoose : 2600 ≤ Nat.choose (23 + 3) 3 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 3)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 2600) (Nat.cast_le.mpr hchoose)
  have hcount : ((23589 / 1000) : ℝ) / 3 ≤ Real.log (Nat.choose (23 + 3) 3 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 83) (M := 23) (k := 3) (by norm_num only)
      hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 7: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_07 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((23589 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (717 / 25)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 181 8 12 (40613256843 / 7812500000)
        (129962430281 / 25000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 14190 14 12 (956029276651 / 100000000000)
        (9560292773521 / 1000000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((23589 / 1000) : ℚ)) (b := ((717 / 25) : ℚ)) (k := 3) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 42 ≤ (181 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 41) (B := 181) (by rw [NumberTheory.primeByIndex_at_41])
    norm_num only at h
    exact h
  have hs : (3 : ℝ) * Real.log 181 ≤ (2 / 3 : ℝ) * (23589 / 1000) := by linarith only [h.1]
  have hchoose : 14190 ≤ Nat.choose (42 + 3) 3 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 3)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 14190) (Nat.cast_le.mpr hchoose)
  have hcount : ((717 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose (42 + 3) 3 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 181) (M := 42) (k := 3)
      (by norm_num only) hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 8: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_08 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((717 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (834 / 25)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 359 9 12 (367707636637 / 62500000000)
        (5883322622893 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 67525 16 12 (11120253174501 / 1000000000000)
        (5560126591251 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((717 / 25) : ℚ)) (b := ((834 / 25) : ℚ)) (k := 3) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 72 ≤ (359 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 71) (B := 359) (by rw [NumberTheory.primeByIndex_at_71])
    norm_num only at h
    exact h
  have hs : (3 : ℝ) * Real.log 359 ≤ (2 / 3 : ℝ) * (717 / 25) := by linarith only [h.1]
  have hchoose : 67525 ≤ Nat.choose (72 + 3) 3 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 3)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 67525) (Nat.cast_le.mpr hchoose)
  have hcount : ((834 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose (72 + 3) 3 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 359) (M := 72) (k := 3)
      (by norm_num only) hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 9: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_09 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((834 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (9771 / 250)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 257 8 12 (1109815216563 / 200000000000)
        (173408627713 / 31250000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 455126 19 12 (13028329577731 / 1000000000000)
        (325708239681 / 25000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((834 / 25) : ℚ)) (b := ((9771 / 250) : ℚ)) (k := 4) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 55 ≤ (257 : ℕ).primeCounting := by
    have h := primeCount_ge_of_index (i := 54) (B := 257) (by rw [NumberTheory.primeByIndex_at_54])
    norm_num only at h
    exact h
  have hs : (4 : ℝ) * Real.log 257 ≤ (2 / 3 : ℝ) * (834 / 25) := by linarith only [h.1]
  have hchoose : 455126 ≤ Nat.choose (55 + 4) 4 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 4)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 455126) (Nat.cast_le.mpr hchoose)
  have hcount : ((9771 / 250) : ℝ) / 3 ≤ Real.log (Nat.choose (55 + 4) 4 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 257) (M := 55) (k := 4)
      (by norm_num only) hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 10: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_10 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((9771 / 250) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (48357 / 1000)) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 673 9 12 (1302348976213 / 200000000000)
        (6511745743037 / 1000000000000) =
      true := by
    decide +kernel
  have hc :
    Analysis.rationalLogIntervalCheck 10009125 23 12 (16119007728223 / 1000000000000)
        (8059503870509 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((9771 / 250) : ℚ)) (b := ((48357 / 1000) : ℚ)) (k := 4) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 122 ≤ (673 : ℕ).primeCounting := by
    have h :=
      primeCount_ge_of_index (i := 121) (B := 673) (by rw [NumberTheory.primeByIndex_at_121])
    norm_num only at h
    exact h
  have hs : (4 : ℝ) * Real.log 673 ≤ (2 / 3 : ℝ) * (9771 / 250) := by linarith only [h.1]
  have hchoose : 10009125 ≤ Nat.choose (122 + 4) 4 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 4)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 10009125) (Nat.cast_le.mpr hchoose)
  have hcount : ((48357 / 1000) : ℝ) / 3 ≤ Real.log (Nat.choose (122 + 4) 4 : ℝ) := by
    linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 673) (M := 122) (k := 4)
      (by norm_num only) hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- Low semiprime cell 11: checked rational logarithms and multichoose
give a four-ninths MR witness in the large-factor branch. -/
theorem semiprime_low_cell_11 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hq2 : q ≠ 2) (hprod : n = p * q) (hlo : ((48357 / 1000) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 50) (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
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
    Analysis.rationalLogIntervalCheck 190578024 28 12 (9532786051119 / 500000000000)
        (9532786202913 / 500000000000) =
      true := by
    decide +kernel
  have h :=
    semiprime_cell_checked_logs (a := ((48357 / 1000) : ℚ)) (b := (50 : ℚ)) (k := 5) hb hc
      (by norm_num only) (by norm_num only)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hpi : 115 ≤ (631 : ℕ).primeCounting := by
    have h :=
      primeCount_ge_of_index (i := 114) (B := 631) (by rw [NumberTheory.primeByIndex_at_114])
    norm_num only at h
    exact h
  have hs : (5 : ℝ) * Real.log 631 ≤ (2 / 3 : ℝ) * (48357 / 1000) := by linarith only [h.1]
  have hchoose : 190578024 ≤ Nat.choose (115 + 5) 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.reduceAdd, Nat.descFactorial, Nat.factorial, Nat.mul_succ, Nat.mul_zero,
      Nat.add_zero]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 190578024) (Nat.cast_le.mpr hchoose)
  have hcount : (50 : ℝ) / 3 ≤ Real.log (Nat.choose (115 + 5) 5 : ℝ) := by linarith only [h.2, hl]
  apply
    semiprime_cell_multichoose hn ho hp hq hq2 hprod (B := 631) (M := 115) (k := 5)
      (by norm_num only) hpi (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
