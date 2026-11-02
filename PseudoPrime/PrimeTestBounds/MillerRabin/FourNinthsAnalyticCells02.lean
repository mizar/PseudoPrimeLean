/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsPrimeCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourNinthsCellChecks

/-! # Analytic cells for the four-ninths witness bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- RH supplies the certified prime count for analytic cell 11. -/
theorem analytic_cell_11_primeCount (hRH : RiemannHypothesis) : 162 ≤ (1352 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1352 10 12 (112645932533 / 15625000000)
        (7209340786577 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1352 : ℝ) ≤ (22981 / 625) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((33 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 11, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_11_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((6489 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6551 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1352 10 12 (112645932533 / 15625000000)
        (7209340786577 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 168899 17 12 (12037056036431 / 1000000000000)
        (1203705631577 / 100000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (9 : ℝ) * Real.log 1352 < (6489 / 100) := by linarith only [hlB]
  have hchoose : 168899 * 10 ^ 9 ≤ Nat.choose 162 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((168899 : ℝ) * 10 ^ 9) ≤ Real.log (Nat.choose 162 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (168899 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6551 / 100) : ℝ) < 2 * Real.log (Nat.choose 162 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1352) (M := 162) (k := 9) (by norm_num only)
      (analytic_cell_11_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 11, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_11_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((6489 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6551 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1352 10 12 (112645932533 / 15625000000)
        (7209340786577 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 228603 18 12 (6169871074467 / 500000000000)
        (12339742157941 / 1000000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (6 : ℝ) * Real.log 1352 ≤ (2 / 3 : ℝ) * (6489 / 100) := by linarith only [hlB]
  have hchoose : 228603 * 10 ^ 5 ≤ Nat.choose 162 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((228603 : ℝ) * 10 ^ 5) ≤ Real.log (Nat.choose 162 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (228603 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6551 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 162 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1352) (M := 162) (k := 6) (by norm_num only)
      (analytic_cell_11_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 12. -/
theorem analytic_cell_12_primeCount (hRH : RiemannHypothesis) : 172 ≤ (1438 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1438 11 12 (3550297043 / 488281250)
        (7271008763183 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1438 : ℝ) ≤ (37921 / 1000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((13 / 200) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 12, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_12_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((1636 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6661 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1438 11 12 (3550297043 / 488281250)
        (7271008763183 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 293466 18 12 (3147379265897 / 250000000000)
        (786844817037 / 62500000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (9 : ℝ) * Real.log 1438 < (1636 / 25) := by linarith only [hlB]
  have hchoose : 293466 * 10 ^ 9 ≤ Nat.choose 172 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((293466 : ℝ) * 10 ^ 9) ≤ Real.log (Nat.choose 172 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (293466 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6661 / 100) : ℝ) < 2 * Real.log (Nat.choose 172 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1438) (M := 172) (k := 9) (by norm_num only)
      (analytic_cell_12_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 12, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_12_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((1636 / 25) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6661 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1438 11 12 (3550297043 / 488281250)
        (7271008763183 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 329270 18 12 (12704633328577 / 1000000000000)
        (12704633392287 / 1000000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (6 : ℝ) * Real.log 1438 ≤ (2 / 3 : ℝ) * (1636 / 25) := by linarith only [hlB]
  have hchoose : 329270 * 10 ^ 5 ≤ Nat.choose 172 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((329270 : ℝ) * 10 ^ 5) ≤ Real.log (Nat.choose 172 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (329270 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6661 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 172 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1438) (M := 172) (k := 6) (by norm_num only)
      (analytic_cell_12_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 13. -/
theorem analytic_cell_13_primeCount (hRH : RiemannHypothesis) : 191 ≤ (1619 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1619 11 12 (7389563949069 / 1000000000000)
        (7389563958353 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1619 : ℝ) ≤ (25148 / 625) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((31 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 13, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_13_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((6651 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (3427 / 50)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1619 11 12 (7389563949069 / 1000000000000)
        (7389563958353 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 769907 20 12 (6777012480279 / 500000000000)
        (2710805012083 / 200000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (9 : ℝ) * Real.log 1619 < (6651 / 100) := by linarith only [hlB]
  have hchoose : 769907 * 10 ^ 9 ≤ Nat.choose 191 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((769907 : ℝ) * 10 ^ 9) ≤ Real.log (Nat.choose 191 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (769907 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3427 / 50) : ℝ) < 2 * Real.log (Nat.choose 191 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1619) (M := 191) (k := 9) (by norm_num only)
      (analytic_cell_13_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 13, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_13_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((6651 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3427 / 50))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1619 11 12 (7389563949069 / 1000000000000)
        (7389563958353 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 622914 19 12 (13342163741089 / 1000000000000)
        (26684327503 / 2000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (6 : ℝ) * Real.log 1619 ≤ (2 / 3 : ℝ) * (6651 / 100) := by linarith only [hlB]
  have hchoose : 622914 * 10 ^ 5 ≤ Nat.choose 191 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((622914 : ℝ) * 10 ^ 5) ≤ Real.log (Nat.choose 191 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (622914 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3427 / 50) : ℝ) / 3 ≤ Real.log (Nat.choose 191 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1619) (M := 191) (k := 6) (by norm_num only)
      (analytic_cell_13_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 14. -/
theorem analytic_cell_14_primeCount (hRH : RiemannHypothesis) : 233 ≤ (2007 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 2007 11 12 (475274771621 / 62500000000)
        (7604396351437 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (2007 : ℝ) ≤ (111999 / 2500) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((29 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 14, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_14_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((1711 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (7219 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2007 11 12 (475274771621 / 62500000000)
        (7604396351437 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 476988 19 12 (6537623303691 / 500000000000)
        (13075246616883 / 1000000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (9 : ℝ) * Real.log 2007 < (1711 / 25) := by linarith only [hlB]
  have hchoose : 476988 * 10 ^ 10 ≤ Nat.choose 233 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((476988 : ℝ) * 10 ^ 10) ≤ Real.log (Nat.choose 233 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (476988 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((7219 / 100) : ℝ) < 2 * Real.log (Nat.choose 233 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 2007) (M := 233) (k := 9) (by norm_num only)
      (analytic_cell_14_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 14, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_14_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((1711 / 25) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (7219 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2007 11 12 (475274771621 / 62500000000)
        (7604396351437 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 208267 18 12 (765411011457 / 62500000000)
        (3061644048813 / 250000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (6 : ℝ) * Real.log 2007 ≤ (2 / 3 : ℝ) * (1711 / 25) := by linarith only [hlB]
  have hchoose : 208267 * 10 ^ 6 ≤ Nat.choose 233 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((208267 : ℝ) * 10 ^ 6) ≤ Real.log (Nat.choose 233 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (208267 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((7219 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 233 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 2007) (M := 233) (k := 6) (by norm_num only)
      (analytic_cell_14_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 15. -/
theorem analytic_cell_15_primeCount (hRH : RiemannHypothesis) : 265 ≤ (2309 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 2309 11 12 (1936142451623 / 250000000000)
        (3872284905999 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (2309 : ℝ) ≤ (480521 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((11 / 200) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 15, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_15_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((7209 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (3727 / 50)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2309 11 12 (1936142451623 / 250000000000)
        (3872284905999 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 154814 17 12 (5974989835307 / 500000000000)
        (11949979679667 / 1000000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (9 : ℝ) * Real.log 2309 < (7209 / 100) := by linarith only [hlB]
  have hchoose : 154814 * 10 ^ 11 ≤ Nat.choose 265 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((154814 : ℝ) * 10 ^ 11) ≤ Real.log (Nat.choose 265 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (154814 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3727 / 50) : ℝ) < 2 * Real.log (Nat.choose 265 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 2309) (M := 265) (k := 9) (by norm_num only)
      (analytic_cell_15_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 15, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_15_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((7209 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3727 / 50))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2309 11 12 (1936142451623 / 250000000000)
        (3872284905999 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 454347 19 12 (6513308248659 / 500000000000)
        (13026616506829 / 1000000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (6 : ℝ) * Real.log 2309 ≤ (2 / 3 : ℝ) * (7209 / 100) := by linarith only [hlB]
  have hchoose : 454347 * 10 ^ 6 ≤ Nat.choose 265 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((454347 : ℝ) * 10 ^ 6) ≤ Real.log (Nat.choose 265 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (454347 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3727 / 50) : ℝ) / 3 ≤ Real.log (Nat.choose 265 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 2309) (M := 265) (k := 6) (by norm_num only)
      (analytic_cell_15_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 16. -/
theorem analytic_cell_16_primeCount (hRH : RiemannHypothesis) : 281 ≤ (2462 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 2462 11 12 (1952182325661 / 250000000000)
        (976091163813 / 125000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (2462 : ℝ) ≤ (248093 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((27 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 16, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_16_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((1861 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (7561 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2462 11 12 (1952182325661 / 250000000000)
        (976091163813 / 125000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 264475 18 12 (499420080127 / 40000000000)
        (780343875761 / 62500000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (9 : ℝ) * Real.log 2462 < (1861 / 25) := by linarith only [hlB]
  have hchoose : 264475 * 10 ^ 11 ≤ Nat.choose 281 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((264475 : ℝ) * 10 ^ 11) ≤ Real.log (Nat.choose 281 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (264475 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((7561 / 100) : ℝ) < 2 * Real.log (Nat.choose 281 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 2462) (M := 281) (k := 9) (by norm_num only)
      (analytic_cell_16_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 16, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_16_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((1861 / 25) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (7561 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2462 11 12 (1952182325661 / 250000000000)
        (976091163813 / 125000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 647992 19 12 (13381633615003 / 1000000000000)
        (1338163364289 / 100000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (6 : ℝ) * Real.log 2462 ≤ (2 / 3 : ℝ) * (1861 / 25) := by linarith only [hlB]
  have hchoose : 647992 * 10 ^ 6 ≤ Nat.choose 281 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((647992 : ℝ) * 10 ^ 6) ≤ Real.log (Nat.choose 281 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (647992 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((7561 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 281 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 2462) (M := 281) (k := 6) (by norm_num only)
      (analytic_cell_16_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 17. -/
theorem analytic_cell_17_primeCount (hRH : RiemannHypothesis) : 222 ≤ (1902 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1902 11 12 (1510132248049 / 200000000000)
        (3775330622873 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1902 : ℝ) ≤ (10903 / 250) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((59 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 17, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_17_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((7551 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (3871 / 50)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1902 11 12 (1510132248049 / 200000000000)
        (3775330622873 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 652305 19 12 (13388267502803 / 1000000000000)
        (13388267541323 / 1000000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (10 : ℝ) * Real.log 1902 < (7551 / 100) := by linarith only [hlB]
  have hchoose : 652305 * 10 ^ 11 ≤ Nat.choose 222 10 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 10)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((652305 : ℝ) * 10 ^ 11) ≤ Real.log (Nat.choose 222 10 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (652305 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3871 / 50) : ℝ) < 2 * Real.log (Nat.choose 222 10 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1902) (M := 222) (k := 10) (by norm_num only)
      (analytic_cell_17_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 18. -/
theorem analytic_cell_18_primeCount (hRH : RiemannHypothesis) : 262 ≤ (2280 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 2280 11 12 (483245669943 / 62500000000)
        (773193072459 / 100000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (2280 : ℝ) ≤ (238747 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((11 / 200) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 18, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_18_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((1933 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (404 / 5)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2280 11 12 (483245669943 / 62500000000)
        (773193072459 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 352971 19 12 (12774140508979 / 1000000000000)
        (1596767744601 / 125000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (10 : ℝ) * Real.log 2280 < (1933 / 25) := by linarith only [hlB]
  have hchoose : 352971 * 10 ^ 12 ≤ Nat.choose 262 10 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 10)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((352971 : ℝ) * 10 ^ 12) ≤ Real.log (Nat.choose 262 10 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (352971 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((404 / 5) : ℝ) < 2 * Real.log (Nat.choose 262 10 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 2280) (M := 262) (k := 10) (by norm_num only)
      (analytic_cell_18_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 19. -/
theorem analytic_cell_19_primeCount (hRH : RiemannHypothesis) : 325 ≤ (2894 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 2894 12 12 (3985197373663 / 500000000000)
        (1992598773037 / 250000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (2894 : ℝ) ≤ (13449 / 250) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((51 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 19, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_19_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((807 / 10) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (8517 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2894 12 12 (3985197373663 / 500000000000)
        (1992598773037 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 315023 18 12 (1266040092513 / 100000000000)
        (1582550117053 / 125000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (10 : ℝ) * Real.log 2894 < (807 / 10) := by linarith only [hlB]
  have hchoose : 315023 * 10 ^ 13 ≤ Nat.choose 325 10 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 10)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((315023 : ℝ) * 10 ^ 13) ≤ Real.log (Nat.choose 325 10 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (315023 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((8517 / 100) : ℝ) < 2 * Real.log (Nat.choose 325 10 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 2894) (M := 325) (k := 10) (by norm_num only)
      (analytic_cell_19_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 20. -/
theorem analytic_cell_20_primeCount (hRH : RiemannHypothesis) : 358 ≤ (3216 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 3216 12 12 (2018973406183 / 250000000000)
        (4037946818013 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (3216 : ℝ) ≤ (283549 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((1 / 20) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 20, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_20_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((8507 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (8713 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 3216 12 12 (2018973406183 / 250000000000)
        (4037946818013 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 839436 20 12 (13640485510627 / 1000000000000)
        (13640485522603 / 1000000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (10 : ℝ) * Real.log 3216 < (8507 / 100) := by linarith only [hlB]
  have hchoose : 839436 * 10 ^ 13 ≤ Nat.choose 358 10 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 10)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((839436 : ℝ) * 10 ^ 13) ≤ Real.log (Nat.choose 358 10 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (839436 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((8713 / 100) : ℝ) < 2 * Real.log (Nat.choose 358 10 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 3216) (M := 358) (k := 10) (by norm_num only)
      (analytic_cell_20_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 20, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_20_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((8507 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8713 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 3216 12 12 (2018973406183 / 250000000000)
        (4037946818013 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 140967 17 12 (2371256218999 / 200000000000)
        (1482035137937 / 125000000000) =
      true := by
    decide +kernel
  have ht :
    Analysis.rationalLogIntervalCheck 10 3 12 (460517014283 / 200000000000)
        (575646278163 / 250000000000) =
      true := by
    decide +kernel
  have hlB := (Analysis.rationalLogIntervalCheck_sound hb).2
  have hlM := (Analysis.rationalLogIntervalCheck_sound hm).1
  have hlT := (Analysis.rationalLogIntervalCheck_sound ht).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlB hlM hlT
  have hs : (7 : ℝ) * Real.log 3216 ≤ (2 / 3 : ℝ) * (8507 / 100) := by linarith only [hlB]
  have hchoose : 140967 * 10 ^ 9 ≤ Nat.choose 358 7 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 7)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((140967 : ℝ) * 10 ^ 9) ≤ Real.log (Nat.choose 358 7 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (140967 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((8713 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 358 7 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 3216) (M := 358) (k := 7) (by norm_num only)
      (analytic_cell_20_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
