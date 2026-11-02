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

/-- RH supplies the certified prime count for analytic cell 51. -/
theorem analytic_cell_51_primeCount (hRH : RiemannHypothesis) :
    14767 ≤ (184865 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 184865 18 12 (12127380936649 / 1000000000000)
        (1212738130581 / 100000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (184865 : ℝ) ≤ (2149797 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((2 / 125) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 51, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_51_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((32247 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (2787 / 4)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 184865 18 12 (12127380936649 / 1000000000000)
        (1212738130581 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 199982 18 12 (2441196525543 / 200000000000)
        (12205982656367 / 1000000000000) =
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
  have hs : (53 : ℝ) * Real.log 184865 < (32247 / 50) := by linarith only [hlB]
  have hchoose : 199982 * 10 ^ 146 ≤ Nat.choose 14767 53 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 53)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((199982 : ℝ) * 10 ^ 146) ≤ Real.log (Nat.choose 14767 53 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (199982 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2787 / 4) : ℝ) < 2 * Real.log (Nat.choose 14767 53 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 184865) (M := 14767) (k := 53) (by norm_num only)
      (analytic_cell_51_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 51, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_51_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((32247 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2787 / 4))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 184865 18 12 (12127380936649 / 1000000000000)
        (1212738130581 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 782500 20 12 (6785124586893 / 500000000000)
        (13570249232251 / 1000000000000) =
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
  have hs : (35 : ℝ) * Real.log 184865 ≤ (2 / 3 : ℝ) * (32247 / 50) := by linarith only [hlB]
  have hchoose : 782500 * 10 ^ 100 ≤ Nat.choose 14767 35 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 35)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((782500 : ℝ) * 10 ^ 100) ≤ Real.log (Nat.choose 14767 35 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (782500 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2787 / 4) : ℝ) / 3 ≤ Real.log (Nat.choose 14767 35 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 184865) (M := 14767) (k := 35)
      (by norm_num only) (analytic_cell_51_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 52. -/
theorem analytic_cell_52_primeCount (hRH : RiemannHypothesis) :
    16118 ≤ (203196 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 203196 18 12 (1222192630029 / 100000000000)
        (1222192631899 / 100000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (203196 : ℝ) ≤ (4507727 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((2 / 125) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 52, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_52_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((13933 / 20) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (75139 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 203196 18 12 (1222192630029 / 100000000000)
        (1222192631899 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 146533 17 12 (95160047469 / 8000000000)
        (743437871383 / 62500000000) =
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
  have hs : (57 : ℝ) * Real.log 203196 < (13933 / 20) := by linarith only [hlB]
  have hchoose : 146533 * 10 ^ 158 ≤ Nat.choose 16118 57 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 57)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((146533 : ℝ) * 10 ^ 158) ≤ Real.log (Nat.choose 16118 57 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (146533 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((75139 / 100) : ℝ) < 2 * Real.log (Nat.choose 16118 57 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 203196) (M := 16118) (k := 57) (by norm_num only)
      (analytic_cell_52_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 52, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_52_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((13933 / 20) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (75139 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 203196 18 12 (1222192630029 / 100000000000)
        (1222192631899 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 138148 17 12 (11836080848809 / 1000000000000)
        (1183608085731 / 100000000000) =
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
  have hs : (38 : ℝ) * Real.log 203196 ≤ (2 / 3 : ℝ) * (13933 / 20) := by linarith only [hlB]
  have hchoose : 138148 * 10 ^ 110 ≤ Nat.choose 16118 38 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 38)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((138148 : ℝ) * 10 ^ 110) ≤ Real.log (Nat.choose 16118 38 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (138148 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((75139 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 16118 38 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 203196) (M := 16118) (k := 38)
      (by norm_num only) (analytic_cell_52_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 53. -/
theorem analytic_cell_53_primeCount (hRH : RiemannHypothesis) :
    19595 ≤ (250860 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 250860 18 12 (12432650288899 / 1000000000000)
        (124326502979 / 10000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (250860 : ℝ) ≤ (5008593 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((7 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 53, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_53_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((75129 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (80851 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 250860 18 12 (12432650288899 / 1000000000000)
        (124326502979 / 10000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 370912 19 12 (12823719961439 / 1000000000000)
        (12823720295853 / 1000000000000) =
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
  have hs : (60 : ℝ) * Real.log 250860 < (75129 / 100) := by linarith only [hlB]
  have hchoose : 370912 * 10 ^ 170 ≤ Nat.choose 19595 60 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 60)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((370912 : ℝ) * 10 ^ 170) ≤ Real.log (Nat.choose 19595 60 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (370912 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((80851 / 100) : ℝ) < 2 * Real.log (Nat.choose 19595 60 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 250860) (M := 19595) (k := 60) (by norm_num only)
      (analytic_cell_53_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 53, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_53_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((75129 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (80851 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 250860 18 12 (12432650288899 / 1000000000000)
        (124326502979 / 10000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 571302 19 12 (2651134648111 / 200000000000)
        (1656959156257 / 125000000000) =
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
  have hs : (40 : ℝ) * Real.log 250860 ≤ (2 / 3 : ℝ) * (75129 / 100) := by linarith only [hlB]
  have hchoose : 571302 * 10 ^ 118 ≤ Nat.choose 19595 40 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 40)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((571302 : ℝ) * 10 ^ 118) ≤ Real.log (Nat.choose 19595 40 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (571302 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((80851 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 19595 40 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 250860) (M := 19595) (k := 40)
      (by norm_num only) (analytic_cell_53_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 54. -/
theorem analytic_cell_54_primeCount (hRH : RiemannHypothesis) :
    22448 ≤ (290456 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 290456 18 12 (49137528813 / 3906250000)
        (12579207385129 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (290456 : ℝ) ≤ (5389397 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((7 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 54, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_54_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((80841 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (8719 / 10)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 290456 18 12 (49137528813 / 3906250000)
        (12579207385129 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 215235 18 12 (6139742864277 / 500000000000)
        (491179429521 / 40000000000) =
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
  have hs : (64 : ℝ) * Real.log 290456 < (80841 / 100) := by linarith only [hlB]
  have hchoose : 215235 * 10 ^ 184 ≤ Nat.choose 22448 64 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 64)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((215235 : ℝ) * 10 ^ 184) ≤ Real.log (Nat.choose 22448 64 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (215235 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((8719 / 10) : ℝ) < 2 * Real.log (Nat.choose 22448 64 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 290456) (M := 22448) (k := 64) (by norm_num only)
      (analytic_cell_54_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 54, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_54_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((80841 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8719 / 10))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 290456 18 12 (49137528813 / 3906250000)
        (12579207385129 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 384694 19 12 (12860203444507 / 1000000000000)
        (6430101773063 / 500000000000) =
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
  have hs : (42 : ℝ) * Real.log 290456 ≤ (2 / 3 : ℝ) * (80841 / 100) := by linarith only [hlB]
  have hchoose : 384694 * 10 ^ 126 ≤ Nat.choose 22448 42 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 42)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((384694 : ℝ) * 10 ^ 126) ≤ Real.log (Nat.choose 22448 42 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (384694 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((8719 / 10) : ℝ) / 3 ≤ Real.log (Nat.choose 22448 42 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 290456) (M := 22448) (k := 42)
      (by norm_num only) (analytic_cell_54_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 55. -/
theorem analytic_cell_55_primeCount (hRH : RiemannHypothesis) :
    25825 ≤ (337793 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 337793 18 12 (12730188415001 / 1000000000000)
        (63650943473 / 5000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (337793 : ℝ) ≤ (5811997 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((7 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 55, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_55_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((4359 / 5) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (93753 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 337793 18 12 (12730188415001 / 1000000000000)
        (63650943473 / 5000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 385427 19 12 (803881690309 / 62500000000)
        (2572421428061 / 200000000000) =
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
  have hs : (68 : ℝ) * Real.log 337793 < (4359 / 5) := by linarith only [hlB]
  have hchoose : 385427 * 10 ^ 198 ≤ Nat.choose 25825 68 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 68)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((385427 : ℝ) * 10 ^ 198) ≤ Real.log (Nat.choose 25825 68 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (385427 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((93753 / 100) : ℝ) < 2 * Real.log (Nat.choose 25825 68 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 337793) (M := 25825) (k := 68) (by norm_num only)
      (analytic_cell_55_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 55, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_55_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((4359 / 5) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (93753 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 337793 18 12 (12730188415001 / 1000000000000)
        (63650943473 / 5000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 280120 18 12 (1254297335709 / 100000000000)
        (12542973366091 / 1000000000000) =
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
  have hs : (45 : ℝ) * Real.log 337793 ≤ (2 / 3 : ℝ) * (4359 / 5) := by linarith only [hlB]
  have hchoose : 280120 * 10 ^ 137 ≤ Nat.choose 25825 45 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 45)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((280120 : ℝ) * 10 ^ 137) ≤ Real.log (Nat.choose 25825 45 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (280120 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((93753 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 25825 45 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 337793) (M := 25825) (k := 45)
      (by norm_num only) (analytic_cell_55_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 56. -/
theorem analytic_cell_56_primeCount (hRH : RiemannHypothesis) :
    28639 ≤ (377568 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 377568 19 12 (12841505876029 / 1000000000000)
        (642075303241 / 50000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (377568 : ℝ) ≤ (6144657 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((13 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 56, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_56_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((93743 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (101159 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 377568 19 12 (12841505876029 / 1000000000000)
        (642075303241 / 50000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 465284 19 12 (3262600811471 / 250000000000)
        (6525201627693 / 500000000000) =
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
  have hs : (73 : ℝ) * Real.log 377568 < (93743 / 100) := by linarith only [hlB]
  have hchoose : 465284 * 10 ^ 214 ≤ Nat.choose 28639 73 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 73)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((465284 : ℝ) * 10 ^ 214) ≤ Real.log (Nat.choose 28639 73 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (465284 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((101159 / 100) : ℝ) < 2 * Real.log (Nat.choose 28639 73 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 377568) (M := 28639) (k := 73) (by norm_num only)
      (analytic_cell_56_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 56, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_56_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((93743 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (101159 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 377568 19 12 (12841505876029 / 1000000000000)
        (642075303241 / 50000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 665201 19 12 (1675980558761 / 125000000000)
        (2681568916809 / 200000000000) =
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
  have hs : (48 : ℝ) * Real.log 377568 ≤ (2 / 3 : ℝ) * (93743 / 100) := by linarith only [hlB]
  have hchoose : 665201 * 10 ^ 147 ≤ Nat.choose 28639 48 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 48)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((665201 : ℝ) * 10 ^ 147) ≤ Real.log (Nat.choose 28639 48 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (665201 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((101159 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 28639 48 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 377568) (M := 28639) (k := 48)
      (by norm_num only) (analytic_cell_56_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 57. -/
theorem analytic_cell_57_primeCount (hRH : RiemannHypothesis) :
    32205 ≤ (428403 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 428403 19 12 (12967819615103 / 1000000000000)
        (12967819625231 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (428403 : ℝ) ≤ (6545251 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((13 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 57, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_57_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((101149 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (54461 / 50)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 428403 19 12 (12967819615103 / 1000000000000)
        (12967819625231 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 333793 18 12 (6359138123193 / 500000000000)
        (3179569096531 / 250000000000) =
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
  have hs : (78 : ℝ) * Real.log 428403 < (101149 / 100) := by linarith only [hlB]
  have hchoose : 333793 * 10 ^ 231 ≤ Nat.choose 32205 78 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 78)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((333793 : ℝ) * 10 ^ 231) ≤ Real.log (Nat.choose 32205 78 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (333793 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((54461 / 50) : ℝ) < 2 * Real.log (Nat.choose 32205 78 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 428403) (M := 32205) (k := 78) (by norm_num only)
      (analytic_cell_57_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 57, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_57_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((101149 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (54461 / 50))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 428403 19 12 (12967819615103 / 1000000000000)
        (12967819625231 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 307236 18 12 (12635371456063 / 1000000000000)
        (12635371465343 / 1000000000000) =
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
  have hs : (52 : ℝ) * Real.log 428403 ≤ (2 / 3 : ℝ) * (101149 / 100) := by linarith only [hlB]
  have hchoose : 307236 * 10 ^ 161 ≤ Nat.choose 32205 52 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 52)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((307236 : ℝ) * 10 ^ 161) ≤ Real.log (Nat.choose 32205 52 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (307236 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((54461 / 50) : ℝ) / 3 ≤ Real.log (Nat.choose 32205 52 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 428403) (M := 32205) (k := 52)
      (by norm_num only) (analytic_cell_57_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 58. -/
theorem analytic_cell_58_primeCount (hRH : RiemannHypothesis) : 98 ≤ (785 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 785 10 12 (3332841853913 / 500000000000)
        (6665683728739 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (785 : ℝ) ≤ (280179 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((2 / 25) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 58, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_58_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : (50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5409 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 785 10 12 (3332841853913 / 500000000000)
        (6665683728739 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 679108 19 12 (3357133813583 / 250000000000)
        (839283477017 / 62500000000) =
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
  have hs : (5 : ℝ) * Real.log 785 ≤ (2 / 3 : ℝ) * 50 := by linarith only [hlB]
  have hchoose : 679108 * 10 ^ 2 ≤ Nat.choose 98 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((679108 : ℝ) * 10 ^ 2) ≤ Real.log (Nat.choose 98 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (679108 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((5409 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 98 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 785) (M := 98) (k := 5) (by norm_num only)
      (analytic_cell_58_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 59. -/
theorem analytic_cell_59_primeCount (hRH : RiemannHypothesis) : 156 ≤ (1295 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1295 10 12 (3583132963561 / 500000000000)
        (7166266017087 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1295 : ℝ) ≤ (179931 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((67 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 59, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_59_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((5399 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3059 / 50))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1295 10 12 (3583132963561 / 500000000000)
        (7166266017087 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 721656 20 12 (13489303491209 / 1000000000000)
        (3372326066367 / 250000000000) =
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
  have hs : (5 : ℝ) * Real.log 1295 ≤ (2 / 3 : ℝ) * (5399 / 100) := by linarith only [hlB]
  have hchoose : 721656 * 10 ^ 3 ≤ Nat.choose 156 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((721656 : ℝ) * 10 ^ 3) ≤ Real.log (Nat.choose 156 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (721656 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3059 / 50) : ℝ) / 3 ≤ Real.log (Nat.choose 156 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1295) (M := 156) (k := 5) (by norm_num only)
      (analytic_cell_59_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 60. -/
theorem analytic_cell_60_primeCount (hRH : RiemannHypothesis) : 257 ≤ (2232 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 2232 11 12 (7710653320641 / 1000000000000)
        (3855326663071 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (2232 : ℝ) ≤ (472441 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((7 / 125) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 60, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_60_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((7087 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1599 / 20))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2232 11 12 (7710653320641 / 1000000000000)
        (3855326663071 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 377342 19 12 (12840907127413 / 1000000000000)
        (6420453659969 / 500000000000) =
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
  have hs : (6 : ℝ) * Real.log 2232 ≤ (2 / 3 : ℝ) * (7087 / 100) := by linarith only [hlB]
  have hchoose : 377342 * 10 ^ 6 ≤ Nat.choose 257 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((377342 : ℝ) * 10 ^ 6) ≤ Real.log (Nat.choose 257 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (377342 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((1599 / 20) : ℝ) / 3 ≤ Real.log (Nat.choose 257 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 2232) (M := 257) (k := 6) (by norm_num only)
      (analytic_cell_60_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
