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

/-- RH supplies the certified prime count for analytic cell 21. -/
theorem analytic_cell_21_primeCount (hRH : RiemannHypothesis) : 308 ≤ (2729 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 2729 11 12 (3955844785913 / 500000000000)
        (7911691397927 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (2729 : ℝ) ≤ (522399 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((13 / 250) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 21, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_21_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((8703 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (2267 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2729 11 12 (3955844785913 / 500000000000)
        (7911691397927 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 494826 19 12 (819497591229 / 62500000000)
        (2622392293833 / 200000000000) =
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
  have hs : (11 : ℝ) * Real.log 2729 < (8703 / 100) := by linarith only [hlB]
  have hchoose : 494826 * 10 ^ 14 ≤ Nat.choose 308 11 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 11)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((494826 : ℝ) * 10 ^ 14) ≤ Real.log (Nat.choose 308 11 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (494826 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2267 / 25) : ℝ) < 2 * Real.log (Nat.choose 308 11 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 2729) (M := 308) (k := 11) (by norm_num only)
      (analytic_cell_21_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 21, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_21_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((8703 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2267 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 2729 11 12 (3955844785913 / 500000000000)
        (7911691397927 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 487083 19 12 (2619237962763 / 200000000000)
        (3274047455829 / 250000000000) =
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
  have hs : (7 : ℝ) * Real.log 2729 ≤ (2 / 3 : ℝ) * (8703 / 100) := by linarith only [hlB]
  have hchoose : 487083 * 10 ^ 8 ≤ Nat.choose 308 7 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 7)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((487083 : ℝ) * 10 ^ 8) ≤ Real.log (Nat.choose 308 7 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (487083 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2267 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 308 7 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 2729) (M := 308) (k := 7) (by norm_num only)
      (analytic_cell_21_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 22. -/
theorem analytic_cell_22_primeCount (hRH : RiemannHypothesis) : 402 ≤ (3646 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 3646 12 12 (4100692976059 / 500000000000)
        (205034648953 / 25000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (3646 : ℝ) ≤ (301911 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((6 / 125) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 22, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_22_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((4529 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (9663 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 3646 12 12 (4100692976059 / 500000000000)
        (205034648953 / 25000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 966914 20 12 (13781864830431 / 1000000000000)
        (861366552527 / 62500000000) =
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
  have hs : (11 : ℝ) * Real.log 3646 < (4529 / 50) := by linarith only [hlB]
  have hchoose : 966914 * 10 ^ 15 ≤ Nat.choose 402 11 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 11)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((966914 : ℝ) * 10 ^ 15) ≤ Real.log (Nat.choose 402 11 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (966914 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((9663 / 100) : ℝ) < 2 * Real.log (Nat.choose 402 11 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 3646) (M := 402) (k := 11) (by norm_num only)
      (analytic_cell_22_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 22, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_22_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((4529 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (9663 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 3646 12 12 (4100692976059 / 500000000000)
        (205034648953 / 25000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 319404 18 12 (506968481201 / 40000000000)
        (633710602281 / 50000000000) =
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
  have hs : (7 : ℝ) * Real.log 3646 ≤ (2 / 3 : ℝ) * (4529 / 50) := by linarith only [hlB]
  have hchoose : 319404 * 10 ^ 9 ≤ Nat.choose 402 7 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 7)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((319404 : ℝ) * 10 ^ 9) ≤ Real.log (Nat.choose 402 7 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (319404 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((9663 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 402 7 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 3646) (M := 402) (k := 7) (by norm_num only)
      (analytic_cell_22_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 23. -/
theorem analytic_cell_23_primeCount (hRH : RiemannHypothesis) : 348 ≤ (3115 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 3115 12 12 (125687256527 / 15625000000)
        (1608796889233 / 200000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (3115 : ℝ) ≤ (279061 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((1 / 20) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 23, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_23_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((9653 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (2502 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 3115 12 12 (125687256527 / 15625000000)
        (1608796889233 / 200000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 543657 19 12 (2641214761467 / 200000000000)
        (3301518454209 / 250000000000) =
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
  have hs : (12 : ℝ) * Real.log 3115 < (9653 / 100) := by linarith only [hlB]
  have hchoose : 543657 * 10 ^ 16 ≤ Nat.choose 348 12 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 12)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((543657 : ℝ) * 10 ^ 16) ≤ Real.log (Nat.choose 348 12 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (543657 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2502 / 25) : ℝ) < 2 * Real.log (Nat.choose 348 12 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 3115) (M := 348) (k := 12) (by norm_num only)
      (analytic_cell_23_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 23, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_23_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((9653 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2502 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 3115 12 12 (125687256527 / 15625000000)
        (1608796889233 / 200000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 491944 19 12 (13106120162919 / 1000000000000)
        (655306008621 / 50000000000) =
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
  have hs : (8 : ℝ) * Real.log 3115 ≤ (2 / 3 : ℝ) * (9653 / 100) := by linarith only [hlB]
  have hchoose : 491944 * 10 ^ 10 ≤ Nat.choose 348 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((491944 : ℝ) * 10 ^ 10) ≤ Real.log (Nat.choose 348 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (491944 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2502 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 348 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 3115) (M := 348) (k := 8) (by norm_num only)
      (analytic_cell_23_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 24. -/
theorem analytic_cell_24_primeCount (hRH : RiemannHypothesis) : 453 ≤ (4153 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 4153 12 12 (8331586240511 / 1000000000000)
        (520724140407 / 62500000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (4153 : ℝ) ≤ (322219 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((23 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 24, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_24_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((4999 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (213 / 2)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 4153 12 12 (8331586240511 / 1000000000000)
        (520724140407 / 62500000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 134593 17 12 (11810010684477 / 1000000000000)
        (5905005346489 / 500000000000) =
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
  have hs : (12 : ℝ) * Real.log 4153 < (4999 / 50) := by linarith only [hlB]
  have hchoose : 134593 * 10 ^ 18 ≤ Nat.choose 453 12 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 12)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((134593 : ℝ) * 10 ^ 18) ≤ Real.log (Nat.choose 453 12 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (134593 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((213 / 2) : ℝ) < 2 * Real.log (Nat.choose 453 12 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 4153) (M := 453) (k := 12) (by norm_num only)
      (analytic_cell_24_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 24, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_24_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((4999 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (213 / 2))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 4153 12 12 (8331586240511 / 1000000000000)
        (520724140407 / 62500000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 413306 19 12 (2586388702149 / 200000000000)
        (12931943524593 / 1000000000000) =
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
  have hs : (8 : ℝ) * Real.log 4153 ≤ (2 / 3 : ℝ) * (4999 / 50) := by linarith only [hlB]
  have hchoose : 413306 * 10 ^ 11 ≤ Nat.choose 453 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((413306 : ℝ) * 10 ^ 11) ≤ Real.log (Nat.choose 453 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (413306 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((213 / 2) : ℝ) / 3 ≤ Real.log (Nat.choose 453 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 4153) (M := 453) (k := 8) (by norm_num only)
      (analytic_cell_24_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 25. -/
theorem analytic_cell_25_primeCount (hRH : RiemannHypothesis) : 539 ≤ (5031 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 5031 12 12 (213084351029 / 25000000000)
        (2130843514751 / 250000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (5031 : ℝ) ≤ (44331 / 625) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((43 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 25, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_25_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((532 / 5) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (2768 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 5031 12 12 (213084351029 / 25000000000)
        (2130843514751 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 110960 17 12 (11616925050541 / 1000000000000)
        (11616925059103 / 1000000000000) =
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
  have hs : (12 : ℝ) * Real.log 5031 < (532 / 5) := by linarith only [hlB]
  have hchoose : 110960 * 10 ^ 19 ≤ Nat.choose 539 12 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 12)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((110960 : ℝ) * 10 ^ 19) ≤ Real.log (Nat.choose 539 12 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (110960 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2768 / 25) : ℝ) < 2 * Real.log (Nat.choose 539 12 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 5031) (M := 539) (k := 12) (by norm_num only)
      (analytic_cell_25_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 25, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_25_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((532 / 5) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2768 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 5031 12 12 (213084351029 / 25000000000)
        (2130843514751 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 167696 17 12 (6014953999647 / 500000000000)
        (2405981636691 / 200000000000) =
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
  have hs : (8 : ℝ) * Real.log 5031 ≤ (2 / 3 : ℝ) * (532 / 5) := by linarith only [hlB]
  have hchoose : 167696 * 10 ^ 12 ≤ Nat.choose 539 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((167696 : ℝ) * 10 ^ 12) ≤ Real.log (Nat.choose 539 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (167696 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2768 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 539 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 5031) (M := 539) (k := 8) (by norm_num only)
      (analytic_cell_25_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 26. -/
theorem analytic_cell_26_primeCount (hRH : RiemannHypothesis) : 532 ≤ (4960 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 4960 12 12 (8509161014419 / 1000000000000)
        (8509161024569 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (4960 : ℝ) ≤ (704273 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((43 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 26, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_26_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((5531 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (5889 / 50)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 4960 12 12 (8509161014419 / 1000000000000)
        (8509161024569 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 378783 19 12 (1284471868159 / 100000000000)
        (6422359425747 / 500000000000) =
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
  have hs : (13 : ℝ) * Real.log 4960 < (5531 / 50) := by linarith only [hlB]
  have hchoose : 378783 * 10 ^ 20 ≤ Nat.choose 532 13 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 13)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((378783 : ℝ) * 10 ^ 20) ≤ Real.log (Nat.choose 532 13 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (378783 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((5889 / 50) : ℝ) < 2 * Real.log (Nat.choose 532 13 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 4960) (M := 532) (k := 13) (by norm_num only)
      (analytic_cell_26_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 26, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_26_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((5531 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5889 / 50))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 4960 12 12 (8509161014419 / 1000000000000)
        (8509161024569 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 150940 17 12 (11924637681391 / 1000000000000)
        (2384927537989 / 200000000000) =
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
  have hs : (8 : ℝ) * Real.log 4960 ≤ (2 / 3 : ℝ) * (5531 / 50) := by linarith only [hlB]
  have hchoose : 150940 * 10 ^ 12 ≤ Nat.choose 532 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((150940 : ℝ) * 10 ^ 12) ≤ Real.log (Nat.choose 532 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (150940 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((5889 / 50) : ℝ) / 3 ≤ Real.log (Nat.choose 532 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 4960) (M := 532) (k := 8) (by norm_num only)
      (analytic_cell_26_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 27. -/
theorem analytic_cell_27_primeCount (hRH : RiemannHypothesis) : 648 ≤ (6154 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 6154 13 12 (1090607191911 / 125000000000)
        (1090607197377 / 125000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (6154 : ℝ) ≤ (31379 / 400) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((41 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 27, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_27_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((2942 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (3074 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 6154 13 12 (1090607191911 / 125000000000)
        (1090607197377 / 125000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 505334 19 12 (13132974870837 / 1000000000000)
        (6566487440169 / 500000000000) =
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
  have hs : (13 : ℝ) * Real.log 6154 < (2942 / 25) := by linarith only [hlB]
  have hchoose : 505334 * 10 ^ 21 ≤ Nat.choose 648 13 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 13)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((505334 : ℝ) * 10 ^ 21) ≤ Real.log (Nat.choose 648 13 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (505334 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3074 / 25) : ℝ) < 2 * Real.log (Nat.choose 648 13 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 6154) (M := 648) (k := 13) (by norm_num only)
      (analytic_cell_27_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 27, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_27_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((2942 / 25) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3074 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 6154 13 12 (1090607191911 / 125000000000)
        (1090607197377 / 125000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 738313 20 12 (13512122952599 / 1000000000000)
        (1689015417639 / 125000000000) =
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
  have hs : (8 : ℝ) * Real.log 6154 ≤ (2 / 3 : ℝ) * (2942 / 25) := by linarith only [hlB]
  have hchoose : 738313 * 10 ^ 12 ≤ Nat.choose 648 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((738313 : ℝ) * 10 ^ 12) ≤ Real.log (Nat.choose 648 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (738313 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3074 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 648 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 6154) (M := 648) (k := 8) (by norm_num only)
      (analytic_cell_27_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 28. -/
theorem analytic_cell_28_primeCount (hRH : RiemannHypothesis) : 679 ≤ (6475 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 6475 13 12 (4387851940713 / 500000000000)
        (8775703891739 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (6475 : ℝ) ≤ (402337 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((1 / 25) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 28, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_28_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((6143 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (13191 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 6475 13 12 (4387851940713 / 500000000000)
        (8775703891739 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 443786 19 12 (13003097738273 / 1000000000000)
        (13003097747837 / 1000000000000) =
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
  have hs : (14 : ℝ) * Real.log 6475 < (6143 / 50) := by linarith only [hlB]
  have hchoose : 443786 * 10 ^ 23 ≤ Nat.choose 679 14 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 14)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((443786 : ℝ) * 10 ^ 23) ≤ Real.log (Nat.choose 679 14 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (443786 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((13191 / 100) : ℝ) < 2 * Real.log (Nat.choose 679 14 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 6475) (M := 679) (k := 14) (by norm_num only)
      (analytic_cell_28_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 28, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_28_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((6143 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13191 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 6475 13 12 (4387851940713 / 500000000000)
        (8775703891739 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 801571 20 12 (1699291102187 / 125000000000)
        (849645552843 / 62500000000) =
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
  have hs : (9 : ℝ) * Real.log 6475 ≤ (2 / 3 : ℝ) * (6143 / 50) := by linarith only [hlB]
  have hchoose : 801571 * 10 ^ 14 ≤ Nat.choose 679 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((801571 : ℝ) * 10 ^ 14) ≤ Real.log (Nat.choose 679 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (801571 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((13191 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 679 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 6475) (M := 679) (k := 9) (by norm_num only)
      (analytic_cell_28_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 29. -/
theorem analytic_cell_29_primeCount (hRH : RiemannHypothesis) : 686 ≤ (6550 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 6550 13 12 (351488812971 / 40000000000)
        (2196805083221 / 250000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (6550 : ℝ) ≤ (809321 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((1 / 25) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 29, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_29_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((13181 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (699 / 5)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 6550 13 12 (351488812971 / 40000000000)
        (2196805083221 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 229834 18 12 (2469022516703 / 200000000000)
        (12345112592519 / 1000000000000) =
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
  have hs : (15 : ℝ) * Real.log 6550 < (13181 / 100) := by linarith only [hlB]
  have hchoose : 229834 * 10 ^ 25 ≤ Nat.choose 686 15 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 15)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((229834 : ℝ) * 10 ^ 25) ≤ Real.log (Nat.choose 686 15 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (229834 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((699 / 5) : ℝ) < 2 * Real.log (Nat.choose 686 15 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 6550) (M := 686) (k := 15) (by norm_num only)
      (analytic_cell_29_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 29, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_29_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((13181 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (699 / 5))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 6550 13 12 (351488812971 / 40000000000)
        (2196805083221 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 595466 19 12 (13297099566323 / 1000000000000)
        (13297099575837 / 1000000000000) =
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
  have hs : (10 : ℝ) * Real.log 6550 ≤ (2 / 3 : ℝ) * (13181 / 100) := by linarith only [hlB]
  have hchoose : 595466 * 10 ^ 16 ≤ Nat.choose 686 10 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 10)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((595466 : ℝ) * 10 ^ 16) ≤ Real.log (Nat.choose 686 10 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (595466 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((699 / 5) : ℝ) / 3 ≤ Real.log (Nat.choose 686 10 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 6550) (M := 686) (k := 10) (by norm_num only)
      (analytic_cell_29_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 30. -/
theorem analytic_cell_30_primeCount (hRH : RiemannHypothesis) : 886 ≤ (8673 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 8673 13 12 (1813594005461 / 200000000000)
        (4533985016903 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (8673 : ℝ) ≤ (93129 / 1000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((37 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 30, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_30_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((1397 / 10) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (2951 / 20)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 8673 13 12 (1813594005461 / 200000000000)
        (4533985016903 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 110472 17 12 (5806258684853 / 500000000000)
        (2903129344573 / 250000000000) =
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
  have hs : (15 : ℝ) * Real.log 8673 < (1397 / 10) := by linarith only [hlB]
  have hchoose : 110472 * 10 ^ 27 ≤ Nat.choose 886 15 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 15)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((110472 : ℝ) * 10 ^ 27) ≤ Real.log (Nat.choose 886 15 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (110472 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2951 / 20) : ℝ) < 2 * Real.log (Nat.choose 886 15 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 8673) (M := 886) (k := 15) (by norm_num only)
      (analytic_cell_30_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 30, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_30_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((1397 / 10) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2951 / 20))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 8673 13 12 (1813594005461 / 200000000000)
        (4533985016903 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 780615 20 12 (13567837319707 / 1000000000000)
        (13567837382959 / 1000000000000) =
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
  have hs : (10 : ℝ) * Real.log 8673 ≤ (2 / 3 : ℝ) * (1397 / 10) := by linarith only [hlB]
  have hchoose : 780615 * 10 ^ 17 ≤ Nat.choose 886 10 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 10)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((780615 : ℝ) * 10 ^ 17) ≤ Real.log (Nat.choose 886 10 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (780615 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((2951 / 20) : ℝ) / 3 ≤ Real.log (Nat.choose 886 10 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 8673) (M := 886) (k := 10) (by norm_num only)
      (analytic_cell_30_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
