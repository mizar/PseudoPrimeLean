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

/-- RH supplies the certified prime count for analytic cell 41. -/
theorem analytic_cell_41_primeCount (hRH : RiemannHypothesis) :
    3593 ≤ (39954 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 39954 15 12 (1059548406379 / 100000000000)
        (5297742039121 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (39954 : ℝ) ≤ (39977 / 200) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((3 / 125) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 41, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_41_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((29983 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6449 / 20)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 39954 15 12 (1059548406379 / 100000000000)
        (5297742039121 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 105403 17 12 (5782773186273 / 500000000000)
        (5782773191299 / 500000000000) =
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
  have hs : (28 : ℝ) * Real.log 39954 < (29983 / 100) := by linarith only [hlB]
  have hchoose : 105403 * 10 ^ 65 ≤ Nat.choose 3593 28 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 28)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((105403 : ℝ) * 10 ^ 65) ≤ Real.log (Nat.choose 3593 28 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (105403 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6449 / 20) : ℝ) < 2 * Real.log (Nat.choose 3593 28 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 39954) (M := 3593) (k := 28) (by norm_num only)
      (analytic_cell_41_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 41, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_41_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((29983 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6449 / 20))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 39954 15 12 (1059548406379 / 100000000000)
        (5297742039121 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 149061 17 12 (5956055446347 / 500000000000)
        (11912110901209 / 1000000000000) =
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
  have hs : (18 : ℝ) * Real.log 39954 ≤ (2 / 3 : ℝ) * (29983 / 100) := by linarith only [hlB]
  have hchoose : 149061 * 10 ^ 43 ≤ Nat.choose 3593 18 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 18)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((149061 : ℝ) * 10 ^ 43) ≤ Real.log (Nat.choose 3593 18 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (149061 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6449 / 20) : ℝ) / 3 ≤ Real.log (Nat.choose 3593 18 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 39954) (M := 3593) (k := 18)
      (by norm_num only) (analytic_cell_41_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 42. -/
theorem analytic_cell_42_primeCount (hRH : RiemannHypothesis) :
    4105 ≤ (46182 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 46182 16 12 (5370172607987 / 500000000000)
        (5370172796399 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (46182 : ℝ) ≤ (2149 / 10) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((23 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 42, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_42_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((6447 / 20) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6993 / 20)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 46182 16 12 (5370172607987 / 500000000000)
        (5370172796399 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 850359 20 12 (6826706943297 / 500000000000)
        (2730682779513 / 200000000000) =
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
  have hs : (30 : ℝ) * Real.log 46182 < (6447 / 20) := by linarith only [hlB]
  have hchoose : 850359 * 10 ^ 70 ≤ Nat.choose 4105 30 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 30)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((850359 : ℝ) * 10 ^ 70) ≤ Real.log (Nat.choose 4105 30 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (850359 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6993 / 20) : ℝ) < 2 * Real.log (Nat.choose 4105 30 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 46182) (M := 4105) (k := 30) (by norm_num only)
      (analytic_cell_42_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 42, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_42_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((6447 / 20) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6993 / 20))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 46182 16 12 (5370172607987 / 500000000000)
        (5370172796399 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 724444 20 12 (539726376909 / 40000000000)
        (6746580056913 / 500000000000) =
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
  have hs : (20 : ℝ) * Real.log 46182 ≤ (2 / 3 : ℝ) * (6447 / 20) := by linarith only [hlB]
  have hchoose : 724444 * 10 ^ 48 ≤ Nat.choose 4105 20 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 20)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((724444 : ℝ) * 10 ^ 48) ≤ Real.log (Nat.choose 4105 20 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (724444 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6993 / 20) : ℝ) / 3 ≤ Real.log (Nat.choose 4105 20 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 46182) (M := 4105) (k := 20)
      (by norm_num only) (analytic_cell_42_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 43. -/
theorem analytic_cell_43_primeCount (hRH : RiemannHypothesis) :
    4765 ≤ (54304 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 54304 16 12 (1362794145469 / 125000000000)
        (5451176586009 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (54304 : ℝ) ≤ (1165161 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((11 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 43, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_43_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((6991 / 20) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (9467 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 54304 16 12 (1362794145469 / 125000000000)
        (5451176586009 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 170818 17 12 (376511051959 / 31250000000)
        (2409670839473 / 200000000000) =
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
  have hs : (32 : ℝ) * Real.log 54304 < (6991 / 20) := by linarith only [hlB]
  have hchoose : 170818 * 10 ^ 77 ≤ Nat.choose 4765 32 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 32)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((170818 : ℝ) * 10 ^ 77) ≤ Real.log (Nat.choose 4765 32 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (170818 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((9467 / 25) : ℝ) < 2 * Real.log (Nat.choose 4765 32 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 54304) (M := 4765) (k := 32) (by norm_num only)
      (analytic_cell_43_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 43, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_43_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((6991 / 20) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (9467 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 54304 16 12 (1362794145469 / 125000000000)
        (5451176586009 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 324944 18 12 (6345704061149 / 500000000000)
        (3172852038453 / 250000000000) =
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
  have hs : (21 : ℝ) * Real.log 54304 ≤ (2 / 3 : ℝ) * (6991 / 20) := by linarith only [hlB]
  have hchoose : 324944 * 10 ^ 52 ≤ Nat.choose 4765 21 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 21)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((324944 : ℝ) * 10 ^ 52) ≤ Real.log (Nat.choose 4765 21 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (324944 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((9467 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 4765 21 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 54304) (M := 4765) (k := 21)
      (by norm_num only) (analytic_cell_43_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 44. -/
theorem analytic_cell_44_primeCount (hRH : RiemannHypothesis) :
    5519 ≤ (63699 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 63699 16 12 (1106192413869 / 100000000000)
        (11061924146691 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (63699 : ℝ) ≤ (2523867 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((21 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 44, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_44_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((18929 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (817 / 2)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 63699 16 12 (1106192413869 / 100000000000)
        (11061924146691 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 511509 19 12 (13145120454587 / 1000000000000)
        (1643140058011 / 125000000000) =
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
  have hs : (34 : ℝ) * Real.log 63699 < (18929 / 50) := by linarith only [hlB]
  have hchoose : 511509 * 10 ^ 83 ≤ Nat.choose 5519 34 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 34)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((511509 : ℝ) * 10 ^ 83) ≤ Real.log (Nat.choose 5519 34 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (511509 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((817 / 2) : ℝ) < 2 * Real.log (Nat.choose 5519 34 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 63699) (M := 5519) (k := 34) (by norm_num only)
      (analytic_cell_44_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 44, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_44_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((18929 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (817 / 2))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 63699 16 12 (1106192413869 / 100000000000)
        (11061924146691 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 178632 18 12 (12093082625233 / 1000000000000)
        (12093083655943 / 1000000000000) =
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
  have hs : (22 : ℝ) * Real.log 63699 ≤ (2 / 3 : ℝ) * (18929 / 50) := by linarith only [hlB]
  have hchoose : 178632 * 10 ^ 56 ≤ Nat.choose 5519 22 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 22)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((178632 : ℝ) * 10 ^ 56) ≤ Real.log (Nat.choose 5519 22 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (178632 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((817 / 2) : ℝ) / 3 ≤ Real.log (Nat.choose 5519 22 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 63699) (M := 5519) (k := 22)
      (by norm_num only) (analytic_cell_44_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 45. -/
theorem analytic_cell_45_primeCount (hRH : RiemannHypothesis) :
    6347 ≤ (74129 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 74129 16 12 (11213562093581 / 1000000000000)
        (1121356210159 / 100000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (74129 : ℝ) ≤ (544533 / 2000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((1 / 50) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 45, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_45_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((2042 / 5) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (10969 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 74129 16 12 (11213562093581 / 1000000000000)
        (1121356210159 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 189995 18 12 (12154752963961 / 1000000000000)
        (6077376558223 / 500000000000) =
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
  have hs : (36 : ℝ) * Real.log 74129 < (2042 / 5) := by linarith only [hlB]
  have hchoose : 189995 * 10 ^ 90 ≤ Nat.choose 6347 36 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 36)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((189995 : ℝ) * 10 ^ 90) ≤ Real.log (Nat.choose 6347 36 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (189995 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((10969 / 25) : ℝ) < 2 * Real.log (Nat.choose 6347 36 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 74129) (M := 6347) (k := 36) (by norm_num only)
      (analytic_cell_45_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 45, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_45_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((2042 / 5) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10969 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 74129 16 12 (11213562093581 / 1000000000000)
        (1121356210159 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 281857 18 12 (12549155124427 / 1000000000000)
        (3137288783357 / 250000000000) =
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
  have hs : (24 : ℝ) * Real.log 74129 ≤ (2 / 3 : ℝ) * (2042 / 5) := by linarith only [hlB]
  have hchoose : 281857 * 10 ^ 62 ≤ Nat.choose 6347 24 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 24)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((281857 : ℝ) * 10 ^ 62) ≤ Real.log (Nat.choose 6347 24 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (281857 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((10969 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 6347 24 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 74129) (M := 6347) (k := 24)
      (by norm_num only) (analytic_cell_45_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 46. -/
theorem analytic_cell_46_primeCount (hRH : RiemannHypothesis) :
    6550 ≤ (76702 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 76702 16 12 (2249536611669 / 200000000000)
        (351490095831 / 31250000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (76702 : ℝ) ≤ (2769513 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((1 / 50) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 46, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_46_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((21933 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (4719 / 10)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 76702 16 12 (2249536611669 / 200000000000)
        (351490095831 / 31250000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 298261 18 12 (12605724216403 / 1000000000000)
        (12605724225419 / 1000000000000) =
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
  have hs : (39 : ℝ) * Real.log 76702 < (21933 / 50) := by linarith only [hlB]
  have hchoose : 298261 * 10 ^ 97 ≤ Nat.choose 6550 39 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 39)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((298261 : ℝ) * 10 ^ 97) ≤ Real.log (Nat.choose 6550 39 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (298261 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((4719 / 10) : ℝ) < 2 * Real.log (Nat.choose 6550 39 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 76702) (M := 6550) (k := 39) (by norm_num only)
      (analytic_cell_46_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 46, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_46_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((21933 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4719 / 10))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 76702 16 12 (2249536611669 / 200000000000)
        (351490095831 / 31250000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 393620 19 12 (1610392654163 / 125000000000)
        (12883141280939 / 1000000000000) =
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
  have hs : (26 : ℝ) * Real.log 76702 ≤ (2 / 3 : ℝ) * (21933 / 50) := by linarith only [hlB]
  have hchoose : 393620 * 10 ^ 67 ≤ Nat.choose 6550 26 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 26)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((393620 : ℝ) * 10 ^ 67) ≤ Real.log (Nat.choose 6550 26 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (393620 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((4719 / 10) : ℝ) / 3 ≤ Real.log (Nat.choose 6550 26 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 76702) (M := 6550) (k := 26)
      (by norm_num only) (analytic_cell_46_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 47. -/
theorem analytic_cell_47_primeCount (hRH : RiemannHypothesis) :
    8284 ≤ (98931 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 98931 17 12 (11502177897801 / 1000000000000)
        (11502177937017 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (98931 : ℝ) ≤ (314533 / 1000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((9 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 47, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_47_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((2359 / 5) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (51153 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 98931 17 12 (11502177897801 / 1000000000000)
        (11502177937017 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 120324 17 12 (2924485844723 / 250000000000)
        (11697943387393 / 1000000000000) =
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
  have hs : (41 : ℝ) * Real.log 98931 < (2359 / 5) := by linarith only [hlB]
  have hchoose : 120324 * 10 ^ 106 ≤ Nat.choose 8284 41 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 41)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((120324 : ℝ) * 10 ^ 106) ≤ Real.log (Nat.choose 8284 41 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (120324 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((51153 / 100) : ℝ) < 2 * Real.log (Nat.choose 8284 41 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 98931) (M := 8284) (k := 41) (by norm_num only)
      (analytic_cell_47_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 47, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_47_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((2359 / 5) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (51153 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 98931 17 12 (11502177897801 / 1000000000000)
        (11502177937017 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 545856 19 12 (13210110478739 / 1000000000000)
        (165126381103 / 12500000000) =
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
  have hs : (27 : ℝ) * Real.log 98931 ≤ (2 / 3 : ℝ) * (2359 / 5) := by linarith only [hlB]
  have hchoose : 545856 * 10 ^ 72 ≤ Nat.choose 8284 27 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 27)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((545856 : ℝ) * 10 ^ 72) ≤ Real.log (Nat.choose 8284 27 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (545856 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((51153 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 8284 27 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 98931) (M := 8284) (k := 27)
      (by norm_num only) (analytic_cell_47_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 48. -/
theorem analytic_cell_48_primeCount (hRH : RiemannHypothesis) :
    9265 ≤ (111681 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 111681 17 12 (5811700933837 / 500000000000)
        (11623401876213 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (111681 : ℝ) ≤ (3341871 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((9 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 48, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_48_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((51143 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (27647 / 50)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 111681 17 12 (5811700933837 / 500000000000)
        (11623401876213 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 118082 17 12 (11679134572941 / 1000000000000)
        (5839567290721 / 500000000000) =
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
  have hs : (44 : ℝ) * Real.log 111681 < (51143 / 100) := by linarith only [hlB]
  have hchoose : 118082 * 10 ^ 115 ≤ Nat.choose 9265 44 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 44)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((118082 : ℝ) * 10 ^ 115) ≤ Real.log (Nat.choose 9265 44 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (118082 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((27647 / 50) : ℝ) < 2 * Real.log (Nat.choose 9265 44 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 111681) (M := 9265) (k := 44) (by norm_num only)
      (analytic_cell_48_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 48, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_48_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((51143 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (27647 / 50))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 111681 17 12 (5811700933837 / 500000000000)
        (11623401876213 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 118284 17 12 (5840421893517 / 500000000000)
        (2336168759107 / 200000000000) =
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
  have hs : (29 : ℝ) * Real.log 111681 ≤ (2 / 3 : ℝ) * (51143 / 100) := by linarith only [hlB]
  have hchoose : 118284 * 10 ^ 79 ≤ Nat.choose 9265 29 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 29)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((118284 : ℝ) * 10 ^ 79) ≤ Real.log (Nat.choose 9265 29 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (118284 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((27647 / 50) : ℝ) / 3 ≤ Real.log (Nat.choose 9265 29 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 111681) (M := 9265) (k := 29)
      (by norm_num only) (analytic_cell_48_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 49. -/
theorem analytic_cell_49_primeCount (hRH : RiemannHypothesis) :
    10536 ≤ (128354 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 128354 17 12 (5881273673089 / 500000000000)
        (11762547354679 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (128354 : ℝ) ≤ (3582653 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((9 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 49, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_49_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((13821 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (11937 / 20)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 128354 17 12 (5881273673089 / 500000000000)
        (11762547354679 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 405946 19 12 (6456987707579 / 500000000000)
        (12913975434857 / 1000000000000) =
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
  have hs : (47 : ℝ) * Real.log 128354 < (13821 / 25) := by linarith only [hlB]
  have hchoose : 405946 * 10 ^ 124 ≤ Nat.choose 10536 47 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 47)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((405946 : ℝ) * 10 ^ 124) ≤ Real.log (Nat.choose 10536 47 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (405946 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((11937 / 20) : ℝ) < 2 * Real.log (Nat.choose 10536 47 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 128354) (M := 10536) (k := 47) (by norm_num only)
      (analytic_cell_49_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 49, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_49_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((13821 / 25) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11937 / 20))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 128354 17 12 (5881273673089 / 500000000000)
        (11762547354679 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 587139 19 12 (1660377107889 / 125000000000)
        (2656603374523 / 200000000000) =
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
  have hs : (31 : ℝ) * Real.log 128354 ≤ (2 / 3 : ℝ) * (13821 / 25) := by linarith only [hlB]
  have hchoose : 587139 * 10 ^ 85 ≤ Nat.choose 10536 31 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 31)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((587139 : ℝ) * 10 ^ 85) ≤ Real.log (Nat.choose 10536 31 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (587139 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((11937 / 20) : ℝ) / 3 ≤ Real.log (Nat.choose 10536 31 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 128354) (M := 10536) (k := 31)
      (by norm_num only) (analytic_cell_49_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 50. -/
theorem analytic_cell_50_primeCount (hRH : RiemannHypothesis) :
    12358 ≤ (152512 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 152512 17 12 (11934998555963 / 1000000000000)
        (46621088143 / 3906250000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (152512 : ℝ) ≤ (3905279 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((17 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 50, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_50_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((2387 / 4) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (16126 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 152512 17 12 (11934998555963 / 1000000000000)
        (46621088143 / 3906250000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 117822 17 12 (11676930285559 / 1000000000000)
        (583846514703 / 50000000000) =
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
  have hs : (50 : ℝ) * Real.log 152512 < (2387 / 4) := by linarith only [hlB]
  have hchoose : 117822 * 10 ^ 135 ≤ Nat.choose 12358 50 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 50)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((117822 : ℝ) * 10 ^ 135) ≤ Real.log (Nat.choose 12358 50 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (117822 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((16126 / 25) : ℝ) < 2 * Real.log (Nat.choose 12358 50 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 152512) (M := 12358) (k := 50) (by norm_num only)
      (analytic_cell_50_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 50, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_50_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((2387 / 4) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16126 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 152512 17 12 (11934998555963 / 1000000000000)
        (46621088143 / 3906250000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 119407 17 12 (2922573275067 / 250000000000)
        (11690293108769 / 1000000000000) =
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
  have hs : (33 : ℝ) * Real.log 152512 ≤ (2 / 3 : ℝ) * (2387 / 4) := by linarith only [hlB]
  have hchoose : 119407 * 10 ^ 93 ≤ Nat.choose 12358 33 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 33)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((119407 : ℝ) * 10 ^ 93) ≤ Real.log (Nat.choose 12358 33 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (119407 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((16126 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 12358 33 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 152512) (M := 12358) (k := 33)
      (by norm_num only) (analytic_cell_50_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
