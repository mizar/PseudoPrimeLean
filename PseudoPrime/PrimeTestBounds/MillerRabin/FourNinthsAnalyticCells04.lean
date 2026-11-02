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

/-- RH supplies the certified prime count for analytic cell 31. -/
theorem analytic_cell_31_primeCount (hRH : RiemannHypothesis) : 978 ≤ (9662 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 9662 13 12 (4587977970739 / 500000000000)
        (4587977974233 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (9662 : ℝ) ≤ (196591 / 2000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((9 / 250) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 31, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_31_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((2949 / 20) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (15873 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 9662 13 12 (4587977970739 / 500000000000)
        (4587977974233 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 295958 18 12 (1574746603333 / 125000000000)
        (12597972835671 / 1000000000000) =
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
  have hs : (16 : ℝ) * Real.log 9662 < (2949 / 20) := by linarith only [hlB]
  have hchoose : 295958 * 10 ^ 29 ≤ Nat.choose 978 16 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 16)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((295958 : ℝ) * 10 ^ 29) ≤ Real.log (Nat.choose 978 16 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (295958 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((15873 / 100) : ℝ) < 2 * Real.log (Nat.choose 978 16 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 9662) (M := 978) (k := 16) (by norm_num only)
      (analytic_cell_31_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 31, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_31_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((2949 / 20) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15873 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 9662 13 12 (4587977970739 / 500000000000)
        (4587977974233 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 210657 18 12 (3064496622977 / 250000000000)
        (306449662563 / 25000000000) =
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
  have hs : (10 : ℝ) * Real.log 9662 ≤ (2 / 3 : ℝ) * (2949 / 20) := by linarith only [hlB]
  have hchoose : 210657 * 10 ^ 18 ≤ Nat.choose 978 10 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 10)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((210657 : ℝ) * 10 ^ 18) ≤ Real.log (Nat.choose 978 10 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (210657 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((15873 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 978 10 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 9662) (M := 978) (k := 10) (by norm_num only)
      (analytic_cell_31_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 32. -/
theorem analytic_cell_32_primeCount (hRH : RiemannHypothesis) :
    1118 ≤ (11183 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 11183 14 12 (4661074796337 / 500000000000)
        (9322150573681 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (11183 : ℝ) ≤ (528749 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((17 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 32, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_32_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((15863 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (17139 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 11183 14 12 (4661074796337 / 500000000000)
        (9322150573681 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 165710 17 12 (12017994503639 / 1000000000000)
        (12017994595483 / 1000000000000) =
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
  have hs : (17 : ℝ) * Real.log 11183 < (15863 / 100) := by linarith only [hlB]
  have hchoose : 165710 * 10 ^ 32 ≤ Nat.choose 1118 17 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 17)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((165710 : ℝ) * 10 ^ 32) ≤ Real.log (Nat.choose 1118 17 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (165710 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((17139 / 100) : ℝ) < 2 * Real.log (Nat.choose 1118 17 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 11183) (M := 1118) (k := 17) (by norm_num only)
      (analytic_cell_32_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 32, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_32_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((15863 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17139 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 11183 14 12 (4661074796337 / 500000000000)
        (9322150573681 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 813339 20 12 (2721780653249 / 200000000000)
        (6804451642823 / 500000000000) =
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
  have hs : (11 : ℝ) * Real.log 11183 ≤ (2 / 3 : ℝ) * (15863 / 100) := by linarith only [hlB]
  have hchoose : 813339 * 10 ^ 20 ≤ Nat.choose 1118 11 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 11)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((813339 : ℝ) * 10 ^ 20) ≤ Real.log (Nat.choose 1118 11 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (813339 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((17139 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 1118 11 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 11183) (M := 1118) (k := 11)
      (by norm_num only) (analytic_cell_32_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 33. -/
theorem analytic_cell_33_primeCount (hRH : RiemannHypothesis) :
    1287 ≤ (13040 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 13040 14 12 (4737888415301 / 500000000000)
        (9475776840283 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (13040 : ℝ) ≤ (1141929 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((33 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 33, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_33_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((17129 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (4618 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 13040 14 12 (4737888415301 / 500000000000)
        (9475776840283 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 130079 17 12 (2943974308189 / 250000000000)
        (11775897241257 / 1000000000000) =
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
  have hs : (18 : ℝ) * Real.log 13040 < (17129 / 100) := by linarith only [hlB]
  have hchoose : 130079 * 10 ^ 35 ≤ Nat.choose 1287 18 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 18)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((130079 : ℝ) * 10 ^ 35) ≤ Real.log (Nat.choose 1287 18 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (130079 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((4618 / 25) : ℝ) < 2 * Real.log (Nat.choose 1287 18 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 13040) (M := 1287) (k := 18) (by norm_num only)
      (analytic_cell_33_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 33, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_33_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((17129 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4618 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 13040 14 12 (4737888415301 / 500000000000)
        (9475776840283 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 409512 19 12 (3230680369449 / 250000000000)
        (12922721494089 / 1000000000000) =
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
  have hs : (12 : ℝ) * Real.log 13040 ≤ (2 / 3 : ℝ) * (17129 / 100) := by linarith only [hlB]
  have hchoose : 409512 * 10 ^ 23 ≤ Nat.choose 1287 12 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 12)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((409512 : ℝ) * 10 ^ 23) ≤ Real.log (Nat.choose 1287 12 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (409512 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((4618 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 1287 12 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 13040) (M := 1287) (k := 12)
      (by norm_num only) (analytic_cell_33_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 34. -/
theorem analytic_cell_34_primeCount (hRH : RiemannHypothesis) :
    1476 ≤ (15148 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 15148 14 12 (4812811892691 / 500000000000)
        (9625623792383 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (15148 : ℝ) ≤ (1230773 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((31 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 34, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_34_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((9231 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (4959 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 15148 14 12 (4812811892691 / 500000000000)
        (9625623792383 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 119404 17 12 (11690267975797 / 1000000000000)
        (5845133992149 / 500000000000) =
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
  have hs : (19 : ℝ) * Real.log 15148 < (9231 / 50) := by linarith only [hlB]
  have hchoose : 119404 * 10 ^ 38 ≤ Nat.choose 1476 19 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 19)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((119404 : ℝ) * 10 ^ 38) ≤ Real.log (Nat.choose 1476 19 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (119404 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((4959 / 25) : ℝ) < 2 * Real.log (Nat.choose 1476 19 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 15148) (M := 1476) (k := 19) (by norm_num only)
      (analytic_cell_34_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 34, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_34_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((9231 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4959 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 15148 14 12 (4812811892691 / 500000000000)
        (9625623792383 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 213417 18 12 (3067750818061 / 250000000000)
        (6135501641011 / 500000000000) =
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
  have hs : (12 : ℝ) * Real.log 15148 ≤ (2 / 3 : ℝ) * (9231 / 50) := by linarith only [hlB]
  have hchoose : 213417 * 10 ^ 24 ≤ Nat.choose 1476 12 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 12)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((213417 : ℝ) * 10 ^ 24) ≤ Real.log (Nat.choose 1476 12 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (213417 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((4959 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 1476 12 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 15148) (M := 1476) (k := 12)
      (by norm_num only) (analytic_cell_34_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 35. -/
theorem analytic_cell_35_primeCount (hRH : RiemannHypothesis) :
    1682 ≤ (17469 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 17469 14 12 (1953636631373 / 200000000000)
        (4884091581933 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (17469 : ℝ) ≤ (165213 / 1250) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((3 / 100) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 35, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_35_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((9913 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (1061 / 5)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 17469 14 12 (1953636631373 / 200000000000)
        (4884091581933 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 120544 17 12 (1462471263259 / 125000000000)
        (11699770114573 / 1000000000000) =
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
  have hs : (20 : ℝ) * Real.log 17469 < (9913 / 50) := by linarith only [hlB]
  have hchoose : 120544 * 10 ^ 41 ≤ Nat.choose 1682 20 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 20)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((120544 : ℝ) * 10 ^ 41) ≤ Real.log (Nat.choose 1682 20 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (120544 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((1061 / 5) : ℝ) < 2 * Real.log (Nat.choose 1682 20 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 17469) (M := 1682) (k := 20) (by norm_num only)
      (analytic_cell_35_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 35, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_35_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((9913 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1061 / 5))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 17469 14 12 (1953636631373 / 200000000000)
        (4884091581933 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 132211 17 12 (589607720289 / 50000000000)
        (11792154414281 / 1000000000000) =
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
  have hs : (13 : ℝ) * Real.log 17469 ≤ (2 / 3 : ℝ) * (9913 / 50) := by linarith only [hlB]
  have hchoose : 132211 * 10 ^ 27 ≤ Nat.choose 1682 13 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 13)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((132211 : ℝ) * 10 ^ 27) ≤ Real.log (Nat.choose 1682 13 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (132211 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((1061 / 5) : ℝ) / 3 ≤ Real.log (Nat.choose 1682 13 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 17469) (M := 1682) (k := 13)
      (by norm_num only) (analytic_cell_35_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 36. -/
theorem analytic_cell_36_primeCount (hRH : RiemannHypothesis) :
    1903 ≤ (19993 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 19993 14 12 (4951568741881 / 500000000000)
        (1237892187267 / 125000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (19993 : ℝ) ≤ (1413967 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((29 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 36, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_36_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((2121 / 10) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (4523 / 20)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 19993 14 12 (4951568741881 / 500000000000)
        (1237892187267 / 125000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 129351 17 12 (11770284914127 / 1000000000000)
        (2942571230657 / 250000000000) =
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
  have hs : (21 : ℝ) * Real.log 19993 < (2121 / 10) := by linarith only [hlB]
  have hchoose : 129351 * 10 ^ 44 ≤ Nat.choose 1903 21 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 21)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((129351 : ℝ) * 10 ^ 44) ≤ Real.log (Nat.choose 1903 21 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (129351 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((4523 / 20) : ℝ) < 2 * Real.log (Nat.choose 1903 21 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 19993) (M := 1903) (k := 21) (by norm_num only)
      (analytic_cell_36_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 36, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_36_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((2121 / 10) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4523 / 20))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 19993 14 12 (4951568741881 / 500000000000)
        (1237892187267 / 125000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 893136 20 12 (6851247069339 / 500000000000)
        (6851247074359 / 500000000000) =
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
  have hs : (14 : ℝ) * Real.log 19993 ≤ (2 / 3 : ℝ) * (2121 / 10) := by linarith only [hlB]
  have hchoose : 893136 * 10 ^ 29 ≤ Nat.choose 1903 14 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 14)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((893136 : ℝ) * 10 ^ 29) ≤ Real.log (Nat.choose 1903 14 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (893136 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((4523 / 20) : ℝ) / 3 ≤ Real.log (Nat.choose 1903 14 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 19993) (M := 1903) (k := 14)
      (by norm_num only) (analytic_cell_36_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 37. -/
theorem analytic_cell_37_primeCount (hRH : RiemannHypothesis) :
    1777 ≤ (18550 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 18550 14 12 (9828225064391 / 1000000000000)
        (9828225071401 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (18550 : ℝ) ≤ (85124 / 625) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((3 / 100) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 37, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_37_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((4521 / 20) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (24069 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 18550 14 12 (9828225064391 / 1000000000000)
        (9828225071401 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 185447 18 12 (6065262125347 / 500000000000)
        (12130524585119 / 1000000000000) =
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
  have hs : (23 : ℝ) * Real.log 18550 < (4521 / 20) := by linarith only [hlB]
  have hchoose : 185447 * 10 ^ 47 ≤ Nat.choose 1777 23 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 23)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((185447 : ℝ) * 10 ^ 47) ≤ Real.log (Nat.choose 1777 23 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (185447 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((24069 / 100) : ℝ) < 2 * Real.log (Nat.choose 1777 23 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 18550) (M := 1777) (k := 23) (by norm_num only)
      (analytic_cell_37_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 37, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_37_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((4521 / 20) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24069 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 18550 14 12 (9828225064391 / 1000000000000)
        (9828225071401 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 400940 19 12 (6450783528019 / 500000000000)
        (12901567083233 / 1000000000000) =
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
  have hs : (15 : ℝ) * Real.log 18550 ≤ (2 / 3 : ℝ) * (4521 / 20) := by linarith only [hlB]
  have hchoose : 400940 * 10 ^ 31 ≤ Nat.choose 1777 15 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 15)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((400940 : ℝ) * 10 ^ 31) ≤ Real.log (Nat.choose 1777 15 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (400940 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((24069 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 1777 15 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 18550) (M := 1777) (k := 15)
      (by norm_num only) (analytic_cell_37_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 38. -/
theorem analytic_cell_38_primeCount (hRH : RiemannHypothesis) :
    2127 ≤ (22574 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 22574 15 12 (10024553733207 / 1000000000000)
        (2506138620719 / 250000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (22574 : ℝ) ≤ (300493 / 2000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((7 / 250) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 38, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_38_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((24059 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (5159 / 20)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 22574 15 12 (10024553733207 / 1000000000000)
        (2506138620719 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 104028 17 12 (5776207683403 / 500000000000)
        (11552415378403 / 1000000000000) =
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
  have hs : (24 : ℝ) * Real.log 22574 < (24059 / 100) := by linarith only [hlB]
  have hchoose : 104028 * 10 ^ 51 ≤ Nat.choose 2127 24 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 24)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((104028 : ℝ) * 10 ^ 51) ≤ Real.log (Nat.choose 2127 24 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (104028 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((5159 / 20) : ℝ) < 2 * Real.log (Nat.choose 2127 24 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 22574) (M := 2127) (k := 24) (by norm_num only)
      (analytic_cell_38_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 38, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_38_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((24059 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5159 / 20))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 22574 15 12 (10024553733207 / 1000000000000)
        (2506138620719 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 792681 20 12 (13583176131303 / 1000000000000)
        (13583176170113 / 1000000000000) =
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
  have hs : (16 : ℝ) * Real.log 22574 ≤ (2 / 3 : ℝ) * (24059 / 100) := by linarith only [hlB]
  have hchoose : 792681 * 10 ^ 34 ≤ Nat.choose 2127 16 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 16)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((792681 : ℝ) * 10 ^ 34) ≤ Real.log (Nat.choose 2127 16 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (792681 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((5159 / 20) : ℝ) / 3 ≤ Real.log (Nat.choose 2127 16 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 22574) (M := 2127) (k := 16)
      (by norm_num only) (analytic_cell_38_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 39. -/
theorem analytic_cell_39_primeCount (hRH : RiemannHypothesis) :
    2723 ≤ (29549 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 29549 15 12 (5146902588707 / 500000000000)
        (2058761036983 / 200000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (29549 : ℝ) ≤ (1718983 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((13 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 39, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_39_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((5157 / 20) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (27923 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 29549 15 12 (5146902588707 / 500000000000)
        (2058761036983 / 200000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 434064 19 12 (12980947262579 / 1000000000000)
        (12980947272361 / 1000000000000) =
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
  have hs : (25 : ℝ) * Real.log 29549 < (5157 / 20) := by linarith only [hlB]
  have hchoose : 434064 * 10 ^ 55 ≤ Nat.choose 2723 25 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 25)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((434064 : ℝ) * 10 ^ 55) ≤ Real.log (Nat.choose 2723 25 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (434064 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((27923 / 100) : ℝ) < 2 * Real.log (Nat.choose 2723 25 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 29549) (M := 2723) (k := 25) (by norm_num only)
      (analytic_cell_39_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 39, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_39_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((5157 / 20) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (27923 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 29549 15 12 (5146902588707 / 500000000000)
        (2058761036983 / 200000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 417798 19 12 (12942753335013 / 1000000000000)
        (12942753347027 / 1000000000000) =
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
  have hs : (16 : ℝ) * Real.log 29549 ≤ (2 / 3 : ℝ) * (5157 / 20) := by linarith only [hlB]
  have hchoose : 417798 * 10 ^ 36 ≤ Nat.choose 2723 16 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 16)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((417798 : ℝ) * 10 ^ 36) ≤ Real.log (Nat.choose 2723 16 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (417798 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((27923 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 2723 16 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 29549) (M := 2723) (k := 16)
      (by norm_num only) (analytic_cell_39_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 40. -/
theorem analytic_cell_40_primeCount (hRH : RiemannHypothesis) :
    2836 ≤ (30888 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 30888 15 12 (2584530758511 / 250000000000)
        (2067624608309 / 200000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (30888 : ℝ) ≤ (1757499 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((13 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 40, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_40_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((27913 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (29993 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 30888 15 12 (2584530758511 / 250000000000)
        (2067624608309 / 200000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 135570 17 12 (5908621693327 / 500000000000)
        (2363448679031 / 200000000000) =
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
  have hs : (27 : ℝ) * Real.log 30888 < (27913 / 100) := by linarith only [hlB]
  have hchoose : 135570 * 10 ^ 60 ≤ Nat.choose 2836 27 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 27)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((135570 : ℝ) * 10 ^ 60) ≤ Real.log (Nat.choose 2836 27 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (135570 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((29993 / 100) : ℝ) < 2 * Real.log (Nat.choose 2836 27 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 30888) (M := 2836) (k := 27) (by norm_num only)
      (analytic_cell_40_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 40, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_40_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((27913 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (29993 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 30888 15 12 (2584530758511 / 250000000000)
        (2067624608309 / 200000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 208397 18 12 (12247200187369 / 1000000000000)
        (765450012451 / 62500000000) =
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
  have hs : (18 : ℝ) * Real.log 30888 ≤ (2 / 3 : ℝ) * (27913 / 100) := by linarith only [hlB]
  have hchoose : 208397 * 10 ^ 41 ≤ Nat.choose 2836 18 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 18)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((208397 : ℝ) * 10 ^ 41) ≤ Real.log (Nat.choose 2836 18 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (208397 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((29993 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 2836 18 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 30888) (M := 2836) (k := 18)
      (by norm_num only) (analytic_cell_40_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs
      hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
