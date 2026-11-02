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

/-- RH supplies the certified prime count for analytic cell 1. -/
theorem analytic_cell_01_primeCount (hRH : RiemannHypothesis) : 134 ≤ (1096 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1096 10 12 (1749855616227 / 250000000000)
        (6999422469909 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1096 : ℝ) ≤ (331059 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((71 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 1, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_01_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : (56 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (1418 / 25)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1096 10 12 (1749855616227 / 250000000000)
        (6999422469909 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 208366 18 12 (12247051421753 / 1000000000000)
        (6123525716811 / 500000000000) =
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
  have hs : (8 : ℝ) * Real.log 1096 < 56 := by linarith only [hlB]
  have hchoose : 208366 * 10 ^ 7 ≤ Nat.choose 134 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((208366 : ℝ) * 10 ^ 7) ≤ Real.log (Nat.choose 134 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (208366 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((1418 / 25) : ℝ) < 2 * Real.log (Nat.choose 134 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1096) (M := 134) (k := 8) (by norm_num only)
      (analytic_cell_01_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 1, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_01_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : (56 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1418 / 25))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1096 10 12 (1749855616227 / 250000000000)
        (6999422469909 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 333859 18 12 (1271847395333 / 100000000000)
        (397452315459 / 31250000000) =
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
  have hs : (5 : ℝ) * Real.log 1096 ≤ (2 / 3 : ℝ) * 56 := by linarith only [hlB]
  have hchoose : 333859 * 10 ^ 3 ≤ Nat.choose 134 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((333859 : ℝ) * 10 ^ 3) ≤ Real.log (Nat.choose 134 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (333859 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((1418 / 25) : ℝ) / 3 ≤ Real.log (Nat.choose 134 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1096) (M := 134) (k := 5) (by norm_num only)
      (analytic_cell_01_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 2. -/
theorem analytic_cell_02_primeCount (hRH : RiemannHypothesis) : 144 ≤ (1187 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1187 10 12 (7079184391957 / 1000000000000)
        (3539592198529 / 500000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1187 : ℝ) ≤ (344529 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((69 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 2, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_02_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((1416 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (579 / 10)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1187 10 12 (7079184391957 / 1000000000000)
        (3539592198529 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 376207 19 12 (12837894704011 / 1000000000000)
        (32094737291 / 2500000000) =
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
  have hs : (8 : ℝ) * Real.log 1187 < (1416 / 25) := by linarith only [hlB]
  have hchoose : 376207 * 10 ^ 7 ≤ Nat.choose 144 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((376207 : ℝ) * 10 ^ 7) ≤ Real.log (Nat.choose 144 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (376207 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((579 / 10) : ℝ) < 2 * Real.log (Nat.choose 144 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1187) (M := 144) (k := 8) (by norm_num only)
      (analytic_cell_02_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 2, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_02_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((1416 / 25) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (579 / 10))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1187 10 12 (7079184391957 / 1000000000000)
        (3539592198529 / 500000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 481008 19 12 (13083639176027 / 1000000000000)
        (1635454898191 / 125000000000) =
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
  have hs : (5 : ℝ) * Real.log 1187 ≤ (2 / 3 : ℝ) * (1416 / 25) := by linarith only [hlB]
  have hchoose : 481008 * 10 ^ 3 ≤ Nat.choose 144 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((481008 : ℝ) * 10 ^ 3) ≤ Real.log (Nat.choose 144 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (481008 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((579 / 10) : ℝ) / 3 ≤ Real.log (Nat.choose 144 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1187) (M := 144) (k := 5) (by norm_num only)
      (analytic_cell_02_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 3. -/
theorem analytic_cell_03_primeCount (hRH : RiemannHypothesis) : 165 ≤ (1373 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1373 11 12 (7224752655169 / 1000000000000)
        (7224754276327 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1373 : ℝ) ≤ (370541 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((33 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 3, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_03_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((289 / 5) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6013 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1373 11 12 (7224752655169 / 1000000000000)
        (7224754276327 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 114685 17 12 (11649944514207 / 1000000000000)
        (1456243065339 / 125000000000) =
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
  have hs : (8 : ℝ) * Real.log 1373 < (289 / 5) := by linarith only [hlB]
  have hchoose : 114685 * 10 ^ 8 ≤ Nat.choose 165 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((114685 : ℝ) * 10 ^ 8) ≤ Real.log (Nat.choose 165 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (114685 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6013 / 100) : ℝ) < 2 * Real.log (Nat.choose 165 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1373) (M := 165) (k := 8) (by norm_num only)
      (analytic_cell_03_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 3, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_03_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((289 / 5) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6013 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1373 11 12 (7224752655169 / 1000000000000)
        (7224754276327 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 958683 20 12 (13773315741363 / 1000000000000)
        (3443328937841 / 250000000000) =
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
  have hs : (5 : ℝ) * Real.log 1373 ≤ (2 / 3 : ℝ) * (289 / 5) := by linarith only [hlB]
  have hchoose : 958683 * 10 ^ 3 ≤ Nat.choose 165 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((958683 : ℝ) * 10 ^ 3) ≤ Real.log (Nat.choose 165 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (958683 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6013 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 165 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1373) (M := 165) (k := 5) (by norm_num only)
      (analytic_cell_03_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 4. -/
theorem analytic_cell_04_primeCount (hRH : RiemannHypothesis) : 189 ≤ (1601 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1601 11 12 (92229796339 / 12500000000)
        (7378383719147 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1601 : ℝ) ≤ (3201 / 80) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((31 / 500) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 4, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_04_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((6003 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (3117 / 50)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1601 11 12 (92229796339 / 12500000000)
        (7378383719147 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 347508 18 12 (12758542246743 / 1000000000000)
        (3189635907201 / 250000000000) =
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
  have hs : (8 : ℝ) * Real.log 1601 < (6003 / 100) := by linarith only [hlB]
  have hchoose : 347508 * 10 ^ 8 ≤ Nat.choose 189 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((347508 : ℝ) * 10 ^ 8) ≤ Real.log (Nat.choose 189 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (347508 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3117 / 50) : ℝ) < 2 * Real.log (Nat.choose 189 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1601) (M := 189) (k := 8) (by norm_num only)
      (analytic_cell_04_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 4, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_04_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((6003 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3117 / 50))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1601 11 12 (92229796339 / 12500000000)
        (7378383719147 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 190530 18 12 (12157564876711 / 1000000000000)
        (12157565015597 / 1000000000000) =
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
  have hs : (5 : ℝ) * Real.log 1601 ≤ (2 / 3 : ℝ) * (6003 / 100) := by linarith only [hlB]
  have hchoose : 190530 * 10 ^ 4 ≤ Nat.choose 189 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((190530 : ℝ) * 10 ^ 4) ≤ Real.log (Nat.choose 189 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (190530 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3117 / 50) : ℝ) / 3 ≤ Real.log (Nat.choose 189 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1601) (M := 189) (k := 5) (by norm_num only)
      (analytic_cell_04_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 5. -/
theorem analytic_cell_05_primeCount (hRH : RiemannHypothesis) : 202 ≤ (1721 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1721 11 12 (7450660793303 / 1000000000000)
        (7450660798909 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1721 : ℝ) ≤ (8297 / 200) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((61 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 5, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_05_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((1556 / 25) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6343 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1721 11 12 (7450660793303 / 1000000000000)
        (7450660798909 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 597491 19 12 (3325123623741 / 250000000000)
        (13300494504483 / 1000000000000) =
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
  have hs : (8 : ℝ) * Real.log 1721 < (1556 / 25) := by linarith only [hlB]
  have hchoose : 597491 * 10 ^ 8 ≤ Nat.choose 202 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((597491 : ℝ) * 10 ^ 8) ≤ Real.log (Nat.choose 202 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (597491 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6343 / 100) : ℝ) < 2 * Real.log (Nat.choose 202 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1721) (M := 202) (k := 8) (by norm_num only)
      (analytic_cell_05_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 5, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_05_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((1556 / 25) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6343 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1721 11 12 (7450660793303 / 1000000000000)
        (7450660798909 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 266633 18 12 (3123407113833 / 250000000000)
        (12493628464333 / 1000000000000) =
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
  have hs : (5 : ℝ) * Real.log 1721 ≤ (2 / 3 : ℝ) * (1556 / 25) := by linarith only [hlB]
  have hchoose : 266633 * 10 ^ 4 ≤ Nat.choose 202 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((266633 : ℝ) * 10 ^ 4) ≤ Real.log (Nat.choose 202 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (266633 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6343 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 202 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1721) (M := 202) (k := 5) (by norm_num only)
      (analytic_cell_05_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 6. -/
theorem analytic_cell_06_primeCount (hRH : RiemannHypothesis) : 209 ≤ (1782 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1782 11 12 (467843225323 / 62500000000)
        (1871372902669 / 250000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1782 : ℝ) ≤ (211069 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((3 / 50) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 6, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_06_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((6333 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (3199 / 50)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1782 11 12 (467843225323 / 62500000000)
        (1871372902669 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 788420 20 12 (3394446549993 / 250000000000)
        (108622289967 / 8000000000) =
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
  have hs : (8 : ℝ) * Real.log 1782 < (6333 / 100) := by linarith only [hlB]
  have hchoose : 788420 * 10 ^ 8 ≤ Nat.choose 209 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((788420 : ℝ) * 10 ^ 8) ≤ Real.log (Nat.choose 209 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (788420 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3199 / 50) : ℝ) < 2 * Real.log (Nat.choose 209 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1782) (M := 209) (k := 8) (by norm_num only)
      (analytic_cell_06_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 6, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_06_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((6333 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3199 / 50))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1782 11 12 (467843225323 / 62500000000)
        (1871372902669 / 250000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 316679 18 12 (506625756601 / 40000000000)
        (6332821963739 / 500000000000) =
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
  have hs : (5 : ℝ) * Real.log 1782 ≤ (2 / 3 : ℝ) * (6333 / 100) := by linarith only [hlB]
  have hchoose : 316679 * 10 ^ 4 ≤ Nat.choose 209 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((316679 : ℝ) * 10 ^ 4) ≤ Real.log (Nat.choose 209 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (316679 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((3199 / 50) : ℝ) / 3 ≤ Real.log (Nat.choose 209 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1782) (M := 209) (k := 5) (by norm_num only)
      (analytic_cell_06_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 7. -/
theorem analytic_cell_07_primeCount (hRH : RiemannHypothesis) : 212 ≤ (1815 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1815 11 12 (3751920371919 / 500000000000)
        (7503840749341 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1815 : ℝ) ≤ (426029 / 10000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((3 / 50) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 7, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_07_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((6391 / 100) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6421 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1815 11 12 (3751920371919 / 500000000000)
        (7503840749341 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 885356 20 12 (6846872548879 / 500000000000)
        (6846872553917 / 500000000000) =
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
  have hs : (8 : ℝ) * Real.log 1815 < (6391 / 100) := by linarith only [hlB]
  have hchoose : 885356 * 10 ^ 8 ≤ Nat.choose 212 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((885356 : ℝ) * 10 ^ 8) ≤ Real.log (Nat.choose 212 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (885356 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6421 / 100) : ℝ) < 2 * Real.log (Nat.choose 212 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1815) (M := 212) (k := 8) (by norm_num only)
      (analytic_cell_07_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 7, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_07_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((6391 / 100) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6421 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1815 11 12 (3751920371919 / 500000000000)
        (7503840749341 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 340303 18 12 (636879572651 / 50000000000)
        (3184397970323 / 250000000000) =
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
  have hs : (5 : ℝ) * Real.log 1815 ≤ (2 / 3 : ℝ) * (6391 / 100) := by linarith only [hlB]
  have hchoose : 340303 * 10 ^ 4 ≤ Nat.choose 212 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((340303 : ℝ) * 10 ^ 4) ≤ Real.log (Nat.choose 212 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (340303 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6421 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 212 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1815) (M := 212) (k := 5) (by norm_num only)
      (analytic_cell_07_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 8. -/
theorem analytic_cell_08_primeCount (hRH : RiemannHypothesis) : 214 ≤ (1830 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1830 11 12 (300482849719 / 40000000000)
        (7512071248477 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1830 : ℝ) ≤ (85557 / 2000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((3 / 50) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 8, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_08_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((3209 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6437 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1830 11 12 (300482849719 / 40000000000)
        (7512071248477 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 955631 20 12 (688506356453 / 50000000000)
        (13770127139061 / 1000000000000) =
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
  have hs : (8 : ℝ) * Real.log 1830 < (3209 / 50) := by linarith only [hlB]
  have hchoose : 955631 * 10 ^ 8 ≤ Nat.choose 214 8 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 8)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((955631 : ℝ) * 10 ^ 8) ≤ Real.log (Nat.choose 214 8 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (955631 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6437 / 100) : ℝ) < 2 * Real.log (Nat.choose 214 8 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1830) (M := 214) (k := 8) (by norm_num only)
      (analytic_cell_08_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 8, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_08_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((3209 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6437 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1830 11 12 (300482849719 / 40000000000)
        (7512071248477 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 356820 19 12 (12784986236979 / 1000000000000)
        (12784987305381 / 1000000000000) =
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
  have hs : (5 : ℝ) * Real.log 1830 ≤ (2 / 3 : ℝ) * (3209 / 50) := by linarith only [hlB]
  have hchoose : 356820 * 10 ^ 4 ≤ Nat.choose 214 5 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 5)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((356820 : ℝ) * 10 ^ 4) ≤ Real.log (Nat.choose 214 5 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (356820 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6437 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 214 5 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1830) (M := 214) (k := 5) (by norm_num only)
      (analytic_cell_08_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 9. -/
theorem analytic_cell_09_primeCount (hRH : RiemannHypothesis) : 154 ≤ (1274 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1274 10 12 (3574958409181 / 500000000000)
        (714991685233 / 100000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1274 : ℝ) ≤ (89233 / 2500) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((67 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 9, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_09_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((1287 / 20) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6457 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1274 10 12 (3574958409181 / 500000000000)
        (714991685233 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 105798 17 12 (11569286889633 / 1000000000000)
        (2892321724849 / 250000000000) =
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
  have hs : (9 : ℝ) * Real.log 1274 < (1287 / 20) := by linarith only [hlB]
  have hchoose : 105798 * 10 ^ 9 ≤ Nat.choose 154 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((105798 : ℝ) * 10 ^ 9) ≤ Real.log (Nat.choose 154 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (105798 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6457 / 100) : ℝ) < 2 * Real.log (Nat.choose 154 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1274) (M := 154) (k := 9) (by norm_num only)
      (analytic_cell_09_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 9, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_09_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((1287 / 20) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6457 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1274 10 12 (3574958409181 / 500000000000)
        (714991685233 / 100000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 167871 17 12 (6015475502071 / 500000000000)
        (300773779997 / 25000000000) =
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
  have hs : (6 : ℝ) * Real.log 1274 ≤ (2 / 3 : ℝ) * (1287 / 20) := by linarith only [hlB]
  have hchoose : 167871 * 10 ^ 5 ≤ Nat.choose 154 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((167871 : ℝ) * 10 ^ 5) ≤ Real.log (Nat.choose 154 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (167871 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6457 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 154 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1274) (M := 154) (k := 6) (by norm_num only)
      (analytic_cell_09_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

/-- RH supplies the certified prime count for analytic cell 10. -/
theorem analytic_cell_10_primeCount (hRH : RiemannHypothesis) : 157 ≤ (1301 : ℕ).primeCounting := by
  have hb :
    Analysis.rationalLogIntervalCheck 1301 10 12 (448180526027 / 62500000000)
        (7170888535287 / 1000000000000) =
      true := by
    decide +kernel
  have hlog := (Analysis.rationalLogIntervalCheck_sound hb).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hs : Real.sqrt (1301 : ℝ) ≤ (180347 / 5000) := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num only
  apply
    primeCount_ge_of_relative_psi hRH (h := ((67 / 1000) : ℝ)) (by norm_num only) (by norm_num only)
      (by norm_num only)
  linarith only [hlog, hs]

/-- Analytic cell 10, square branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_10_square {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpow : n = p ^ 2) (hRH : RiemannHypothesis) (hlo : ((3227 / 50) : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ (6493 / 100)) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1301 10 12 (448180526027 / 62500000000)
        (7170888535287 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 126445 17 12 (1468445338197 / 125000000000)
        (11747562714077 / 1000000000000) =
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
  have hs : (9 : ℝ) * Real.log 1301 < (3227 / 50) := by linarith only [hlB]
  have hchoose : 126445 * 10 ^ 9 ≤ Nat.choose 157 9 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 9)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((126445 : ℝ) * 10 ^ 9) ≤ Real.log (Nat.choose 157 9 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (126445 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6493 / 100) : ℝ) < 2 * Real.log (Nat.choose 157 9 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    square_cell_choose hn ho hp hp2 hpow (B := 1301) (M := 157) (k := 9) (by norm_num only)
      (analytic_cell_10_primeCount hRH) (by norm_num only) hlo hhi hs hcount
  norm_num only

/-- Analytic cell 10, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_10_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((3227 / 50) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6493 / 100))
    (hqLarge : (2 / 3 : ℝ) * Real.log n < Real.log q) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (4 / 9 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hb :
    Analysis.rationalLogIntervalCheck 1301 10 12 (448180526027 / 62500000000)
        (7170888535287 / 1000000000000) =
      true := by
    decide +kernel
  have hm :
    Analysis.rationalLogIntervalCheck 188833 18 12 (12148618218683 / 1000000000000)
        (6074309202689 / 500000000000) =
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
  have hs : (6 : ℝ) * Real.log 1301 ≤ (2 / 3 : ℝ) * (3227 / 50) := by linarith only [hlB]
  have hchoose : 188833 * 10 ^ 5 ≤ Nat.choose 157 6 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 6)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((188833 : ℝ) * 10 ^ 5) ≤ Real.log (Nat.choose 157 6 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (188833 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((6493 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 157 6 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 1301) (M := 157) (k := 6) (by norm_num only)
      (analytic_cell_10_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
