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

/-- RH supplies the certified prime count for analytic cell 61. -/
theorem analytic_cell_61_primeCount (hRH : RiemannHypothesis) : 233 ≤ (2007 : ℕ).primeCounting := by
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

/-- Analytic cell 61, semiprime branch: RH and the certified scalar
budgets give a rejecting prime within the four-ninths bound. -/
theorem analytic_cell_61_semiprime {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hq : q.Prime) (hq2 : q ≠ 2) (hprod : n = p * q) (hRH : RiemannHypothesis)
    (hlo : ((1597 / 20) : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8861 / 100))
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
    Analysis.rationalLogIntervalCheck 675381 19 12 (6711516055759 / 500000000000)
        (1677879048343 / 125000000000) =
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
  have hs : (7 : ℝ) * Real.log 2007 ≤ (2 / 3 : ℝ) * (1597 / 20) := by linarith only [hlB]
  have hchoose : 675381 * 10 ^ 7 ≤ Nat.choose 233 7 := by
    apply Nat.le_of_mul_le_mul_left ?_ (Nat.factorial_pos 7)
    rw [← Nat.descFactorial_eq_factorial_mul_choose]
    norm_num only [Nat.descFactorial, Nat.factorial, Nat.pow_succ, Nat.pow_zero, Nat.mul_succ,
      Nat.mul_zero, Nat.add_zero]
  have hle : Real.log ((675381 : ℝ) * 10 ^ 7) ≤ Real.log (Nat.choose 233 7 : ℝ) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hchoose
  rw [Real.log_mul (by norm_num only : (675381 : ℝ) ≠ 0) (by positivity), Real.log_pow] at hle
  norm_num only [Nat.cast_ofNat] at hle
  have hcount : ((8861 / 100) : ℝ) / 3 ≤ Real.log (Nat.choose 233 7 : ℝ) := by
    linarith only [hlM, hlT, hle]
  apply
    semiprime_cell_choose hn ho hp hq hq2 hprod (B := 2007) (M := 233) (k := 7) (by norm_num only)
      (analytic_cell_61_primeCount hRH) (by norm_num only) hlo hhi hqLarge hs hcount
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
