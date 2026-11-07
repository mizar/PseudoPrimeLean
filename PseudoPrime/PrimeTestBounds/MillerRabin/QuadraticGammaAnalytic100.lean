/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticCaps
public import PseudoPrime.Analysis.GammaExpRationalBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # First analytic Gamma main-sum certificate -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational square-root caps for the first analytic scale and cutoff.
The two exact squared comparisons certify the main and boundary errors. -/
theorem gamma_analytic100_roots :
    Real.sqrt (60000 / 37 : ℝ) ≤ 201347 / 5000 ∧ Real.sqrt (3000 : ℝ) ≤ 547723 / 10000 := by
  constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor interval checks supply the logarithmic upper caps at the
first analytic scale and its cutoff. -/
theorem gamma_analytic100_logs :
    Real.log (60000 / 37 : ℝ) ≤ 9239 / 1250 ∧ Real.log (3000 : ℝ) ≤ 5004 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (60000 / 37) 11 20 0 (9239 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3000 12 20 0 (5004 / 625) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- A rational Taylor sum bounds the exponential at the fixed cutoff ratio. -/
theorem gamma_analytic100_exp : Real.exp (-(37 / 20 : ℝ)) ≤ 78619 / 500000 := by
  have hc : Analysis.gammaExpTaylorUpper (37 / 20) ≤ (78619 / 500000 : ℚ) := by decide +kernel
  have h := Analysis.gamma_exp_taylor_upper_valid (t := 37 / 20) (by norm_num only)
  have hcR := (Rat.cast_le (K := ℝ)).2 hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hcR
  exact h.trans hcR

/-- Under RH, the first analytic cell has a normalized finite main sum of at
least 32.711. Rational root, logarithm and exponential caps instantiate the
uniform signed-variation estimate. -/
theorem gamma_analytic100_main (hRH : RiemannHypothesis) :
    (32711 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3000,
        Real.exp (-(n : ℝ) / (60000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((60000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((60000 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      182249 / 1000 := by
    norm_num only at ⊢
    linarith only [gamma_analytic100_roots.2]
  have hs :
    Real.sqrt ((60000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((60000 / 37) * (37 / 20)) +
        21 / 20 ≤
      18513 / 1000 := by
    norm_num only at ⊢
    linarith only [gamma_analytic100_roots.2, gamma_analytic100_logs.2]
  have hz :
    Real.sqrt (60000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (60000 / 37) + 2469 / 800 ≤
      3059 / 200 := by
    linarith only [gamma_analytic100_roots.1, gamma_analytic100_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 60000 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      201347 / 5000) (e := 78619 / 500000) (p := 182249 / 1000) (s := 18513 / 1000) (z :=
      3059 / 200) (F := 32711 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gamma_analytic100_roots.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (60000 / 37 : ℝ) * (37 / 20) = 3000 by norm_num only, Nat.floor_ofNat] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
