/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticWideCombined

/-! # Analytic Gamma cells after logarithmic scale 100.21 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact root caps for analytic cell 0. -/
theorem gammaAnalyticHigh0_roots :
    ((97641 / 1250 : ℝ) ≤ Real.sqrt (225760 / 37 : ℝ) ∧
      Real.sqrt (225760 / 37 : ℝ) ≤ 781129 / 10000 ∧ Real.sqrt (11288 : ℝ) ≤ 21249 / 200) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 0. -/
theorem gammaAnalyticHigh0_logs :
    Real.log (225760 / 37 : ℝ) ≤ 21791 / 2500 ∧ Real.log (11288 : ℝ) ≤ 18663 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (225760 / 37) 13 20 0 (21791 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 11288 14 20 0 (18663 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh0_main (hRH : RiemannHypothesis) :
    (32259 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 11288,
        Real.exp (-(n : ℝ) / (225760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (225760 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 12187) * ((225760 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((225760 / 37) * (37 / 20)) + 1) / (500 / 12187) +
        1839 / 1000 ≤
      243559 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh0_roots.2.2]
  have hs :
    Real.sqrt ((225760 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((225760 / 37) * (37 / 20)) +
        21 / 20 ≤
      23523 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh0_roots.2.2, gammaAnalyticHigh0_logs.2]
  have hz :
    Real.sqrt (225760 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (225760 / 37) + 2469 / 800 ≤
      9507 / 500 := by
    linarith only [gammaAnalyticHigh0_roots.2.1, gammaAnalyticHigh0_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 225760 / 37) (y := 37 / 20) (h := 500 / 12187) (r :=
      781129 / 10000) (e := 78619 / 500000) (p := 243559 / 500) (s := 23523 / 1000) (z :=
      9507 / 500) (F := 32259 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh0_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (225760 / 37 : ℝ) * (37 / 20) = 11288 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh0_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (225760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (225760 / 37 : ℝ)) ≤
      78357 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 97641 / 1250) (T := 781129 / 10000) (Z := 21791 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh0_roots.1 gammaAnalyticHigh0_roots.2.1
      gammaAnalyticHigh0_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh0_power : (225760 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 743 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 0 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh0_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (9699 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19569 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (11288 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 9699 / 50)]
  apply
    reject_03_of_analytic_caps (B := 11288) (x := 225760 / 37) (H := 19569 / 100) (R :=
      97641 / 1250) (W := 743 / 100000) (F := 32259 / 500) (U := 78357 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh0_power (gammaAnalyticHigh0_main hGRH.riemann)
      (gammaAnalyticHigh0_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 1. -/
theorem gammaAnalyticHigh1_roots :
    ((394009 / 5000 : ℝ) ≤ Real.sqrt (229760 / 37 : ℝ) ∧
      Real.sqrt (229760 / 37 : ℝ) ≤ 788019 / 10000 ∧ Real.sqrt (11488 : ℝ) ≤ 1071821 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 1. -/
theorem gammaAnalyticHigh1_logs :
    Real.log (229760 / 37 : ℝ) ≤ 87339 / 10000 ∧ Real.log (11488 : ℝ) ≤ 93491 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (229760 / 37) 13 20 0 (87339 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 11488 14 20 0 (93491 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh1_main (hRH : RiemannHypothesis) :
    (65097 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 11488,
        Real.exp (-(n : ℝ) / (229760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (229760 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 97923) * ((229760 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((229760 / 37) * (37 / 20)) + 1) / (4000 / 97923) +
        1839 / 1000 ≤
      123383 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh1_roots.2.2]
  have hs :
    Real.sqrt ((229760 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((229760 / 37) * (37 / 20)) +
        21 / 20 ≤
      23603 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh1_roots.2.2, gammaAnalyticHigh1_logs.2]
  have hz :
    Real.sqrt (229760 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (229760 / 37) + 2469 / 800 ≤
      19073 / 1000 := by
    linarith only [gammaAnalyticHigh1_roots.2.1, gammaAnalyticHigh1_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 229760 / 37) (y := 37 / 20) (h := 4000 / 97923) (r :=
      788019 / 10000) (e := 78619 / 500000) (p := 123383 / 250) (s := 23603 / 1000) (z :=
      19073 / 1000) (F := 65097 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh1_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (229760 / 37 : ℝ) * (37 / 20) = 11488 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh1_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (229760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (229760 / 37 : ℝ)) ≤
      19761 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 394009 / 5000) (T := 788019 / 10000) (Z := 87339 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh1_roots.1 gammaAnalyticHigh1_roots.2.1
      gammaAnalyticHigh1_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh1_power : (229760 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 23 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 1 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh1_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19569 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (9871 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (11488 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19569 / 100)]
  apply
    reject_03_of_analytic_caps (B := 11488) (x := 229760 / 37) (H := 9871 / 50) (R := 394009 / 5000)
      (W := 23 / 3125) (F := 65097 / 1000) (U := 19761 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh1_power (gammaAnalyticHigh1_main hGRH.riemann)
      (gammaAnalyticHigh1_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 2. -/
theorem gammaAnalyticHigh2_roots :
    ((99373 / 1250 : ℝ) ≤ Real.sqrt (6320 : ℝ) ∧
      Real.sqrt (6320 : ℝ) ≤ 158997 / 2000 ∧ Real.sqrt (11692 : ℝ) ≤ 67581 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 2. -/
theorem gammaAnalyticHigh2_logs :
    Real.log (6320 : ℝ) ≤ 17503 / 2000 ∧ Real.log (11692 : ℝ) ≤ 93667 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (6320) 13 20 0 (17503 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 11692 14 20 0 (93667 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh2_main (hRH : RiemannHypothesis) :
    (65681 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 11692,
        Real.exp (-(n : ℝ) / (6320)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (6320 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 98357) * ((6320) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((6320) * (37 / 20)) + 1) / (4000 / 98357) +
        1839 / 1000 ≤
      250023 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh2_roots.2.2]
  have hs :
    Real.sqrt ((6320 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((6320) * (37 / 20)) +
        21 / 20 ≤
      11841 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh2_roots.2.2, gammaAnalyticHigh2_logs.2]
  have hz :
    Real.sqrt (6320 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (6320) + 2469 / 800 ≤ 4783 / 250 := by
    linarith only [gammaAnalyticHigh2_roots.2.1, gammaAnalyticHigh2_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 6320) (y := 37 / 20) (h := 4000 / 98357) (r :=
      158997 / 2000) (e := 78619 / 500000) (p := 250023 / 500) (s := 11841 / 500) (z := 4783 / 250)
      (F := 65681 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh2_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (6320 : ℝ) * (37 / 20) = 11692 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh2_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (6320)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (6320 : ℝ)) ≤
      3987 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 99373 / 1250) (T := 158997 / 2000) (Z := 17503 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh2_roots.1 gammaAnalyticHigh2_roots.2.1
      gammaAnalyticHigh2_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh2_power : (6320 : ℝ) ^ (-9 / 16 : ℝ) ≤ 91 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 2 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh2_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (9871 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19917 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (11692 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 9871 / 50)]
  apply
    reject_03_of_analytic_caps (B := 11692) (x := 6320) (H := 19917 / 100) (R := 99373 / 1250) (W :=
      91 / 12500) (F := 65681 / 1000) (U := 3987 / 50) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh2_power (gammaAnalyticHigh2_main hGRH.riemann)
      (gammaAnalyticHigh2_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 3. -/
theorem gammaAnalyticHigh3_roots :
    ((100253 / 1250 : ℝ) ≤ Real.sqrt (238000 / 37 : ℝ) ∧
      Real.sqrt (238000 / 37 : ℝ) ≤ 32081 / 400 ∧ Real.sqrt (11900 : ℝ) ≤ 136359 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 3. -/
theorem gammaAnalyticHigh3_logs :
    Real.log (238000 / 37 : ℝ) ≤ 21923 / 2500 ∧ Real.log (11900 : ℝ) ≤ 93843 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (238000 / 37) 13 20 0 (21923 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 11900 14 20 0 (93843 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh3_main (hRH : RiemannHypothesis) :
    (8284 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 11900,
        Real.exp (-(n : ℝ) / (238000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (238000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 98791) * ((238000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((238000 / 37) * (37 / 20)) + 1) / (4000 / 98791) +
        1839 / 1000 ≤
      506659 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh3_roots.2.2]
  have hs :
    Real.sqrt ((238000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((238000 / 37) * (37 / 20)) +
        21 / 20 ≤
      23763 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh3_roots.2.2, gammaAnalyticHigh3_logs.2]
  have hz :
    Real.sqrt (238000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (238000 / 37) + 2469 / 800 ≤
      2399 / 125 := by
    linarith only [gammaAnalyticHigh3_roots.2.1, gammaAnalyticHigh3_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 238000 / 37) (y := 37 / 20) (h := 4000 / 98791) (r :=
      32081 / 400) (e := 78619 / 500000) (p := 506659 / 1000) (s := 23763 / 1000) (z := 2399 / 125)
      (F := 8284 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh3_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (238000 / 37 : ℝ) * (37 / 20) = 11900 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh3_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (238000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (238000 / 37 : ℝ)) ≤
      40221 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 100253 / 1250) (T := 32081 / 400) (Z := 21923 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh3_roots.1 gammaAnalyticHigh3_roots.2.1
      gammaAnalyticHigh3_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh3_power : (238000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 721 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 3 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh3_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19917 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20093 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (11900 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19917 / 100)]
  apply
    reject_03_of_analytic_caps (B := 11900) (x := 238000 / 37) (H := 20093 / 100) (R :=
      100253 / 1250) (W := 721 / 100000) (F := 8284 / 125) (U := 40221 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh3_power (gammaAnalyticHigh3_main hGRH.riemann)
      (gammaAnalyticHigh3_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 4. -/
theorem gammaAnalyticHigh4_roots :
    ((809103 / 10000 : ℝ) ≤ Real.sqrt (242220 / 37 : ℝ) ∧
      Real.sqrt (242220 / 37 : ℝ) ≤ 50569 / 625 ∧ Real.sqrt (12111 : ℝ) ≤ 2201 / 20) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 4. -/
theorem gammaAnalyticHigh4_logs :
    Real.log (242220 / 37 : ℝ) ≤ 87867 / 10000 ∧ Real.log (12111 : ℝ) ≤ 94019 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (242220 / 37) 13 20 0 (87867 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 12111 14 20 0 (94019 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh4_main (hRH : RiemannHypothesis) :
    (33433 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 12111,
        Real.exp (-(n : ℝ) / (242220 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (242220 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (160 / 3969) * ((242220 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((242220 / 37) * (37 / 20)) + 1) / (160 / 3969) +
        1839 / 1000 ≤
      513337 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh4_roots.2.2]
  have hs :
    Real.sqrt ((242220 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((242220 / 37) * (37 / 20)) +
        21 / 20 ≤
      23843 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh4_roots.2.2, gammaAnalyticHigh4_logs.2]
  have hz :
    Real.sqrt (242220 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (242220 / 37) + 2469 / 800 ≤
      19251 / 1000 := by
    linarith only [gammaAnalyticHigh4_roots.2.1, gammaAnalyticHigh4_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 242220 / 37) (y := 37 / 20) (h := 160 / 3969) (r :=
      50569 / 625) (e := 78619 / 500000) (p := 513337 / 1000) (s := 23843 / 1000) (z :=
      19251 / 1000) (F := 33433 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh4_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (242220 / 37 : ℝ) * (37 / 20) = 12111 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh4_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (242220 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (242220 / 37 : ℝ)) ≤
      81149 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 809103 / 10000) (T := 50569 / 625) (Z := 87867 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh4_roots.1 gammaAnalyticHigh4_roots.2.1
      gammaAnalyticHigh4_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh4_power : (242220 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 357 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 4 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh4_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20093 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20271 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (12111 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20093 / 100)]
  apply
    reject_03_of_analytic_caps (B := 12111) (x := 242220 / 37) (H := 20271 / 100) (R :=
      809103 / 10000) (W := 357 / 50000) (F := 33433 / 500) (U := 81149 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh4_power (gammaAnalyticHigh4_main hGRH.riemann)
      (gammaAnalyticHigh4_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 5. -/
theorem gammaAnalyticHigh5_roots :
    ((408143 / 5000 : ℝ) ≤ Real.sqrt (246540 / 37 : ℝ) ∧
      Real.sqrt (246540 / 37 : ℝ) ≤ 816287 / 10000 ∧ Real.sqrt (12327 : ℝ) ≤ 1110271 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 5. -/
theorem gammaAnalyticHigh5_logs :
    Real.log (246540 / 37 : ℝ) ≤ 22011 / 2500 ∧ Real.log (12327 : ℝ) ≤ 23549 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (246540 / 37) 13 20 0 (22011 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 12327 14 20 0 (23549 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh5_main (hRH : RiemannHypothesis) :
    (67469 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 12327,
        Real.exp (-(n : ℝ) / (246540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (246540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 49833) * ((246540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((246540 / 37) * (37 / 20)) + 1) / (2000 / 49833) +
        1839 / 1000 ≤
      520143 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh5_roots.2.2]
  have hs :
    Real.sqrt ((246540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((246540 / 37) * (37 / 20)) +
        21 / 20 ≤
      5981 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh5_roots.2.2, gammaAnalyticHigh5_logs.2]
  have hz :
    Real.sqrt (246540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (246540 / 37) + 2469 / 800 ≤
      2414 / 125 := by
    linarith only [gammaAnalyticHigh5_roots.2.1, gammaAnalyticHigh5_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 246540 / 37) (y := 37 / 20) (h := 2000 / 49833) (r :=
      816287 / 10000) (e := 78619 / 500000) (p := 520143 / 1000) (s := 5981 / 250) (z := 2414 / 125)
      (F := 67469 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh5_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (246540 / 37 : ℝ) * (37 / 20) = 12327 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh5_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (246540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (246540 / 37 : ℝ)) ≤
      40933 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 408143 / 5000) (T := 816287 / 10000) (Z := 22011 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh5_roots.1 gammaAnalyticHigh5_roots.2.1
      gammaAnalyticHigh5_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh5_power : (246540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 707 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 5 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh5_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20271 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20451 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (12327 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20271 / 100)]
  apply
    reject_03_of_analytic_caps (B := 12327) (x := 246540 / 37) (H := 20451 / 100) (R :=
      408143 / 5000) (W := 707 / 100000) (F := 67469 / 1000) (U := 40933 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh5_power (gammaAnalyticHigh5_main hGRH.riemann)
      (gammaAnalyticHigh5_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 6. -/
theorem gammaAnalyticHigh6_roots :
    ((411769 / 5000 : ℝ) ≤ Real.sqrt (250940 / 37 : ℝ) ∧
      Real.sqrt (250940 / 37 : ℝ) ≤ 823539 / 10000 ∧ Real.sqrt (12547 : ℝ) ≤ 560067 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 6. -/
theorem gammaAnalyticHigh6_logs :
    Real.log (250940 / 37 : ℝ) ≤ 88221 / 10000 ∧ Real.log (12547 : ℝ) ≤ 94373 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (250940 / 37) 13 20 0 (88221 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 12547 14 20 0 (94373 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh6_main (hRH : RiemannHypothesis) :
    (34039 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 12547,
        Real.exp (-(n : ℝ) / (250940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (250940 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 100107) * ((250940 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((250940 / 37) * (37 / 20)) + 1) / (4000 / 100107) +
        1839 / 1000 ≤
      105409 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh6_roots.2.2]
  have hs :
    Real.sqrt ((250940 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((250940 / 37) * (37 / 20)) +
        21 / 20 ≤
      12003 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh6_roots.2.2, gammaAnalyticHigh6_logs.2]
  have hz :
    Real.sqrt (250940 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (250940 / 37) + 2469 / 800 ≤
      4843 / 250 := by
    linarith only [gammaAnalyticHigh6_roots.2.1, gammaAnalyticHigh6_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 250940 / 37) (y := 37 / 20) (h := 4000 / 100107) (r :=
      823539 / 10000) (e := 78619 / 500000) (p := 105409 / 200) (s := 12003 / 500) (z := 4843 / 250)
      (F := 34039 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh6_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (250940 / 37 : ℝ) * (37 / 20) = 12547 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh6_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (250940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (250940 / 37 : ℝ)) ≤
      8259 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 411769 / 5000) (T := 823539 / 10000) (Z := 88221 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh6_roots.1 gammaAnalyticHigh6_roots.2.1
      gammaAnalyticHigh6_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh6_power : (250940 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 7 / 1000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 6 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh6_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20451 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20633 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (12547 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20451 / 100)]
  apply
    reject_03_of_analytic_caps (B := 12547) (x := 250940 / 37) (H := 20633 / 100) (R :=
      411769 / 5000) (W := 7 / 1000) (F := 34039 / 500) (U := 8259 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh6_power (gammaAnalyticHigh6_main hGRH.riemann)
      (gammaAnalyticHigh6_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 7. -/
theorem gammaAnalyticHigh7_roots :
    ((830857 / 10000 : ℝ) ≤ Real.sqrt (255420 / 37 : ℝ) ∧
      Real.sqrt (255420 / 37 : ℝ) ≤ 415429 / 5000 ∧ Real.sqrt (12771 : ℝ) ≤ 1130089 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 7. -/
theorem gammaAnalyticHigh7_logs :
    Real.log (255420 / 37 : ℝ) ≤ 44199 / 5000 ∧ Real.log (12771 : ℝ) ≤ 1891 / 200 := by
  have hc1 : Analysis.rationalLogIntervalCheck (255420 / 37) 13 20 0 (44199 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 12771 14 20 0 (1891 / 200) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh7_main (hRH : RiemannHypothesis) :
    (17173 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 12771,
        Real.exp (-(n : ℝ) / (255420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (255420 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 20111) * ((255420 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((255420 / 37) * (37 / 20)) + 1) / (800 / 20111) +
        1839 / 1000 ≤
      534041 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh7_roots.2.2]
  have hs :
    Real.sqrt ((255420 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((255420 / 37) * (37 / 20)) +
        21 / 20 ≤
      24089 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh7_roots.2.2, gammaAnalyticHigh7_logs.2]
  have hz :
    Real.sqrt (255420 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (255420 / 37) + 2469 / 800 ≤
      19433 / 1000 := by
    linarith only [gammaAnalyticHigh7_roots.2.1, gammaAnalyticHigh7_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 255420 / 37) (y := 37 / 20) (h := 800 / 20111) (r :=
      415429 / 5000) (e := 78619 / 500000) (p := 534041 / 1000) (s := 24089 / 1000) (z :=
      19433 / 1000) (F := 17173 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh7_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (255420 / 37 : ℝ) * (37 / 20) = 12771 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh7_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (255420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (255420 / 37 : ℝ)) ≤
      2083 / 25 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 830857 / 10000) (T := 415429 / 5000) (Z := 44199 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh7_roots.1 gammaAnalyticHigh7_roots.2.1
      gammaAnalyticHigh7_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh7_power : (255420 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 693 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 7 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh7_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20633 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20817 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (12771 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20633 / 100)]
  apply
    reject_03_of_analytic_caps (B := 12771) (x := 255420 / 37) (H := 20817 / 100) (R :=
      830857 / 10000) (W := 693 / 100000) (F := 17173 / 250) (U := 2083 / 25) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh7_power (gammaAnalyticHigh7_main hGRH.riemann)
      (gammaAnalyticHigh7_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 8. -/
theorem gammaAnalyticHigh8_roots :
    ((838273 / 10000 : ℝ) ≤ Real.sqrt (260000 / 37 : ℝ) ∧
      Real.sqrt (260000 / 37 : ℝ) ≤ 419137 / 5000 ∧ Real.sqrt (13000 : ℝ) ≤ 71261 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 8. -/
theorem gammaAnalyticHigh8_logs :
    Real.log (260000 / 37 : ℝ) ≤ 5536 / 625 ∧ Real.log (13000 : ℝ) ≤ 11841 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (260000 / 37) 13 20 0 (5536 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 13000 14 20 0 (11841 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh8_main (hRH : RiemannHypothesis) :
    (34657 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 13000,
        Real.exp (-(n : ℝ) / (260000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (260000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 101003) * ((260000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((260000 / 37) * (37 / 20)) + 1) / (4000 / 101003) +
        1839 / 1000 ≤
      541161 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh8_roots.2.2]
  have hs :
    Real.sqrt ((260000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((260000 / 37) * (37 / 20)) +
        21 / 20 ≤
      6043 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh8_roots.2.2, gammaAnalyticHigh8_logs.2]
  have hz :
    Real.sqrt (260000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (260000 / 37) + 2469 / 800 ≤
      3899 / 200 := by
    linarith only [gammaAnalyticHigh8_roots.2.1, gammaAnalyticHigh8_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 260000 / 37) (y := 37 / 20) (h := 4000 / 101003) (r :=
      419137 / 5000) (e := 78619 / 500000) (p := 541161 / 1000) (s := 6043 / 250) (z := 3899 / 200)
      (F := 34657 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh8_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (260000 / 37 : ℝ) * (37 / 20) = 13000 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh8_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (260000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (260000 / 37 : ℝ)) ≤
      4203 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 838273 / 10000) (T := 419137 / 5000) (Z := 5536 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh8_roots.1 gammaAnalyticHigh8_roots.2.1
      gammaAnalyticHigh8_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh8_power : (260000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 343 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 8 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh8_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20817 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21003 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (13000 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20817 / 100)]
  apply
    reject_03_of_analytic_caps (B := 13000) (x := 260000 / 37) (H := 21003 / 100) (R :=
      838273 / 10000) (W := 343 / 50000) (F := 34657 / 500) (U := 4203 / 50) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh8_power (gammaAnalyticHigh8_main hGRH.riemann)
      (gammaAnalyticHigh8_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 9. -/
theorem gammaAnalyticHigh9_roots :
    ((105719 / 1250 : ℝ) ≤ Real.sqrt (264660 / 37 : ℝ) ∧
      Real.sqrt (264660 / 37 : ℝ) ≤ 845753 / 10000 ∧ Real.sqrt (13233 : ℝ) ≤ 287587 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 9. -/
theorem gammaAnalyticHigh9_logs :
    Real.log (264660 / 37 : ℝ) ≤ 88753 / 10000 ∧ Real.log (13233 : ℝ) ≤ 18981 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (264660 / 37) 13 20 0 (88753 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 13233 14 20 0 (18981 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh9_main (hRH : RiemannHypothesis) :
    (34971 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 13233,
        Real.exp (-(n : ℝ) / (264660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (264660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 101451) * ((264660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((264660 / 37) * (37 / 20)) + 1) / (4000 / 101451) +
        1839 / 1000 ≤
      274187 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh9_roots.2.2]
  have hs :
    Real.sqrt ((264660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((264660 / 37) * (37 / 20)) +
        21 / 20 ≤
      4851 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh9_roots.2.2, gammaAnalyticHigh9_logs.2]
  have hz :
    Real.sqrt (264660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (264660 / 37) + 2469 / 800 ≤
      19557 / 1000 := by
    linarith only [gammaAnalyticHigh9_roots.2.1, gammaAnalyticHigh9_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 264660 / 37) (y := 37 / 20) (h := 4000 / 101451) (r :=
      845753 / 10000) (e := 78619 / 500000) (p := 274187 / 500) (s := 4851 / 200) (z :=
      19557 / 1000) (F := 34971 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh9_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (264660 / 37 : ℝ) * (37 / 20) = 13233 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh9_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (264660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (264660 / 37 : ℝ)) ≤
      84807 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 105719 / 1250) (T := 845753 / 10000) (Z := 88753 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh9_roots.1 gammaAnalyticHigh9_roots.2.1
      gammaAnalyticHigh9_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh9_power : (264660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 679 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 9 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh9_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21003 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21191 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (13233 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21003 / 100)]
  apply
    reject_03_of_analytic_caps (B := 13233) (x := 264660 / 37) (H := 21191 / 100) (R :=
      105719 / 1250) (W := 679 / 100000) (F := 34971 / 500) (U := 84807 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh9_power (gammaAnalyticHigh9_main hGRH.riemann)
      (gammaAnalyticHigh9_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 10. -/
theorem gammaAnalyticHigh10_roots :
    ((213331 / 2500 : ℝ) ≤ Real.sqrt (269420 / 37 : ℝ) ∧
      Real.sqrt (269420 / 37 : ℝ) ≤ 34133 / 400 ∧ Real.sqrt (13471 : ℝ) ≤ 1160647 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 10. -/
theorem gammaAnalyticHigh10_logs :
    Real.log (269420 / 37 : ℝ) ≤ 22233 / 2500 ∧ Real.log (13471 : ℝ) ≤ 95083 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (269420 / 37) 13 20 0 (22233 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 13471 14 20 0 (95083 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh10_main (hRH : RiemannHypothesis) :
    (70577 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 13471,
        Real.exp (-(n : ℝ) / (269420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (269420 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 50953) * ((269420 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((269420 / 37) * (37 / 20)) + 1) / (2000 / 50953) +
        1839 / 1000 ≤
      555709 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh10_roots.2.2]
  have hs :
    Real.sqrt ((269420 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((269420 / 37) * (37 / 20)) +
        21 / 20 ≤
      24339 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh10_roots.2.2, gammaAnalyticHigh10_logs.2]
  have hz :
    Real.sqrt (269420 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (269420 / 37) + 2469 / 800 ≤
      19619 / 1000 := by
    linarith only [gammaAnalyticHigh10_roots.2.1, gammaAnalyticHigh10_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 269420 / 37) (y := 37 / 20) (h := 2000 / 50953) (r :=
      34133 / 400) (e := 78619 / 500000) (p := 555709 / 1000) (s := 24339 / 1000) (z :=
      19619 / 1000) (F := 70577 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh10_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (269420 / 37 : ℝ) * (37 / 20) = 13471 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh10_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (269420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (269420 / 37 : ℝ)) ≤
      85563 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 213331 / 2500) (T := 34133 / 400) (Z := 22233 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh10_roots.1
      gammaAnalyticHigh10_roots.2.1 gammaAnalyticHigh10_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh10_power : (269420 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 673 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 10 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh10_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21191 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1069 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (13471 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21191 / 100)]
  apply
    reject_03_of_analytic_caps (B := 13471) (x := 269420 / 37) (H := 1069 / 5) (R := 213331 / 2500)
      (W := 673 / 100000) (F := 70577 / 1000) (U := 85563 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh10_power (gammaAnalyticHigh10_main hGRH.riemann)
      (gammaAnalyticHigh10_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 11. -/
theorem gammaAnalyticHigh11_roots :
    ((430477 / 5000 : ℝ) ≤ Real.sqrt (274260 / 37 : ℝ) ∧
      Real.sqrt (274260 / 37 : ℝ) ≤ 172191 / 2000 ∧ Real.sqrt (13713 : ℝ) ≤ 585513 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 11. -/
theorem gammaAnalyticHigh11_logs :
    Real.log (274260 / 37 : ℝ) ≤ 8911 / 1000 ∧ Real.log (13713 : ℝ) ≤ 95261 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (274260 / 37) 13 20 0 (8911 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 13713 14 20 0 (95261 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh11_main (hRH : RiemannHypothesis) :
    (35609 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 13713,
        Real.exp (-(n : ℝ) / (274260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (274260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 51177) * ((274260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((274260 / 37) * (37 / 20)) + 1) / (2000 / 51177) +
        1839 / 1000 ≤
      281567 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh11_roots.2.2]
  have hs :
    Real.sqrt ((274260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((274260 / 37) * (37 / 20)) +
        21 / 20 ≤
      3053 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh11_roots.2.2, gammaAnalyticHigh11_logs.2]
  have hz :
    Real.sqrt (274260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (274260 / 37) + 2469 / 800 ≤
      9841 / 500 := by
    linarith only [gammaAnalyticHigh11_roots.2.1, gammaAnalyticHigh11_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 274260 / 37) (y := 37 / 20) (h := 2000 / 51177) (r :=
      172191 / 2000) (e := 78619 / 500000) (p := 281567 / 500) (s := 3053 / 125) (z := 9841 / 500)
      (F := 35609 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh11_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (274260 / 37 : ℝ) * (37 / 20) = 13713 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh11_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (274260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (274260 / 37 : ℝ)) ≤
      3453 / 40 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 430477 / 5000) (T := 172191 / 2000) (Z := 8911 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh11_roots.1
      gammaAnalyticHigh11_roots.2.1 gammaAnalyticHigh11_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh11_power : (274260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 333 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 11 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh11_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1069 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5393 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (13713 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1069 / 5)]
  apply
    reject_03_of_analytic_caps (B := 13713) (x := 274260 / 37) (H := 5393 / 25) (R := 430477 / 5000)
      (W := 333 / 50000) (F := 35609 / 500) (U := 3453 / 40) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh11_power (gammaAnalyticHigh11_main hGRH.riemann)
      (gammaAnalyticHigh11_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 12. -/
theorem gammaAnalyticHigh12_roots :
    ((434337 / 5000 : ℝ) ≤ Real.sqrt (279200 / 37 : ℝ) ∧
      Real.sqrt (279200 / 37 : ℝ) ≤ 34747 / 400 ∧ Real.sqrt (13960 : ℝ) ≤ 47261 / 400) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 12. -/
theorem gammaAnalyticHigh12_logs :
    Real.log (279200 / 37 : ℝ) ≤ 11161 / 1250 ∧ Real.log (13960 : ℝ) ≤ 1193 / 125 := by
  have hc1 : Analysis.rationalLogIntervalCheck (279200 / 37) 13 20 0 (11161 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 13960 14 20 0 (1193 / 125) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh12_main (hRH : RiemannHypothesis) :
    (35933 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 13960,
        Real.exp (-(n : ℝ) / (279200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (279200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (125 / 3213) * ((279200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((279200 / 37) * (37 / 20)) + 1) / (125 / 3213) +
        1839 / 1000 ≤
      285339 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh12_roots.2.2]
  have hs :
    Real.sqrt ((279200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((279200 / 37) * (37 / 20)) +
        21 / 20 ≤
      2451 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh12_roots.2.2, gammaAnalyticHigh12_logs.2]
  have hz :
    Real.sqrt (279200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (279200 / 37) + 2469 / 800 ≤
      3949 / 200 := by
    linarith only [gammaAnalyticHigh12_roots.2.1, gammaAnalyticHigh12_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 279200 / 37) (y := 37 / 20) (h := 125 / 3213) (r :=
      34747 / 400) (e := 78619 / 500000) (p := 285339 / 500) (s := 2451 / 100) (z := 3949 / 200)
      (F := 35933 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh12_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (279200 / 37 : ℝ) * (37 / 20) = 13960 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh12_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (279200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (279200 / 37 : ℝ)) ≤
      17419 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 434337 / 5000) (T := 34747 / 400) (Z := 11161 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh12_roots.1
      gammaAnalyticHigh12_roots.2.1 gammaAnalyticHigh12_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh12_power : (279200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 659 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 12 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh12_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5393 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10883 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (13960 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5393 / 25)]
  apply
    reject_03_of_analytic_caps (B := 13960) (x := 279200 / 37) (H := 10883 / 50) (R :=
      434337 / 5000) (W := 659 / 100000) (F := 35933 / 500) (U := 17419 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh12_power (gammaAnalyticHigh12_main hGRH.riemann)
      (gammaAnalyticHigh12_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 13. -/
theorem gammaAnalyticHigh13_roots :
    ((876479 / 10000 : ℝ) ≤ Real.sqrt (284240 / 37 : ℝ) ∧
      Real.sqrt (284240 / 37 : ℝ) ≤ 10956 / 125 ∧ Real.sqrt (14212 : ℝ) ≤ 1192141 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 13. -/
theorem gammaAnalyticHigh13_logs :
    Real.log (284240 / 37 : ℝ) ≤ 89467 / 10000 ∧ Real.log (14212 : ℝ) ≤ 95619 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (284240 / 37) 13 20 0 (89467 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 14212 14 20 0 (95619 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh13_main (hRH : RiemannHypothesis) :
    (72521 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 14212,
        Real.exp (-(n : ℝ) / (284240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (284240 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 51639) * ((284240 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((284240 / 37) * (37 / 20)) + 1) / (2000 / 51639) +
        1839 / 1000 ≤
      28917 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh13_roots.2.2]
  have hs :
    Real.sqrt ((284240 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((284240 / 37) * (37 / 20)) +
        21 / 20 ≤
      6149 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh13_roots.2.2, gammaAnalyticHigh13_logs.2]
  have hz :
    Real.sqrt (284240 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (284240 / 37) + 2469 / 800 ≤
      19809 / 1000 := by
    linarith only [gammaAnalyticHigh13_roots.2.1, gammaAnalyticHigh13_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 284240 / 37) (y := 37 / 20) (h := 2000 / 51639) (r :=
      10956 / 125) (e := 78619 / 500000) (p := 28917 / 50) (s := 6149 / 250) (z := 19809 / 1000)
      (F := 72521 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh13_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (284240 / 37 : ℝ) * (37 / 20) = 14212 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh13_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (284240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (284240 / 37 : ℝ)) ≤
      43937 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 876479 / 10000) (T := 10956 / 125) (Z := 89467 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh13_roots.1
      gammaAnalyticHigh13_roots.2.1 gammaAnalyticHigh13_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh13_power : (284240 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 653 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 13 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh13_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10883 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10981 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (14212 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10883 / 50)]
  apply
    reject_03_of_analytic_caps (B := 14212) (x := 284240 / 37) (H := 10981 / 50) (R :=
      876479 / 10000) (W := 653 / 100000) (F := 72521 / 1000) (U := 43937 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh13_power (gammaAnalyticHigh13_main hGRH.riemann)
      (gammaAnalyticHigh13_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 14. -/
theorem gammaAnalyticHigh14_roots :
    ((55273 / 625 : ℝ) ≤ Real.sqrt (289380 / 37 : ℝ) ∧
      Real.sqrt (289380 / 37 : ℝ) ≤ 884369 / 10000 ∧ Real.sqrt (14469 : ℝ) ≤ 150359 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 14. -/
theorem gammaAnalyticHigh14_logs :
    Real.log (289380 / 37 : ℝ) ≤ 44823 / 5000 ∧ Real.log (14469 : ℝ) ≤ 47899 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (289380 / 37) 13 20 0 (44823 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 14469 14 20 0 (47899 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh14_main (hRH : RiemannHypothesis) :
    (73183 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 14469,
        Real.exp (-(n : ℝ) / (289380 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (289380 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (200 / 5187) * ((289380 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((289380 / 37) * (37 / 20)) + 1) / (200 / 5187) +
        1839 / 1000 ≤
      14653 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh14_roots.2.2]
  have hs :
    Real.sqrt ((289380 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((289380 / 37) * (37 / 20)) +
        21 / 20 ≤
      12341 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh14_roots.2.2, gammaAnalyticHigh14_logs.2]
  have hz :
    Real.sqrt (289380 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (289380 / 37) + 2469 / 800 ≤
      19873 / 1000 := by
    linarith only [gammaAnalyticHigh14_roots.2.1, gammaAnalyticHigh14_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 289380 / 37) (y := 37 / 20) (h := 200 / 5187) (r :=
      884369 / 10000) (e := 78619 / 500000) (p := 14653 / 25) (s := 12341 / 500) (z := 19873 / 1000)
      (F := 73183 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh14_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (289380 / 37 : ℝ) * (37 / 20) = 14469 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh14_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (289380 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (289380 / 37 : ℝ)) ≤
      44331 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 55273 / 625) (T := 884369 / 10000) (Z := 44823 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh14_roots.1
      gammaAnalyticHigh14_roots.2.1 gammaAnalyticHigh14_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh14_power : (289380 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 323 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 14 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh14_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10981 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22159 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (14469 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10981 / 50)]
  apply
    reject_03_of_analytic_caps (B := 14469) (x := 289380 / 37) (H := 22159 / 100) (R := 55273 / 625)
      (W := 323 / 50000) (F := 73183 / 1000) (U := 44331 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh14_power (gammaAnalyticHigh14_main hGRH.riemann)
      (gammaAnalyticHigh14_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 15. -/
theorem gammaAnalyticHigh15_roots :
    ((892309 / 10000 : ℝ) ≤ Real.sqrt (294600 / 37 : ℝ) ∧
      Real.sqrt (294600 / 37 : ℝ) ≤ 89231 / 1000 ∧ Real.sqrt (14730 : ℝ) ≤ 1213673 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 15. -/
theorem gammaAnalyticHigh15_logs :
    Real.log (294600 / 37 : ℝ) ≤ 3593 / 400 ∧ Real.log (14730 : ℝ) ≤ 95977 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (294600 / 37) 13 20 0 (3593 / 400) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 14730 14 20 0 (95977 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh15_main (hRH : RiemannHypothesis) :
    (73849 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 14730,
        Real.exp (-(n : ℝ) / (294600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (294600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 52101) * ((294600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((294600 / 37) * (37 / 20)) + 1) / (2000 / 52101) +
        1839 / 1000 ≤
      296993 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh15_roots.2.2]
  have hs :
    Real.sqrt ((294600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((294600 / 37) * (37 / 20)) +
        21 / 20 ≤
      24769 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh15_roots.2.2, gammaAnalyticHigh15_logs.2]
  have hz :
    Real.sqrt (294600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (294600 / 37) + 2469 / 800 ≤
      19937 / 1000 := by
    linarith only [gammaAnalyticHigh15_roots.2.1, gammaAnalyticHigh15_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 294600 / 37) (y := 37 / 20) (h := 2000 / 52101) (r :=
      89231 / 1000) (e := 78619 / 500000) (p := 296993 / 500) (s := 24769 / 1000) (z :=
      19937 / 1000) (F := 73849 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh15_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (294600 / 37 : ℝ) * (37 / 20) = 14730 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh15_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (294600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (294600 / 37 : ℝ)) ≤
      17891 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 892309 / 10000) (T := 89231 / 1000) (Z := 3593 / 400)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh15_roots.1
      gammaAnalyticHigh15_roots.2.1 gammaAnalyticHigh15_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh15_power : (294600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 4 / 625 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 15 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh15_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22159 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11179 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (14730 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22159 / 100)]
  apply
    reject_03_of_analytic_caps (B := 14730) (x := 294600 / 37) (H := 11179 / 50) (R :=
      892309 / 10000) (W := 4 / 625) (F := 73849 / 1000) (U := 17891 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh15_power (gammaAnalyticHigh15_main hGRH.riemann)
      (gammaAnalyticHigh15_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 16. -/
theorem gammaAnalyticHigh16_roots :
    ((90033 / 1000 : ℝ) ≤ Real.sqrt (299920 / 37 : ℝ) ∧
      Real.sqrt (299920 / 37 : ℝ) ≤ 900331 / 10000 ∧ Real.sqrt (14996 : ℝ) ≤ 612291 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 16. -/
theorem gammaAnalyticHigh16_logs :
    Real.log (299920 / 37 : ℝ) ≤ 22501 / 2500 ∧ Real.log (14996 : ℝ) ≤ 24039 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (299920 / 37) 13 20 0 (22501 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 14996 14 20 0 (24039 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh16_main (hRH : RiemannHypothesis) :
    (37261 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 14996,
        Real.exp (-(n : ℝ) / (299920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (299920 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 104671) * ((299920 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((299920 / 37) * (37 / 20)) + 1) / (4000 / 104671) +
        1839 / 1000 ≤
      300983 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh16_roots.2.2]
  have hs :
    Real.sqrt ((299920 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((299920 / 37) * (37 / 20)) +
        21 / 20 ≤
      3107 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh16_roots.2.2, gammaAnalyticHigh16_logs.2]
  have hz :
    Real.sqrt (299920 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (299920 / 37) + 2469 / 800 ≤
      10001 / 500 := by
    linarith only [gammaAnalyticHigh16_roots.2.1, gammaAnalyticHigh16_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 299920 / 37) (y := 37 / 20) (h := 4000 / 104671) (r :=
      900331 / 10000) (e := 78619 / 500000) (p := 300983 / 500) (s := 3107 / 125) (z := 10001 / 500)
      (F := 37261 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh16_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (299920 / 37 : ℝ) * (37 / 20) = 14996 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh16_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (299920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (299920 / 37 : ℝ)) ≤
      11282 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 90033 / 1000) (T := 900331 / 10000) (Z := 22501 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh16_roots.1
      gammaAnalyticHigh16_roots.2.1 gammaAnalyticHigh16_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh16_power : (299920 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 633 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 16 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh16_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11179 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1128 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (14996 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11179 / 50)]
  apply
    reject_03_of_analytic_caps (B := 14996) (x := 299920 / 37) (H := 1128 / 5) (R := 90033 / 1000)
      (W := 633 / 100000) (F := 37261 / 500) (U := 11282 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh16_power (gammaAnalyticHigh16_main hGRH.riemann)
      (gammaAnalyticHigh16_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 17. -/
theorem gammaAnalyticHigh17_roots :
    ((454229 / 5000 : ℝ) ≤ Real.sqrt (305360 / 37 : ℝ) ∧
      Real.sqrt (305360 / 37 : ℝ) ≤ 908459 / 10000 ∧ Real.sqrt (15268 : ℝ) ≤ 617819 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 17. -/
theorem gammaAnalyticHigh17_logs :
    Real.log (305360 / 37 : ℝ) ≤ 11273 / 1250 ∧ Real.log (15268 : ℝ) ≤ 6021 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (305360 / 37) 14 20 0 (11273 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 15268 14 20 0 (6021 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh17_main (hRH : RiemannHypothesis) :
    (18801 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 15268,
        Real.exp (-(n : ℝ) / (305360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (305360 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (200 / 5257) * ((305360 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((305360 / 37) * (37 / 20)) + 1) / (200 / 5257) +
        1839 / 1000 ≤
      61009 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh17_roots.2.2]
  have hs :
    Real.sqrt ((305360 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((305360 / 37) * (37 / 20)) +
        21 / 20 ≤
      4989 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh17_roots.2.2, gammaAnalyticHigh17_logs.2]
  have hz :
    Real.sqrt (305360 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (305360 / 37) + 2469 / 800 ≤
      5017 / 250 := by
    linarith only [gammaAnalyticHigh17_roots.2.1, gammaAnalyticHigh17_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 305360 / 37) (y := 37 / 20) (h := 200 / 5257) (r :=
      908459 / 10000) (e := 78619 / 500000) (p := 61009 / 100) (s := 4989 / 200) (z := 5017 / 250)
      (F := 18801 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh17_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (305360 / 37 : ℝ) * (37 / 20) = 15268 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh17_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (305360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (305360 / 37 : ℝ)) ≤
      91067 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 454229 / 5000) (T := 908459 / 10000) (Z := 11273 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh17_roots.1
      gammaAnalyticHigh17_roots.2.1 gammaAnalyticHigh17_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh17_power : (305360 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 627 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 17 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh17_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1128 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22763 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (15268 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1128 / 5)]
  apply
    reject_03_of_analytic_caps (B := 15268) (x := 305360 / 37) (H := 22763 / 100) (R :=
      454229 / 5000) (W := 627 / 100000) (F := 18801 / 250) (U := 91067 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh17_power (gammaAnalyticHigh17_main hGRH.riemann)
      (gammaAnalyticHigh17_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 18. -/
theorem gammaAnalyticHigh18_roots :
    ((916633 / 10000 : ℝ) ≤ Real.sqrt (310880 / 37 : ℝ) ∧
      Real.sqrt (310880 / 37 : ℝ) ≤ 458317 / 5000 ∧ Real.sqrt (15544 : ℝ) ≤ 311689 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 18. -/
theorem gammaAnalyticHigh18_logs :
    Real.log (310880 / 37 : ℝ) ≤ 90363 / 10000 ∧ Real.log (15544 : ℝ) ≤ 19303 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (310880 / 37) 14 20 0 (90363 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 15544 14 20 0 (19303 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh18_main (hRH : RiemannHypothesis) :
    (7589 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 15544,
        Real.exp (-(n : ℝ) / (310880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (310880 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (250 / 6601) * ((310880 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((310880 / 37) * (37 / 20)) + 1) / (250 / 6601) +
        1839 / 1000 ≤
      123659 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh18_roots.2.2]
  have hs :
    Real.sqrt ((310880 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((310880 / 37) * (37 / 20)) +
        21 / 20 ≤
      25033 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh18_roots.2.2, gammaAnalyticHigh18_logs.2]
  have hz :
    Real.sqrt (310880 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (310880 / 37) + 2469 / 800 ≤
      20133 / 1000 := by
    linarith only [gammaAnalyticHigh18_roots.2.1, gammaAnalyticHigh18_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 310880 / 37) (y := 37 / 20) (h := 250 / 6601) (r :=
      458317 / 5000) (e := 78619 / 500000) (p := 123659 / 200) (s := 25033 / 1000) (z :=
      20133 / 1000) (F := 7589 / 100) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh18_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (310880 / 37 : ℝ) * (37 / 20) = 15544 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh18_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (310880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (310880 / 37 : ℝ)) ≤
      22971 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 916633 / 10000) (T := 458317 / 5000) (Z := 90363 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh18_roots.1
      gammaAnalyticHigh18_roots.2.1 gammaAnalyticHigh18_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh18_power : (310880 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 621 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 18 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh18_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22763 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5742 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (15544 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22763 / 100)]
  apply
    reject_03_of_analytic_caps (B := 15544) (x := 310880 / 37) (H := 5742 / 25) (R :=
      916633 / 10000) (W := 621 / 100000) (F := 7589 / 100) (U := 22971 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh18_power (gammaAnalyticHigh18_main hGRH.riemann)
      (gammaAnalyticHigh18_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 19. -/
theorem gammaAnalyticHigh19_roots :
    ((924881 / 10000 : ℝ) ≤ Real.sqrt (316500 / 37 : ℝ) ∧
      Real.sqrt (316500 / 37 : ℝ) ≤ 462441 / 5000 ∧ Real.sqrt (15825 : ℝ) ≤ 50319 / 400) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 19. -/
theorem gammaAnalyticHigh19_logs :
    Real.log (316500 / 37 : ℝ) ≤ 45271 / 5000 ∧ Real.log (15825 : ℝ) ≤ 48347 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (316500 / 37) 14 20 0 (45271 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 15825 14 20 0 (48347 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh19_main (hRH : RiemannHypothesis) :
    (38291 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 15825,
        Real.exp (-(n : ℝ) / (316500 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (316500 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 26523) * ((316500 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((316500 / 37) * (37 / 20)) + 1) / (1000 / 26523) +
        1839 / 1000 ≤
      626613 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh19_roots.2.2]
  have hs :
    Real.sqrt ((316500 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((316500 / 37) * (37 / 20)) +
        21 / 20 ≤
      12561 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh19_roots.2.2, gammaAnalyticHigh19_logs.2]
  have hz :
    Real.sqrt (316500 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (316500 / 37) + 2469 / 800 ≤
      20199 / 1000 := by
    linarith only [gammaAnalyticHigh19_roots.2.1, gammaAnalyticHigh19_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 316500 / 37) (y := 37 / 20) (h := 1000 / 26523) (r :=
      462441 / 5000) (e := 78619 / 500000) (p := 626613 / 1000) (s := 12561 / 500) (z :=
      20199 / 1000) (F := 38291 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh19_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (316500 / 37 : ℝ) * (37 / 20) = 15825 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh19_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (316500 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (316500 / 37 : ℝ)) ≤
      92707 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 924881 / 10000) (T := 462441 / 5000) (Z := 45271 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh19_roots.1
      gammaAnalyticHigh19_roots.2.1 gammaAnalyticHigh19_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh19_power : (316500 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 307 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 19 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh19_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5742 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (927 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (15825 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5742 / 25)]
  apply
    reject_03_of_analytic_caps (B := 15825) (x := 316500 / 37) (H := 927 / 4) (R := 924881 / 10000)
      (W := 307 / 50000) (F := 38291 / 500) (U := 92707 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh19_power (gammaAnalyticHigh19_main hGRH.riemann)
      (gammaAnalyticHigh19_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 20. -/
theorem gammaAnalyticHigh20_roots :
    ((93323 / 1000 : ℝ) ≤ Real.sqrt (322240 / 37 : ℝ) ∧
      Real.sqrt (322240 / 37 : ℝ) ≤ 933231 / 10000 ∧ Real.sqrt (16112 : ℝ) ≤ 1269331 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 20. -/
theorem gammaAnalyticHigh20_logs :
    Real.log (322240 / 37 : ℝ) ≤ 45361 / 5000 ∧ Real.log (16112 : ℝ) ≤ 48437 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (322240 / 37) 14 20 0 (45361 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 16112 14 20 0 (48437 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh20_main (hRH : RiemannHypothesis) :
    (77283 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 16112,
        Real.exp (-(n : ℝ) / (322240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (322240 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 13321) * ((322240 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((322240 / 37) * (37 / 20)) + 1) / (500 / 13321) +
        1839 / 1000 ≤
      635069 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh20_roots.2.2]
  have hs :
    Real.sqrt ((322240 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((322240 / 37) * (37 / 20)) +
        21 / 20 ≤
      6303 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh20_roots.2.2, gammaAnalyticHigh20_logs.2]
  have hz :
    Real.sqrt (322240 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (322240 / 37) + 2469 / 800 ≤
      10133 / 500 := by
    linarith only [gammaAnalyticHigh20_roots.2.1, gammaAnalyticHigh20_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 322240 / 37) (y := 37 / 20) (h := 500 / 13321) (r :=
      933231 / 10000) (e := 78619 / 500000) (p := 635069 / 1000) (s := 6303 / 250) (z :=
      10133 / 500) (F := 77283 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh20_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (322240 / 37 : ℝ) * (37 / 20) = 16112 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh20_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (322240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (322240 / 37 : ℝ)) ≤
      93541 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 93323 / 1000) (T := 933231 / 10000) (Z := 45361 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh20_roots.1
      gammaAnalyticHigh20_roots.2.1 gammaAnalyticHigh20_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh20_power : (322240 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 19 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 20 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh20_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (927 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4677 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (16112 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 927 / 4)]
  apply
    reject_03_of_analytic_caps (B := 16112) (x := 322240 / 37) (H := 4677 / 20) (R := 93323 / 1000)
      (W := 19 / 3125) (F := 77283 / 1000) (U := 93541 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh20_power (gammaAnalyticHigh20_main hGRH.riemann)
      (gammaAnalyticHigh20_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 21. -/
theorem gammaAnalyticHigh21_roots :
    ((941677 / 10000 : ℝ) ≤ Real.sqrt (328100 / 37 : ℝ) ∧
      Real.sqrt (328100 / 37 : ℝ) ≤ 470839 / 5000 ∧ Real.sqrt (16405 : ℝ) ≤ 1280821 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 21. -/
theorem gammaAnalyticHigh21_logs :
    Real.log (328100 / 37 : ℝ) ≤ 45451 / 5000 ∧ Real.log (16405 : ℝ) ≤ 48527 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (328100 / 37) 14 20 0 (45451 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 16405 15 20 0 (48527 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh21_main (hRH : RiemannHypothesis) :
    (9749 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 16405,
        Real.exp (-(n : ℝ) / (328100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (328100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 107051) * ((328100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((328100 / 37) * (37 / 20)) + 1) / (4000 / 107051) +
        1839 / 1000 ≤
      80458 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh21_roots.2.2]
  have hs :
    Real.sqrt ((328100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((328100 / 37) * (37 / 20)) +
        21 / 20 ≤
      25303 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh21_roots.2.2, gammaAnalyticHigh21_logs.2]
  have hz :
    Real.sqrt (328100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (328100 / 37) + 2469 / 800 ≤
      20333 / 1000 := by
    linarith only [gammaAnalyticHigh21_roots.2.1, gammaAnalyticHigh21_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 328100 / 37) (y := 37 / 20) (h := 4000 / 107051) (r :=
      470839 / 5000) (e := 78619 / 500000) (p := 80458 / 125) (s := 25303 / 1000) (z :=
      20333 / 1000) (F := 9749 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh21_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (328100 / 37 : ℝ) * (37 / 20) = 16405 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh21_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (328100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (328100 / 37 : ℝ)) ≤
      11798 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 941677 / 10000) (T := 470839 / 5000) (Z := 45451 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh21_roots.1
      gammaAnalyticHigh21_roots.2.1 gammaAnalyticHigh21_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh21_power : (328100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 301 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 21 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh21_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (4677 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5899 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (16405 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 4677 / 20)]
  apply
    reject_03_of_analytic_caps (B := 16405) (x := 328100 / 37) (H := 5899 / 25) (R :=
      941677 / 10000) (W := 301 / 50000) (F := 9749 / 125) (U := 11798 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh21_power (gammaAnalyticHigh21_main hGRH.riemann)
      (gammaAnalyticHigh21_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 22. -/
theorem gammaAnalyticHigh22_roots :
    ((59387 / 625 : ℝ) ≤ Real.sqrt (334060 / 37 : ℝ) ∧
      Real.sqrt (334060 / 37 : ℝ) ≤ 950193 / 10000 ∧ Real.sqrt (16703 : ℝ) ≤ 1292401 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 22. -/
theorem gammaAnalyticHigh22_logs :
    Real.log (334060 / 37 : ℝ) ≤ 45541 / 5000 ∧ Real.log (16703 : ℝ) ≤ 48617 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (334060 / 37) 14 20 0 (45541 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 16703 15 20 0 (48617 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh22_main (hRH : RiemannHypothesis) :
    (39353 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 16703,
        Real.exp (-(n : ℝ) / (334060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (334060 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 107527) * ((334060 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((334060 / 37) * (37 / 20)) + 1) / (4000 / 107527) +
        1839 / 1000 ≤
      326183 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh22_roots.2.2]
  have hs :
    Real.sqrt ((334060 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((334060 / 37) * (37 / 20)) +
        21 / 20 ≤
      12697 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh22_roots.2.2, gammaAnalyticHigh22_logs.2]
  have hz :
    Real.sqrt (334060 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (334060 / 37) + 2469 / 800 ≤
      102 / 5 := by
    linarith only [gammaAnalyticHigh22_roots.2.1, gammaAnalyticHigh22_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 334060 / 37) (y := 37 / 20) (h := 4000 / 107527) (r :=
      950193 / 10000) (e := 78619 / 500000) (p := 326183 / 500) (s := 12697 / 500) (z := 102 / 5)
      (F := 39353 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh22_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (334060 / 37 : ℝ) * (37 / 20) = 16703 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh22_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (334060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (334060 / 37 : ℝ)) ≤
      47617 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 59387 / 625) (T := 950193 / 10000) (Z := 45541 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh22_roots.1
      gammaAnalyticHigh22_roots.2.1 gammaAnalyticHigh22_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh22_power : (334060 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 149 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 22 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh22_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5899 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2381 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (16703 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5899 / 25)]
  apply
    reject_03_of_analytic_caps (B := 16703) (x := 334060 / 37) (H := 2381 / 10) (R := 59387 / 625)
      (W := 149 / 25000) (F := 39353 / 500) (U := 47617 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh22_power (gammaAnalyticHigh22_main hGRH.riemann)
      (gammaAnalyticHigh22_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 23. -/
theorem gammaAnalyticHigh23_roots :
    ((958799 / 10000 : ℝ) ≤ Real.sqrt (340140 / 37 : ℝ) ∧
      Real.sqrt (340140 / 37 : ℝ) ≤ 2397 / 25 ∧ Real.sqrt (17007 : ℝ) ≤ 1304109 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 23. -/
theorem gammaAnalyticHigh23_logs :
    Real.log (340140 / 37 : ℝ) ≤ 45631 / 5000 ∧ Real.log (17007 : ℝ) ≤ 48707 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (340140 / 37) 14 20 0 (45631 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 17007 15 20 0 (48707 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh23_main (hRH : RiemannHypothesis) :
    (19857 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 17007,
        Real.exp (-(n : ℝ) / (340140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (340140 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 108017) * ((340140 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((340140 / 37) * (37 / 20)) + 1) / (4000 / 108017) +
        1839 / 1000 ≤
      661203 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh23_roots.2.2]
  have hs :
    Real.sqrt ((340140 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((340140 / 37) * (37 / 20)) +
        21 / 20 ≤
      5097 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh23_roots.2.2, gammaAnalyticHigh23_logs.2]
  have hz :
    Real.sqrt (340140 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (340140 / 37) + 2469 / 800 ≤
      5117 / 250 := by
    linarith only [gammaAnalyticHigh23_roots.2.1, gammaAnalyticHigh23_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 340140 / 37) (y := 37 / 20) (h := 4000 / 108017) (r :=
      2397 / 25) (e := 78619 / 500000) (p := 661203 / 1000) (s := 5097 / 200) (z := 5117 / 250)
      (F := 19857 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh23_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (340140 / 37 : ℝ) * (37 / 20) = 17007 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh23_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (340140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (340140 / 37 : ℝ)) ≤
      48047 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 958799 / 10000) (T := 2397 / 25) (Z := 45631 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh23_roots.1
      gammaAnalyticHigh23_roots.2.1 gammaAnalyticHigh23_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh23_power : (340140 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 59 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 23 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh23_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2381 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (961 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (17007 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2381 / 10)]
  apply
    reject_03_of_analytic_caps (B := 17007) (x := 340140 / 37) (H := 961 / 4) (R := 958799 / 10000)
      (W := 59 / 10000) (F := 19857 / 250) (U := 48047 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh23_power (gammaAnalyticHigh23_main hGRH.riemann)
      (gammaAnalyticHigh23_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 24. -/
theorem gammaAnalyticHigh24_roots :
    ((96747 / 1000 : ℝ) ≤ Real.sqrt (9360 : ℝ) ∧
      Real.sqrt (9360 : ℝ) ≤ 967471 / 10000 ∧ Real.sqrt (17316 : ℝ) ≤ 1315903 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 24. -/
theorem gammaAnalyticHigh24_logs :
    Real.log (9360 : ℝ) ≤ 91443 / 10000 ∧ Real.log (17316 : ℝ) ≤ 48797 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (9360) 14 20 0 (91443 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 17316 15 20 0 (48797 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh24_main (hRH : RiemannHypothesis) :
    (20039 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 17316,
        Real.exp (-(n : ℝ) / (9360)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (9360 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (8 / 217) * ((9360) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((9360) * (37 / 20)) + 1) / (8 / 217) +
        1839 / 1000 ≤
      335073 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh24_roots.2.2]
  have hs :
    Real.sqrt ((9360 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((9360) * (37 / 20)) +
        21 / 20 ≤
      12789 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh24_roots.2.2, gammaAnalyticHigh24_logs.2]
  have hz :
    Real.sqrt (9360 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (9360) + 2469 / 800 ≤ 2567 / 125 := by
    linarith only [gammaAnalyticHigh24_roots.2.1, gammaAnalyticHigh24_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 9360) (y := 37 / 20) (h := 8 / 217) (r := 967471 / 10000)
      (e := 78619 / 500000) (p := 335073 / 500) (s := 12789 / 500) (z := 2567 / 125) (F :=
      20039 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh24_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (9360 : ℝ) * (37 / 20) = 17316 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh24_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (9360)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (9360 : ℝ)) ≤
      2424 / 25 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 96747 / 1000) (T := 967471 / 10000) (Z := 91443 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh24_roots.1
      gammaAnalyticHigh24_roots.2.1 gammaAnalyticHigh24_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh24_power : (9360 : ℝ) ^ (-9 / 16 : ℝ) ≤ 73 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 24 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh24_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (961 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24243 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (17316 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 961 / 4)]
  apply
    reject_03_of_analytic_caps (B := 17316) (x := 9360) (H := 24243 / 100) (R := 96747 / 1000) (W :=
      73 / 12500) (F := 20039 / 250) (U := 2424 / 25) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh24_power (gammaAnalyticHigh24_main hGRH.riemann)
      (gammaAnalyticHigh24_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 25. -/
theorem gammaAnalyticHigh25_roots :
    ((976231 / 10000 : ℝ) ≤ Real.sqrt (352620 / 37 : ℝ) ∧
      Real.sqrt (352620 / 37 : ℝ) ≤ 122029 / 1250 ∧ Real.sqrt (17631 : ℝ) ≤ 663909 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 25. -/
theorem gammaAnalyticHigh25_logs :
    Real.log (352620 / 37 : ℝ) ≤ 91623 / 10000 ∧ Real.log (17631 : ℝ) ≤ 3911 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (352620 / 37) 14 20 0 (91623 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 17631 15 20 0 (3911 / 400) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh25_main (hRH : RiemannHypothesis) :
    (80891 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 17631,
        Real.exp (-(n : ℝ) / (352620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (352620 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 108997) * ((352620 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((352620 / 37) * (37 / 20)) + 1) / (4000 / 108997) +
        1839 / 1000 ≤
      33961 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh25_roots.2.2]
  have hs :
    Real.sqrt ((352620 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((352620 / 37) * (37 / 20)) +
        21 / 20 ≤
      2567 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh25_roots.2.2, gammaAnalyticHigh25_logs.2]
  have hz :
    Real.sqrt (352620 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (352620 / 37) + 2469 / 800 ≤
      4121 / 200 := by
    linarith only [gammaAnalyticHigh25_roots.2.1, gammaAnalyticHigh25_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 352620 / 37) (y := 37 / 20) (h := 4000 / 108997) (r :=
      122029 / 1250) (e := 78619 / 500000) (p := 33961 / 50) (s := 2567 / 100) (z := 4121 / 200)
      (F := 80891 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh25_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (352620 / 37 : ℝ) * (37 / 20) = 17631 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh25_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (352620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (352620 / 37 : ℝ)) ≤
      19567 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 976231 / 10000) (T := 122029 / 1250) (Z := 91623 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh25_roots.1
      gammaAnalyticHigh25_roots.2.1 gammaAnalyticHigh25_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh25_power : (352620 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 289 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 25 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh25_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24243 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12231 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (17631 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24243 / 100)]
  apply
    reject_03_of_analytic_caps (B := 17631) (x := 352620 / 37) (H := 12231 / 50) (R :=
      976231 / 10000) (W := 289 / 50000) (F := 80891 / 1000) (U := 19567 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh25_power (gammaAnalyticHigh25_main hGRH.riemann)
      (gammaAnalyticHigh25_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 26. -/
theorem gammaAnalyticHigh26_roots :
    ((19701 / 200 : ℝ) ≤ Real.sqrt (359020 / 37 : ℝ) ∧
      Real.sqrt (359020 / 37 : ℝ) ≤ 985051 / 10000 ∧ Real.sqrt (17951 : ℝ) ≤ 669907 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 26. -/
theorem gammaAnalyticHigh26_logs :
    Real.log (359020 / 37 : ℝ) ≤ 91803 / 10000 ∧ Real.log (17951 : ℝ) ≤ 19591 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (359020 / 37) 14 20 0 (91803 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 17951 15 20 0 (19591 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh26_main (hRH : RiemannHypothesis) :
    (81631 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 17951,
        Real.exp (-(n : ℝ) / (359020 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (359020 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 109487) * ((359020 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((359020 / 37) * (37 / 20)) + 1) / (4000 / 109487) +
        1839 / 1000 ≤
      688397 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh26_roots.2.2]
  have hs :
    Real.sqrt ((359020 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((359020 / 37) * (37 / 20)) +
        21 / 20 ≤
      25763 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh26_roots.2.2, gammaAnalyticHigh26_logs.2]
  have hz :
    Real.sqrt (359020 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (359020 / 37) + 2469 / 800 ≤
      10337 / 500 := by
    linarith only [gammaAnalyticHigh26_roots.2.1, gammaAnalyticHigh26_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 359020 / 37) (y := 37 / 20) (h := 4000 / 109487) (r :=
      985051 / 10000) (e := 78619 / 500000) (p := 688397 / 1000) (s := 25763 / 1000) (z :=
      10337 / 500) (F := 81631 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh26_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (359020 / 37 : ℝ) * (37 / 20) = 17951 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh26_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (359020 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (359020 / 37 : ℝ)) ≤
      19743 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 19701 / 200) (T := 985051 / 10000) (Z := 91803 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh26_roots.1
      gammaAnalyticHigh26_roots.2.1 gammaAnalyticHigh26_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh26_power : (359020 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 143 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 26 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh26_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12231 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24683 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (17951 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12231 / 50)]
  apply
    reject_03_of_analytic_caps (B := 17951) (x := 359020 / 37) (H := 24683 / 100) (R := 19701 / 200)
      (W := 143 / 25000) (F := 81631 / 1000) (U := 19743 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh26_power (gammaAnalyticHigh26_main hGRH.riemann)
      (gammaAnalyticHigh26_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 27. -/
theorem gammaAnalyticHigh27_roots :
    ((496977 / 5000 : ℝ) ≤ Real.sqrt (365540 / 37 : ℝ) ∧
      Real.sqrt (365540 / 37 : ℝ) ≤ 198791 / 2000 ∧ Real.sqrt (18277 : ℝ) ≤ 54077 / 400) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 27. -/
theorem gammaAnalyticHigh27_logs :
    Real.log (365540 / 37 : ℝ) ≤ 91983 / 10000 ∧ Real.log (18277 : ℝ) ≤ 49067 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (365540 / 37) 14 20 0 (91983 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 18277 15 20 0 (49067 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh27_main (hRH : RiemannHypothesis) :
    (41189 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 18277,
        Real.exp (-(n : ℝ) / (365540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (365540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 109977) * ((365540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((365540 / 37) * (37 / 20)) + 1) / (4000 / 109977) +
        1839 / 1000 ≤
      87213 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh27_roots.2.2]
  have hs :
    Real.sqrt ((365540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((365540 / 37) * (37 / 20)) +
        21 / 20 ≤
      25857 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh27_roots.2.2, gammaAnalyticHigh27_logs.2]
  have hz :
    Real.sqrt (365540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (365540 / 37) + 2469 / 800 ≤
      20743 / 1000 := by
    linarith only [gammaAnalyticHigh27_roots.2.1, gammaAnalyticHigh27_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 365540 / 37) (y := 37 / 20) (h := 4000 / 109977) (r :=
      198791 / 2000) (e := 78619 / 500000) (p := 87213 / 125) (s := 25857 / 1000) (z :=
      20743 / 1000) (F := 41189 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh27_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (365540 / 37 : ℝ) * (37 / 20) = 18277 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh27_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (365540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (365540 / 37 : ℝ)) ≤
      19921 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 496977 / 5000) (T := 198791 / 2000) (Z := 91983 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh27_roots.1
      gammaAnalyticHigh27_roots.2.1 gammaAnalyticHigh27_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh27_power : (365540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 567 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 27 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh27_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24683 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12453 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (18277 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24683 / 100)]
  apply
    reject_03_of_analytic_caps (B := 18277) (x := 365540 / 37) (H := 12453 / 50) (R :=
      496977 / 5000) (W := 567 / 100000) (F := 41189 / 500) (U := 19921 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh27_power (gammaAnalyticHigh27_main hGRH.riemann)
      (gammaAnalyticHigh27_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 28. -/
theorem gammaAnalyticHigh28_roots :
    ((1002941 / 10000 : ℝ) ≤ Real.sqrt (372180 / 37 : ℝ) ∧
      Real.sqrt (372180 / 37 : ℝ) ≤ 501471 / 5000 ∧ Real.sqrt (18609 : ℝ) ≤ 1364149 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 28. -/
theorem gammaAnalyticHigh28_logs :
    Real.log (372180 / 37 : ℝ) ≤ 92163 / 10000 ∧ Real.log (18609 : ℝ) ≤ 19663 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (372180 / 37) 14 20 0 (92163 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 18609 15 20 0 (19663 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh28_main (hRH : RiemannHypothesis) :
    (20783 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 18609,
        Real.exp (-(n : ℝ) / (372180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (372180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 55237) * ((372180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((372180 / 37) * (37 / 20)) + 1) / (2000 / 55237) +
        1839 / 1000 ≤
      35357 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh28_roots.2.2]
  have hs :
    Real.sqrt ((372180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((372180 / 37) * (37 / 20)) +
        21 / 20 ≤
      25951 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh28_roots.2.2, gammaAnalyticHigh28_logs.2]
  have hz :
    Real.sqrt (372180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (372180 / 37) + 2469 / 800 ≤
      20813 / 1000 := by
    linarith only [gammaAnalyticHigh28_roots.2.1, gammaAnalyticHigh28_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 372180 / 37) (y := 37 / 20) (h := 2000 / 55237) (r :=
      501471 / 5000) (e := 78619 / 500000) (p := 35357 / 50) (s := 25951 / 1000) (z := 20813 / 1000)
      (F := 20783 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh28_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (372180 / 37 : ℝ) * (37 / 20) = 18609 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh28_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (372180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (372180 / 37 : ℝ)) ≤
      50251 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1002941 / 10000) (T := 501471 / 5000) (Z :=
      92163 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh28_roots.1
      gammaAnalyticHigh28_roots.2.1 gammaAnalyticHigh28_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh28_power : (372180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 561 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 28 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh28_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12453 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6283 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (18609 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12453 / 50)]
  apply
    reject_03_of_analytic_caps (B := 18609) (x := 372180 / 37) (H := 6283 / 25) (R :=
      1002941 / 10000) (W := 561 / 100000) (F := 20783 / 250) (U := 50251 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh28_power (gammaAnalyticHigh28_main hGRH.riemann)
      (gammaAnalyticHigh28_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 29. -/
theorem gammaAnalyticHigh29_roots :
    ((202407 / 2000 : ℝ) ≤ Real.sqrt (378960 / 37 : ℝ) ∧
      Real.sqrt (378960 / 37 : ℝ) ≤ 253009 / 2500 ∧ Real.sqrt (18948 : ℝ) ≤ 688259 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 29. -/
theorem gammaAnalyticHigh29_logs :
    Real.log (378960 / 37 : ℝ) ≤ 92343 / 10000 ∧ Real.log (18948 : ℝ) ≤ 19699 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (378960 / 37) 14 20 0 (92343 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 18948 15 20 0 (19699 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh29_main (hRH : RiemannHypothesis) :
    (16779 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 18948,
        Real.exp (-(n : ℝ) / (378960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (378960 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 55489) * ((378960 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((378960 / 37) * (37 / 20)) + 1) / (2000 / 55489) +
        1839 / 1000 ≤
      716731 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh29_roots.2.2]
  have hs :
    Real.sqrt ((378960 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((378960 / 37) * (37 / 20)) +
        21 / 20 ≤
      13023 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh29_roots.2.2, gammaAnalyticHigh29_logs.2]
  have hz :
    Real.sqrt (378960 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (378960 / 37) + 2469 / 800 ≤
      20883 / 1000 := by
    linarith only [gammaAnalyticHigh29_roots.2.1, gammaAnalyticHigh29_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 378960 / 37) (y := 37 / 20) (h := 2000 / 55489) (r :=
      253009 / 2500) (e := 78619 / 500000) (p := 716731 / 1000) (s := 13023 / 500) (z :=
      20883 / 1000) (F := 16779 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh29_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (378960 / 37 : ℝ) * (37 / 20) = 18948 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh29_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (378960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (378960 / 37 : ℝ)) ≤
      10141 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 202407 / 2000) (T := 253009 / 2500) (Z := 92343 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh29_roots.1
      gammaAnalyticHigh29_roots.2.1 gammaAnalyticHigh29_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh29_power : (378960 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 111 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 29 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh29_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (6283 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (25359 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (18948 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 6283 / 25)]
  apply
    reject_03_of_analytic_caps (B := 18948) (x := 378960 / 37) (H := 25359 / 100) (R :=
      202407 / 2000) (W := 111 / 20000) (F := 16779 / 200) (U := 10141 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh29_power (gammaAnalyticHigh29_main hGRH.riemann)
      (gammaAnalyticHigh29_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 30. -/
theorem gammaAnalyticHigh30_roots :
    ((1021181 / 10000 : ℝ) ≤ Real.sqrt (385840 / 37 : ℝ) ∧
      Real.sqrt (385840 / 37 : ℝ) ≤ 510591 / 5000 ∧ Real.sqrt (19292 : ℝ) ≤ 1388957 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 30. -/
theorem gammaAnalyticHigh30_logs :
    Real.log (385840 / 37 : ℝ) ≤ 92523 / 10000 ∧ Real.log (19292 : ℝ) ≤ 3947 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (385840 / 37) 14 20 0 (92523 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 19292 15 20 0 (3947 / 400) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh30_main (hRH : RiemannHypothesis) :
    (84663 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 19292,
        Real.exp (-(n : ℝ) / (385840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (385840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (160 / 4459) * ((385840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((385840 / 37) * (37 / 20)) + 1) / (160 / 4459) +
        1839 / 1000 ≤
      36321 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh30_roots.2.2]
  have hs :
    Real.sqrt ((385840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((385840 / 37) * (37 / 20)) +
        21 / 20 ≤
      13071 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh30_roots.2.2, gammaAnalyticHigh30_logs.2]
  have hz :
    Real.sqrt (385840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (385840 / 37) + 2469 / 800 ≤
      10477 / 500 := by
    linarith only [gammaAnalyticHigh30_roots.2.1, gammaAnalyticHigh30_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 385840 / 37) (y := 37 / 20) (h := 160 / 4459) (r :=
      510591 / 5000) (e := 78619 / 500000) (p := 36321 / 50) (s := 13071 / 500) (z := 10477 / 500)
      (F := 84663 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh30_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (385840 / 37 : ℝ) * (37 / 20) = 19292 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh30_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (385840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (385840 / 37 : ℝ)) ≤
      25581 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1021181 / 10000) (T := 510591 / 5000) (Z :=
      92523 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh30_roots.1
      gammaAnalyticHigh30_roots.2.1 gammaAnalyticHigh30_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh30_power : (385840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 11 / 2000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 30 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh30_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (25359 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (25589 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (19292 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 25359 / 100)]
  apply
    reject_03_of_analytic_caps (B := 19292) (x := 385840 / 37) (H := 25589 / 100) (R :=
      1021181 / 10000) (W := 11 / 2000) (F := 84663 / 1000) (U := 25581 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh30_power (gammaAnalyticHigh30_main hGRH.riemann)
      (gammaAnalyticHigh30_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 31. -/
theorem gammaAnalyticHigh31_roots :
    ((257607 / 2500 : ℝ) ≤ Real.sqrt (392860 / 37 : ℝ) ∧
      Real.sqrt (392860 / 37 : ℝ) ≤ 1030429 / 10000 ∧ Real.sqrt (19643 : ℝ) ≤ 280307 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 31. -/
theorem gammaAnalyticHigh31_logs :
    Real.log (392860 / 37 : ℝ) ≤ 92703 / 10000 ∧ Real.log (19643 : ℝ) ≤ 19771 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (392860 / 37) 14 20 0 (92703 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 19643 15 20 0 (19771 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh31_main (hRH : RiemannHypothesis) :
    (85439 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 19643,
        Real.exp (-(n : ℝ) / (392860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (392860 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 111979) * ((392860 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((392860 / 37) * (37 / 20)) + 1) / (4000 / 111979) +
        1839 / 1000 ≤
      368131 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh31_roots.2.2]
  have hs :
    Real.sqrt ((392860 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((392860 / 37) * (37 / 20)) +
        21 / 20 ≤
      13119 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh31_roots.2.2, gammaAnalyticHigh31_logs.2]
  have hz :
    Real.sqrt (392860 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (392860 / 37) + 2469 / 800 ≤
      841 / 40 := by
    linarith only [gammaAnalyticHigh31_roots.2.1, gammaAnalyticHigh31_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 392860 / 37) (y := 37 / 20) (h := 4000 / 111979) (r :=
      1030429 / 10000) (e := 78619 / 500000) (p := 368131 / 500) (s := 13119 / 500) (z := 841 / 40)
      (F := 85439 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh31_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (392860 / 37 : ℝ) * (37 / 20) = 19643 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh31_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (392860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (392860 / 37 : ℝ)) ≤
      103247 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 257607 / 2500) (T := 1030429 / 10000) (Z :=
      92703 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh31_roots.1
      gammaAnalyticHigh31_roots.2.1 gammaAnalyticHigh31_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh31_power : (392860 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 17 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 31 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh31_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (25589 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (25821 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (19643 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 25589 / 100)]
  apply
    reject_03_of_analytic_caps (B := 19643) (x := 392860 / 37) (H := 25821 / 100) (R :=
      257607 / 2500) (W := 17 / 3125) (F := 85439 / 1000) (U := 103247 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh31_power (gammaAnalyticHigh31_main hGRH.riemann)
      (gammaAnalyticHigh31_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 32. -/
theorem gammaAnalyticHigh32_roots :
    ((64986 / 625 : ℝ) ≤ Real.sqrt (400020 / 37 : ℝ) ∧
      Real.sqrt (400020 / 37 : ℝ) ≤ 1039777 / 10000 ∧ Real.sqrt (20001 : ℝ) ≤ 1414249 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 32. -/
theorem gammaAnalyticHigh32_logs :
    Real.log (400020 / 37 : ℝ) ≤ 23221 / 2500 ∧ Real.log (20001 : ℝ) ≤ 24759 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (400020 / 37) 14 20 0 (23221 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 20001 15 20 0 (24759 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh32_main (hRH : RiemannHypothesis) :
    (86223 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 20001,
        Real.exp (-(n : ℝ) / (400020 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (400020 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 112483) * ((400020 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((400020 / 37) * (37 / 20)) + 1) / (4000 / 112483) +
        1839 / 1000 ≤
      149251 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh32_roots.2.2]
  have hs :
    Real.sqrt ((400020 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((400020 / 37) * (37 / 20)) +
        21 / 20 ≤
      13167 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh32_roots.2.2, gammaAnalyticHigh32_logs.2]
  have hz :
    Real.sqrt (400020 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (400020 / 37) + 2469 / 800 ≤
      21097 / 1000 := by
    linarith only [gammaAnalyticHigh32_roots.2.1, gammaAnalyticHigh32_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 400020 / 37) (y := 37 / 20) (h := 4000 / 112483) (r :=
      1039777 / 10000) (e := 78619 / 500000) (p := 149251 / 200) (s := 13167 / 500) (z :=
      21097 / 1000) (F := 86223 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh32_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (400020 / 37 : ℝ) * (37 / 20) = 20001 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh32_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (400020 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (400020 / 37 : ℝ)) ≤
      104181 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 64986 / 625) (T := 1039777 / 10000) (Z := 23221 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh32_roots.1
      gammaAnalyticHigh32_roots.2.1 gammaAnalyticHigh32_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh32_power : (400020 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 539 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 32 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh32_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (25821 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5211 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (20001 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 25821 / 100)]
  apply
    reject_03_of_analytic_caps (B := 20001) (x := 400020 / 37) (H := 5211 / 20) (R := 64986 / 625)
      (W := 539 / 100000) (F := 86223 / 1000) (U := 104181 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh32_power (gammaAnalyticHigh32_main hGRH.riemann)
      (gammaAnalyticHigh32_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 33. -/
theorem gammaAnalyticHigh33_roots :
    ((209839 / 2000 : ℝ) ≤ Real.sqrt (407300 / 37 : ℝ) ∧
      Real.sqrt (407300 / 37 : ℝ) ≤ 262299 / 2500 ∧ Real.sqrt (20365 : ℝ) ≤ 71353 / 500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 33. -/
theorem gammaAnalyticHigh33_logs :
    Real.log (407300 / 37 : ℝ) ≤ 11633 / 1250 ∧ Real.log (20365 : ℝ) ≤ 6201 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (407300 / 37) 14 20 0 (11633 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 20365 15 20 0 (6201 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh33_main (hRH : RiemannHypothesis) :
    (87013 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 20365,
        Real.exp (-(n : ℝ) / (407300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (407300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 56497) * ((407300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((407300 / 37) * (37 / 20)) + 1) / (2000 / 56497) +
        1839 / 1000 ≤
      756369 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh33_roots.2.2]
  have hs :
    Real.sqrt ((407300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((407300 / 37) * (37 / 20)) +
        21 / 20 ≤
      3304 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh33_roots.2.2, gammaAnalyticHigh33_logs.2]
  have hz :
    Real.sqrt (407300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (407300 / 37) + 2469 / 800 ≤
      21169 / 1000 := by
    linarith only [gammaAnalyticHigh33_roots.2.1, gammaAnalyticHigh33_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 407300 / 37) (y := 37 / 20) (h := 2000 / 56497) (r :=
      262299 / 2500) (e := 78619 / 500000) (p := 756369 / 1000) (s := 3304 / 125) (z :=
      21169 / 1000) (F := 87013 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh33_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (407300 / 37 : ℝ) * (37 / 20) = 20365 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh33_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (407300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (407300 / 37 : ℝ)) ≤
      52561 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 209839 / 2000) (T := 262299 / 2500) (Z := 11633 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh33_roots.1
      gammaAnalyticHigh33_roots.2.1 gammaAnalyticHigh33_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh33_power : (407300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 533 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 33 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh33_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5211 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2629 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (20365 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5211 / 20)]
  apply
    reject_03_of_analytic_caps (B := 20365) (x := 407300 / 37) (H := 2629 / 10) (R := 209839 / 2000)
      (W := 533 / 100000) (F := 87013 / 1000) (U := 52561 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh33_power (gammaAnalyticHigh33_main hGRH.riemann)
      (gammaAnalyticHigh33_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 34. -/
theorem gammaAnalyticHigh34_roots :
    ((1058657 / 10000 : ℝ) ≤ Real.sqrt (414680 / 37 : ℝ) ∧
      Real.sqrt (414680 / 37 : ℝ) ≤ 529329 / 5000 ∧ Real.sqrt (20734 : ℝ) ≤ 1439931 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 34. -/
theorem gammaAnalyticHigh34_logs :
    Real.log (414680 / 37 : ℝ) ≤ 23311 / 2500 ∧ Real.log (20734 : ℝ) ≤ 24849 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (414680 / 37) 14 20 0 (23311 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 20734 15 20 0 (24849 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh34_main (hRH : RiemannHypothesis) :
    (87807 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 20734,
        Real.exp (-(n : ℝ) / (414680 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (414680 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 22701) * ((414680 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((414680 / 37) * (37 / 20)) + 1) / (800 / 22701) +
        1839 / 1000 ≤
      95822 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh34_roots.2.2]
  have hs :
    Real.sqrt ((414680 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((414680 / 37) * (37 / 20)) +
        21 / 20 ≤
      26529 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh34_roots.2.2, gammaAnalyticHigh34_logs.2]
  have hz :
    Real.sqrt (414680 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (414680 / 37) + 2469 / 800 ≤
      21241 / 1000 := by
    linarith only [gammaAnalyticHigh34_roots.2.1, gammaAnalyticHigh34_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 414680 / 37) (y := 37 / 20) (h := 800 / 22701) (r :=
      529329 / 5000) (e := 78619 / 500000) (p := 95822 / 125) (s := 26529 / 1000) (z :=
      21241 / 1000) (F := 87807 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh34_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (414680 / 37 : ℝ) * (37 / 20) = 20734 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh34_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (414680 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (414680 / 37 : ℝ)) ≤
      106067 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1058657 / 10000) (T := 529329 / 5000) (Z := 23311 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh34_roots.1
      gammaAnalyticHigh34_roots.2.1 gammaAnalyticHigh34_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh34_power : (414680 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 33 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 34 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh34_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2629 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (26527 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (20734 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2629 / 10)]
  apply
    reject_03_of_analytic_caps (B := 20734) (x := 414680 / 37) (H := 26527 / 100) (R :=
      1058657 / 10000) (W := 33 / 6250) (F := 87807 / 1000) (U := 106067 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh34_power (gammaAnalyticHigh34_main hGRH.riemann)
      (gammaAnalyticHigh34_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 35. -/
theorem gammaAnalyticHigh35_roots :
    ((1068213 / 10000 : ℝ) ≤ Real.sqrt (422200 / 37 : ℝ) ∧
      Real.sqrt (422200 / 37 : ℝ) ≤ 534107 / 5000 ∧ Real.sqrt (21110 : ℝ) ≤ 1452929 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 35. -/
theorem gammaAnalyticHigh35_logs :
    Real.log (422200 / 37 : ℝ) ≤ 5839 / 625 ∧ Real.log (21110 : ℝ) ≤ 12447 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (422200 / 37) 14 20 0 (5839 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 21110 15 20 0 (12447 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh35_main (hRH : RiemannHypothesis) :
    (88609 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 21110,
        Real.exp (-(n : ℝ) / (422200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (422200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (125 / 3563) * ((422200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((422200 / 37) * (37 / 20)) + 1) / (125 / 3563) +
        1839 / 1000 ≤
      77693 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh35_roots.2.2]
  have hs :
    Real.sqrt ((422200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((422200 / 37) * (37 / 20)) +
        21 / 20 ≤
      26627 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh35_roots.2.2, gammaAnalyticHigh35_logs.2]
  have hz :
    Real.sqrt (422200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (422200 / 37) + 2469 / 800 ≤
      21313 / 1000 := by
    linarith only [gammaAnalyticHigh35_roots.2.1, gammaAnalyticHigh35_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 422200 / 37) (y := 37 / 20) (h := 125 / 3563) (r :=
      534107 / 5000) (e := 78619 / 500000) (p := 77693 / 100) (s := 26627 / 1000) (z :=
      21313 / 1000) (F := 88609 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh35_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (422200 / 37 : ℝ) * (37 / 20) = 21110 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh35_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (422200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (422200 / 37 : ℝ)) ≤
      107021 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1068213 / 10000) (T := 534107 / 5000) (Z := 5839 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh35_roots.1
      gammaAnalyticHigh35_roots.2.1 gammaAnalyticHigh35_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh35_power : (422200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 523 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 35 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh35_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (26527 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (26767 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (21110 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 26527 / 100)]
  apply
    reject_03_of_analytic_caps (B := 21110) (x := 422200 / 37) (H := 26767 / 100) (R :=
      1068213 / 10000) (W := 523 / 100000) (F := 88609 / 1000) (U := 107021 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh35_power (gammaAnalyticHigh35_main hGRH.riemann)
      (gammaAnalyticHigh35_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 36. -/
theorem gammaAnalyticHigh36_roots :
    ((215577 / 2000 : ℝ) ≤ Real.sqrt (429880 / 37 : ℝ) ∧
      Real.sqrt (429880 / 37 : ℝ) ≤ 538943 / 5000 ∧ Real.sqrt (21494 : ℝ) ≤ 366521 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 36. -/
theorem gammaAnalyticHigh36_logs :
    Real.log (429880 / 37 : ℝ) ≤ 23401 / 2500 ∧ Real.log (21494 : ℝ) ≤ 24939 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (429880 / 37) 14 20 0 (23401 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 21494 15 20 0 (24939 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh36_main (hRH : RiemannHypothesis) :
    (4471 / 50 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 21494,
        Real.exp (-(n : ℝ) / (429880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (429880 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 114527) * ((429880 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((429880 / 37) * (37 / 20)) + 1) / (4000 / 114527) +
        1839 / 1000 ≤
      98432 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh36_roots.2.2]
  have hs :
    Real.sqrt ((429880 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((429880 / 37) * (37 / 20)) +
        21 / 20 ≤
      13363 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh36_roots.2.2, gammaAnalyticHigh36_logs.2]
  have hz :
    Real.sqrt (429880 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (429880 / 37) + 2469 / 800 ≤
      21387 / 1000 := by
    linarith only [gammaAnalyticHigh36_roots.2.1, gammaAnalyticHigh36_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 429880 / 37) (y := 37 / 20) (h := 4000 / 114527) (r :=
      538943 / 5000) (e := 78619 / 500000) (p := 98432 / 125) (s := 13363 / 500) (z := 21387 / 1000)
      (F := 4471 / 50) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh36_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (429880 / 37 : ℝ) * (37 / 20) = 21494 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh36_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (429880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (429880 / 37 : ℝ)) ≤
      26997 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 215577 / 2000) (T := 538943 / 5000) (Z := 23401 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh36_roots.1
      gammaAnalyticHigh36_roots.2.1 gammaAnalyticHigh36_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh36_power : (429880 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 517 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 36 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh36_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (26767 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (27009 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (21494 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 26767 / 100)]
  apply
    reject_03_of_analytic_caps (B := 21494) (x := 429880 / 37) (H := 27009 / 100) (R :=
      215577 / 2000) (W := 517 / 100000) (F := 4471 / 50) (U := 26997 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh36_power (gammaAnalyticHigh36_main hGRH.riemann)
      (gammaAnalyticHigh36_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 37. -/
theorem gammaAnalyticHigh37_roots :
    ((54381 / 500 : ℝ) ≤ Real.sqrt (437680 / 37 : ℝ) ∧
      Real.sqrt (437680 / 37 : ℝ) ≤ 1087621 / 10000 ∧ Real.sqrt (21884 : ℝ) ≤ 59173 / 400) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 37. -/
theorem gammaAnalyticHigh37_logs :
    Real.log (437680 / 37 : ℝ) ≤ 11723 / 1250 ∧ Real.log (21884 : ℝ) ≤ 6246 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (437680 / 37) 14 20 0 (11723 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 21884 15 20 0 (6246 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh37_main (hRH : RiemannHypothesis) :
    (90237 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 21884,
        Real.exp (-(n : ℝ) / (437680 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (437680 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 23009) * ((437680 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((437680 / 37) * (37 / 20)) + 1) / (800 / 23009) +
        1839 / 1000 ≤
      798099 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh37_roots.2.2]
  have hs :
    Real.sqrt ((437680 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((437680 / 37) * (37 / 20)) +
        21 / 20 ≤
      1073 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh37_roots.2.2, gammaAnalyticHigh37_logs.2]
  have hz :
    Real.sqrt (437680 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (437680 / 37) + 2469 / 800 ≤
      1073 / 50 := by
    linarith only [gammaAnalyticHigh37_roots.2.1, gammaAnalyticHigh37_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 437680 / 37) (y := 37 / 20) (h := 800 / 23009) (r :=
      1087621 / 10000) (e := 78619 / 500000) (p := 798099 / 1000) (s := 1073 / 40) (z := 1073 / 50)
      (F := 90237 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh37_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (437680 / 37 : ℝ) * (37 / 20) = 21884 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh37_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (437680 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (437680 / 37 : ℝ)) ≤
      2724 / 25 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 54381 / 500) (T := 1087621 / 10000) (Z := 11723 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh37_roots.1
      gammaAnalyticHigh37_roots.2.1 gammaAnalyticHigh37_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh37_power : (437680 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 16 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 37 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh37_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (27009 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (27253 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (21884 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 27009 / 100)]
  apply
    reject_03_of_analytic_caps (B := 21884) (x := 437680 / 37) (H := 27253 / 100) (R := 54381 / 500)
      (W := 16 / 3125) (F := 90237 / 1000) (U := 2724 / 25) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh37_power (gammaAnalyticHigh37_main hGRH.riemann)
      (gammaAnalyticHigh37_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 38. -/
theorem gammaAnalyticHigh38_roots :
    ((1097441 / 10000 : ℝ) ≤ Real.sqrt (445620 / 37 : ℝ) ∧
      Real.sqrt (445620 / 37 : ℝ) ≤ 548721 / 5000 ∧ Real.sqrt (22281 : ℝ) ≤ 1492683 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 38. -/
theorem gammaAnalyticHigh38_logs :
    Real.log (445620 / 37 : ℝ) ≤ 23491 / 2500 ∧ Real.log (22281 : ℝ) ≤ 20023 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (445620 / 37) 14 20 0 (23491 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 22281 15 20 0 (20023 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh38_main (hRH : RiemannHypothesis) :
    (91061 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 22281,
        Real.exp (-(n : ℝ) / (445620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (445620 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 115563) * ((445620 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((445620 / 37) * (37 / 20)) + 1) / (4000 / 115563) +
        1839 / 1000 ≤
      161777 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh38_roots.2.2]
  have hs :
    Real.sqrt ((445620 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((445620 / 37) * (37 / 20)) +
        21 / 20 ≤
      1077 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh38_roots.2.2, gammaAnalyticHigh38_logs.2]
  have hz :
    Real.sqrt (445620 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (445620 / 37) + 2469 / 800 ≤
      10767 / 500 := by
    linarith only [gammaAnalyticHigh38_roots.2.1, gammaAnalyticHigh38_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 445620 / 37) (y := 37 / 20) (h := 4000 / 115563) (r :=
      548721 / 5000) (e := 78619 / 500000) (p := 161777 / 200) (s := 1077 / 40) (z := 10767 / 500)
      (F := 91061 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh38_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (445620 / 37 : ℝ) * (37 / 20) = 22281 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh38_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (445620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (445620 / 37 : ℝ)) ≤
      109941 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1097441 / 10000) (T := 548721 / 5000) (Z := 23491 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh38_roots.1
      gammaAnalyticHigh38_roots.2.1 gammaAnalyticHigh38_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh38_power : (445620 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 507 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 38 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh38_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (27253 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (27499 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (22281 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 27253 / 100)]
  apply
    reject_03_of_analytic_caps (B := 22281) (x := 445620 / 37) (H := 27499 / 100) (R :=
      1097441 / 10000) (W := 507 / 100000) (F := 91061 / 1000) (U := 109941 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh38_power (gammaAnalyticHigh38_main hGRH.riemann)
      (gammaAnalyticHigh38_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 39. -/
theorem gammaAnalyticHigh39_roots :
    ((553673 / 5000 : ℝ) ≤ Real.sqrt (453700 / 37 : ℝ) ∧
      Real.sqrt (453700 / 37 : ℝ) ≤ 1107347 / 10000 ∧ Real.sqrt (22685 : ℝ) ≤ 301231 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 39. -/
theorem gammaAnalyticHigh39_logs :
    Real.log (453700 / 37 : ℝ) ≤ 94143 / 10000 ∧ Real.log (22685 : ℝ) ≤ 20059 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (453700 / 37) 14 20 0 (94143 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 22685 15 20 0 (20059 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh39_main (hRH : RiemannHypothesis) :
    (22973 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 22685,
        Real.exp (-(n : ℝ) / (453700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (453700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 116081) * ((453700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((453700 / 37) * (37 / 20)) + 1) / (4000 / 116081) +
        1839 / 1000 ≤
      819811 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh39_roots.2.2]
  have hs :
    Real.sqrt ((453700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((453700 / 37) * (37 / 20)) +
        21 / 20 ≤
      13513 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh39_roots.2.2, gammaAnalyticHigh39_logs.2]
  have hz :
    Real.sqrt (453700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (453700 / 37) + 2469 / 800 ≤
      2701 / 125 := by
    linarith only [gammaAnalyticHigh39_roots.2.1, gammaAnalyticHigh39_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 453700 / 37) (y := 37 / 20) (h := 4000 / 116081) (r :=
      1107347 / 10000) (e := 78619 / 500000) (p := 819811 / 1000) (s := 13513 / 500) (z :=
      2701 / 125) (F := 22973 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh39_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (453700 / 37 : ℝ) * (37 / 20) = 22685 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh39_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (453700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (453700 / 37 : ℝ)) ≤
      11093 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 553673 / 5000) (T := 1107347 / 10000) (Z :=
      94143 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh39_roots.1
      gammaAnalyticHigh39_roots.2.1 gammaAnalyticHigh39_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh39_power : (453700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 251 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 39 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh39_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (27499 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (27747 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (22685 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 27499 / 100)]
  apply
    reject_03_of_analytic_caps (B := 22685) (x := 453700 / 37) (H := 27747 / 100) (R :=
      553673 / 5000) (W := 251 / 50000) (F := 22973 / 250) (U := 11093 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh39_power (gammaAnalyticHigh39_main hGRH.riemann)
      (gammaAnalyticHigh39_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 40. -/
theorem gammaAnalyticHigh40_roots :
    ((279333 / 2500 : ℝ) ≤ Real.sqrt (461920 / 37 : ℝ) ∧
      Real.sqrt (461920 / 37 : ℝ) ≤ 1117333 / 10000 ∧ Real.sqrt (23096 : ℝ) ≤ 1519737 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 40. -/
theorem gammaAnalyticHigh40_logs :
    Real.log (461920 / 37 : ℝ) ≤ 94323 / 10000 ∧ Real.log (23096 : ℝ) ≤ 4019 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (461920 / 37) 14 20 0 (94323 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 23096 15 20 0 (4019 / 400) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh40_main (hRH : RiemannHypothesis) :
    (9273 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 23096,
        Real.exp (-(n : ℝ) / (461920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (461920 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 58303) * ((461920 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((461920 / 37) * (37 / 20)) + 1) / (2000 / 58303) +
        1839 / 1000 ≤
      207719 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh40_roots.2.2]
  have hs :
    Real.sqrt ((461920 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((461920 / 37) * (37 / 20)) +
        21 / 20 ≤
      27127 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh40_roots.2.2, gammaAnalyticHigh40_logs.2]
  have hz :
    Real.sqrt (461920 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (461920 / 37) + 2469 / 800 ≤
      21683 / 1000 := by
    linarith only [gammaAnalyticHigh40_roots.2.1, gammaAnalyticHigh40_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 461920 / 37) (y := 37 / 20) (h := 2000 / 58303) (r :=
      1117333 / 10000) (e := 78619 / 500000) (p := 207719 / 250) (s := 27127 / 1000) (z :=
      21683 / 1000) (F := 9273 / 100) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh40_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (461920 / 37 : ℝ) * (37 / 20) = 23096 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh40_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (461920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (461920 / 37 : ℝ)) ≤
      13991 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 279333 / 2500) (T := 1117333 / 10000) (Z :=
      94323 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh40_roots.1
      gammaAnalyticHigh40_roots.2.1 gammaAnalyticHigh40_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh40_power : (461920 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 497 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 40 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh40_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (27747 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (27997 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (23096 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 27747 / 100)]
  apply
    reject_03_of_analytic_caps (B := 23096) (x := 461920 / 37) (H := 27997 / 100) (R :=
      279333 / 2500) (W := 497 / 100000) (F := 9273 / 100) (U := 13991 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh40_power (gammaAnalyticHigh40_main hGRH.riemann)
      (gammaAnalyticHigh40_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 41. -/
theorem gammaAnalyticHigh41_roots :
    ((563699 / 5000 : ℝ) ≤ Real.sqrt (470280 / 37 : ℝ) ∧
      Real.sqrt (470280 / 37 : ℝ) ≤ 1127399 / 10000 ∧ Real.sqrt (23514 : ℝ) ≤ 383357 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 41. -/
theorem gammaAnalyticHigh41_logs :
    Real.log (470280 / 37 : ℝ) ≤ 47251 / 5000 ∧ Real.log (23514 : ℝ) ≤ 50327 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (470280 / 37) 14 20 0 (47251 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 23514 15 20 0 (50327 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh41_main (hRH : RiemannHypothesis) :
    (3743 / 40 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 23514,
        Real.exp (-(n : ℝ) / (470280 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (470280 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 117131) * ((470280 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((470280 / 37) * (37 / 20)) + 1) / (4000 / 117131) +
        1839 / 1000 ≤
      21052 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh41_roots.2.2]
  have hs :
    Real.sqrt ((470280 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((470280 / 37) * (37 / 20)) +
        21 / 20 ≤
      6807 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh41_roots.2.2, gammaAnalyticHigh41_logs.2]
  have hz :
    Real.sqrt (470280 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (470280 / 37) + 2469 / 800 ≤
      10879 / 500 := by
    linarith only [gammaAnalyticHigh41_roots.2.1, gammaAnalyticHigh41_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 470280 / 37) (y := 37 / 20) (h := 4000 / 117131) (r :=
      1127399 / 10000) (e := 78619 / 500000) (p := 21052 / 25) (s := 6807 / 250) (z := 10879 / 500)
      (F := 3743 / 40) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh41_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (470280 / 37 : ℝ) * (37 / 20) = 23514 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh41_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (470280 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (470280 / 37 : ℝ)) ≤
      112933 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 563699 / 5000) (T := 1127399 / 10000) (Z := 47251 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh41_roots.1
      gammaAnalyticHigh41_roots.2.1 gammaAnalyticHigh41_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh41_power : (470280 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 123 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 41 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh41_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (27997 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (28249 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (23514 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 27997 / 100)]
  apply
    reject_03_of_analytic_caps (B := 23514) (x := 470280 / 37) (H := 28249 / 100) (R :=
      563699 / 5000) (W := 123 / 25000) (F := 3743 / 40) (U := 112933 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh41_power (gammaAnalyticHigh41_main hGRH.riemann)
      (gammaAnalyticHigh41_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 42. -/
theorem gammaAnalyticHigh42_roots :
    ((284391 / 2500 : ℝ) ≤ Real.sqrt (478800 / 37 : ℝ) ∧
      Real.sqrt (478800 / 37 : ℝ) ≤ 227513 / 2000 ∧ Real.sqrt (23940 : ℝ) ≤ 193407 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 42. -/
theorem gammaAnalyticHigh42_logs :
    Real.log (478800 / 37 : ℝ) ≤ 47341 / 5000 ∧ Real.log (23940 : ℝ) ≤ 50417 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (478800 / 37) 14 20 0 (47341 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 23940 15 20 0 (50417 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh42_main (hRH : RiemannHypothesis) :
    (23607 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 23940,
        Real.exp (-(n : ℝ) / (478800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (478800 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 14707) * ((478800 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((478800 / 37) * (37 / 20)) + 1) / (500 / 14707) +
        1839 / 1000 ≤
      426723 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh42_roots.2.2]
  have hs :
    Real.sqrt ((478800 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((478800 / 37) * (37 / 20)) +
        21 / 20 ≤
      2733 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh42_roots.2.2, gammaAnalyticHigh42_logs.2]
  have hz :
    Real.sqrt (478800 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (478800 / 37) + 2469 / 800 ≤
      10917 / 500 := by
    linarith only [gammaAnalyticHigh42_roots.2.1, gammaAnalyticHigh42_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 478800 / 37) (y := 37 / 20) (h := 500 / 14707) (r :=
      227513 / 2000) (e := 78619 / 500000) (p := 426723 / 500) (s := 2733 / 100) (z := 10917 / 500)
      (F := 23607 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh42_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (478800 / 37 : ℝ) * (37 / 20) = 23940 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh42_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (478800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (478800 / 37 : ℝ)) ≤
      113949 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 284391 / 2500) (T := 227513 / 2000) (Z := 47341 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh42_roots.1
      gammaAnalyticHigh42_roots.2.1 gammaAnalyticHigh42_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh42_power : (478800 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 487 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 42 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh42_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (28249 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (7126 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (23940 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 28249 / 100)]
  apply
    reject_03_of_analytic_caps (B := 23940) (x := 478800 / 37) (H := 7126 / 25) (R := 284391 / 2500)
      (W := 487 / 100000) (F := 23607 / 250) (U := 113949 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh42_power (gammaAnalyticHigh42_main hGRH.riemann)
      (gammaAnalyticHigh42_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 43. -/
theorem gammaAnalyticHigh43_roots :
    ((1147829 / 10000 : ℝ) ≤ Real.sqrt (487480 / 37 : ℝ) ∧
      Real.sqrt (487480 / 37 : ℝ) ≤ 114783 / 1000 ∧ Real.sqrt (24374 : ℝ) ≤ 780609 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 43. -/
theorem gammaAnalyticHigh43_logs :
    Real.log (487480 / 37 : ℝ) ≤ 94861 / 10000 ∧ Real.log (24374 : ℝ) ≤ 101013 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (487480 / 37) 14 20 0 (94861 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 24374 15 20 0 (101013 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh43_main (hRH : RiemannHypothesis) :
    (95289 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 24374,
        Real.exp (-(n : ℝ) / (487480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (487480 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 29547) * ((487480 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((487480 / 37) * (37 / 20)) + 1) / (1000 / 29547) +
        1839 / 1000 ≤
      432487 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh43_roots.2.2]
  have hs :
    Real.sqrt ((487480 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((487480 / 37) * (37 / 20)) +
        21 / 20 ≤
      27433 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh43_roots.2.2, gammaAnalyticHigh43_logs.2]
  have hz :
    Real.sqrt (487480 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (487480 / 37) + 2469 / 800 ≤
      2191 / 100 := by
    linarith only [gammaAnalyticHigh43_roots.2.1, gammaAnalyticHigh43_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 487480 / 37) (y := 37 / 20) (h := 1000 / 29547) (r :=
      114783 / 1000) (e := 78619 / 500000) (p := 432487 / 500) (s := 27433 / 1000) (z := 2191 / 100)
      (F := 95289 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh43_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (487480 / 37 : ℝ) * (37 / 20) = 24374 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh43_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (487480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (487480 / 37 : ℝ)) ≤
      57487 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1147829 / 10000) (T := 114783 / 1000) (Z :=
      94861 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh43_roots.1
      gammaAnalyticHigh43_roots.2.1 gammaAnalyticHigh43_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh43_power : (487480 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 241 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 43 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh43_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (7126 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (28761 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (24374 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 7126 / 25)]
  apply
    reject_03_of_analytic_caps (B := 24374) (x := 487480 / 37) (H := 28761 / 100) (R :=
      1147829 / 10000) (W := 241 / 50000) (F := 95289 / 1000) (U := 57487 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh43_power (gammaAnalyticHigh43_main hGRH.riemann)
      (gammaAnalyticHigh43_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 44. -/
theorem gammaAnalyticHigh44_roots :
    ((1158167 / 10000 : ℝ) ≤ Real.sqrt (496300 / 37 : ℝ) ∧
      Real.sqrt (496300 / 37 : ℝ) ≤ 144771 / 1250 ∧ Real.sqrt (24815 : ℝ) ≤ 787639 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 44. -/
theorem gammaAnalyticHigh44_logs :
    Real.log (496300 / 37 : ℝ) ≤ 95041 / 10000 ∧ Real.log (24815 : ℝ) ≤ 101193 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (496300 / 37) 14 20 0 (95041 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 24815 15 20 0 (101193 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh44_main (hRH : RiemannHypothesis) :
    (24039 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 24815,
        Real.exp (-(n : ℝ) / (496300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (496300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (25 / 742) * ((496300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((496300 / 37) * (37 / 20)) + 1) / (25 / 742) +
        1839 / 1000 ≤
      219159 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh44_roots.2.2]
  have hs :
    Real.sqrt ((496300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((496300 / 37) * (37 / 20)) +
        21 / 20 ≤
      3442 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh44_roots.2.2, gammaAnalyticHigh44_logs.2]
  have hz :
    Real.sqrt (496300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (496300 / 37) + 2469 / 800 ≤
      10993 / 500 := by
    linarith only [gammaAnalyticHigh44_roots.2.1, gammaAnalyticHigh44_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 496300 / 37) (y := 37 / 20) (h := 25 / 742) (r :=
      144771 / 1250) (e := 78619 / 500000) (p := 219159 / 250) (s := 3442 / 125) (z := 10993 / 500)
      (F := 24039 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh44_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (496300 / 37 : ℝ) * (37 / 20) = 24815 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh44_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (496300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (496300 / 37 : ℝ)) ≤
      116007 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1158167 / 10000) (T := 144771 / 1250) (Z :=
      95041 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh44_roots.1
      gammaAnalyticHigh44_roots.2.1 gammaAnalyticHigh44_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh44_power : (496300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 477 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 44 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh44_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (28761 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1451 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (24815 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 28761 / 100)]
  apply
    reject_03_of_analytic_caps (B := 24815) (x := 496300 / 37) (H := 1451 / 5) (R :=
      1158167 / 10000) (W := 477 / 100000) (F := 24039 / 250) (U := 116007 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh44_power (gammaAnalyticHigh44_main hGRH.riemann)
      (gammaAnalyticHigh44_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 45. -/
theorem gammaAnalyticHigh45_roots :
    ((584299 / 5000 : ℝ) ≤ Real.sqrt (505280 / 37 : ℝ) ∧
      Real.sqrt (505280 / 37 : ℝ) ≤ 1168599 / 10000 ∧ Real.sqrt (25264 : ℝ) ≤ 794733 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 45. -/
theorem gammaAnalyticHigh45_logs :
    Real.log (505280 / 37 : ℝ) ≤ 4761 / 500 ∧ Real.log (25264 : ℝ) ≤ 25343 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (505280 / 37) 14 20 0 (4761 / 500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 25264 15 20 0 (25343 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh45_main (hRH : RiemannHypothesis) :
    (97031 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 25264,
        Real.exp (-(n : ℝ) / (505280 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (505280 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 29813) * ((505280 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((505280 / 37) * (37 / 20)) + 1) / (1000 / 29813) +
        1839 / 1000 ≤
      111057 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh45_roots.2.2]
  have hs :
    Real.sqrt ((505280 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((505280 / 37) * (37 / 20)) +
        21 / 20 ≤
      691 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh45_roots.2.2, gammaAnalyticHigh45_logs.2]
  have hz :
    Real.sqrt (505280 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (505280 / 37) + 2469 / 800 ≤
      22063 / 1000 := by
    linarith only [gammaAnalyticHigh45_roots.2.1, gammaAnalyticHigh45_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 505280 / 37) (y := 37 / 20) (h := 1000 / 29813) (r :=
      1168599 / 10000) (e := 78619 / 500000) (p := 111057 / 125) (s := 691 / 25) (z := 22063 / 1000)
      (F := 97031 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh45_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (505280 / 37 : ℝ) * (37 / 20) = 25264 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh45_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (505280 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (505280 / 37 : ℝ)) ≤
      117049 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 584299 / 5000) (T := 1168599 / 10000) (Z := 4761 / 500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh45_roots.1
      gammaAnalyticHigh45_roots.2.1 gammaAnalyticHigh45_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh45_power : (505280 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 59 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 45 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh45_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1451 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (29281 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (25264 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1451 / 5)]
  apply
    reject_03_of_analytic_caps (B := 25264) (x := 505280 / 37) (H := 29281 / 100) (R :=
      584299 / 5000) (W := 59 / 12500) (F := 97031 / 1000) (U := 117049 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh45_power (gammaAnalyticHigh45_main hGRH.riemann)
      (gammaAnalyticHigh45_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 46. -/
theorem gammaAnalyticHigh46_roots :
    ((14739 / 125 : ℝ) ≤ Real.sqrt (514420 / 37 : ℝ) ∧
      Real.sqrt (514420 / 37 : ℝ) ≤ 1179121 / 10000 ∧ Real.sqrt (25721 : ℝ) ≤ 1603777 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 46. -/
theorem gammaAnalyticHigh46_logs :
    Real.log (514420 / 37 : ℝ) ≤ 95399 / 10000 ∧ Real.log (25721 : ℝ) ≤ 101551 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (514420 / 37) 14 20 0 (95399 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 25721 15 20 0 (101551 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh46_main (hRH : RiemannHypothesis) :
    (48957 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 25721,
        Real.exp (-(n : ℝ) / (514420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (514420 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 14973) * ((514420 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((514420 / 37) * (37 / 20)) + 1) / (500 / 14973) +
        1839 / 1000 ≤
      900433 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh46_roots.2.2]
  have hs :
    Real.sqrt ((514420 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((514420 / 37) * (37 / 20)) +
        21 / 20 ≤
      5549 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh46_roots.2.2, gammaAnalyticHigh46_logs.2]
  have hz :
    Real.sqrt (514420 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (514420 / 37) + 2469 / 800 ≤
      1107 / 50 := by
    linarith only [gammaAnalyticHigh46_roots.2.1, gammaAnalyticHigh46_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 514420 / 37) (y := 37 / 20) (h := 500 / 14973) (r :=
      1179121 / 10000) (e := 78619 / 500000) (p := 900433 / 1000) (s := 5549 / 200) (z := 1107 / 50)
      (F := 48957 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh46_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (514420 / 37 : ℝ) * (37 / 20) = 25721 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh46_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (514420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (514420 / 37 : ℝ)) ≤
      1181 / 10 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 14739 / 125) (T := 1179121 / 10000) (Z := 95399 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh46_roots.1
      gammaAnalyticHigh46_roots.2.1 gammaAnalyticHigh46_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh46_power : (514420 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 117 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 46 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh46_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (29281 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (7386 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (25721 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 29281 / 100)]
  apply
    reject_03_of_analytic_caps (B := 25721) (x := 514420 / 37) (H := 7386 / 25) (R := 14739 / 125)
      (W := 117 / 25000) (F := 48957 / 500) (U := 1181 / 10) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh46_power (gammaAnalyticHigh46_main hGRH.riemann)
      (gammaAnalyticHigh46_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 47. -/
theorem gammaAnalyticHigh47_roots :
    ((297427 / 2500 : ℝ) ≤ Real.sqrt (523700 / 37 : ℝ) ∧
      Real.sqrt (523700 / 37 : ℝ) ≤ 1189709 / 10000 ∧ Real.sqrt (26185 : ℝ) ≤ 809089 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 47. -/
theorem gammaAnalyticHigh47_logs :
    Real.log (523700 / 37 : ℝ) ≤ 47789 / 5000 ∧ Real.log (26185 : ℝ) ≤ 10173 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (523700 / 37) 14 20 0 (47789 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 26185 15 20 0 (10173 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh47_main (hRH : RiemannHypothesis) :
    (98803 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 26185,
        Real.exp (-(n : ℝ) / (523700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (523700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 120323) * ((523700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((523700 / 37) * (37 / 20)) + 1) / (4000 / 120323) +
        1839 / 1000 ≤
      456269 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh47_roots.2.2]
  have hs :
    Real.sqrt ((523700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((523700 / 37) * (37 / 20)) +
        21 / 20 ≤
      557 / 20 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh47_roots.2.2, gammaAnalyticHigh47_logs.2]
  have hz :
    Real.sqrt (523700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (523700 / 37) + 2469 / 800 ≤
      11109 / 500 := by
    linarith only [gammaAnalyticHigh47_roots.2.1, gammaAnalyticHigh47_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 523700 / 37) (y := 37 / 20) (h := 4000 / 120323) (r :=
      1189709 / 10000) (e := 78619 / 500000) (p := 456269 / 500) (s := 557 / 20) (z := 11109 / 500)
      (F := 98803 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh47_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (523700 / 37 : ℝ) * (37 / 20) = 26185 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh47_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (523700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (523700 / 37 : ℝ)) ≤
      59579 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 297427 / 2500) (T := 1189709 / 10000) (Z := 47789 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh47_roots.1
      gammaAnalyticHigh47_roots.2.1 gammaAnalyticHigh47_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh47_power : (523700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 463 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 47 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh47_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (7386 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2981 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (26185 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 7386 / 25)]
  apply
    reject_03_of_analytic_caps (B := 26185) (x := 523700 / 37) (H := 2981 / 10) (R := 297427 / 2500)
      (W := 463 / 100000) (F := 98803 / 1000) (U := 59579 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh47_power (gammaAnalyticHigh47_main hGRH.riemann)
      (gammaAnalyticHigh47_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 48. -/
theorem gammaAnalyticHigh48_roots :
    ((1200427 / 10000 : ℝ) ≤ Real.sqrt (533180 / 37 : ℝ) ∧
      Real.sqrt (533180 / 37 : ℝ) ≤ 300107 / 2500 ∧ Real.sqrt (26659 : ℝ) ≤ 1632759 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 48. -/
theorem gammaAnalyticHigh48_logs :
    Real.log (533180 / 37 : ℝ) ≤ 95757 / 10000 ∧ Real.log (26659 : ℝ) ≤ 101909 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (533180 / 37) 14 20 0 (95757 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 26659 15 20 0 (101909 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh48_main (hRH : RiemannHypothesis) :
    (49851 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 26659,
        Real.exp (-(n : ℝ) / (533180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (533180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 60431) * ((533180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((533180 / 37) * (37 / 20)) + 1) / (2000 / 60431) +
        1839 / 1000 ≤
      924849 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh48_roots.2.2]
  have hs :
    Real.sqrt ((533180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((533180 / 37) * (37 / 20)) +
        21 / 20 ≤
      5591 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh48_roots.2.2, gammaAnalyticHigh48_logs.2]
  have hz :
    Real.sqrt (533180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (533180 / 37) + 2469 / 800 ≤
      2787 / 125 := by
    linarith only [gammaAnalyticHigh48_roots.2.1, gammaAnalyticHigh48_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 533180 / 37) (y := 37 / 20) (h := 2000 / 60431) (r :=
      300107 / 2500) (e := 78619 / 500000) (p := 924849 / 1000) (s := 5591 / 200) (z := 2787 / 125)
      (F := 49851 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh48_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (533180 / 37 : ℝ) * (37 / 20) = 26659 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh48_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (533180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (533180 / 37 : ℝ)) ≤
      120229 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1200427 / 10000) (T := 300107 / 2500) (Z :=
      95757 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh48_roots.1
      gammaAnalyticHigh48_roots.2.1 gammaAnalyticHigh48_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh48_power : (533180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 229 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 48 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh48_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2981 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15039 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (26659 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2981 / 10)]
  apply
    reject_03_of_analytic_caps (B := 26659) (x := 533180 / 37) (H := 15039 / 50) (R :=
      1200427 / 10000) (W := 229 / 50000) (F := 49851 / 500) (U := 120229 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh48_power (gammaAnalyticHigh48_main hGRH.riemann)
      (gammaAnalyticHigh48_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 49. -/
theorem gammaAnalyticHigh49_roots :
    ((151401 / 1250 : ℝ) ≤ Real.sqrt (542800 / 37 : ℝ) ∧
      Real.sqrt (542800 / 37 : ℝ) ≤ 1211209 / 10000 ∧ Real.sqrt (27140 : ℝ) ≤ 1647423 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 49. -/
theorem gammaAnalyticHigh49_logs :
    Real.log (542800 / 37 : ℝ) ≤ 5996 / 625 ∧ Real.log (27140 : ℝ) ≤ 12761 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (542800 / 37) 14 20 0 (5996 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 27140 15 20 0 (12761 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh49_main (hRH : RiemannHypothesis) :
    (100607 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 27140,
        Real.exp (-(n : ℝ) / (542800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (542800 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (125 / 3794) * ((542800 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((542800 / 37) * (37 / 20)) + 1) / (125 / 3794) +
        1839 / 1000 ≤
      468643 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh49_roots.2.2]
  have hs :
    Real.sqrt ((542800 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((542800 / 37) * (37 / 20)) +
        21 / 20 ≤
      14031 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh49_roots.2.2, gammaAnalyticHigh49_logs.2]
  have hz :
    Real.sqrt (542800 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (542800 / 37) + 2469 / 800 ≤
      179 / 8 := by
    linarith only [gammaAnalyticHigh49_roots.2.1, gammaAnalyticHigh49_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 542800 / 37) (y := 37 / 20) (h := 125 / 3794) (r :=
      1211209 / 10000) (e := 78619 / 500000) (p := 468643 / 500) (s := 14031 / 500) (z := 179 / 8)
      (F := 100607 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh49_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (542800 / 37 : ℝ) * (37 / 20) = 27140 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh49_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (542800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (542800 / 37 : ℝ)) ≤
      60653 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 151401 / 1250) (T := 1211209 / 10000) (Z := 5996 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh49_roots.1
      gammaAnalyticHigh49_roots.2.1 gammaAnalyticHigh49_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh49_power : (542800 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 227 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 49 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh49_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15039 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (7587 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (27140 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15039 / 50)]
  apply
    reject_03_of_analytic_caps (B := 27140) (x := 542800 / 37) (H := 7587 / 25) (R := 151401 / 1250)
      (W := 227 / 50000) (F := 100607 / 1000) (U := 60653 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh49_power (gammaAnalyticHigh49_main hGRH.riemann)
      (gammaAnalyticHigh49_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 50. -/
theorem gammaAnalyticHigh50_roots :
    ((1222093 / 10000 : ℝ) ≤ Real.sqrt (552600 / 37 : ℝ) ∧
      Real.sqrt (552600 / 37 : ℝ) ≤ 611047 / 5000 ∧ Real.sqrt (27630 : ℝ) ≤ 415557 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 50. -/
theorem gammaAnalyticHigh50_logs :
    Real.log (552600 / 37 : ℝ) ≤ 19223 / 2000 ∧ Real.log (27630 : ℝ) ≤ 102267 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (552600 / 37) 14 20 0 (19223 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 27630 15 20 0 (102267 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh50_main (hRH : RiemannHypothesis) :
    (2538 / 25 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 27630,
        Real.exp (-(n : ℝ) / (552600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (552600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 121947) * ((552600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((552600 / 37) * (37 / 20)) + 1) / (4000 / 121947) +
        1839 / 1000 ≤
      9499 / 10 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh50_roots.2.2]
  have hs :
    Real.sqrt ((552600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((552600 / 37) * (37 / 20)) +
        21 / 20 ≤
      28169 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh50_roots.2.2, gammaAnalyticHigh50_logs.2]
  have hz :
    Real.sqrt (552600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (552600 / 37) + 2469 / 800 ≤
      11227 / 500 := by
    linarith only [gammaAnalyticHigh50_roots.2.1, gammaAnalyticHigh50_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 552600 / 37) (y := 37 / 20) (h := 4000 / 121947) (r :=
      611047 / 5000) (e := 78619 / 500000) (p := 9499 / 10) (s := 28169 / 1000) (z := 11227 / 500)
      (F := 2538 / 25) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh50_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (552600 / 37 : ℝ) * (37 / 20) = 27630 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh50_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (552600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (552600 / 37 : ℝ)) ≤
      61197 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1222093 / 10000) (T := 611047 / 5000) (Z := 19223 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh50_roots.1
      gammaAnalyticHigh50_roots.2.1 gammaAnalyticHigh50_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh50_power : (552600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 449 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 50 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh50_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (7587 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1531 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (27630 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 7587 / 25)]
  apply
    reject_03_of_analytic_caps (B := 27630) (x := 552600 / 37) (H := 1531 / 5) (R :=
      1222093 / 10000) (W := 449 / 100000) (F := 2538 / 25) (U := 61197 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh50_power (gammaAnalyticHigh50_main hGRH.riemann)
      (gammaAnalyticHigh50_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 51. -/
theorem gammaAnalyticHigh51_roots :
    ((308259 / 2500 : ℝ) ≤ Real.sqrt (562540 / 37 : ℝ) ∧
      Real.sqrt (562540 / 37 : ℝ) ≤ 1233037 / 10000 ∧ Real.sqrt (28127 : ℝ) ≤ 1677111 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 51. -/
theorem gammaAnalyticHigh51_logs :
    Real.log (562540 / 37 : ℝ) ≤ 96293 / 10000 ∧ Real.log (28127 : ℝ) ≤ 20489 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (562540 / 37) 14 20 0 (96293 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 28127 15 20 0 (20489 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh51_main (hRH : RiemannHypothesis) :
    (51219 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 28127,
        Real.exp (-(n : ℝ) / (562540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (562540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 122493) * ((562540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((562540 / 37) * (37 / 20)) + 1) / (4000 / 122493) +
        1839 / 1000 ≤
      240659 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh51_roots.2.2]
  have hs :
    Real.sqrt ((562540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((562540 / 37) * (37 / 20)) +
        21 / 20 ≤
      7069 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh51_roots.2.2, gammaAnalyticHigh51_logs.2]
  have hz :
    Real.sqrt (562540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (562540 / 37) + 2469 / 800 ≤
      22533 / 1000 := by
    linarith only [gammaAnalyticHigh51_roots.2.1, gammaAnalyticHigh51_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 562540 / 37) (y := 37 / 20) (h := 4000 / 122493) (r :=
      1233037 / 10000) (e := 78619 / 500000) (p := 240659 / 250) (s := 7069 / 250) (z :=
      22533 / 1000) (F := 51219 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh51_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (562540 / 37 : ℝ) * (37 / 20) = 28127 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh51_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (562540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (562540 / 37 : ℝ)) ≤
      123487 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 308259 / 2500) (T := 1233037 / 10000) (Z :=
      96293 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh51_roots.1
      gammaAnalyticHigh51_roots.2.1 gammaAnalyticHigh51_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh51_power : (562540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 89 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 51 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh51_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1531 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15447 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (28127 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1531 / 5)]
  apply
    reject_03_of_analytic_caps (B := 28127) (x := 562540 / 37) (H := 15447 / 50) (R :=
      308259 / 2500) (W := 89 / 20000) (F := 51219 / 500) (U := 123487 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh51_power (gammaAnalyticHigh51_main hGRH.riemann)
      (gammaAnalyticHigh51_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 52. -/
theorem gammaAnalyticHigh52_roots :
    ((1244077 / 10000 : ℝ) ≤ Real.sqrt (572660 / 37 : ℝ) ∧
      Real.sqrt (572660 / 37 : ℝ) ≤ 622039 / 5000 ∧ Real.sqrt (28633 : ℝ) ≤ 1692129 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 52. -/
theorem gammaAnalyticHigh52_logs :
    Real.log (572660 / 37 : ℝ) ≤ 12059 / 1250 ∧ Real.log (28633 : ℝ) ≤ 6414 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (572660 / 37) 14 20 0 (12059 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 28633 15 20 0 (6414 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh52_main (hRH : RiemannHypothesis) :
    (20673 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 28633,
        Real.exp (-(n : ℝ) / (572660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (572660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 123039) * ((572660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((572660 / 37) * (37 / 20)) + 1) / (4000 / 123039) +
        1839 / 1000 ≤
      195109 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh52_roots.2.2]
  have hs :
    Real.sqrt ((572660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((572660 / 37) * (37 / 20)) +
        21 / 20 ≤
      3548 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh52_roots.2.2, gammaAnalyticHigh52_logs.2]
  have hz :
    Real.sqrt (572660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (572660 / 37) + 2469 / 800 ≤
      22613 / 1000 := by
    linarith only [gammaAnalyticHigh52_roots.2.1, gammaAnalyticHigh52_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 572660 / 37) (y := 37 / 20) (h := 4000 / 123039) (r :=
      622039 / 5000) (e := 78619 / 500000) (p := 195109 / 200) (s := 3548 / 125) (z := 22613 / 1000)
      (F := 20673 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh52_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (572660 / 37 : ℝ) * (37 / 20) = 28633 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh52_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (572660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (572660 / 37 : ℝ)) ≤
      12459 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1244077 / 10000) (T := 622039 / 5000) (Z := 12059 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh52_roots.1
      gammaAnalyticHigh52_roots.2.1 gammaAnalyticHigh52_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh52_power : (572660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 11 / 2500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 52 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh52_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15447 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (31171 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (28633 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15447 / 50)]
  apply
    reject_03_of_analytic_caps (B := 28633) (x := 572660 / 37) (H := 31171 / 100) (R :=
      1244077 / 10000) (W := 11 / 2500) (F := 20673 / 200) (U := 12459 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh52_power (gammaAnalyticHigh52_main hGRH.riemann)
      (gammaAnalyticHigh52_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 53. -/
theorem gammaAnalyticHigh53_roots :
    ((78451 / 625 : ℝ) ≤ Real.sqrt (582960 / 37 : ℝ) ∧
      Real.sqrt (582960 / 37 : ℝ) ≤ 1255217 / 10000 ∧ Real.sqrt (29148 : ℝ) ≤ 1707279 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 53. -/
theorem gammaAnalyticHigh53_logs :
    Real.log (582960 / 37 : ℝ) ≤ 1933 / 200 ∧ Real.log (29148 : ℝ) ≤ 51401 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (582960 / 37) 14 20 0 (1933 / 200) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 29148 15 20 0 (51401 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh53_main (hRH : RiemannHypothesis) :
    (104299 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 29148,
        Real.exp (-(n : ℝ) / (582960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (582960 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 15449) * ((582960 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((582960 / 37) * (37 / 20)) + 1) / (500 / 15449) +
        1839 / 1000 ≤
      7909 / 8 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh53_roots.2.2]
  have hs :
    Real.sqrt ((582960 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((582960 / 37) * (37 / 20)) +
        21 / 20 ≤
      7123 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh53_roots.2.2, gammaAnalyticHigh53_logs.2]
  have hz :
    Real.sqrt (582960 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (582960 / 37) + 2469 / 800 ≤
      22693 / 1000 := by
    linarith only [gammaAnalyticHigh53_roots.2.1, gammaAnalyticHigh53_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 582960 / 37) (y := 37 / 20) (h := 500 / 15449) (r :=
      1255217 / 10000) (e := 78619 / 500000) (p := 7909 / 8) (s := 7123 / 250) (z := 22693 / 1000)
      (F := 104299 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh53_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (582960 / 37 : ℝ) * (37 / 20) = 29148 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh53_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (582960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (582960 / 37 : ℝ)) ≤
      125703 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 78451 / 625) (T := 1255217 / 10000) (Z := 1933 / 200)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh53_roots.1
      gammaAnalyticHigh53_roots.2.1 gammaAnalyticHigh53_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh53_power : (582960 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 109 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 53 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh53_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (31171 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (31449 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (29148 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 31171 / 100)]
  apply
    reject_03_of_analytic_caps (B := 29148) (x := 582960 / 37) (H := 31449 / 100) (R := 78451 / 625)
      (W := 109 / 25000) (F := 104299 / 1000) (U := 125703 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh53_power (gammaAnalyticHigh53_main hGRH.riemann)
      (gammaAnalyticHigh53_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 54. -/
theorem gammaAnalyticHigh54_roots :
    ((1266427 / 10000 : ℝ) ≤ Real.sqrt (593420 / 37 : ℝ) ∧
      Real.sqrt (593420 / 37 : ℝ) ≤ 316607 / 2500 ∧ Real.sqrt (29671 : ℝ) ≤ 107658 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 54. -/
theorem gammaAnalyticHigh54_logs :
    Real.log (593420 / 37 : ℝ) ≤ 24207 / 2500 ∧ Real.log (29671 : ℝ) ≤ 5149 / 500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (593420 / 37) 14 20 0 (24207 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 29671 15 20 0 (5149 / 500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh54_main (hRH : RiemannHypothesis) :
    (2631 / 25 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 29671,
        Real.exp (-(n : ℝ) / (593420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (593420 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 62069) * ((593420 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((593420 / 37) * (37 / 20)) + 1) / (2000 / 62069) +
        1839 / 1000 ≤
      1001849 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh54_roots.2.2]
  have hs :
    Real.sqrt ((593420 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((593420 / 37) * (37 / 20)) +
        21 / 20 ≤
      28601 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh54_roots.2.2, gammaAnalyticHigh54_logs.2]
  have hz :
    Real.sqrt (593420 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (593420 / 37) + 2469 / 800 ≤
      11387 / 500 := by
    linarith only [gammaAnalyticHigh54_roots.2.1, gammaAnalyticHigh54_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 593420 / 37) (y := 37 / 20) (h := 2000 / 62069) (r :=
      316607 / 2500) (e := 78619 / 500000) (p := 1001849 / 1000) (s := 28601 / 1000) (z :=
      11387 / 500) (F := 2631 / 25) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh54_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (593420 / 37 : ℝ) * (37 / 20) = 29671 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh54_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (593420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (593420 / 37 : ℝ)) ≤
      126823 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1266427 / 10000) (T := 316607 / 2500) (Z := 24207 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh54_roots.1
      gammaAnalyticHigh54_roots.2.1 gammaAnalyticHigh54_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh54_power : (593420 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 27 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 54 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh54_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (31449 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3173 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (29671 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 31449 / 100)]
  apply
    reject_03_of_analytic_caps (B := 29671) (x := 593420 / 37) (H := 3173 / 10) (R :=
      1266427 / 10000) (W := 27 / 6250) (F := 2631 / 25) (U := 126823 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh54_power (gammaAnalyticHigh54_main hGRH.riemann)
      (gammaAnalyticHigh54_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 55. -/
theorem gammaAnalyticHigh55_roots :
    ((127773 / 1000 : ℝ) ≤ Real.sqrt (604060 / 37 : ℝ) ∧
      Real.sqrt (604060 / 37 : ℝ) ≤ 1277731 / 10000 ∧ Real.sqrt (30203 : ℝ) ≤ 868951 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 55. -/
theorem gammaAnalyticHigh55_logs :
    Real.log (604060 / 37 : ℝ) ≤ 48503 / 5000 ∧ Real.log (30203 : ℝ) ≤ 103157 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (604060 / 37) 14 20 0 (48503 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 30203 15 20 0 (103157 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh55_main (hRH : RiemannHypothesis) :
    (26547 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 30203,
        Real.exp (-(n : ℝ) / (604060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (604060 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 124691) * ((604060 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((604060 / 37) * (37 / 20)) + 1) / (4000 / 124691) +
        1839 / 1000 ≤
      1015241 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh55_roots.2.2]
  have hs :
    Real.sqrt ((604060 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((604060 / 37) * (37 / 20)) +
        21 / 20 ≤
      28711 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh55_roots.2.2, gammaAnalyticHigh55_logs.2]
  have hz :
    Real.sqrt (604060 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (604060 / 37) + 2469 / 800 ≤
      4571 / 200 := by
    linarith only [gammaAnalyticHigh55_roots.2.1, gammaAnalyticHigh55_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 604060 / 37) (y := 37 / 20) (h := 4000 / 124691) (r :=
      1277731 / 10000) (e := 78619 / 500000) (p := 1015241 / 1000) (s := 28711 / 1000) (z :=
      4571 / 200) (F := 26547 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh55_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (604060 / 37 : ℝ) * (37 / 20) = 30203 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh55_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (604060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (604060 / 37 : ℝ)) ≤
      15994 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 127773 / 1000) (T := 1277731 / 10000) (Z := 48503 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh55_roots.1
      gammaAnalyticHigh55_roots.2.1 gammaAnalyticHigh55_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh55_power : (604060 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 427 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 55 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh55_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3173 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (32013 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (30203 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3173 / 10)]
  apply
    reject_03_of_analytic_caps (B := 30203) (x := 604060 / 37) (H := 32013 / 100) (R :=
      127773 / 1000) (W := 427 / 100000) (F := 26547 / 250) (U := 15994 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh55_power (gammaAnalyticHigh55_main hGRH.riemann)
      (gammaAnalyticHigh55_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 56. -/
theorem gammaAnalyticHigh56_roots :
    ((644561 / 5000 : ℝ) ≤ Real.sqrt (614880 / 37 : ℝ) ∧
      Real.sqrt (614880 / 37 : ℝ) ≤ 1289123 / 10000 ∧ Real.sqrt (30744 : ℝ) ≤ 1753397 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 56. -/
theorem gammaAnalyticHigh56_logs :
    Real.log (614880 / 37 : ℝ) ≤ 97183 / 10000 ∧ Real.log (30744 : ℝ) ≤ 20667 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (614880 / 37) 15 20 0 (97183 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 30744 15 20 0 (20667 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh56_main (hRH : RiemannHypothesis) :
    (13393 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 30744,
        Real.exp (-(n : ℝ) / (614880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (614880 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 125251) * ((614880 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((614880 / 37) * (37 / 20)) + 1) / (4000 / 125251) +
        1839 / 1000 ≤
      1028799 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh56_roots.2.2]
  have hs :
    Real.sqrt ((614880 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((614880 / 37) * (37 / 20)) +
        21 / 20 ≤
      28821 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh56_roots.2.2, gammaAnalyticHigh56_logs.2]
  have hz :
    Real.sqrt (614880 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (614880 / 37) + 2469 / 800 ≤
      2867 / 125 := by
    linarith only [gammaAnalyticHigh56_roots.2.1, gammaAnalyticHigh56_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 614880 / 37) (y := 37 / 20) (h := 4000 / 125251) (r :=
      1289123 / 10000) (e := 78619 / 500000) (p := 1028799 / 1000) (s := 28821 / 1000) (z :=
      2867 / 125) (F := 13393 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh56_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (614880 / 37 : ℝ) * (37 / 20) = 30744 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh56_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (614880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (614880 / 37 : ℝ)) ≤
      129091 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 644561 / 5000) (T := 1289123 / 10000) (Z :=
      97183 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh56_roots.1
      gammaAnalyticHigh56_roots.2.1 gammaAnalyticHigh56_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh56_power : (614880 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 423 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 56 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh56_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (32013 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16149 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (30744 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 32013 / 100)]
  apply
    reject_03_of_analytic_caps (B := 30744) (x := 614880 / 37) (H := 16149 / 50) (R :=
      644561 / 5000) (W := 423 / 100000) (F := 13393 / 125) (U := 129091 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh56_power (gammaAnalyticHigh56_main hGRH.riemann)
      (gammaAnalyticHigh56_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 57. -/
theorem gammaAnalyticHigh57_roots :
    ((650301 / 5000 : ℝ) ≤ Real.sqrt (625880 / 37 : ℝ) ∧
      Real.sqrt (625880 / 37 : ℝ) ≤ 1300603 / 10000 ∧ Real.sqrt (31294 : ℝ) ≤ 442253 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 57. -/
theorem gammaAnalyticHigh57_logs :
    Real.log (625880 / 37 : ℝ) ≤ 1217 / 125 ∧ Real.log (31294 : ℝ) ≤ 12939 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (625880 / 37) 15 20 0 (1217 / 125) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 31294 15 20 0 (12939 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh57_main (hRH : RiemannHypothesis) :
    (108107 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 31294,
        Real.exp (-(n : ℝ) / (625880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (625880 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 31451) * ((625880 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((625880 / 37) * (37 / 20)) + 1) / (1000 / 31451) +
        1839 / 1000 ≤
      521261 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh57_roots.2.2]
  have hs :
    Real.sqrt ((625880 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((625880 / 37) * (37 / 20)) +
        21 / 20 ≤
      28931 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh57_roots.2.2, gammaAnalyticHigh57_logs.2]
  have hz :
    Real.sqrt (625880 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (625880 / 37) + 2469 / 800 ≤
      11509 / 500 := by
    linarith only [gammaAnalyticHigh57_roots.2.1, gammaAnalyticHigh57_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 625880 / 37) (y := 37 / 20) (h := 1000 / 31451) (r :=
      1300603 / 10000) (e := 78619 / 500000) (p := 521261 / 500) (s := 28931 / 1000) (z :=
      11509 / 500) (F := 108107 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh57_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (625880 / 37 : ℝ) * (37 / 20) = 31294 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh57_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (625880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (625880 / 37 : ℝ)) ≤
      65119 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 650301 / 5000) (T := 1300603 / 10000) (Z := 1217 / 125)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh57_roots.1
      gammaAnalyticHigh57_roots.2.1 gammaAnalyticHigh57_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh57_power : (625880 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 419 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 57 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh57_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16149 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6517 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (31294 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16149 / 50)]
  apply
    reject_03_of_analytic_caps (B := 31294) (x := 625880 / 37) (H := 6517 / 20) (R := 650301 / 5000)
      (W := 419 / 100000) (F := 108107 / 1000) (U := 65119 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh57_power (gammaAnalyticHigh57_main hGRH.riemann)
      (gammaAnalyticHigh57_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 58. -/
theorem gammaAnalyticHigh58_roots :
    ((1312167 / 10000 : ℝ) ≤ Real.sqrt (637060 / 37 : ℝ) ∧
      Real.sqrt (637060 / 37 : ℝ) ≤ 164021 / 1250 ∧ Real.sqrt (31853 : ℝ) ≤ 1784741 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 58. -/
theorem gammaAnalyticHigh58_logs :
    Real.log (637060 / 37 : ℝ) ≤ 48769 / 5000 ∧ Real.log (31853 : ℝ) ≤ 103689 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (637060 / 37) 15 20 0 (48769 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 31853 15 20 0 (103689 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh58_main (hRH : RiemannHypothesis) :
    (54539 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 31853,
        Real.exp (-(n : ℝ) / (637060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (637060 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 31591) * ((637060 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((637060 / 37) * (37 / 20)) + 1) / (1000 / 31591) +
        1839 / 1000 ≤
      1056407 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh58_roots.2.2]
  have hs :
    Real.sqrt ((637060 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((637060 / 37) * (37 / 20)) +
        21 / 20 ≤
      29043 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh58_roots.2.2, gammaAnalyticHigh58_logs.2]
  have hz :
    Real.sqrt (637060 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (637060 / 37) + 2469 / 800 ≤
      23101 / 1000 := by
    linarith only [gammaAnalyticHigh58_roots.2.1, gammaAnalyticHigh58_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 637060 / 37) (y := 37 / 20) (h := 1000 / 31591) (r :=
      164021 / 1250) (e := 78619 / 500000) (p := 1056407 / 1000) (s := 29043 / 1000) (z :=
      23101 / 1000) (F := 54539 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh58_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (637060 / 37 : ℝ) * (37 / 20) = 31853 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh58_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (637060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (637060 / 37 : ℝ)) ≤
      131393 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1312167 / 10000) (T := 164021 / 1250) (Z := 48769 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh58_roots.1
      gammaAnalyticHigh58_roots.2.1 gammaAnalyticHigh58_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh58_power : (637060 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 83 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 58 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh58_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (6517 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1315 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (31853 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 6517 / 20)]
  apply
    reject_03_of_analytic_caps (B := 31853) (x := 637060 / 37) (H := 1315 / 4) (R :=
      1312167 / 10000) (W := 83 / 20000) (F := 54539 / 500) (U := 131393 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh58_power (gammaAnalyticHigh58_main hGRH.riemann)
      (gammaAnalyticHigh58_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 59. -/
theorem gammaAnalyticHigh59_roots :
    ((264767 / 2000 : ℝ) ≤ Real.sqrt (648440 / 37 : ℝ) ∧
      Real.sqrt (648440 / 37 : ℝ) ≤ 330959 / 2500 ∧ Real.sqrt (32422 : ℝ) ≤ 450153 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 59. -/
theorem gammaAnalyticHigh59_logs :
    Real.log (648440 / 37 : ℝ) ≤ 19543 / 2000 ∧ Real.log (32422 : ℝ) ≤ 51933 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (648440 / 37) 15 20 0 (19543 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 32422 15 20 0 (51933 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh59_main (hRH : RiemannHypothesis) :
    (110057 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 32422,
        Real.exp (-(n : ℝ) / (648440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (648440 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 31731) * ((648440 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((648440 / 37) * (37 / 20)) + 1) / (1000 / 31731) +
        1839 / 1000 ≤
      535239 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh59_roots.2.2]
  have hs :
    Real.sqrt ((648440 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((648440 / 37) * (37 / 20)) +
        21 / 20 ≤
      5831 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh59_roots.2.2, gammaAnalyticHigh59_logs.2]
  have hz :
    Real.sqrt (648440 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (648440 / 37) + 2469 / 800 ≤
      23183 / 1000 := by
    linarith only [gammaAnalyticHigh59_roots.2.1, gammaAnalyticHigh59_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 648440 / 37) (y := 37 / 20) (h := 1000 / 31731) (r :=
      330959 / 2500) (e := 78619 / 500000) (p := 535239 / 500) (s := 5831 / 200) (z := 23183 / 1000)
      (F := 110057 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh59_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (648440 / 37 : ℝ) * (37 / 20) = 32422 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh59_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (648440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (648440 / 37 : ℝ)) ≤
      132559 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 264767 / 2000) (T := 330959 / 2500) (Z := 19543 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh59_roots.1
      gammaAnalyticHigh59_roots.2.1 gammaAnalyticHigh59_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh59_power : (648440 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 411 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 59 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh59_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1315 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (33167 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (32422 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1315 / 4)]
  apply
    reject_03_of_analytic_caps (B := 32422) (x := 648440 / 37) (H := 33167 / 100) (R :=
      264767 / 2000) (W := 411 / 100000) (F := 110057 / 1000) (U := 132559 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh59_power (gammaAnalyticHigh59_main hGRH.riemann)
      (gammaAnalyticHigh59_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 60. -/
theorem gammaAnalyticHigh60_roots :
    ((1335603 / 10000 : ℝ) ≤ Real.sqrt (660020 / 37 : ℝ) ∧
      Real.sqrt (660020 / 37 : ℝ) ≤ 333901 / 2500 ∧ Real.sqrt (33001 : ℝ) ≤ 908309 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 60. -/
theorem gammaAnalyticHigh60_logs :
    Real.log (660020 / 37 : ℝ) ≤ 24473 / 2500 ∧ Real.log (33001 : ℝ) ≤ 104043 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (660020 / 37) 15 20 0 (24473 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 33001 16 20 0 (104043 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh60_main (hRH : RiemannHypothesis) :
    (27761 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 33001,
        Real.exp (-(n : ℝ) / (660020 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (660020 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 31871) * ((660020 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((660020 / 37) * (37 / 20)) + 1) / (1000 / 31871) +
        1839 / 1000 ≤
      1084733 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh60_roots.2.2]
  have hs :
    Real.sqrt ((660020 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((660020 / 37) * (37 / 20)) +
        21 / 20 ≤
      29267 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh60_roots.2.2, gammaAnalyticHigh60_logs.2]
  have hz :
    Real.sqrt (660020 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (660020 / 37) + 2469 / 800 ≤
      23267 / 1000 := by
    linarith only [gammaAnalyticHigh60_roots.2.1, gammaAnalyticHigh60_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 660020 / 37) (y := 37 / 20) (h := 1000 / 31871) (r :=
      333901 / 2500) (e := 78619 / 500000) (p := 1084733 / 1000) (s := 29267 / 1000) (z :=
      23267 / 1000) (F := 27761 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh60_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (660020 / 37 : ℝ) * (37 / 20) = 33001 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh60_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (660020 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (660020 / 37 : ℝ)) ≤
      26747 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1335603 / 10000) (T := 333901 / 2500) (Z := 24473 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh60_roots.1
      gammaAnalyticHigh60_roots.2.1 gammaAnalyticHigh60_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh60_power : (660020 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 407 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 60 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh60_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (33167 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16731 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (33001 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 33167 / 100)]
  apply
    reject_03_of_analytic_caps (B := 33001) (x := 660020 / 37) (H := 16731 / 50) (R :=
      1335603 / 10000) (W := 407 / 100000) (F := 27761 / 250) (U := 26747 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh60_power (gammaAnalyticHigh60_main hGRH.riemann)
      (gammaAnalyticHigh60_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 61. -/
theorem gammaAnalyticHigh61_roots :
    ((134749 / 1000 : ℝ) ≤ Real.sqrt (671820 / 37 : ℝ) ∧
      Real.sqrt (671820 / 37 : ℝ) ≤ 1347491 / 10000 ∧ Real.sqrt (33591 : ℝ) ≤ 366557 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 61. -/
theorem gammaAnalyticHigh61_logs :
    Real.log (671820 / 37 : ℝ) ≤ 98069 / 10000 ∧ Real.log (33591 : ℝ) ≤ 104221 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (671820 / 37) 15 20 0 (98069 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 33591 16 20 0 (104221 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh61_main (hRH : RiemannHypothesis) :
    (112041 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 33591,
        Real.exp (-(n : ℝ) / (671820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (671820 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 128051) * ((671820 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((671820 / 37) * (37 / 20)) + 1) / (4000 / 128051) +
        1839 / 1000 ≤
      219839 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh61_roots.2.2]
  have hs :
    Real.sqrt ((671820 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((671820 / 37) * (37 / 20)) +
        21 / 20 ≤
      29381 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh61_roots.2.2, gammaAnalyticHigh61_logs.2]
  have hz :
    Real.sqrt (671820 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (671820 / 37) + 2469 / 800 ≤
      467 / 20 := by
    linarith only [gammaAnalyticHigh61_roots.2.1, gammaAnalyticHigh61_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 671820 / 37) (y := 37 / 20) (h := 4000 / 128051) (r :=
      1347491 / 10000) (e := 78619 / 500000) (p := 219839 / 200) (s := 29381 / 1000) (z := 467 / 20)
      (F := 112041 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh61_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (671820 / 37 : ℝ) * (37 / 20) = 33591 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh61_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (671820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (671820 / 37 : ℝ)) ≤
      134923 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 134749 / 1000) (T := 1347491 / 10000) (Z :=
      98069 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh61_roots.1
      gammaAnalyticHigh61_roots.2.1 gammaAnalyticHigh61_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh61_power : (671820 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 403 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 61 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh61_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16731 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (33759 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (33591 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16731 / 50)]
  apply
    reject_03_of_analytic_caps (B := 33591) (x := 671820 / 37) (H := 33759 / 100) (R :=
      134749 / 1000) (W := 403 / 100000) (F := 112041 / 1000) (U := 134923 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh61_power (gammaAnalyticHigh61_main hGRH.riemann)
      (gammaAnalyticHigh61_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 62. -/
theorem gammaAnalyticHigh62_roots :
    ((1359451 / 10000 : ℝ) ≤ Real.sqrt (683800 / 37 : ℝ) ∧
      Real.sqrt (683800 / 37 : ℝ) ≤ 339863 / 2500 ∧ Real.sqrt (34190 : ℝ) ≤ 924527 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 62. -/
theorem gammaAnalyticHigh62_logs :
    Real.log (683800 / 37 : ℝ) ≤ 49123 / 5000 ∧ Real.log (34190 : ℝ) ≤ 104397 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (683800 / 37) 15 20 0 (49123 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 34190 16 20 0 (104397 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh62_main (hRH : RiemannHypothesis) :
    (22609 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 34190,
        Real.exp (-(n : ℝ) / (683800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (683800 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 64309) * ((683800 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((683800 / 37) * (37 / 20)) + 1) / (2000 / 64309) +
        1839 / 1000 ≤
      278453 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh62_roots.2.2]
  have hs :
    Real.sqrt ((683800 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((683800 / 37) * (37 / 20)) +
        21 / 20 ≤
      14747 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh62_roots.2.2, gammaAnalyticHigh62_logs.2]
  have hz :
    Real.sqrt (683800 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (683800 / 37) + 2469 / 800 ≤
      4687 / 200 := by
    linarith only [gammaAnalyticHigh62_roots.2.1, gammaAnalyticHigh62_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 683800 / 37) (y := 37 / 20) (h := 2000 / 64309) (r :=
      339863 / 2500) (e := 78619 / 500000) (p := 278453 / 250) (s := 14747 / 500) (z := 4687 / 200)
      (F := 22609 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh62_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (683800 / 37 : ℝ) * (37 / 20) = 34190 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh62_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (683800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (683800 / 37 : ℝ)) ≤
      68059 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1359451 / 10000) (T := 339863 / 2500) (Z := 49123 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh62_roots.1
      gammaAnalyticHigh62_roots.2.1 gammaAnalyticHigh62_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh62_power : (683800 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 399 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 62 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh62_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (33759 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (34059 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (34190 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 33759 / 100)]
  apply
    reject_03_of_analytic_caps (B := 34190) (x := 683800 / 37) (H := 34059 / 100) (R :=
      1359451 / 10000) (W := 399 / 100000) (F := 22609 / 200) (U := 68059 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh62_power (gammaAnalyticHigh62_main hGRH.riemann)
      (gammaAnalyticHigh62_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 63. -/
theorem gammaAnalyticHigh63_roots :
    ((54861 / 400 : ℝ) ≤ Real.sqrt (696000 / 37 : ℝ) ∧
      Real.sqrt (696000 / 37 : ℝ) ≤ 685763 / 5000 ∧ Real.sqrt (34800 : ℝ) ≤ 466369 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 63. -/
theorem gammaAnalyticHigh63_logs :
    Real.log (696000 / 37 : ℝ) ≤ 49211 / 5000 ∧ Real.log (34800 : ℝ) ≤ 52287 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (696000 / 37) 15 20 0 (49211 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 34800 16 20 0 (52287 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh63_main (hRH : RiemannHypothesis) :
    (57029 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 34800,
        Real.exp (-(n : ℝ) / (696000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (696000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 16149) * ((696000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((696000 / 37) * (37 / 20)) + 1) / (500 / 16149) +
        1839 / 1000 ≤
      141079 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh63_roots.2.2]
  have hs :
    Real.sqrt ((696000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((696000 / 37) * (37 / 20)) +
        21 / 20 ≤
      29609 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh63_roots.2.2, gammaAnalyticHigh63_logs.2]
  have hz :
    Real.sqrt (696000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (696000 / 37) + 2469 / 800 ≤
      23519 / 1000 := by
    linarith only [gammaAnalyticHigh63_roots.2.1, gammaAnalyticHigh63_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 696000 / 37) (y := 37 / 20) (h := 500 / 16149) (r :=
      685763 / 5000) (e := 78619 / 500000) (p := 141079 / 125) (s := 29609 / 1000) (z :=
      23519 / 1000) (F := 57029 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh63_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (696000 / 37 : ℝ) * (37 / 20) = 34800 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh63_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (696000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (696000 / 37 : ℝ)) ≤
      5493 / 40 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 54861 / 400) (T := 685763 / 5000) (Z := 49211 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh63_roots.1
      gammaAnalyticHigh63_roots.2.1 gammaAnalyticHigh63_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh63_power : (696000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 79 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 63 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh63_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (34059 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (34361 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (34800 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 34059 / 100)]
  apply
    reject_03_of_analytic_caps (B := 34800) (x := 696000 / 37) (H := 34361 / 100) (R := 54861 / 400)
      (W := 79 / 20000) (F := 57029 / 500) (U := 5493 / 40) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh63_power (gammaAnalyticHigh63_main hGRH.riemann)
      (gammaAnalyticHigh63_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 64. -/
theorem gammaAnalyticHigh64_roots :
    ((172961 / 1250 : ℝ) ≤ Real.sqrt (708400 / 37 : ℝ) ∧
      Real.sqrt (708400 / 37 : ℝ) ≤ 1383689 / 10000 ∧ Real.sqrt (35420 : ℝ) ≤ 1882021 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 64. -/
theorem gammaAnalyticHigh64_logs :
    Real.log (708400 / 37 : ℝ) ≤ 98599 / 10000 ∧ Real.log (35420 : ℝ) ≤ 104751 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (708400 / 37) 15 20 0 (98599 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 35420 16 20 0 (104751 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh64_main (hRH : RiemannHypothesis) :
    (115079 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 35420,
        Real.exp (-(n : ℝ) / (708400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (708400 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 129759) * ((708400 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((708400 / 37) * (37 / 20)) + 1) / (4000 / 129759) +
        1839 / 1000 ≤
      1143629 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh64_roots.2.2]
  have hs :
    Real.sqrt ((708400 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((708400 / 37) * (37 / 20)) +
        21 / 20 ≤
      7431 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh64_roots.2.2, gammaAnalyticHigh64_logs.2]
  have hz :
    Real.sqrt (708400 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (708400 / 37) + 2469 / 800 ≤
      5901 / 250 := by
    linarith only [gammaAnalyticHigh64_roots.2.1, gammaAnalyticHigh64_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 708400 / 37) (y := 37 / 20) (h := 4000 / 129759) (r :=
      1383689 / 10000) (e := 78619 / 500000) (p := 1143629 / 1000) (s := 7431 / 250) (z :=
      5901 / 250) (F := 115079 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh64_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (708400 / 37 : ℝ) * (37 / 20) = 35420 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh64_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (708400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (708400 / 37 : ℝ)) ≤
      6927 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 172961 / 1250) (T := 1383689 / 10000) (Z :=
      98599 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh64_roots.1
      gammaAnalyticHigh64_roots.2.1 gammaAnalyticHigh64_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh64_power : (708400 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 391 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 64 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh64_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (34361 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6933 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (35420 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 34361 / 100)]
  apply
    reject_03_of_analytic_caps (B := 35420) (x := 708400 / 37) (H := 6933 / 20) (R := 172961 / 1250)
      (W := 391 / 100000) (F := 115079 / 1000) (U := 6927 / 50) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh64_power (gammaAnalyticHigh64_main hGRH.riemann)
      (gammaAnalyticHigh64_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 65. -/
theorem gammaAnalyticHigh65_roots :
    ((17449 / 125 : ℝ) ≤ Real.sqrt (720980 / 37 : ℝ) ∧
      Real.sqrt (720980 / 37 : ℝ) ≤ 1395921 / 10000 ∧ Real.sqrt (36049 : ℝ) ≤ 949329 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 65. -/
theorem gammaAnalyticHigh65_logs :
    Real.log (720980 / 37 : ℝ) ≤ 3951 / 400 ∧ Real.log (36049 : ℝ) ≤ 104927 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (720980 / 37) 15 20 0 (3951 / 400) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 36049 16 20 0 (104927 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh65_main (hRH : RiemannHypothesis) :
    (23221 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 36049,
        Real.exp (-(n : ℝ) / (720980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (720980 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 130333) * ((720980 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((720980 / 37) * (37 / 20)) + 1) / (4000 / 130333) +
        1839 / 1000 ≤
      144847 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh65_roots.2.2]
  have hs :
    Real.sqrt ((720980 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((720980 / 37) * (37 / 20)) +
        21 / 20 ≤
      746 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh65_roots.2.2, gammaAnalyticHigh65_logs.2]
  have hz :
    Real.sqrt (720980 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (720980 / 37) + 2469 / 800 ≤
      2369 / 100 := by
    linarith only [gammaAnalyticHigh65_roots.2.1, gammaAnalyticHigh65_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 720980 / 37) (y := 37 / 20) (h := 4000 / 130333) (r :=
      1395921 / 10000) (e := 78619 / 500000) (p := 144847 / 125) (s := 746 / 25) (z := 2369 / 100)
      (F := 23221 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh65_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (720980 / 37 : ℝ) * (37 / 20) = 36049 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh65_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (720980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (720980 / 37 : ℝ)) ≤
      69881 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 17449 / 125) (T := 1395921 / 10000) (Z := 3951 / 400)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh65_roots.1
      gammaAnalyticHigh65_roots.2.1 gammaAnalyticHigh65_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh65_power : (720980 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 387 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 65 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh65_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (6933 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (34971 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (36049 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 6933 / 20)]
  apply
    reject_03_of_analytic_caps (B := 36049) (x := 720980 / 37) (H := 34971 / 100) (R := 17449 / 125)
      (W := 387 / 100000) (F := 23221 / 200) (U := 69881 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh65_power (gammaAnalyticHigh65_main hGRH.riemann)
      (gammaAnalyticHigh65_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 66. -/
theorem gammaAnalyticHigh66_roots :
    ((1408257 / 10000 : ℝ) ≤ Real.sqrt (733780 / 37 : ℝ) ∧
      Real.sqrt (733780 / 37 : ℝ) ≤ 704129 / 5000 ∧ Real.sqrt (36689 : ℝ) ≤ 957719 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 66. -/
theorem gammaAnalyticHigh66_logs :
    Real.log (733780 / 37 : ℝ) ≤ 98951 / 10000 ∧ Real.log (36689 : ℝ) ≤ 105103 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (733780 / 37) 15 20 0 (98951 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 36689 16 20 0 (105103 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh66_main (hRH : RiemannHypothesis) :
    (5857 / 50 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 36689,
        Real.exp (-(n : ℝ) / (733780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (733780 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 130907) * ((733780 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((733780 / 37) * (37 / 20)) + 1) / (4000 / 130907) +
        1839 / 1000 ≤
      29353 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh66_roots.2.2]
  have hs :
    Real.sqrt ((733780 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((733780 / 37) * (37 / 20)) +
        21 / 20 ≤
      7489 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh66_roots.2.2, gammaAnalyticHigh66_logs.2]
  have hz :
    Real.sqrt (733780 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (733780 / 37) + 2469 / 800 ≤
      2972 / 125 := by
    linarith only [gammaAnalyticHigh66_roots.2.1, gammaAnalyticHigh66_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 733780 / 37) (y := 37 / 20) (h := 4000 / 130907) (r :=
      704129 / 5000) (e := 78619 / 500000) (p := 29353 / 25) (s := 7489 / 250) (z := 2972 / 125)
      (F := 5857 / 50) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh66_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (733780 / 37 : ℝ) * (37 / 20) = 36689 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh66_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (733780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (733780 / 37 : ℝ)) ≤
      28199 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1408257 / 10000) (T := 704129 / 5000) (Z :=
      98951 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh66_roots.1
      gammaAnalyticHigh66_roots.2.1 gammaAnalyticHigh66_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh66_power : (733780 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 383 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 66 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh66_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (34971 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1764 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (36689 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 34971 / 100)]
  apply
    reject_03_of_analytic_caps (B := 36689) (x := 733780 / 37) (H := 1764 / 5) (R :=
      1408257 / 10000) (W := 383 / 100000) (F := 5857 / 50) (U := 28199 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh66_power (gammaAnalyticHigh66_main hGRH.riemann)
      (gammaAnalyticHigh66_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 67. -/
theorem gammaAnalyticHigh67_roots :
    ((177587 / 1250 : ℝ) ≤ Real.sqrt (746800 / 37 : ℝ) ∧
      Real.sqrt (746800 / 37 : ℝ) ≤ 1420697 / 10000 ∧ Real.sqrt (37340 : ℝ) ≤ 1932357 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 67. -/
theorem gammaAnalyticHigh67_logs :
    Real.log (746800 / 37 : ℝ) ≤ 99127 / 10000 ∧ Real.log (37340 : ℝ) ≤ 105279 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (746800 / 37) 15 20 0 (99127 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 37340 16 20 0 (105279 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh67_main (hRH : RiemannHypothesis) :
    (14773 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 37340,
        Real.exp (-(n : ℝ) / (746800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (746800 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 131481) * ((746800 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((746800 / 37) * (37 / 20)) + 1) / (4000 / 131481) +
        1839 / 1000 ≤
      1189659 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh67_roots.2.2]
  have hs :
    Real.sqrt ((746800 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((746800 / 37) * (37 / 20)) +
        21 / 20 ≤
      30073 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh67_roots.2.2, gammaAnalyticHigh67_logs.2]
  have hz :
    Real.sqrt (746800 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (746800 / 37) + 2469 / 800 ≤
      11931 / 500 := by
    linarith only [gammaAnalyticHigh67_roots.2.1, gammaAnalyticHigh67_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 746800 / 37) (y := 37 / 20) (h := 4000 / 131481) (r :=
      1420697 / 10000) (e := 78619 / 500000) (p := 1189659 / 1000) (s := 30073 / 1000) (z :=
      11931 / 500) (F := 14773 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh67_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (746800 / 37 : ℝ) * (37 / 20) = 37340 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh67_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (746800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (746800 / 37 : ℝ)) ≤
      71119 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 177587 / 1250) (T := 1420697 / 10000) (Z :=
      99127 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh67_roots.1
      gammaAnalyticHigh67_roots.2.1 gammaAnalyticHigh67_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh67_power : (746800 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 379 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 67 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh67_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1764 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8898 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (37340 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1764 / 5)]
  apply
    reject_03_of_analytic_caps (B := 37340) (x := 746800 / 37) (H := 8898 / 25) (R := 177587 / 1250)
      (W := 379 / 100000) (F := 14773 / 125) (U := 71119 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh67_power (gammaAnalyticHigh67_main hGRH.riemann)
      (gammaAnalyticHigh67_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 68. -/
theorem gammaAnalyticHigh68_roots :
    ((1433253 / 10000 : ℝ) ≤ Real.sqrt (760060 / 37 : ℝ) ∧
      Real.sqrt (760060 / 37 : ℝ) ≤ 716627 / 5000 ∧ Real.sqrt (38003 : ℝ) ≤ 487359 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 68. -/
theorem gammaAnalyticHigh68_logs :
    Real.log (760060 / 37 : ℝ) ≤ 99303 / 10000 ∧ Real.log (38003 : ℝ) ≤ 21091 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (760060 / 37) 15 20 0 (99303 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 38003 16 20 0 (21091 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh68_main (hRH : RiemannHypothesis) :
    (59619 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 38003,
        Real.exp (-(n : ℝ) / (760060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (760060 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 66031) * ((760060 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((760060 / 37) * (37 / 20)) + 1) / (2000 / 66031) +
        1839 / 1000 ≤
      241083 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh68_roots.2.2]
  have hs :
    Real.sqrt ((760060 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((760060 / 37) * (37 / 20)) +
        21 / 20 ≤
      30191 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh68_roots.2.2, gammaAnalyticHigh68_logs.2]
  have hz :
    Real.sqrt (760060 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (760060 / 37) + 2469 / 800 ≤
      23949 / 1000 := by
    linarith only [gammaAnalyticHigh68_roots.2.1, gammaAnalyticHigh68_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 760060 / 37) (y := 37 / 20) (h := 2000 / 66031) (r :=
      716627 / 5000) (e := 78619 / 500000) (p := 241083 / 200) (s := 30191 / 1000) (z :=
      23949 / 1000) (F := 59619 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh68_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (760060 / 37 : ℝ) * (37 / 20) = 38003 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh68_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (760060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (760060 / 37 : ℝ)) ≤
      143493 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1433253 / 10000) (T := 716627 / 5000) (Z :=
      99303 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh68_roots.1
      gammaAnalyticHigh68_roots.2.1 gammaAnalyticHigh68_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh68_power : (760060 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 47 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 68 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh68_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (8898 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17953 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (38003 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 8898 / 25)]
  apply
    reject_03_of_analytic_caps (B := 38003) (x := 760060 / 37) (H := 17953 / 50) (R :=
      1433253 / 10000) (W := 47 / 12500) (F := 59619 / 500) (U := 143493 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh68_power (gammaAnalyticHigh68_main hGRH.riemann)
      (gammaAnalyticHigh68_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 69. -/
theorem gammaAnalyticHigh69_roots :
    ((1445907 / 10000 : ℝ) ≤ Real.sqrt (773540 / 37 : ℝ) ∧
      Real.sqrt (773540 / 37 : ℝ) ≤ 361477 / 2500 ∧ Real.sqrt (38677 : ℝ) ≤ 1966647 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 69. -/
theorem gammaAnalyticHigh69_logs :
    Real.log (773540 / 37 : ℝ) ≤ 99479 / 10000 ∧ Real.log (38677 : ℝ) ≤ 105631 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (773540 / 37) 15 20 0 (99479 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 38677 16 20 0 (105631 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh69_main (hRH : RiemannHypothesis) :
    (1203 / 10 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 38677,
        Real.exp (-(n : ℝ) / (773540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (773540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 132643) * ((773540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((773540 / 37) * (37 / 20)) + 1) / (4000 / 132643) +
        1839 / 1000 ≤
      610681 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh69_roots.2.2]
  have hs :
    Real.sqrt ((773540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((773540 / 37) * (37 / 20)) +
        21 / 20 ≤
      30309 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh69_roots.2.2, gammaAnalyticHigh69_logs.2]
  have hz :
    Real.sqrt (773540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (773540 / 37) + 2469 / 800 ≤
      24037 / 1000 := by
    linarith only [gammaAnalyticHigh69_roots.2.1, gammaAnalyticHigh69_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 773540 / 37) (y := 37 / 20) (h := 4000 / 132643) (r :=
      361477 / 2500) (e := 78619 / 500000) (p := 610681 / 500) (s := 30309 / 1000) (z :=
      24037 / 1000) (F := 1203 / 10) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh69_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (773540 / 37 : ℝ) * (37 / 20) = 38677 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh69_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (773540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (773540 / 37 : ℝ)) ≤
      72379 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1445907 / 10000) (T := 361477 / 2500) (Z :=
      99479 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh69_roots.1
      gammaAnalyticHigh69_roots.2.1 gammaAnalyticHigh69_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh69_power : (773540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 93 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 69 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh69_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17953 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (36223 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (38677 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17953 / 50)]
  apply
    reject_03_of_analytic_caps (B := 38677) (x := 773540 / 37) (H := 36223 / 100) (R :=
      1445907 / 10000) (W := 93 / 25000) (F := 1203 / 10) (U := 72379 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh69_power (gammaAnalyticHigh69_main hGRH.riemann)
      (gammaAnalyticHigh69_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 70. -/
theorem gammaAnalyticHigh70_roots :
    ((1458673 / 10000 : ℝ) ≤ Real.sqrt (787260 / 37 : ℝ) ∧
      Real.sqrt (787260 / 37 : ℝ) ≤ 729337 / 5000 ∧ Real.sqrt (39363 : ℝ) ≤ 496003 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 70. -/
theorem gammaAnalyticHigh70_logs :
    Real.log (787260 / 37 : ℝ) ≤ 49827 / 5000 ∧ Real.log (39363 : ℝ) ≤ 52903 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (787260 / 37) 15 20 0 (49827 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 39363 16 20 0 (52903 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh70_main (hRH : RiemannHypothesis) :
    (121371 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 39363,
        Real.exp (-(n : ℝ) / (787260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (787260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 133231) * ((787260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((787260 / 37) * (37 / 20)) + 1) / (4000 / 133231) +
        1839 / 1000 ≤
      618761 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh70_roots.2.2]
  have hs :
    Real.sqrt ((787260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((787260 / 37) * (37 / 20)) +
        21 / 20 ≤
      7607 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh70_roots.2.2, gammaAnalyticHigh70_logs.2]
  have hz :
    Real.sqrt (787260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (787260 / 37) + 2469 / 800 ≤
      193 / 8 := by
    linarith only [gammaAnalyticHigh70_roots.2.1, gammaAnalyticHigh70_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 787260 / 37) (y := 37 / 20) (h := 4000 / 133231) (r :=
      729337 / 5000) (e := 78619 / 500000) (p := 618761 / 500) (s := 7607 / 250) (z := 193 / 8)
      (F := 121371 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh70_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (787260 / 37 : ℝ) * (37 / 20) = 39363 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh70_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (787260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (787260 / 37 : ℝ)) ≤
      146033 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1458673 / 10000) (T := 729337 / 5000) (Z := 49827 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh70_roots.1
      gammaAnalyticHigh70_roots.2.1 gammaAnalyticHigh70_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh70_power : (787260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 23 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 70 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh70_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (36223 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18271 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (39363 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 36223 / 100)]
  apply
    reject_03_of_analytic_caps (B := 39363) (x := 787260 / 37) (H := 18271 / 50) (R :=
      1458673 / 10000) (W := 23 / 6250) (F := 121371 / 1000) (U := 146033 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh70_power (gammaAnalyticHigh70_main hGRH.riemann)
      (gammaAnalyticHigh70_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 71. -/
theorem gammaAnalyticHigh71_roots :
    ((1471513 / 10000 : ℝ) ≤ Real.sqrt (801180 / 37 : ℝ) ∧
      Real.sqrt (801180 / 37 : ℝ) ≤ 735757 / 5000 ∧ Real.sqrt (40059 : ℝ) ≤ 80059 / 400) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 71. -/
theorem gammaAnalyticHigh71_logs :
    Real.log (801180 / 37 : ℝ) ≤ 9983 / 1000 ∧ Real.log (40059 : ℝ) ≤ 52991 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (801180 / 37) 15 20 0 (9983 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 40059 16 20 0 (52991 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh71_main (hRH : RiemannHypothesis) :
    (15306 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 40059,
        Real.exp (-(n : ℝ) / (801180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (801180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 33453) * ((801180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((801180 / 37) * (37 / 20)) + 1) / (1000 / 33453) +
        1839 / 1000 ≤
      626923 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh71_roots.2.2]
  have hs :
    Real.sqrt ((801180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((801180 / 37) * (37 / 20)) +
        21 / 20 ≤
      7637 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh71_roots.2.2, gammaAnalyticHigh71_logs.2]
  have hz :
    Real.sqrt (801180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (801180 / 37) + 2469 / 800 ≤
      24213 / 1000 := by
    linarith only [gammaAnalyticHigh71_roots.2.1, gammaAnalyticHigh71_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 801180 / 37) (y := 37 / 20) (h := 1000 / 33453) (r :=
      735757 / 5000) (e := 78619 / 500000) (p := 626923 / 500) (s := 7637 / 250) (z := 24213 / 1000)
      (F := 15306 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh71_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (801180 / 37 : ℝ) * (37 / 20) = 40059 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh71_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (801180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (801180 / 37 : ℝ)) ≤
      36829 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1471513 / 10000) (T := 735757 / 5000) (Z := 9983 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh71_roots.1
      gammaAnalyticHigh71_roots.2.1 gammaAnalyticHigh71_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh71_power : (801180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 73 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 71 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh71_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18271 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (36863 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (40059 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18271 / 50)]
  apply
    reject_03_of_analytic_caps (B := 40059) (x := 801180 / 37) (H := 36863 / 100) (R :=
      1471513 / 10000) (W := 73 / 20000) (F := 15306 / 125) (U := 36829 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh71_power (gammaAnalyticHigh71_main hGRH.riemann)
      (gammaAnalyticHigh71_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 72. -/
theorem gammaAnalyticHigh72_roots :
    ((1484441 / 10000 : ℝ) ≤ Real.sqrt (815320 / 37 : ℝ) ∧
      Real.sqrt (815320 / 37 : ℝ) ≤ 742221 / 5000 ∧ Real.sqrt (40766 : ℝ) ≤ 100953 / 500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 72. -/
theorem gammaAnalyticHigh72_logs :
    Real.log (815320 / 37 : ℝ) ≤ 20001 / 2000 ∧ Real.log (40766 : ℝ) ≤ 106157 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (815320 / 37) 15 20 0 (20001 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 40766 16 20 0 (106157 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh72_main (hRH : RiemannHypothesis) :
    (123533 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 40766,
        Real.exp (-(n : ℝ) / (815320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (815320 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (5 / 168) * ((815320 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((815320 / 37) * (37 / 20)) + 1) / (5 / 168) +
        1839 / 1000 ≤
      254071 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh72_roots.2.2]
  have hs :
    Real.sqrt ((815320 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((815320 / 37) * (37 / 20)) +
        21 / 20 ≤
      7667 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh72_roots.2.2, gammaAnalyticHigh72_logs.2]
  have hz :
    Real.sqrt (815320 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (815320 / 37) + 2469 / 800 ≤
      12151 / 500 := by
    linarith only [gammaAnalyticHigh72_roots.2.1, gammaAnalyticHigh72_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 815320 / 37) (y := 37 / 20) (h := 5 / 168) (r :=
      742221 / 5000) (e := 78619 / 500000) (p := 254071 / 200) (s := 7667 / 250) (z := 12151 / 500)
      (F := 123533 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh72_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (815320 / 37 : ℝ) * (37 / 20) = 40766 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh72_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (815320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (815320 / 37 : ℝ)) ≤
      18576 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1484441 / 10000) (T := 742221 / 5000) (Z := 20001 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh72_roots.1
      gammaAnalyticHigh72_roots.2.1 gammaAnalyticHigh72_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh72_power : (815320 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 361 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 72 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh72_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (36863 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (37187 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (40766 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 36863 / 100)]
  apply
    reject_03_of_analytic_caps (B := 40766) (x := 815320 / 37) (H := 37187 / 100) (R :=
      1484441 / 10000) (W := 361 / 100000) (F := 123533 / 1000) (U := 18576 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh72_power (gammaAnalyticHigh72_main hGRH.riemann)
      (gammaAnalyticHigh72_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 73. -/
theorem gammaAnalyticHigh73_roots :
    ((1497493 / 10000 : ℝ) ≤ Real.sqrt (829720 / 37 : ℝ) ∧
      Real.sqrt (829720 / 37 : ℝ) ≤ 748747 / 5000 ∧ Real.sqrt (41486 : ℝ) ≤ 509203 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 73. -/
theorem gammaAnalyticHigh73_logs :
    Real.log (829720 / 37 : ℝ) ≤ 5009 / 500 ∧ Real.log (41486 : ℝ) ≤ 26583 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (829720 / 37) 15 20 0 (5009 / 500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 41486 16 20 0 (26583 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh73_main (hRH : RiemannHypothesis) :
    (31157 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 41486,
        Real.exp (-(n : ℝ) / (829720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (829720 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 33747) * ((829720 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((829720 / 37) * (37 / 20)) + 1) / (1000 / 33747) +
        1839 / 1000 ≤
      643547 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh73_roots.2.2]
  have hs :
    Real.sqrt ((829720 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((829720 / 37) * (37 / 20)) +
        21 / 20 ≤
      30789 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh73_roots.2.2, gammaAnalyticHigh73_logs.2]
  have hz :
    Real.sqrt (829720 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (829720 / 37) + 2469 / 800 ≤
      3049 / 125 := by
    linarith only [gammaAnalyticHigh73_roots.2.1, gammaAnalyticHigh73_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 829720 / 37) (y := 37 / 20) (h := 1000 / 33747) (r :=
      748747 / 5000) (e := 78619 / 500000) (p := 643547 / 500) (s := 30789 / 1000) (z := 3049 / 125)
      (F := 31157 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh73_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (829720 / 37 : ℝ) * (37 / 20) = 41486 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh73_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (829720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (829720 / 37 : ℝ)) ≤
      149913 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1497493 / 10000) (T := 748747 / 5000) (Z := 5009 / 500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh73_roots.1
      gammaAnalyticHigh73_roots.2.1 gammaAnalyticHigh73_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh73_power : (829720 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 179 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 73 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh73_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (37187 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (37513 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (41486 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 37187 / 100)]
  apply
    reject_03_of_analytic_caps (B := 41486) (x := 829720 / 37) (H := 37513 / 100) (R :=
      1497493 / 10000) (W := 179 / 50000) (F := 31157 / 250) (U := 149913 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh73_power (gammaAnalyticHigh73_main hGRH.riemann)
      (gammaAnalyticHigh73_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 74. -/
theorem gammaAnalyticHigh74_roots :
    ((1510611 / 10000 : ℝ) ≤ Real.sqrt (844320 / 37 : ℝ) ∧
      Real.sqrt (844320 / 37 : ℝ) ≤ 377653 / 2500 ∧ Real.sqrt (42216 : ℝ) ≤ 1027327 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 74. -/
theorem gammaAnalyticHigh74_logs :
    Real.log (844320 / 37 : ℝ) ≤ 50177 / 5000 ∧ Real.log (42216 : ℝ) ≤ 53253 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (844320 / 37) 15 20 0 (50177 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 42216 16 20 0 (53253 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh74_main (hRH : RiemannHypothesis) :
    (125729 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 42216,
        Real.exp (-(n : ℝ) / (844320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (844320 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 135583) * ((844320 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((844320 / 37) * (37 / 20)) + 1) / (4000 / 135583) +
        1839 / 1000 ≤
      1303991 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh74_roots.2.2]
  have hs :
    Real.sqrt ((844320 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((844320 / 37) * (37 / 20)) +
        21 / 20 ≤
      3091 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh74_roots.2.2, gammaAnalyticHigh74_logs.2]
  have hz :
    Real.sqrt (844320 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (844320 / 37) + 2469 / 800 ≤
      24481 / 1000 := by
    linarith only [gammaAnalyticHigh74_roots.2.1, gammaAnalyticHigh74_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 844320 / 37) (y := 37 / 20) (h := 4000 / 135583) (r :=
      377653 / 2500) (e := 78619 / 500000) (p := 1303991 / 1000) (s := 3091 / 100) (z :=
      24481 / 1000) (F := 125729 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh74_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (844320 / 37 : ℝ) * (37 / 20) = 42216 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh74_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (844320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (844320 / 37 : ℝ)) ≤
      18903 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1510611 / 10000) (T := 377653 / 2500) (Z := 50177 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh74_roots.1
      gammaAnalyticHigh74_roots.2.1 gammaAnalyticHigh74_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh74_power : (844320 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 177 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 74 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh74_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (37513 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18921 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (42216 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 37513 / 100)]
  apply
    reject_03_of_analytic_caps (B := 42216) (x := 844320 / 37) (H := 18921 / 50) (R :=
      1510611 / 10000) (W := 177 / 50000) (F := 125729 / 1000) (U := 18903 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh74_power (gammaAnalyticHigh74_main hGRH.riemann)
      (gammaAnalyticHigh74_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 75. -/
theorem gammaAnalyticHigh75_roots :
    ((190483 / 1250 : ℝ) ≤ Real.sqrt (859200 / 37 : ℝ) ∧
      Real.sqrt (859200 / 37 : ℝ) ≤ 304773 / 2000 ∧ Real.sqrt (42960 : ℝ) ≤ 51817 / 250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 75. -/
theorem gammaAnalyticHigh75_logs :
    Real.log (859200 / 37 : ℝ) ≤ 100529 / 10000 ∧ Real.log (42960 : ℝ) ≤ 106681 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (859200 / 37) 15 20 0 (100529 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 42960 16 20 0 (106681 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh75_main (hRH : RiemannHypothesis) :
    (126841 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 42960,
        Real.exp (-(n : ℝ) / (859200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (859200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 68089) * ((859200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((859200 / 37) * (37 / 20)) + 1) / (2000 / 68089) +
        1839 / 1000 ≤
      1321137 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh75_roots.2.2]
  have hs :
    Real.sqrt ((859200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((859200 / 37) * (37 / 20)) +
        21 / 20 ≤
      31033 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh75_roots.2.2, gammaAnalyticHigh75_logs.2]
  have hz :
    Real.sqrt (859200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (859200 / 37) + 2469 / 800 ≤
      6143 / 250 := by
    linarith only [gammaAnalyticHigh75_roots.2.1, gammaAnalyticHigh75_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 859200 / 37) (y := 37 / 20) (h := 2000 / 68089) (r :=
      304773 / 2000) (e := 78619 / 500000) (p := 1321137 / 1000) (s := 31033 / 1000) (z :=
      6143 / 250) (F := 126841 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh75_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (859200 / 37 : ℝ) * (37 / 20) = 42960 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh75_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (859200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (859200 / 37 : ℝ)) ≤
      38137 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 190483 / 1250) (T := 304773 / 2000) (Z := 100529 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh75_roots.1
      gammaAnalyticHigh75_roots.2.1 gammaAnalyticHigh75_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh75_power : (859200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 351 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 75 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh75_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18921 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (38173 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (42960 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18921 / 50)]
  apply
    reject_03_of_analytic_caps (B := 42960) (x := 859200 / 37) (H := 38173 / 100) (R :=
      190483 / 1250) (W := 351 / 100000) (F := 126841 / 1000) (U := 38137 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh75_power (gammaAnalyticHigh75_main hGRH.riemann)
      (gammaAnalyticHigh75_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 76. -/
theorem gammaAnalyticHigh76_roots :
    ((384299 / 2500 : ℝ) ≤ Real.sqrt (874300 / 37 : ℝ) ∧
      Real.sqrt (874300 / 37 : ℝ) ≤ 1537197 / 10000 ∧ Real.sqrt (43715 : ℝ) ≤ 1045407 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 76. -/
theorem gammaAnalyticHigh76_logs :
    Real.log (874300 / 37 : ℝ) ≤ 100703 / 10000 ∧ Real.log (43715 : ℝ) ≤ 21371 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (874300 / 37) 15 20 0 (100703 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 43715 16 20 0 (21371 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh76_main (hRH : RiemannHypothesis) :
    (3199 / 25 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 43715,
        Real.exp (-(n : ℝ) / (874300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (874300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 68383) * ((874300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((874300 / 37) * (37 / 20)) + 1) / (2000 / 68383) +
        1839 / 1000 ≤
      1338461 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh76_roots.2.2]
  have hs :
    Real.sqrt ((874300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((874300 / 37) * (37 / 20)) +
        21 / 20 ≤
      6231 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh76_roots.2.2, gammaAnalyticHigh76_logs.2]
  have hz :
    Real.sqrt (874300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (874300 / 37) + 2469 / 800 ≤
      12331 / 500 := by
    linarith only [gammaAnalyticHigh76_roots.2.1, gammaAnalyticHigh76_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 874300 / 37) (y := 37 / 20) (h := 2000 / 68383) (r :=
      1537197 / 10000) (e := 78619 / 500000) (p := 1338461 / 1000) (s := 6231 / 200) (z :=
      12331 / 500) (F := 3199 / 25) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh76_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (874300 / 37 : ℝ) * (37 / 20) = 43715 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh76_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (874300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (874300 / 37 : ℝ)) ≤
      153881 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 384299 / 2500) (T := 1537197 / 10000) (Z :=
      100703 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh76_roots.1
      gammaAnalyticHigh76_roots.2.1 gammaAnalyticHigh76_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh76_power : (874300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 347 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 76 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh76_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (38173 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (38507 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (43715 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 38173 / 100)]
  apply
    reject_03_of_analytic_caps (B := 43715) (x := 874300 / 37) (H := 38507 / 100) (R :=
      384299 / 2500) (W := 347 / 100000) (F := 3199 / 25) (U := 153881 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh76_power (gammaAnalyticHigh76_main hGRH.riemann)
      (gammaAnalyticHigh76_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 77. -/
theorem gammaAnalyticHigh77_roots :
    ((19383 / 125 : ℝ) ≤ Real.sqrt (889660 / 37 : ℝ) ∧
      Real.sqrt (889660 / 37 : ℝ) ≤ 1550641 / 10000 ∧ Real.sqrt (44483 : ℝ) ≤ 21091 / 100) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 77. -/
theorem gammaAnalyticHigh77_logs :
    Real.log (889660 / 37 : ℝ) ≤ 100877 / 10000 ∧ Real.log (44483 : ℝ) ≤ 107029 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (889660 / 37) 15 20 0 (100877 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 44483 16 20 0 (107029 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh77_main (hRH : RiemannHypothesis) :
    (16136 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 44483,
        Real.exp (-(n : ℝ) / (889660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (889660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 17171) * ((889660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((889660 / 37) * (37 / 20)) + 1) / (500 / 17171) +
        1839 / 1000 ≤
      678003 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh77_roots.2.2]
  have hs :
    Real.sqrt ((889660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((889660 / 37) * (37 / 20)) +
        21 / 20 ≤
      31279 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh77_roots.2.2, gammaAnalyticHigh77_logs.2]
  have hz :
    Real.sqrt (889660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (889660 / 37) + 2469 / 800 ≤
      24753 / 1000 := by
    linarith only [gammaAnalyticHigh77_roots.2.1, gammaAnalyticHigh77_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 889660 / 37) (y := 37 / 20) (h := 500 / 17171) (r :=
      1550641 / 10000) (e := 78619 / 500000) (p := 678003 / 500) (s := 31279 / 1000) (z :=
      24753 / 1000) (F := 16136 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh77_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (889660 / 37 : ℝ) * (37 / 20) = 44483 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh77_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (889660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (889660 / 37 : ℝ)) ≤
      19403 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 19383 / 125) (T := 1550641 / 10000) (Z := 100877 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh77_roots.1
      gammaAnalyticHigh77_roots.2.1 gammaAnalyticHigh77_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh77_power : (889660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 43 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 77 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh77_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (38507 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (9711 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (44483 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 38507 / 100)]
  apply
    reject_03_of_analytic_caps (B := 44483) (x := 889660 / 37) (H := 9711 / 25) (R := 19383 / 125)
      (W := 43 / 12500) (F := 16136 / 125) (U := 19403 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh77_power (gammaAnalyticHigh77_main hGRH.riemann)
      (gammaAnalyticHigh77_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 78. -/
theorem gammaAnalyticHigh78_roots :
    ((1564211 / 10000 : ℝ) ≤ Real.sqrt (905300 / 37 : ℝ) ∧
      Real.sqrt (905300 / 37 : ℝ) ≤ 391053 / 2500 ∧ Real.sqrt (45265 : ℝ) ≤ 1063779 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 78. -/
theorem gammaAnalyticHigh78_logs :
    Real.log (905300 / 37 : ℝ) ≤ 25263 / 2500 ∧ Real.log (45265 : ℝ) ≤ 107203 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (905300 / 37) 15 20 0 (25263 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 45265 16 20 0 (107203 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh78_main (hRH : RiemannHypothesis) :
    (130227 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 45265,
        Real.exp (-(n : ℝ) / (905300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (905300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 137963) * ((905300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((905300 / 37) * (37 / 20)) + 1) / (4000 / 137963) +
        1839 / 1000 ≤
      686897 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh78_roots.2.2]
  have hs :
    Real.sqrt ((905300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((905300 / 37) * (37 / 20)) +
        21 / 20 ≤
      31403 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh78_roots.2.2, gammaAnalyticHigh78_logs.2]
  have hz :
    Real.sqrt (905300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (905300 / 37) + 2469 / 800 ≤
      4969 / 200 := by
    linarith only [gammaAnalyticHigh78_roots.2.1, gammaAnalyticHigh78_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 905300 / 37) (y := 37 / 20) (h := 4000 / 137963) (r :=
      391053 / 2500) (e := 78619 / 500000) (p := 686897 / 500) (s := 31403 / 1000) (z := 4969 / 200)
      (F := 130227 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh78_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (905300 / 37 : ℝ) * (37 / 20) = 45265 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh78_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (905300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (905300 / 37 : ℝ)) ≤
      156581 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1564211 / 10000) (T := 391053 / 2500) (Z := 25263 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh78_roots.1
      gammaAnalyticHigh78_roots.2.1 gammaAnalyticHigh78_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh78_power : (905300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 17 / 5000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 78 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh78_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (9711 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (39183 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (45265 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 9711 / 25)]
  apply
    reject_03_of_analytic_caps (B := 45265) (x := 905300 / 37) (H := 39183 / 100) (R :=
      1564211 / 10000) (W := 17 / 5000) (F := 130227 / 1000) (U := 156581 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh78_power (gammaAnalyticHigh78_main hGRH.riemann)
      (gammaAnalyticHigh78_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 79. -/
theorem gammaAnalyticHigh79_roots :
    ((157787 / 1000 : ℝ) ≤ Real.sqrt (921180 / 37 : ℝ) ∧
      Real.sqrt (921180 / 37 : ℝ) ≤ 1577871 / 10000 ∧ Real.sqrt (46059 : ℝ) ≤ 2146137 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 79. -/
theorem gammaAnalyticHigh79_logs :
    Real.log (921180 / 37 : ℝ) ≤ 4049 / 400 ∧ Real.log (46059 : ℝ) ≤ 107377 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (921180 / 37) 15 20 0 (4049 / 400) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 46059 16 20 0 (107377 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh79_main (hRH : RiemannHypothesis) :
    (131373 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 46059,
        Real.exp (-(n : ℝ) / (921180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (921180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 27713) * ((921180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((921180 / 37) * (37 / 20)) + 1) / (800 / 27713) +
        1839 / 1000 ≤
      173972 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh79_roots.2.2]
  have hs :
    Real.sqrt ((921180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((921180 / 37) * (37 / 20)) +
        21 / 20 ≤
      3941 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh79_roots.2.2, gammaAnalyticHigh79_logs.2]
  have hz :
    Real.sqrt (921180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (921180 / 37) + 2469 / 800 ≤
      12469 / 500 := by
    linarith only [gammaAnalyticHigh79_roots.2.1, gammaAnalyticHigh79_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 921180 / 37) (y := 37 / 20) (h := 800 / 27713) (r :=
      1577871 / 10000) (e := 78619 / 500000) (p := 173972 / 125) (s := 3941 / 125) (z :=
      12469 / 500) (F := 131373 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh79_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (921180 / 37 : ℝ) * (37 / 20) = 46059 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh79_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (921180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (921180 / 37 : ℝ)) ≤
      78973 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 157787 / 1000) (T := 1577871 / 10000) (Z := 4049 / 400)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh79_roots.1
      gammaAnalyticHigh79_roots.2.1 gammaAnalyticHigh79_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh79_power : (921180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 337 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 79 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh79_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (39183 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1581 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (46059 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 39183 / 100)]
  apply
    reject_03_of_analytic_caps (B := 46059) (x := 921180 / 37) (H := 1581 / 4) (R := 157787 / 1000)
      (W := 337 / 100000) (F := 131373 / 1000) (U := 78973 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh79_power (gammaAnalyticHigh79_main hGRH.riemann)
      (gammaAnalyticHigh79_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 80. -/
theorem gammaAnalyticHigh80_roots :
    ((1591633 / 10000 : ℝ) ≤ Real.sqrt (937320 / 37 : ℝ) ∧
      Real.sqrt (937320 / 37 : ℝ) ≤ 795817 / 5000 ∧ Real.sqrt (46866 : ℝ) ≤ 270607 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 80. -/
theorem gammaAnalyticHigh80_logs :
    Real.log (937320 / 37 : ℝ) ≤ 101399 / 10000 ∧ Real.log (46866 : ℝ) ≤ 107551 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (937320 / 37) 15 20 0 (101399 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 46866 16 20 0 (107551 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh80_main (hRH : RiemannHypothesis) :
    (16566 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 46866,
        Real.exp (-(n : ℝ) / (937320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (937320 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 139167) * ((937320 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((937320 / 37) * (37 / 20)) + 1) / (4000 / 139167) +
        1839 / 1000 ≤
      1409973 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh80_roots.2.2]
  have hs :
    Real.sqrt ((937320 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((937320 / 37) * (37 / 20)) +
        21 / 20 ≤
      31653 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh80_roots.2.2, gammaAnalyticHigh80_logs.2]
  have hz :
    Real.sqrt (937320 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (937320 / 37) + 2469 / 800 ≤
      2503 / 100 := by
    linarith only [gammaAnalyticHigh80_roots.2.1, gammaAnalyticHigh80_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 937320 / 37) (y := 37 / 20) (h := 4000 / 139167) (r :=
      795817 / 5000) (e := 78619 / 500000) (p := 1409973 / 1000) (s := 31653 / 1000) (z :=
      2503 / 100) (F := 16566 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh80_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (937320 / 37 : ℝ) * (37 / 20) = 46866 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh80_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (937320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (937320 / 37 : ℝ)) ≤
      159321 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1591633 / 10000) (T := 795817 / 5000) (Z :=
      101399 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh80_roots.1
      gammaAnalyticHigh80_roots.2.1 gammaAnalyticHigh80_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh80_power : (937320 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 167 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 80 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh80_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1581 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (39869 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (46866 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1581 / 4)]
  apply
    reject_03_of_analytic_caps (B := 46866) (x := 937320 / 37) (H := 39869 / 100) (R :=
      1591633 / 10000) (W := 167 / 50000) (F := 16566 / 125) (U := 159321 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh80_power (gammaAnalyticHigh80_main hGRH.riemann)
      (gammaAnalyticHigh80_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 81. -/
theorem gammaAnalyticHigh81_roots :
    ((1605497 / 10000 : ℝ) ≤ Real.sqrt (953720 / 37 : ℝ) ∧
      Real.sqrt (953720 / 37 : ℝ) ≤ 802749 / 5000 ∧ Real.sqrt (47686 : ℝ) ≤ 2183713 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 81. -/
theorem gammaAnalyticHigh81_logs :
    Real.log (953720 / 37 : ℝ) ≤ 101573 / 10000 ∧ Real.log (47686 : ℝ) ≤ 26931 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (953720 / 37) 15 20 0 (101573 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 47686 16 20 0 (26931 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh81_main (hRH : RiemannHypothesis) :
    (33423 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 47686,
        Real.exp (-(n : ℝ) / (953720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (953720 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (125 / 4368) * ((953720 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((953720 / 37) * (37 / 20)) + 1) / (125 / 4368) +
        1839 / 1000 ≤
      1428383 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh81_roots.2.2]
  have hs :
    Real.sqrt ((953720 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((953720 / 37) * (37 / 20)) +
        21 / 20 ≤
      1589 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh81_roots.2.2, gammaAnalyticHigh81_logs.2]
  have hz :
    Real.sqrt (953720 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (953720 / 37) + 2469 / 800 ≤
      6281 / 250 := by
    linarith only [gammaAnalyticHigh81_roots.2.1, gammaAnalyticHigh81_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 953720 / 37) (y := 37 / 20) (h := 125 / 4368) (r :=
      802749 / 5000) (e := 78619 / 500000) (p := 1428383 / 1000) (s := 1589 / 50) (z := 6281 / 250)
      (F := 33423 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh81_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (953720 / 37 : ℝ) * (37 / 20) = 47686 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh81_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (953720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (953720 / 37 : ℝ)) ≤
      160707 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1605497 / 10000) (T := 802749 / 5000) (Z :=
      101573 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh81_roots.1
      gammaAnalyticHigh81_roots.2.1 gammaAnalyticHigh81_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh81_power : (953720 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 331 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 81 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh81_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (39869 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (40217 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (47686 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 39869 / 100)]
  apply
    reject_03_of_analytic_caps (B := 47686) (x := 953720 / 37) (H := 40217 / 100) (R :=
      1605497 / 10000) (W := 331 / 100000) (F := 33423 / 250) (U := 160707 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh81_power (gammaAnalyticHigh81_main hGRH.riemann)
      (gammaAnalyticHigh81_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 82. -/
theorem gammaAnalyticHigh82_roots :
    ((1619509 / 10000 : ℝ) ≤ Real.sqrt (970440 / 37 : ℝ) ∧
      Real.sqrt (970440 / 37 : ℝ) ≤ 161951 / 1000 ∧ Real.sqrt (48522 : ℝ) ≤ 2202771 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 82. -/
theorem gammaAnalyticHigh82_logs :
    Real.log (970440 / 37 : ℝ) ≤ 50873 / 5000 ∧ Real.log (48522 : ℝ) ≤ 53949 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (970440 / 37) 15 20 0 (50873 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 48522 16 20 0 (53949 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh82_main (hRH : RiemannHypothesis) :
    (33717 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 48522,
        Real.exp (-(n : ℝ) / (970440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (970440 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 28077) * ((970440 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((970440 / 37) * (37 / 20)) + 1) / (800 / 28077) +
        1839 / 1000 ≤
      1447071 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh82_roots.2.2]
  have hs :
    Real.sqrt ((970440 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((970440 / 37) * (37 / 20)) +
        21 / 20 ≤
      31907 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh82_roots.2.2, gammaAnalyticHigh82_logs.2]
  have hz :
    Real.sqrt (970440 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (970440 / 37) + 2469 / 800 ≤
      12609 / 500 := by
    linarith only [gammaAnalyticHigh82_roots.2.1, gammaAnalyticHigh82_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 970440 / 37) (y := 37 / 20) (h := 800 / 28077) (r :=
      161951 / 1000) (e := 78619 / 500000) (p := 1447071 / 1000) (s := 31907 / 1000) (z :=
      12609 / 500) (F := 33717 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh82_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (970440 / 37 : ℝ) * (37 / 20) = 48522 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh82_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (970440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (970440 / 37 : ℝ)) ≤
      162107 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1619509 / 10000) (T := 161951 / 1000) (Z := 50873 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh82_roots.1
      gammaAnalyticHigh82_roots.2.1 gammaAnalyticHigh82_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh82_power : (970440 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 327 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 82 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh82_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (40217 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (40567 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (48522 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 40217 / 100)]
  apply
    reject_03_of_analytic_caps (B := 48522) (x := 970440 / 37) (H := 40567 / 100) (R :=
      1619509 / 10000) (W := 327 / 100000) (F := 33717 / 250) (U := 162107 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh82_power (gammaAnalyticHigh82_main hGRH.riemann)
      (gammaAnalyticHigh82_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 83. -/
theorem gammaAnalyticHigh83_roots :
    ((1633599 / 10000 : ℝ) ≤ Real.sqrt (987400 / 37 : ℝ) ∧
      Real.sqrt (987400 / 37 : ℝ) ≤ 4084 / 25 ∧ Real.sqrt (49370 : ℝ) ≤ 2221937 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 83. -/
theorem gammaAnalyticHigh83_logs :
    Real.log (987400 / 37 : ℝ) ≤ 1274 / 125 ∧ Real.log (49370 : ℝ) ≤ 108071 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (987400 / 37) 15 20 0 (1274 / 125) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 49370 16 20 0 (108071 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh83_main (hRH : RiemannHypothesis) :
    (2721 / 20 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 49370,
        Real.exp (-(n : ℝ) / (987400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (987400 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 70497) * ((987400 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((987400 / 37) * (37 / 20)) + 1) / (2000 / 70497) +
        1839 / 1000 ≤
      293189 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh83_roots.2.2]
  have hs :
    Real.sqrt ((987400 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((987400 / 37) * (37 / 20)) +
        21 / 20 ≤
      16017 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh83_roots.2.2, gammaAnalyticHigh83_logs.2]
  have hz :
    Real.sqrt (987400 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (987400 / 37) + 2469 / 800 ≤
      3164 / 125 := by
    linarith only [gammaAnalyticHigh83_roots.2.1, gammaAnalyticHigh83_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 987400 / 37) (y := 37 / 20) (h := 2000 / 70497) (r :=
      4084 / 25) (e := 78619 / 500000) (p := 293189 / 200) (s := 16017 / 500) (z := 3164 / 125)
      (F := 2721 / 20) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh83_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (987400 / 37 : ℝ) * (37 / 20) = 49370 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh83_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (987400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (987400 / 37 : ℝ)) ≤
      32703 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1633599 / 10000) (T := 4084 / 25) (Z := 1274 / 125)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh83_roots.1
      gammaAnalyticHigh83_roots.2.1 gammaAnalyticHigh83_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh83_power : (987400 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 81 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 83 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh83_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (40567 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2046 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (49370 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 40567 / 100)]
  apply
    reject_03_of_analytic_caps (B := 49370) (x := 987400 / 37) (H := 2046 / 5) (R :=
      1633599 / 10000) (W := 81 / 25000) (F := 2721 / 20) (U := 32703 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh83_power (gammaAnalyticHigh83_main hGRH.riemann)
      (gammaAnalyticHigh83_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 84. -/
theorem gammaAnalyticHigh84_roots :
    ((329563 / 2000 : ℝ) ≤ Real.sqrt (1004660 / 37 : ℝ) ∧
      Real.sqrt (1004660 / 37 : ℝ) ≤ 205977 / 1250 ∧ Real.sqrt (50233 : ℝ) ≤ 280159 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 84. -/
theorem gammaAnalyticHigh84_logs :
    Real.log (1004660 / 37 : ℝ) ≤ 102093 / 10000 ∧ Real.log (50233 : ℝ) ≤ 21649 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1004660 / 37) 15 20 0 (102093 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 50233 16 20 0 (21649 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh84_main (hRH : RiemannHypothesis) :
    (137243 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 50233,
        Real.exp (-(n : ℝ) / (1004660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1004660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 141603) * ((1004660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1004660 / 37) * (37 / 20)) + 1) / (4000 / 141603) +
        1839 / 1000 ≤
      1485069 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh84_roots.2.2]
  have hs :
    Real.sqrt ((1004660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1004660 / 37) * (37 / 20)) +
        21 / 20 ≤
      32163 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh84_roots.2.2, gammaAnalyticHigh84_logs.2]
  have hz :
    Real.sqrt (1004660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1004660 / 37) + 2469 / 800 ≤
      25407 / 1000 := by
    linarith only [gammaAnalyticHigh84_roots.2.1, gammaAnalyticHigh84_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1004660 / 37) (y := 37 / 20) (h := 4000 / 141603) (r :=
      205977 / 1250) (e := 78619 / 500000) (p := 1485069 / 1000) (s := 32163 / 1000) (z :=
      25407 / 1000) (F := 137243 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh84_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1004660 / 37 : ℝ) * (37 / 20) = 50233 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh84_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1004660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1004660 / 37 : ℝ)) ≤
      20617 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 329563 / 2000) (T := 205977 / 1250) (Z := 102093 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh84_roots.1
      gammaAnalyticHigh84_roots.2.1 gammaAnalyticHigh84_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh84_power : (1004660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 321 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 84 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh84_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2046 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1651 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (50233 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2046 / 5)]
  apply
    reject_03_of_analytic_caps (B := 50233) (x := 1004660 / 37) (H := 1651 / 4) (R := 329563 / 2000)
      (W := 321 / 100000) (F := 137243 / 1000) (U := 20617 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh84_power (gammaAnalyticHigh84_main hGRH.riemann)
      (gammaAnalyticHigh84_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 85. -/
theorem gammaAnalyticHigh85_roots :
    ((332421 / 2000 : ℝ) ≤ Real.sqrt (1022160 / 37 : ℝ) ∧
      Real.sqrt (1022160 / 37 : ℝ) ≤ 831053 / 5000 ∧ Real.sqrt (51108 : ℝ) ≤ 565177 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 85. -/
theorem gammaAnalyticHigh85_logs :
    Real.log (1022160 / 37 : ℝ) ≤ 51133 / 5000 ∧ Real.log (51108 : ℝ) ≤ 108417 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1022160 / 37) 15 20 0 (51133 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 51108 16 20 0 (108417 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh85_main (hRH : RiemannHypothesis) :
    (69221 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 51108,
        Real.exp (-(n : ℝ) / (1022160 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1022160 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 142219) * ((1022160 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1022160 / 37) * (37 / 20)) + 1) / (4000 / 142219) +
        1839 / 1000 ≤
      188047 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh85_roots.2.2]
  have hs :
    Real.sqrt ((1022160 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1022160 / 37) * (37 / 20)) +
        21 / 20 ≤
      8073 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh85_roots.2.2, gammaAnalyticHigh85_logs.2]
  have hz :
    Real.sqrt (1022160 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1022160 / 37) + 2469 / 800 ≤
      12751 / 500 := by
    linarith only [gammaAnalyticHigh85_roots.2.1, gammaAnalyticHigh85_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1022160 / 37) (y := 37 / 20) (h := 4000 / 142219) (r :=
      831053 / 5000) (e := 78619 / 500000) (p := 188047 / 125) (s := 8073 / 250) (z := 12751 / 500)
      (F := 69221 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh85_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1022160 / 37 : ℝ) * (37 / 20) = 51108 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh85_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1022160 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1022160 / 37 : ℝ)) ≤
      33273 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 332421 / 2000) (T := 831053 / 5000) (Z := 51133 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh85_roots.1
      gammaAnalyticHigh85_roots.2.1 gammaAnalyticHigh85_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh85_power : (1022160 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 159 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 85 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh85_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1651 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (41633 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (51108 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1651 / 4)]
  apply
    reject_03_of_analytic_caps (B := 51108) (x := 1022160 / 37) (H := 41633 / 100) (R :=
      332421 / 2000) (W := 159 / 50000) (F := 69221 / 500) (U := 33273 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh85_power (gammaAnalyticHigh85_main hGRH.riemann)
      (gammaAnalyticHigh85_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 86. -/
theorem gammaAnalyticHigh86_roots :
    ((1676531 / 10000 : ℝ) ≤ Real.sqrt (1039980 / 37 : ℝ) ∧
      Real.sqrt (1039980 / 37 : ℝ) ≤ 419133 / 2500 ∧ Real.sqrt (51999 : ℝ) ≤ 2280329 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 86. -/
theorem gammaAnalyticHigh86_logs :
    Real.log (1039980 / 37 : ℝ) ≤ 51219 / 5000 ∧ Real.log (51999 : ℝ) ≤ 10859 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1039980 / 37) 15 20 0 (51219 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 51999 16 20 0 (10859 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh86_main (hRH : RiemannHypothesis) :
    (139653 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 51999,
        Real.exp (-(n : ℝ) / (1039980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1039980 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 28567) * ((1039980 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1039980 / 37) * (37 / 20)) + 1) / (800 / 28567) +
        1839 / 1000 ≤
      1523951 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh86_roots.2.2]
  have hs :
    Real.sqrt ((1039980 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1039980 / 37) * (37 / 20)) +
        21 / 20 ≤
      16211 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh86_roots.2.2, gammaAnalyticHigh86_logs.2]
  have hz :
    Real.sqrt (1039980 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1039980 / 37) + 2469 / 800 ≤
      12799 / 500 := by
    linarith only [gammaAnalyticHigh86_roots.2.1, gammaAnalyticHigh86_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1039980 / 37) (y := 37 / 20) (h := 800 / 28567) (r :=
      419133 / 2500) (e := 78619 / 500000) (p := 1523951 / 1000) (s := 16211 / 500) (z :=
      12799 / 500) (F := 139653 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh86_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1039980 / 37 : ℝ) * (37 / 20) = 51999 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh86_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1039980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1039980 / 37 : ℝ)) ≤
      83903 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1676531 / 10000) (T := 419133 / 2500) (Z := 51219 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh86_roots.1
      gammaAnalyticHigh86_roots.2.1 gammaAnalyticHigh86_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh86_power : (1039980 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 63 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 86 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh86_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (41633 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20997 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (51999 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 41633 / 100)]
  apply
    reject_03_of_analytic_caps (B := 51999) (x := 1039980 / 37) (H := 20997 / 50) (R :=
      1676531 / 10000) (W := 63 / 20000) (F := 139653 / 1000) (U := 83903 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh86_power (gammaAnalyticHigh86_main hGRH.riemann)
      (gammaAnalyticHigh86_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 87. -/
theorem gammaAnalyticHigh87_roots :
    ((1691057 / 10000 : ℝ) ≤ Real.sqrt (1058080 / 37 : ℝ) ∧
      Real.sqrt (1058080 / 37 : ℝ) ≤ 845529 / 5000 ∧ Real.sqrt (52904 : ℝ) ≤ 2300087 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 87. -/
theorem gammaAnalyticHigh87_logs :
    Real.log (1058080 / 37 : ℝ) ≤ 102611 / 10000 ∧ Real.log (52904 : ℝ) ≤ 108763 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1058080 / 37) 15 20 0 (102611 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 52904 16 20 0 (108763 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh87_main (hRH : RiemannHypothesis) :
    (17609 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 52904,
        Real.exp (-(n : ℝ) / (1058080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1058080 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 143451) * ((1058080 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1058080 / 37) * (37 / 20)) + 1) / (4000 / 143451) +
        1839 / 1000 ≤
      385937 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh87_roots.2.2]
  have hs :
    Real.sqrt ((1058080 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1058080 / 37) * (37 / 20)) +
        21 / 20 ≤
      4069 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh87_roots.2.2, gammaAnalyticHigh87_logs.2]
  have hz :
    Real.sqrt (1058080 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1058080 / 37) + 2469 / 800 ≤
      5139 / 200 := by
    linarith only [gammaAnalyticHigh87_roots.2.1, gammaAnalyticHigh87_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1058080 / 37) (y := 37 / 20) (h := 4000 / 143451) (r :=
      845529 / 5000) (e := 78619 / 500000) (p := 385937 / 250) (s := 4069 / 125) (z := 5139 / 200)
      (F := 17609 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh87_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1058080 / 37 : ℝ) * (37 / 20) = 52904 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh87_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1058080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1058080 / 37 : ℝ)) ≤
      84629 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1691057 / 10000) (T := 845529 / 5000) (Z :=
      102611 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh87_roots.1
      gammaAnalyticHigh87_roots.2.1 gammaAnalyticHigh87_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh87_power : (1058080 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 39 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 87 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh87_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20997 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21179 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (52904 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20997 / 50)]
  apply
    reject_03_of_analytic_caps (B := 52904) (x := 1058080 / 37) (H := 21179 / 50) (R :=
      1691057 / 10000) (W := 39 / 12500) (F := 17609 / 125) (U := 84629 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh87_power (gammaAnalyticHigh87_main hGRH.riemann)
      (gammaAnalyticHigh87_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 88. -/
theorem gammaAnalyticHigh88_roots :
    ((1705729 / 10000 : ℝ) ≤ Real.sqrt (1076520 / 37 : ℝ) ∧
      Real.sqrt (1076520 / 37 : ℝ) ≤ 170573 / 1000 ∧ Real.sqrt (53826 : ℝ) ≤ 580011 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 88. -/
theorem gammaAnalyticHigh88_logs :
    Real.log (1076520 / 37 : ℝ) ≤ 6424 / 625 ∧ Real.log (53826 : ℝ) ≤ 13617 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1076520 / 37) 15 20 0 (6424 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 53826 16 20 0 (13617 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh88_main (hRH : RiemannHypothesis) :
    (142103 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 53826,
        Real.exp (-(n : ℝ) / (1076520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1076520 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 72037) * ((1076520 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1076520 / 37) * (37 / 20)) + 1) / (2000 / 72037) +
        1839 / 1000 ≤
      1563829 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh88_roots.2.2]
  have hs :
    Real.sqrt ((1076520 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1076520 / 37) * (37 / 20)) +
        21 / 20 ≤
      8171 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh88_roots.2.2, gammaAnalyticHigh88_logs.2]
  have hz :
    Real.sqrt (1076520 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1076520 / 37) + 2469 / 800 ≤
      3224 / 125 := by
    linarith only [gammaAnalyticHigh88_roots.2.1, gammaAnalyticHigh88_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1076520 / 37) (y := 37 / 20) (h := 2000 / 72037) (r :=
      170573 / 1000) (e := 78619 / 500000) (p := 1563829 / 1000) (s := 8171 / 250) (z := 3224 / 125)
      (F := 142103 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh88_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1076520 / 37 : ℝ) * (37 / 20) = 53826 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh88_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1076520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1076520 / 37 : ℝ)) ≤
      6829 / 40 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1705729 / 10000) (T := 170573 / 1000) (Z := 6424 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh88_roots.1
      gammaAnalyticHigh88_roots.2.1 gammaAnalyticHigh88_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh88_power : (1076520 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 309 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 88 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh88_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21179 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1709 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (53826 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21179 / 50)]
  apply
    reject_03_of_analytic_caps (B := 53826) (x := 1076520 / 37) (H := 1709 / 4) (R :=
      1705729 / 10000) (W := 309 / 100000) (F := 142103 / 1000) (U := 6829 / 40) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh88_power (gammaAnalyticHigh88_main hGRH.riemann)
      (gammaAnalyticHigh88_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 89. -/
theorem gammaAnalyticHigh89_roots :
    ((107531 / 625 : ℝ) ≤ Real.sqrt (1095240 / 37 : ℝ) ∧
      Real.sqrt (1095240 / 37 : ℝ) ≤ 1720497 / 10000 ∧
      Real.sqrt (54762 : ℝ) ≤ 2340129 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 89. -/
theorem gammaAnalyticHigh89_logs :
    Real.log (1095240 / 37 : ℝ) ≤ 25739 / 2500 ∧ Real.log (54762 : ℝ) ≤ 27277 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1095240 / 37) 15 20 0 (25739 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 54762 16 20 0 (27277 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh89_main (hRH : RiemannHypothesis) :
    (143343 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 54762,
        Real.exp (-(n : ℝ) / (1095240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1095240 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 144697) * ((1095240 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1095240 / 37) * (37 / 20)) + 1) / (4000 / 144697) +
        1839 / 1000 ≤
      198016 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh89_roots.2.2]
  have hs :
    Real.sqrt ((1095240 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1095240 / 37) * (37 / 20)) +
        21 / 20 ≤
      4102 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh89_roots.2.2, gammaAnalyticHigh89_logs.2]
  have hz :
    Real.sqrt (1095240 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1095240 / 37) + 2469 / 800 ≤
      25889 / 1000 := by
    linarith only [gammaAnalyticHigh89_roots.2.1, gammaAnalyticHigh89_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1095240 / 37) (y := 37 / 20) (h := 4000 / 144697) (r :=
      1720497 / 10000) (e := 78619 / 500000) (p := 198016 / 125) (s := 4102 / 125) (z :=
      25889 / 1000) (F := 143343 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh89_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1095240 / 37 : ℝ) * (37 / 20) = 54762 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh89_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1095240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1095240 / 37 : ℝ)) ≤
      172201 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 107531 / 625) (T := 1720497 / 10000) (Z := 25739 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh89_roots.1
      gammaAnalyticHigh89_roots.2.1 gammaAnalyticHigh89_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh89_power : (1095240 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 153 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 89 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh89_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1709 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21547 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (54762 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1709 / 4)]
  apply
    reject_03_of_analytic_caps (B := 54762) (x := 1095240 / 37) (H := 21547 / 50) (R :=
      107531 / 625) (W := 153 / 50000) (F := 143343 / 1000) (U := 172201 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh89_power (gammaAnalyticHigh89_main hGRH.riemann)
      (gammaAnalyticHigh89_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 90. -/
theorem gammaAnalyticHigh90_roots :
    ((347071 / 2000 : ℝ) ≤ Real.sqrt (1114240 / 37 : ℝ) ∧
      Real.sqrt (1114240 / 37 : ℝ) ≤ 433839 / 2500 ∧ Real.sqrt (55712 : ℝ) ≤ 2360339 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 90. -/
theorem gammaAnalyticHigh90_logs :
    Real.log (1114240 / 37 : ℝ) ≤ 12891 / 1250 ∧ Real.log (55712 : ℝ) ≤ 1366 / 125 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1114240 / 37) 15 20 0 (12891 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 55712 16 20 0 (1366 / 125) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh90_main (hRH : RiemannHypothesis) :
    (14459 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 55712,
        Real.exp (-(n : ℝ) / (1114240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1114240 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (100 / 3633) * ((1114240 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1114240 / 37) * (37 / 20)) + 1) / (100 / 3633) +
        1839 / 1000 ≤
      1604641 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh90_roots.2.2]
  have hs :
    Real.sqrt ((1114240 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1114240 / 37) * (37 / 20)) +
        21 / 20 ≤
      32949 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh90_roots.2.2, gammaAnalyticHigh90_logs.2]
  have hz :
    Real.sqrt (1114240 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1114240 / 37) + 2469 / 800 ≤
      25987 / 1000 := by
    linarith only [gammaAnalyticHigh90_roots.2.1, gammaAnalyticHigh90_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1114240 / 37) (y := 37 / 20) (h := 100 / 3633) (r :=
      433839 / 2500) (e := 78619 / 500000) (p := 1604641 / 1000) (s := 32949 / 1000) (z :=
      25987 / 1000) (F := 14459 / 100) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh90_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1114240 / 37 : ℝ) * (37 / 20) = 55712 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh90_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1114240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1114240 / 37 : ℝ)) ≤
      86843 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 347071 / 2000) (T := 433839 / 2500) (Z := 12891 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh90_roots.1
      gammaAnalyticHigh90_roots.2.1 gammaAnalyticHigh90_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh90_power : (1114240 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 303 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 90 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh90_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21547 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21733 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (55712 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21547 / 50)]
  apply
    reject_03_of_analytic_caps (B := 55712) (x := 1114240 / 37) (H := 21733 / 50) (R :=
      347071 / 2000) (W := 303 / 100000) (F := 14459 / 100) (U := 86843 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh90_power (gammaAnalyticHigh90_main hGRH.riemann)
      (gammaAnalyticHigh90_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 91. -/
theorem gammaAnalyticHigh91_roots :
    ((350067 / 2000 : ℝ) ≤ Real.sqrt (1133560 / 37 : ℝ) ∧
      Real.sqrt (1133560 / 37 : ℝ) ≤ 109396 / 625 ∧ Real.sqrt (56678 : ℝ) ≤ 476143 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 91. -/
theorem gammaAnalyticHigh91_logs :
    Real.log (1133560 / 37 : ℝ) ≤ 1033 / 100 ∧ Real.log (56678 : ℝ) ≤ 27363 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1133560 / 37) 15 20 0 (1033 / 100) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 56678 16 20 0 (27363 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh91_main (hRH : RiemannHypothesis) :
    (145847 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 56678,
        Real.exp (-(n : ℝ) / (1133560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1133560 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 145943) * ((1133560 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1133560 / 37) * (37 / 20)) + 1) / (4000 / 145943) +
        1839 / 1000 ≤
      1625411 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh91_roots.2.2]
  have hs :
    Real.sqrt ((1133560 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1133560 / 37) * (37 / 20)) +
        21 / 20 ≤
      16541 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh91_roots.2.2, gammaAnalyticHigh91_logs.2]
  have hz :
    Real.sqrt (1133560 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1133560 / 37) + 2469 / 800 ≤
      13043 / 500 := by
    linarith only [gammaAnalyticHigh91_roots.2.1, gammaAnalyticHigh91_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1133560 / 37) (y := 37 / 20) (h := 4000 / 145943) (r :=
      109396 / 625) (e := 78619 / 500000) (p := 1625411 / 1000) (s := 16541 / 500) (z :=
      13043 / 500) (F := 145847 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh91_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1133560 / 37 : ℝ) * (37 / 20) = 56678 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh91_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1133560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1133560 / 37 : ℝ)) ≤
      175183 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 350067 / 2000) (T := 109396 / 625) (Z := 1033 / 100)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh91_roots.1
      gammaAnalyticHigh91_roots.2.1 gammaAnalyticHigh91_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh91_power : (1133560 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 3 / 1000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 91 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh91_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21733 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (43841 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (56678 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21733 / 50)]
  apply
    reject_03_of_analytic_caps (B := 56678) (x := 1133560 / 37) (H := 43841 / 100) (R :=
      350067 / 2000) (W := 3 / 1000) (F := 145847 / 1000) (U := 175183 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh91_power (gammaAnalyticHigh91_main hGRH.riemann)
      (gammaAnalyticHigh91_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 92. -/
theorem gammaAnalyticHigh92_roots :
    ((1765433 / 10000 : ℝ) ≤ Real.sqrt (1153200 / 37 : ℝ) ∧
      Real.sqrt (1153200 / 37 : ℝ) ≤ 882717 / 5000 ∧ Real.sqrt (57660 : ℝ) ≤ 1921 / 8) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 92. -/
theorem gammaAnalyticHigh92_logs :
    Real.log (1153200 / 37 : ℝ) ≤ 6467 / 625 ∧ Real.log (57660 : ℝ) ≤ 13703 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1153200 / 37) 15 20 0 (6467 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 57660 16 20 0 (13703 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh92_main (hRH : RiemannHypothesis) :
    (73557 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 57660,
        Real.exp (-(n : ℝ) / (1153200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1153200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 146573) * ((1153200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1153200 / 37) * (37 / 20)) + 1) / (4000 / 146573) +
        1839 / 1000 ≤
      823217 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh92_roots.2.2]
  have hs :
    Real.sqrt ((1153200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1153200 / 37) * (37 / 20)) +
        21 / 20 ≤
      33217 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh92_roots.2.2, gammaAnalyticHigh92_logs.2]
  have hz :
    Real.sqrt (1153200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1153200 / 37) + 2469 / 800 ≤
      5237 / 200 := by
    linarith only [gammaAnalyticHigh92_roots.2.1, gammaAnalyticHigh92_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1153200 / 37) (y := 37 / 20) (h := 4000 / 146573) (r :=
      882717 / 5000) (e := 78619 / 500000) (p := 823217 / 500) (s := 33217 / 1000) (z := 5237 / 200)
      (F := 73557 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh92_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1153200 / 37 : ℝ) * (37 / 20) = 57660 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh92_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1153200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1153200 / 37 : ℝ)) ≤
      44173 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1765433 / 10000) (T := 882717 / 5000) (Z := 6467 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh92_roots.1
      gammaAnalyticHigh92_roots.2.1 gammaAnalyticHigh92_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh92_power : (1153200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 297 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 92 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh92_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (43841 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (44219 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (57660 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 43841 / 100)]
  apply
    reject_03_of_analytic_caps (B := 57660) (x := 1153200 / 37) (H := 44219 / 100) (R :=
      1765433 / 10000) (W := 297 / 100000) (F := 73557 / 500) (U := 44173 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh92_power (gammaAnalyticHigh92_main hGRH.riemann)
      (gammaAnalyticHigh92_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 93. -/
theorem gammaAnalyticHigh93_roots :
    ((1780661 / 10000 : ℝ) ≤ Real.sqrt (1173180 / 37 : ℝ) ∧
      Real.sqrt (1173180 / 37 : ℝ) ≤ 890331 / 5000 ∧ Real.sqrt (58659 : ℝ) ≤ 2421963 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 93. -/
theorem gammaAnalyticHigh93_logs :
    Real.log (1173180 / 37 : ℝ) ≤ 25911 / 2500 ∧ Real.log (58659 : ℝ) ≤ 21959 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1173180 / 37) 15 20 0 (25911 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 58659 16 20 0 (21959 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh93_main (hRH : RiemannHypothesis) :
    (18549 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 58659,
        Real.exp (-(n : ℝ) / (1173180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1173180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 147203) * ((1173180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1173180 / 37) * (37 / 20)) + 1) / (4000 / 147203) +
        1839 / 1000 ≤
      1667729 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh93_roots.2.2]
  have hs :
    Real.sqrt ((1173180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1173180 / 37) * (37 / 20)) +
        21 / 20 ≤
      4169 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh93_roots.2.2, gammaAnalyticHigh93_logs.2]
  have hz :
    Real.sqrt (1173180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1173180 / 37) + 2469 / 800 ≤
      5257 / 200 := by
    linarith only [gammaAnalyticHigh93_roots.2.1, gammaAnalyticHigh93_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1173180 / 37) (y := 37 / 20) (h := 4000 / 147203) (r :=
      890331 / 5000) (e := 78619 / 500000) (p := 1667729 / 1000) (s := 4169 / 125) (z := 5257 / 200)
      (F := 18549 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh93_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1173180 / 37 : ℝ) * (37 / 20) = 58659 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh93_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1173180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1173180 / 37 : ℝ)) ≤
      89107 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1780661 / 10000) (T := 890331 / 5000) (Z := 25911 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh93_roots.1
      gammaAnalyticHigh93_roots.2.1 gammaAnalyticHigh93_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh93_power : (1173180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 147 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 93 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh93_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (44219 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (446 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (58659 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 44219 / 100)]
  apply
    reject_03_of_analytic_caps (B := 58659) (x := 1173180 / 37) (H := 446) (R := 1780661 / 10000)
      (W := 147 / 50000) (F := 18549 / 125) (U := 89107 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh93_power (gammaAnalyticHigh93_main hGRH.riemann)
      (gammaAnalyticHigh93_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 94. -/
theorem gammaAnalyticHigh94_roots :
    ((1796001 / 10000 : ℝ) ≤ Real.sqrt (1193480 / 37 : ℝ) ∧
      Real.sqrt (1193480 / 37 : ℝ) ≤ 898001 / 5000 ∧ Real.sqrt (59674 : ℝ) ≤ 2442827 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 94. -/
theorem gammaAnalyticHigh94_logs :
    Real.log (1193480 / 37 : ℝ) ≤ 20763 / 2000 ∧ Real.log (59674 : ℝ) ≤ 109967 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1193480 / 37) 15 20 0 (20763 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 59674 16 20 0 (109967 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh94_main (hRH : RiemannHypothesis) :
    (3742 / 25 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 59674,
        Real.exp (-(n : ℝ) / (1193480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1193480 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 147833) * ((1193480 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1193480 / 37) * (37 / 20)) + 1) / (4000 / 147833) +
        1839 / 1000 ≤
      211159 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh94_roots.2.2]
  have hs :
    Real.sqrt ((1193480 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1193480 / 37) * (37 / 20)) +
        21 / 20 ≤
      4186 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh94_roots.2.2, gammaAnalyticHigh94_logs.2]
  have hz :
    Real.sqrt (1193480 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1193480 / 37) + 2469 / 800 ≤
      5277 / 200 := by
    linarith only [gammaAnalyticHigh94_roots.2.1, gammaAnalyticHigh94_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1193480 / 37) (y := 37 / 20) (h := 4000 / 147833) (r :=
      898001 / 5000) (e := 78619 / 500000) (p := 211159 / 125) (s := 4186 / 125) (z := 5277 / 200)
      (F := 3742 / 25) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh94_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1193480 / 37 : ℝ) * (37 / 20) = 59674 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh94_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1193480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1193480 / 37 : ℝ)) ≤
      44937 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1796001 / 10000) (T := 898001 / 5000) (Z := 20763 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh94_roots.1
      gammaAnalyticHigh94_roots.2.1 gammaAnalyticHigh94_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh94_power : (1193480 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 73 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 94 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh94_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (446 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11246 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (59674 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 446)]
  apply
    reject_03_of_analytic_caps (B := 59674) (x := 1193480 / 37) (H := 11246 / 25) (R :=
      1796001 / 10000) (W := 73 / 25000) (F := 3742 / 25) (U := 44937 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh94_power (gammaAnalyticHigh94_main hGRH.riemann)
      (gammaAnalyticHigh94_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 95. -/
theorem gammaAnalyticHigh95_roots :
    ((226433 / 1250 : ℝ) ≤ Real.sqrt (1214120 / 37 : ℝ) ∧
      Real.sqrt (1214120 / 37 : ℝ) ≤ 362293 / 2000 ∧ Real.sqrt (60706 : ℝ) ≤ 2463859 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 95. -/
theorem gammaAnalyticHigh95_logs :
    Real.log (1214120 / 37 : ℝ) ≤ 103987 / 10000 ∧ Real.log (60706 : ℝ) ≤ 55069 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1214120 / 37) 16 20 0 (103987 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 60706 16 20 0 (55069 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh95_main (hRH : RiemannHypothesis) :
    (150977 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 60706,
        Real.exp (-(n : ℝ) / (1214120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1214120 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (400 / 14847) * ((1214120 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1214120 / 37) * (37 / 20)) + 1) / (400 / 14847) +
        1839 / 1000 ≤
      855541 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh95_roots.2.2]
  have hs :
    Real.sqrt ((1214120 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1214120 / 37) * (37 / 20)) +
        21 / 20 ≤
      4203 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh95_roots.2.2, gammaAnalyticHigh95_logs.2]
  have hz :
    Real.sqrt (1214120 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1214120 / 37) + 2469 / 800 ≤
      13243 / 500 := by
    linarith only [gammaAnalyticHigh95_roots.2.1, gammaAnalyticHigh95_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1214120 / 37) (y := 37 / 20) (h := 400 / 14847) (r :=
      362293 / 2000) (e := 78619 / 500000) (p := 855541 / 500) (s := 4203 / 125) (z := 13243 / 500)
      (F := 150977 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh95_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1214120 / 37 : ℝ) * (37 / 20) = 60706 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh95_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1214120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1214120 / 37 : ℝ)) ≤
      181293 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 226433 / 1250) (T := 362293 / 2000) (Z := 103987 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh95_roots.1
      gammaAnalyticHigh95_roots.2.1 gammaAnalyticHigh95_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh95_power : (1214120 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 289 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 95 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh95_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11246 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (45371 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (60706 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11246 / 25)]
  apply
    reject_03_of_analytic_caps (B := 60706) (x := 1214120 / 37) (H := 45371 / 100) (R :=
      226433 / 1250) (W := 289 / 100000) (F := 150977 / 1000) (U := 181293 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh95_power (gammaAnalyticHigh95_main hGRH.riemann)
      (gammaAnalyticHigh95_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 96. -/
theorem gammaAnalyticHigh96_roots :
    ((1827049 / 10000 : ℝ) ≤ Real.sqrt (1235100 / 37 : ℝ) ∧
      Real.sqrt (1235100 / 37 : ℝ) ≤ 36541 / 200 ∧ Real.sqrt (61755 : ℝ) ≤ 155316 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 96. -/
theorem gammaAnalyticHigh96_logs :
    Real.log (1235100 / 37 : ℝ) ≤ 52079 / 5000 ∧ Real.log (61755 : ℝ) ≤ 11031 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1235100 / 37) 16 20 0 (52079 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 61755 16 20 0 (11031 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh96_main (hRH : RiemannHypothesis) :
    (30457 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 61755,
        Real.exp (-(n : ℝ) / (1235100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1235100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 149107) * ((1235100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1235100 / 37) * (37 / 20)) + 1) / (4000 / 149107) +
        1839 / 1000 ≤
      1733157 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh96_roots.2.2]
  have hs :
    Real.sqrt ((1235100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1235100 / 37) * (37 / 20)) +
        21 / 20 ≤
      16881 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh96_roots.2.2, gammaAnalyticHigh96_logs.2]
  have hz :
    Real.sqrt (1235100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1235100 / 37) + 2469 / 800 ≤
      6647 / 250 := by
    linarith only [gammaAnalyticHigh96_roots.2.1, gammaAnalyticHigh96_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1235100 / 37) (y := 37 / 20) (h := 4000 / 149107) (r :=
      36541 / 200) (e := 78619 / 500000) (p := 1733157 / 1000) (s := 16881 / 500) (z := 6647 / 250)
      (F := 30457 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh96_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1235100 / 37 : ℝ) * (37 / 20) = 61755 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh96_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1235100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1235100 / 37 : ℝ)) ≤
      182851 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1827049 / 10000) (T := 36541 / 200) (Z := 52079 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh96_roots.1
      gammaAnalyticHigh96_roots.2.1 gammaAnalyticHigh96_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh96_power : (1235100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 143 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 96 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh96_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (45371 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (45761 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (61755 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 45371 / 100)]
  apply
    reject_03_of_analytic_caps (B := 61755) (x := 1235100 / 37) (H := 45761 / 100) (R :=
      1827049 / 10000) (W := 143 / 50000) (F := 30457 / 200) (U := 182851 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh96_power (gammaAnalyticHigh96_main hGRH.riemann)
      (gammaAnalyticHigh96_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 97. -/
theorem gammaAnalyticHigh97_roots :
    ((368553 / 2000 : ℝ) ≤ Real.sqrt (1256440 / 37 : ℝ) ∧
      Real.sqrt (1256440 / 37 : ℝ) ≤ 921383 / 5000 ∧ Real.sqrt (62822 : ℝ) ≤ 156652 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 97. -/
theorem gammaAnalyticHigh97_logs :
    Real.log (1256440 / 37 : ℝ) ≤ 104329 / 10000 ∧ Real.log (62822 : ℝ) ≤ 110481 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1256440 / 37) 16 20 0 (104329 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 62822 16 20 0 (110481 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh97_main (hRH : RiemannHypothesis) :
    (38401 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 62822,
        Real.exp (-(n : ℝ) / (1256440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1256440 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (250 / 9359) * ((1256440 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1256440 / 37) * (37 / 20)) + 1) / (250 / 9359) +
        1839 / 1000 ≤
      351103 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh97_roots.2.2]
  have hs :
    Real.sqrt ((1256440 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1256440 / 37) * (37 / 20)) +
        21 / 20 ≤
      339 / 10 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh97_roots.2.2, gammaAnalyticHigh97_logs.2]
  have hz :
    Real.sqrt (1256440 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1256440 / 37) + 2469 / 800 ≤
      2669 / 100 := by
    linarith only [gammaAnalyticHigh97_roots.2.1, gammaAnalyticHigh97_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1256440 / 37) (y := 37 / 20) (h := 250 / 9359) (r :=
      921383 / 5000) (e := 78619 / 500000) (p := 351103 / 200) (s := 339 / 10) (z := 2669 / 100)
      (F := 38401 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh97_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1256440 / 37 : ℝ) * (37 / 20) = 62822 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh97_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1256440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1256440 / 37 : ℝ)) ≤
      92211 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 368553 / 2000) (T := 921383 / 5000) (Z := 104329 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh97_roots.1
      gammaAnalyticHigh97_roots.2.1 gammaAnalyticHigh97_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh97_power : (1256440 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 283 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 97 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh97_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (45761 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23077 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (62822 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 45761 / 100)]
  apply
    reject_03_of_analytic_caps (B := 62822) (x := 1256440 / 37) (H := 23077 / 50) (R :=
      368553 / 2000) (W := 283 / 100000) (F := 38401 / 250) (U := 92211 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh97_power (gammaAnalyticHigh97_main hGRH.riemann)
      (gammaAnalyticHigh97_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 98. -/
theorem gammaAnalyticHigh98_roots :
    ((1858581 / 10000 : ℝ) ≤ Real.sqrt (1278100 / 37 : ℝ) ∧
      Real.sqrt (1278100 / 37 : ℝ) ≤ 929291 / 5000 ∧ Real.sqrt (63905 : ℝ) ≤ 315993 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 98. -/
theorem gammaAnalyticHigh98_logs :
    Real.log (1278100 / 37 : ℝ) ≤ 209 / 20 ∧ Real.log (63905 : ℝ) ≤ 27663 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1278100 / 37) 16 20 0 (209 / 20) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 63905 16 20 0 (27663 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh98_main (hRH : RiemannHypothesis) :
    (38733 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 63905,
        Real.exp (-(n : ℝ) / (1278100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1278100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 37597) * ((1278100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1278100 / 37) * (37 / 20)) + 1) / (1000 / 37597) +
        1839 / 1000 ≤
      177811 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh98_roots.2.2]
  have hs :
    Real.sqrt ((1278100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1278100 / 37) * (37 / 20)) +
        21 / 20 ≤
      34039 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh98_roots.2.2, gammaAnalyticHigh98_logs.2]
  have hz :
    Real.sqrt (1278100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1278100 / 37) + 2469 / 800 ≤
      26793 / 1000 := by
    linarith only [gammaAnalyticHigh98_roots.2.1, gammaAnalyticHigh98_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1278100 / 37) (y := 37 / 20) (h := 1000 / 37597) (r :=
      929291 / 5000) (e := 78619 / 500000) (p := 177811 / 100) (s := 34039 / 1000) (z :=
      26793 / 1000) (F := 38733 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh98_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1278100 / 37 : ℝ) * (37 / 20) = 63905 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh98_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1278100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1278100 / 37 : ℝ)) ≤
      186003 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1858581 / 10000) (T := 929291 / 5000) (Z := 209 / 20)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh98_roots.1
      gammaAnalyticHigh98_roots.2.1 gammaAnalyticHigh98_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh98_power : (1278100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 281 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 98 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh98_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23077 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (931 / 2 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (63905 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23077 / 50)]
  apply
    reject_03_of_analytic_caps (B := 63905) (x := 1278100 / 37) (H := 931 / 2) (R :=
      1858581 / 10000) (W := 281 / 100000) (F := 38733 / 250) (U := 186003 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh98_power (gammaAnalyticHigh98_main hGRH.riemann)
      (gammaAnalyticHigh98_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 99. -/
theorem gammaAnalyticHigh99_roots :
    ((1874537 / 10000 : ℝ) ≤ Real.sqrt (1300140 / 37 : ℝ) ∧
      Real.sqrt (1300140 / 37 : ℝ) ≤ 937269 / 5000 ∧ Real.sqrt (65007 : ℝ) ≤ 159353 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 99. -/
theorem gammaAnalyticHigh99_logs :
    Real.log (1300140 / 37 : ℝ) ≤ 104671 / 10000 ∧ Real.log (65007 : ℝ) ≤ 110823 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1300140 / 37) 16 20 0 (104671 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 65007 16 20 0 (110823 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh99_main (hRH : RiemannHypothesis) :
    (156271 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 65007,
        Real.exp (-(n : ℝ) / (1300140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1300140 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 18879) * ((1300140 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1300140 / 37) * (37 / 20)) + 1) / (500 / 18879) +
        1839 / 1000 ≤
      450251 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh99_roots.2.2]
  have hs :
    Real.sqrt ((1300140 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1300140 / 37) * (37 / 20)) +
        21 / 20 ≤
      34179 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh99_roots.2.2, gammaAnalyticHigh99_logs.2]
  have hz :
    Real.sqrt (1300140 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1300140 / 37) + 2469 / 800 ≤
      3362 / 125 := by
    linarith only [gammaAnalyticHigh99_roots.2.1, gammaAnalyticHigh99_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1300140 / 37) (y := 37 / 20) (h := 500 / 18879) (r :=
      937269 / 5000) (e := 78619 / 500000) (p := 450251 / 250) (s := 34179 / 1000) (z := 3362 / 125)
      (F := 156271 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh99_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1300140 / 37 : ℝ) * (37 / 20) = 65007 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh99_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1300140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1300140 / 37 : ℝ)) ≤
      93799 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1874537 / 10000) (T := 937269 / 5000) (Z :=
      104671 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh99_roots.1
      gammaAnalyticHigh99_roots.2.1 gammaAnalyticHigh99_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh99_power : (1300140 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 139 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 99 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh99_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (931 / 2 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (46949 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (65007 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 931 / 2)]
  apply
    reject_03_of_analytic_caps (B := 65007) (x := 1300140 / 37) (H := 46949 / 100) (R :=
      1874537 / 10000) (W := 139 / 50000) (F := 156271 / 1000) (U := 93799 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh99_power (gammaAnalyticHigh99_main hGRH.riemann)
      (gammaAnalyticHigh99_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 100. -/
theorem gammaAnalyticHigh100_roots :
    ((945301 / 5000 : ℝ) ≤ Real.sqrt (1322520 / 37 : ℝ) ∧
      Real.sqrt (1322520 / 37 : ℝ) ≤ 1890603 / 10000 ∧ Real.sqrt (66126 : ℝ) ≤ 1285749 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 100. -/
theorem gammaAnalyticHigh100_logs :
    Real.log (1322520 / 37 : ℝ) ≤ 52421 / 5000 ∧ Real.log (66126 : ℝ) ≤ 55497 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1322520 / 37) 16 20 0 (52421 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 66126 17 20 0 (55497 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh100_main (hRH : RiemannHypothesis) :
    (7881 / 50 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 66126,
        Real.exp (-(n : ℝ) / (1322520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1322520 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 37919) * ((1322520 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1322520 / 37) * (37 / 20)) + 1) / (1000 / 37919) +
        1839 / 1000 ≤
      228019 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh100_roots.2.2]
  have hs :
    Real.sqrt ((1322520 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1322520 / 37) * (37 / 20)) +
        21 / 20 ≤
      858 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh100_roots.2.2, gammaAnalyticHigh100_logs.2]
  have hz :
    Real.sqrt (1322520 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1322520 / 37) + 2469 / 800 ≤
      27 := by
    linarith only [gammaAnalyticHigh100_roots.2.1, gammaAnalyticHigh100_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1322520 / 37) (y := 37 / 20) (h := 1000 / 37919) (r :=
      1890603 / 10000) (e := 78619 / 500000) (p := 228019 / 125) (s := 858 / 25) (z := 27) (F :=
      7881 / 50) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh100_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1322520 / 37 : ℝ) * (37 / 20) = 66126 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh100_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1322520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1322520 / 37 : ℝ)) ≤
      47301 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 945301 / 5000) (T := 1890603 / 10000) (Z := 52421 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh100_roots.1
      gammaAnalyticHigh100_roots.2.1 gammaAnalyticHigh100_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh100_power : (1322520 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 11 / 4000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 100 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh100_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (46949 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (47351 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (66126 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 46949 / 100)]
  apply
    reject_03_of_analytic_caps (B := 66126) (x := 1322520 / 37) (H := 47351 / 100) (R :=
      945301 / 5000) (W := 11 / 4000) (F := 7881 / 50) (U := 47301 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh100_power (gammaAnalyticHigh100_main hGRH.riemann)
      (gammaAnalyticHigh100_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 101. -/
theorem gammaAnalyticHigh101_roots :
    ((1906787 / 10000 : ℝ) ≤ Real.sqrt (1345260 / 37 : ℝ) ∧
      Real.sqrt (1345260 / 37 : ℝ) ≤ 476697 / 2500 ∧ Real.sqrt (67263 : ℝ) ≤ 324189 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 101. -/
theorem gammaAnalyticHigh101_logs :
    Real.log (1345260 / 37 : ℝ) ≤ 26253 / 2500 ∧ Real.log (67263 : ℝ) ≤ 27791 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1345260 / 37) 16 20 0 (26253 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 67263 17 20 0 (27791 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh101_main (hRH : RiemannHypothesis) :
    (79489 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 67263,
        Real.exp (-(n : ℝ) / (1345260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1345260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 152327) * ((1345260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1345260 / 37) * (37 / 20)) + 1) / (4000 / 152327) +
        1839 / 1000 ≤
      461893 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh101_roots.2.2]
  have hs :
    Real.sqrt ((1345260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1345260 / 37) * (37 / 20)) +
        21 / 20 ≤
      34461 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh101_roots.2.2, gammaAnalyticHigh101_logs.2]
  have hz :
    Real.sqrt (1345260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1345260 / 37) + 2469 / 800 ≤
      3388 / 125 := by
    linarith only [gammaAnalyticHigh101_roots.2.1, gammaAnalyticHigh101_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1345260 / 37) (y := 37 / 20) (h := 4000 / 152327) (r :=
      476697 / 2500) (e := 78619 / 500000) (p := 461893 / 250) (s := 34461 / 1000) (z := 3388 / 125)
      (F := 79489 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh101_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1345260 / 37 : ℝ) * (37 / 20) = 67263 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh101_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1345260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1345260 / 37 : ℝ)) ≤
      190821 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1906787 / 10000) (T := 476697 / 2500) (Z := 26253 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh101_roots.1
      gammaAnalyticHigh101_roots.2.1 gammaAnalyticHigh101_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh101_power : (1345260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 273 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 101 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh101_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (47351 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11939 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (67263 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 47351 / 100)]
  apply
    reject_03_of_analytic_caps (B := 67263) (x := 1345260 / 37) (H := 11939 / 25) (R :=
      1906787 / 10000) (W := 273 / 100000) (F := 79489 / 500) (U := 190821 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh101_power (gammaAnalyticHigh101_main hGRH.riemann)
      (gammaAnalyticHigh101_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 102. -/
theorem gammaAnalyticHigh102_roots :
    ((961551 / 5000 : ℝ) ≤ Real.sqrt (1368380 / 37 : ℝ) ∧
      Real.sqrt (1368380 / 37 : ℝ) ≤ 1923103 / 10000 ∧
      Real.sqrt (68419 : ℝ) ≤ 2615703 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 102. -/
theorem gammaAnalyticHigh102_logs :
    Real.log (1368380 / 37 : ℝ) ≤ 105183 / 10000 ∧ Real.log (68419 : ℝ) ≤ 22267 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1368380 / 37) 16 20 0 (105183 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 68419 17 20 0 (22267 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh102_main (hRH : RiemannHypothesis) :
    (160347 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 68419,
        Real.exp (-(n : ℝ) / (1368380 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1368380 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 76489) * ((1368380 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1368380 / 37) * (37 / 20)) + 1) / (2000 / 76489) +
        1839 / 1000 ≤
      935641 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh102_roots.2.2]
  have hs :
    Real.sqrt ((1368380 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1368380 / 37) * (37 / 20)) +
        21 / 20 ≤
      8651 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh102_roots.2.2, gammaAnalyticHigh102_logs.2]
  have hz :
    Real.sqrt (1368380 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1368380 / 37) + 2469 / 800 ≤
      2721 / 100 := by
    linarith only [gammaAnalyticHigh102_roots.2.1, gammaAnalyticHigh102_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1368380 / 37) (y := 37 / 20) (h := 2000 / 76489) (r :=
      1923103 / 10000) (e := 78619 / 500000) (p := 935641 / 500) (s := 8651 / 250) (z := 2721 / 100)
      (F := 160347 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh102_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1368380 / 37 : ℝ) * (37 / 20) = 68419 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh102_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1368380 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1368380 / 37 : ℝ)) ≤
      48113 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 961551 / 5000) (T := 1923103 / 10000) (Z :=
      105183 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh102_roots.1
      gammaAnalyticHigh102_roots.2.1 gammaAnalyticHigh102_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh102_power : (1368380 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 27 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 102 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh102_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11939 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12041 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (68419 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11939 / 25)]
  apply
    reject_03_of_analytic_caps (B := 68419) (x := 1368380 / 37) (H := 12041 / 25) (R :=
      961551 / 5000) (W := 27 / 10000) (F := 160347 / 1000) (U := 48113 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh102_power (gammaAnalyticHigh102_main hGRH.riemann)
      (gammaAnalyticHigh102_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 103. -/
theorem gammaAnalyticHigh103_roots :
    ((1939531 / 10000 : ℝ) ≤ Real.sqrt (1391860 / 37 : ℝ) ∧
      Real.sqrt (1391860 / 37 : ℝ) ≤ 484883 / 2500 ∧ Real.sqrt (69593 : ℝ) ≤ 2638049 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 103. -/
theorem gammaAnalyticHigh103_logs :
    Real.log (1391860 / 37 : ℝ) ≤ 105353 / 10000 ∧ Real.log (69593 : ℝ) ≤ 22301 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1391860 / 37) 16 20 0 (105353 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 69593 17 20 0 (22301 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh103_main (hRH : RiemannHypothesis) :
    (80863 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 69593,
        Real.exp (-(n : ℝ) / (1391860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1391860 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 153629) * ((1391860 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1391860 / 37) * (37 / 20)) + 1) / (4000 / 153629) +
        1839 / 1000 ≤
      947629 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh103_roots.2.2]
  have hs :
    Real.sqrt ((1391860 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1391860 / 37) * (37 / 20)) +
        21 / 20 ≤
      34747 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh103_roots.2.2, gammaAnalyticHigh103_logs.2]
  have hz :
    Real.sqrt (1391860 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1391860 / 37) + 2469 / 800 ≤
      5463 / 200 := by
    linarith only [gammaAnalyticHigh103_roots.2.1, gammaAnalyticHigh103_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1391860 / 37) (y := 37 / 20) (h := 4000 / 153629) (r :=
      484883 / 2500) (e := 78619 / 500000) (p := 947629 / 500) (s := 34747 / 1000) (z := 5463 / 200)
      (F := 80863 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh103_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1391860 / 37 : ℝ) * (37 / 20) = 69593 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh103_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1391860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1391860 / 37 : ℝ)) ≤
      38819 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1939531 / 10000) (T := 484883 / 2500) (Z :=
      105353 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh103_roots.1
      gammaAnalyticHigh103_roots.2.1 gammaAnalyticHigh103_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh103_power : (1391860 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 267 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 103 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh103_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12041 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1943 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (69593 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12041 / 25)]
  apply
    reject_03_of_analytic_caps (B := 69593) (x := 1391860 / 37) (H := 1943 / 4) (R :=
      1939531 / 10000) (W := 267 / 100000) (F := 80863 / 500) (U := 38819 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh103_power (gammaAnalyticHigh103_main hGRH.riemann)
      (gammaAnalyticHigh103_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 104. -/
theorem gammaAnalyticHigh104_roots :
    ((1956071 / 10000 : ℝ) ≤ Real.sqrt (1415700 / 37 : ℝ) ∧
      Real.sqrt (1415700 / 37 : ℝ) ≤ 244509 / 1250 ∧ Real.sqrt (70785 : ℝ) ≤ 1330273 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 104. -/
theorem gammaAnalyticHigh104_logs :
    Real.log (1415700 / 37 : ℝ) ≤ 105523 / 10000 ∧ Real.log (70785 : ℝ) ≤ 4467 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1415700 / 37) 16 20 0 (105523 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 70785 17 20 0 (4467 / 400) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh104_main (hRH : RiemannHypothesis) :
    (32623 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 70785,
        Real.exp (-(n : ℝ) / (1415700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1415700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (100 / 3857) * ((1415700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1415700 / 37) * (37 / 20)) + 1) / (100 / 3857) +
        1839 / 1000 ≤
      3839 / 2 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh104_roots.2.2]
  have hs :
    Real.sqrt ((1415700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1415700 / 37) * (37 / 20)) +
        21 / 20 ≤
      3489 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh104_roots.2.2, gammaAnalyticHigh104_logs.2]
  have hz :
    Real.sqrt (1415700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1415700 / 37) + 2469 / 800 ≤
      27421 / 1000 := by
    linarith only [gammaAnalyticHigh104_roots.2.1, gammaAnalyticHigh104_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1415700 / 37) (y := 37 / 20) (h := 100 / 3857) (r :=
      244509 / 1250) (e := 78619 / 500000) (p := 3839 / 2) (s := 3489 / 100) (z := 27421 / 1000)
      (F := 32623 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh104_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1415700 / 37 : ℝ) * (37 / 20) = 70785 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh104_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1415700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1415700 / 37 : ℝ)) ≤
      48937 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1956071 / 10000) (T := 244509 / 1250) (Z :=
      105523 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh104_roots.1
      gammaAnalyticHigh104_roots.2.1 gammaAnalyticHigh104_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh104_power : (1415700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 53 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 104 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh104_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1943 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (48989 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (70785 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1943 / 4)]
  apply
    reject_03_of_analytic_caps (B := 70785) (x := 1415700 / 37) (H := 48989 / 100) (R :=
      1956071 / 10000) (W := 53 / 20000) (F := 32623 / 200) (U := 48937 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh104_power (gammaAnalyticHigh104_main hGRH.riemann)
      (gammaAnalyticHigh104_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 105. -/
theorem gammaAnalyticHigh105_roots :
    ((986373 / 5000 : ℝ) ≤ Real.sqrt (1439940 / 37 : ℝ) ∧
      Real.sqrt (1439940 / 37 : ℝ) ≤ 1972747 / 10000 ∧ Real.sqrt (71997 : ℝ) ≤ 1341613 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 105. -/
theorem gammaAnalyticHigh105_logs :
    Real.log (1439940 / 37 : ℝ) ≤ 26423 / 2500 ∧ Real.log (71997 : ℝ) ≤ 27961 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1439940 / 37) 16 20 0 (26423 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 71997 17 20 0 (27961 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh105_main (hRH : RiemannHypothesis) :
    (82257 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 71997,
        Real.exp (-(n : ℝ) / (1439940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1439940 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 77469) * ((1439940 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1439940 / 37) * (37 / 20)) + 1) / (2000 / 77469) +
        1839 / 1000 ≤
      1944043 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh105_roots.2.2]
  have hs :
    Real.sqrt ((1439940 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1439940 / 37) * (37 / 20)) +
        21 / 20 ≤
      7007 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh105_roots.2.2, gammaAnalyticHigh105_logs.2]
  have hz :
    Real.sqrt (1439940 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1439940 / 37) + 2469 / 800 ≤
      3441 / 125 := by
    linarith only [gammaAnalyticHigh105_roots.2.1, gammaAnalyticHigh105_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1439940 / 37) (y := 37 / 20) (h := 2000 / 77469) (r :=
      1972747 / 10000) (e := 78619 / 500000) (p := 1944043 / 1000) (s := 7007 / 200) (z :=
      3441 / 125) (F := 82257 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh105_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1439940 / 37 : ℝ) * (37 / 20) = 71997 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh105_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1439940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1439940 / 37 : ℝ)) ≤
      39483 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 986373 / 5000) (T := 1972747 / 10000) (Z := 26423 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh105_roots.1
      gammaAnalyticHigh105_roots.2.1 gammaAnalyticHigh105_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh105_power : (1439940 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 131 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 105 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh105_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (48989 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24703 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (71997 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 48989 / 100)]
  apply
    reject_03_of_analytic_caps (B := 71997) (x := 1439940 / 37) (H := 24703 / 50) (R :=
      986373 / 5000) (W := 131 / 50000) (F := 82257 / 500) (U := 39483 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh105_power (gammaAnalyticHigh105_main hGRH.riemann)
      (gammaAnalyticHigh105_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 106. -/
theorem gammaAnalyticHigh106_roots :
    ((99477 / 500 : ℝ) ≤ Real.sqrt (1464560 / 37 : ℝ) ∧
      Real.sqrt (1464560 / 37 : ℝ) ≤ 1989541 / 10000 ∧ Real.sqrt (73228 : ℝ) ≤ 676517 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 106. -/
theorem gammaAnalyticHigh106_logs :
    Real.log (1464560 / 37 : ℝ) ≤ 52931 / 5000 ∧ Real.log (73228 : ℝ) ≤ 56007 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1464560 / 37) 16 20 0 (52931 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 73228 17 20 0 (56007 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh106_main (hRH : RiemannHypothesis) :
    (41481 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 73228,
        Real.exp (-(n : ℝ) / (1464560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1464560 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 38899) * ((1464560 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1464560 / 37) * (37 / 20)) + 1) / (1000 / 38899) +
        1839 / 1000 ≤
      393773 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh106_roots.2.2]
  have hs :
    Real.sqrt ((1464560 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1464560 / 37) * (37 / 20)) +
        21 / 20 ≤
      1759 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh106_roots.2.2, gammaAnalyticHigh106_logs.2]
  have hz :
    Real.sqrt (1464560 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1464560 / 37) + 2469 / 800 ≤
      5527 / 200 := by
    linarith only [gammaAnalyticHigh106_roots.2.1, gammaAnalyticHigh106_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1464560 / 37) (y := 37 / 20) (h := 1000 / 38899) (r :=
      1989541 / 10000) (e := 78619 / 500000) (p := 393773 / 200) (s := 1759 / 50) (z := 5527 / 200)
      (F := 41481 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh106_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1464560 / 37 : ℝ) * (37 / 20) = 73228 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh106_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1464560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1464560 / 37 : ℝ)) ≤
      99547 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 99477 / 500) (T := 1989541 / 10000) (Z := 52931 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh106_roots.1
      gammaAnalyticHigh106_roots.2.1 gammaAnalyticHigh106_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh106_power : (1464560 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 13 / 5000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 106 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh106_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24703 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (49827 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (73228 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24703 / 50)]
  apply
    reject_03_of_analytic_caps (B := 73228) (x := 1464560 / 37) (H := 49827 / 100) (R :=
      99477 / 500) (W := 13 / 5000) (F := 41481 / 250) (U := 99547 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh106_power (gammaAnalyticHigh106_main hGRH.riemann)
      (gammaAnalyticHigh106_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 107. -/
theorem gammaAnalyticHigh107_roots :
    ((2006489 / 10000 : ℝ) ≤ Real.sqrt (40260 : ℝ) ∧
      Real.sqrt (40260 : ℝ) ≤ 200649 / 1000 ∧ Real.sqrt (74481 : ℝ) ≤ 2729121 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 107. -/
theorem gammaAnalyticHigh107_logs :
    Real.log (40260 : ℝ) ≤ 6627 / 625 ∧ Real.log (74481 : ℝ) ≤ 112183 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (40260) 16 20 0 (6627 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 74481 17 20 0 (112183 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh107_main (hRH : RiemannHypothesis) :
    (167347 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 74481,
        Real.exp (-(n : ℝ) / (40260)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (40260 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 78127) * ((40260) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((40260) * (37 / 20)) + 1) / (2000 / 78127) +
        1839 / 1000 ≤
      249253 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh107_roots.2.2]
  have hs :
    Real.sqrt ((40260 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((40260) * (37 / 20)) +
        21 / 20 ≤
      35327 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh107_roots.2.2, gammaAnalyticHigh107_logs.2]
  have hz :
    Real.sqrt (40260 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (40260) + 2469 / 800 ≤
      3468 / 125 := by
    linarith only [gammaAnalyticHigh107_roots.2.1, gammaAnalyticHigh107_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 40260) (y := 37 / 20) (h := 2000 / 78127) (r :=
      200649 / 1000) (e := 78619 / 500000) (p := 249253 / 125) (s := 35327 / 1000) (z := 3468 / 125)
      (F := 167347 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh107_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (40260 : ℝ) * (37 / 20) = 74481 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh107_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (40260)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (40260 : ℝ)) ≤
      50197 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2006489 / 10000) (T := 200649 / 1000) (Z := 6627 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh107_roots.1
      gammaAnalyticHigh107_roots.2.1 gammaAnalyticHigh107_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh107_power : (40260 : ℝ) ^ (-9 / 16 : ℝ) ≤ 257 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 107 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh107_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (49827 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (50251 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (74481 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 49827 / 100)]
  apply
    reject_03_of_analytic_caps (B := 74481) (x := 40260) (H := 50251 / 100) (R := 2006489 / 10000)
      (W := 257 / 100000) (F := 167347 / 1000) (U := 50197 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh107_power (gammaAnalyticHigh107_main hGRH.riemann)
      (gammaAnalyticHigh107_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 108. -/
theorem gammaAnalyticHigh108_roots :
    ((2023563 / 10000 : ℝ) ≤ Real.sqrt (1515080 / 37 : ℝ) ∧
      Real.sqrt (1515080 / 37 : ℝ) ≤ 505891 / 2500 ∧ Real.sqrt (75754 : ℝ) ≤ 550469 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 108. -/
theorem gammaAnalyticHigh108_logs :
    Real.log (1515080 / 37 : ℝ) ≤ 106201 / 10000 ∧ Real.log (75754 : ℝ) ≤ 112353 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1515080 / 37) 16 20 0 (106201 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 75754 17 20 0 (112353 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh108_main (hRH : RiemannHypothesis) :
    (8439 / 50 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 75754,
        Real.exp (-(n : ℝ) / (1515080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1515080 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 156919) * ((1515080 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1515080 / 37) * (37 / 20)) + 1) / (4000 / 156919) +
        1839 / 1000 ≤
      504869 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh108_roots.2.2]
  have hs :
    Real.sqrt ((1515080 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1515080 / 37) * (37 / 20)) +
        21 / 20 ≤
      17737 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh108_roots.2.2, gammaAnalyticHigh108_logs.2]
  have hz :
    Real.sqrt (1515080 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1515080 / 37) + 2469 / 800 ≤
      6963 / 250 := by
    linarith only [gammaAnalyticHigh108_roots.2.1, gammaAnalyticHigh108_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1515080 / 37) (y := 37 / 20) (h := 4000 / 156919) (r :=
      505891 / 2500) (e := 78619 / 500000) (p := 504869 / 250) (s := 17737 / 500) (z := 6963 / 250)
      (F := 8439 / 50) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh108_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1515080 / 37 : ℝ) * (37 / 20) = 75754 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh108_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1515080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1515080 / 37 : ℝ)) ≤
      40499 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2023563 / 10000) (T := 505891 / 2500) (Z :=
      106201 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh108_roots.1
      gammaAnalyticHigh108_roots.2.1 gammaAnalyticHigh108_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh108_power : (1515080 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 51 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 108 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh108_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (50251 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (25339 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (75754 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 50251 / 100)]
  apply
    reject_03_of_analytic_caps (B := 75754) (x := 1515080 / 37) (H := 25339 / 50) (R :=
      2023563 / 10000) (W := 51 / 20000) (F := 8439 / 50) (U := 40499 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh108_power (gammaAnalyticHigh108_main hGRH.riemann)
      (gammaAnalyticHigh108_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 109. -/
theorem gammaAnalyticHigh109_roots :
    ((51019 / 250 : ℝ) ≤ Real.sqrt (1540940 / 37 : ℝ) ∧
      Real.sqrt (1540940 / 37 : ℝ) ≤ 2040761 / 10000 ∧ Real.sqrt (77047 : ℝ) ≤ 555147 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 109. -/
theorem gammaAnalyticHigh109_logs :
    Real.log (1540940 / 37 : ℝ) ≤ 10637 / 1000 ∧ Real.log (77047 : ℝ) ≤ 56261 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1540940 / 37) 16 20 0 (10637 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 77047 17 20 0 (56261 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh109_main (hRH : RiemannHypothesis) :
    (170223 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 77047,
        Real.exp (-(n : ℝ) / (1540940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1540940 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (250 / 9849) * ((1540940 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1540940 / 37) * (37 / 20)) + 1) / (250 / 9849) +
        1839 / 1000 ≤
      2045219 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh109_roots.2.2]
  have hs :
    Real.sqrt ((1540940 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1540940 / 37) * (37 / 20)) +
        21 / 20 ≤
      17811 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh109_roots.2.2, gammaAnalyticHigh109_logs.2]
  have hz :
    Real.sqrt (1540940 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1540940 / 37) + 2469 / 800 ≤
      13981 / 500 := by
    linarith only [gammaAnalyticHigh109_roots.2.1, gammaAnalyticHigh109_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1540940 / 37) (y := 37 / 20) (h := 250 / 9849) (r :=
      2040761 / 10000) (e := 78619 / 500000) (p := 2045219 / 1000) (s := 17811 / 500) (z :=
      13981 / 500) (F := 170223 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh109_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1540940 / 37 : ℝ) * (37 / 20) = 77047 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh109_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1540940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1540940 / 37 : ℝ)) ≤
      102107 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 51019 / 250) (T := 2040761 / 10000) (Z := 10637 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh109_roots.1
      gammaAnalyticHigh109_roots.2.1 gammaAnalyticHigh109_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh109_power : (1540940 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 253 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 109 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh109_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (25339 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12777 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (77047 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 25339 / 50)]
  apply
    reject_03_of_analytic_caps (B := 77047) (x := 1540940 / 37) (H := 12777 / 25) (R := 51019 / 250)
      (W := 253 / 100000) (F := 170223 / 1000) (U := 102107 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh109_power (gammaAnalyticHigh109_main hGRH.riemann)
      (gammaAnalyticHigh109_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 110. -/
theorem gammaAnalyticHigh110_roots :
    ((82323 / 400 : ℝ) ≤ Real.sqrt (1567200 / 37 : ℝ) ∧
      Real.sqrt (1567200 / 37 : ℝ) ≤ 514519 / 2500 ∧ Real.sqrt (78360 : ℝ) ≤ 1399643 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 110. -/
theorem gammaAnalyticHigh110_logs :
    Real.log (1567200 / 37 : ℝ) ≤ 106539 / 10000 ∧ Real.log (78360 : ℝ) ≤ 112691 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1567200 / 37) 16 20 0 (106539 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 78360 17 20 0 (112691 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh110_main (hRH : RiemannHypothesis) :
    (171677 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 78360,
        Real.exp (-(n : ℝ) / (1567200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1567200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (250 / 9891) * ((1567200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1567200 / 37) * (37 / 20)) + 1) / (250 / 9891) +
        1839 / 1000 ≤
      2071249 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh110_roots.2.2]
  have hs :
    Real.sqrt ((1567200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1567200 / 37) * (37 / 20)) +
        21 / 20 ≤
      35771 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh110_roots.2.2, gammaAnalyticHigh110_logs.2]
  have hz :
    Real.sqrt (1567200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1567200 / 37) + 2469 / 800 ≤
      3509 / 125 := by
    linarith only [gammaAnalyticHigh110_roots.2.1, gammaAnalyticHigh110_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1567200 / 37) (y := 37 / 20) (h := 250 / 9891) (r :=
      514519 / 2500) (e := 78619 / 500000) (p := 2071249 / 1000) (s := 35771 / 1000) (z :=
      3509 / 125) (F := 171677 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh110_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1567200 / 37 : ℝ) * (37 / 20) = 78360 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh110_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1567200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1567200 / 37 : ℝ)) ≤
      25743 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 82323 / 400) (T := 514519 / 2500) (Z := 106539 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh110_roots.1
      gammaAnalyticHigh110_roots.2.1 gammaAnalyticHigh110_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh110_power : (1567200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1 / 400 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 110 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh110_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12777 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (25771 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (78360 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12777 / 25)]
  apply
    reject_03_of_analytic_caps (B := 78360) (x := 1567200 / 37) (H := 25771 / 50) (R := 82323 / 400)
      (W := 1 / 400) (F := 171677 / 1000) (U := 25743 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh110_power (gammaAnalyticHigh110_main hGRH.riemann)
      (gammaAnalyticHigh110_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 111. -/
theorem gammaAnalyticHigh111_roots :
    ((2075559 / 10000 : ℝ) ≤ Real.sqrt (1593940 / 37 : ℝ) ∧
      Real.sqrt (1593940 / 37 : ℝ) ≤ 51889 / 250 ∧ Real.sqrt (79697 : ℝ) ≤ 1411533 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 111. -/
theorem gammaAnalyticHigh111_logs :
    Real.log (1593940 / 37 : ℝ) ≤ 106709 / 10000 ∧ Real.log (79697 : ℝ) ≤ 5643 / 500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1593940 / 37) 16 20 0 (106709 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 79697 17 20 0 (5643 / 500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh111_main (hRH : RiemannHypothesis) :
    (21643 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 79697,
        Real.exp (-(n : ℝ) / (1593940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1593940 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 158921) * ((1593940 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1593940 / 37) * (37 / 20)) + 1) / (4000 / 158921) +
        1839 / 1000 ≤
      524411 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh111_roots.2.2]
  have hs :
    Real.sqrt ((1593940 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1593940 / 37) * (37 / 20)) +
        21 / 20 ≤
      35921 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh111_roots.2.2, gammaAnalyticHigh111_logs.2]
  have hz :
    Real.sqrt (1593940 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1593940 / 37) + 2469 / 800 ≤
      14091 / 500 := by
    linarith only [gammaAnalyticHigh111_roots.2.1, gammaAnalyticHigh111_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1593940 / 37) (y := 37 / 20) (h := 4000 / 158921) (r :=
      51889 / 250) (e := 78619 / 500000) (p := 524411 / 250) (s := 35921 / 1000) (z := 14091 / 500)
      (F := 21643 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh111_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1593940 / 37 : ℝ) * (37 / 20) = 79697 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh111_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1593940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1593940 / 37 : ℝ)) ≤
      51923 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2075559 / 10000) (T := 51889 / 250) (Z := 106709 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh111_roots.1
      gammaAnalyticHigh111_roots.2.1 gammaAnalyticHigh111_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh111_power : (1593940 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 31 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 111 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh111_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (25771 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (51979 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (79697 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 25771 / 50)]
  apply
    reject_03_of_analytic_caps (B := 79697) (x := 1593940 / 37) (H := 51979 / 100) (R :=
      2075559 / 10000) (W := 31 / 12500) (F := 21643 / 125) (U := 51923 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh111_power (gammaAnalyticHigh111_main hGRH.riemann)
      (gammaAnalyticHigh111_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 112. -/
theorem gammaAnalyticHigh112_roots :
    ((1046577 / 5000 : ℝ) ≤ Real.sqrt (1621080 / 37 : ℝ) ∧
      Real.sqrt (1621080 / 37 : ℝ) ≤ 418631 / 2000 ∧ Real.sqrt (81054 : ℝ) ≤ 2846999 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 112. -/
theorem gammaAnalyticHigh112_logs :
    Real.log (1621080 / 37 : ℝ) ≤ 106877 / 10000 ∧ Real.log (81054 : ℝ) ≤ 113029 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1621080 / 37) 16 20 0 (106877 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 81054 17 20 0 (113029 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh112_main (hRH : RiemannHypothesis) :
    (87311 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 81054,
        Real.exp (-(n : ℝ) / (1621080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1621080 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 159593) * ((1621080 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1621080 / 37) * (37 / 20)) + 1) / (4000 / 159593) +
        1839 / 1000 ≤
      53108 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh112_roots.2.2]
  have hs :
    Real.sqrt ((1621080 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1621080 / 37) * (37 / 20)) +
        21 / 20 ≤
      4509 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh112_roots.2.2, gammaAnalyticHigh112_logs.2]
  have hz :
    Real.sqrt (1621080 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1621080 / 37) + 2469 / 800 ≤
      14147 / 500 := by
    linarith only [gammaAnalyticHigh112_roots.2.1, gammaAnalyticHigh112_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1621080 / 37) (y := 37 / 20) (h := 4000 / 159593) (r :=
      418631 / 2000) (e := 78619 / 500000) (p := 53108 / 25) (s := 4509 / 125) (z := 14147 / 500)
      (F := 87311 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh112_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1621080 / 37 : ℝ) * (37 / 20) = 81054 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh112_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1621080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1621080 / 37 : ℝ)) ≤
      209451 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1046577 / 5000) (T := 418631 / 2000) (Z :=
      106877 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh112_roots.1
      gammaAnalyticHigh112_roots.2.1 gammaAnalyticHigh112_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh112_power : (1621080 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 49 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 112 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh112_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (51979 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2621 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (81054 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 51979 / 100)]
  apply
    reject_03_of_analytic_caps (B := 81054) (x := 1621080 / 37) (H := 2621 / 5) (R :=
      1046577 / 5000) (W := 49 / 20000) (F := 87311 / 500) (U := 209451 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh112_power (gammaAnalyticHigh112_main hGRH.riemann)
      (gammaAnalyticHigh112_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 113. -/
theorem gammaAnalyticHigh113_roots :
    ((2110911 / 10000 : ℝ) ≤ Real.sqrt (1648700 / 37 : ℝ) ∧
      Real.sqrt (1648700 / 37 : ℝ) ≤ 131932 / 625 ∧ Real.sqrt (82435 : ℝ) ≤ 57423 / 200) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 113. -/
theorem gammaAnalyticHigh113_logs :
    Real.log (1648700 / 37 : ℝ) ≤ 53523 / 5000 ∧ Real.log (82435 : ℝ) ≤ 56599 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1648700 / 37) 16 20 0 (53523 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 82435 17 20 0 (56599 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh113_main (hRH : RiemannHypothesis) :
    (22014 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 82435,
        Real.exp (-(n : ℝ) / (1648700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1648700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (250 / 10017) * ((1648700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1648700 / 37) * (37 / 20)) + 1) / (250 / 10017) +
        1839 / 1000 ≤
      2151353 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh113_roots.2.2]
  have hs :
    Real.sqrt ((1648700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1648700 / 37) * (37 / 20)) +
        21 / 20 ≤
      36223 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh113_roots.2.2, gammaAnalyticHigh113_logs.2]
  have hz :
    Real.sqrt (1648700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1648700 / 37) + 2469 / 800 ≤
      14203 / 500 := by
    linarith only [gammaAnalyticHigh113_roots.2.1, gammaAnalyticHigh113_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1648700 / 37) (y := 37 / 20) (h := 250 / 10017) (r :=
      131932 / 625) (e := 78619 / 500000) (p := 2151353 / 1000) (s := 36223 / 1000) (z :=
      14203 / 500) (F := 22014 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh113_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1648700 / 37 : ℝ) * (37 / 20) = 82435 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh113_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1648700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1648700 / 37 : ℝ)) ≤
      105613 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2110911 / 10000) (T := 131932 / 625) (Z := 53523 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh113_roots.1
      gammaAnalyticHigh113_roots.2.1 gammaAnalyticHigh113_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh113_power : (1648700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 243 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 113 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh113_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2621 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13216 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (82435 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2621 / 5)]
  apply
    reject_03_of_analytic_caps (B := 82435) (x := 1648700 / 37) (H := 13216 / 25) (R :=
      2110911 / 10000) (W := 243 / 100000) (F := 22014 / 125) (U := 105613 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh113_power (gammaAnalyticHigh113_main hGRH.riemann)
      (gammaAnalyticHigh113_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 114. -/
theorem gammaAnalyticHigh114_roots :
    ((1064399 / 5000 : ℝ) ≤ Real.sqrt (1676760 / 37 : ℝ) ∧
      Real.sqrt (1676760 / 37 : ℝ) ≤ 2128799 / 10000 ∧ Real.sqrt (83838 : ℝ) ≤ 72387 / 250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 114. -/
theorem gammaAnalyticHigh114_logs :
    Real.log (1676760 / 37 : ℝ) ≤ 21443 / 2000 ∧ Real.log (83838 : ℝ) ≤ 113367 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1676760 / 37) 16 20 0 (21443 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 83838 17 20 0 (113367 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh114_main (hRH : RiemannHypothesis) :
    (88807 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 83838,
        Real.exp (-(n : ℝ) / (1676760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1676760 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 160951) * ((1676760 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1676760 / 37) * (37 / 20)) + 1) / (4000 / 160951) +
        1839 / 1000 ≤
      2178701 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh114_roots.2.2]
  have hs :
    Real.sqrt ((1676760 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1676760 / 37) * (37 / 20)) +
        21 / 20 ≤
      4547 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh114_roots.2.2, gammaAnalyticHigh114_logs.2]
  have hz :
    Real.sqrt (1676760 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1676760 / 37) + 2469 / 800 ≤
      14259 / 500 := by
    linarith only [gammaAnalyticHigh114_roots.2.1, gammaAnalyticHigh114_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1676760 / 37) (y := 37 / 20) (h := 4000 / 160951) (r :=
      2128799 / 10000) (e := 78619 / 500000) (p := 2178701 / 1000) (s := 4547 / 125) (z :=
      14259 / 500) (F := 88807 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh114_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1676760 / 37 : ℝ) * (37 / 20) = 83838 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh114_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1676760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1676760 / 37 : ℝ)) ≤
      106507 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1064399 / 5000) (T := 2128799 / 10000) (Z :=
      21443 / 2000) (by norm_num only) (by norm_num only) gammaAnalyticHigh114_roots.1
      gammaAnalyticHigh114_roots.2.1 gammaAnalyticHigh114_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh114_power : (1676760 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 241 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 114 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh114_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (13216 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (83838 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13216 / 25)]
  apply
    reject_03_of_analytic_caps (B := 83838) (x := 1676760 / 37) (H := 13328 / 25) (R :=
      1064399 / 5000) (W := 241 / 100000) (F := 88807 / 500) (U := 106507 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh114_power (gammaAnalyticHigh114_main hGRH.riemann)
      (gammaAnalyticHigh114_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 115. -/
theorem gammaAnalyticHigh115_roots :
    ((2146839 / 10000 : ℝ) ≤ Real.sqrt (1705300 / 37 : ℝ) ∧
      Real.sqrt (1705300 / 37 : ℝ) ≤ 53671 / 250 ∧ Real.sqrt (85265 : ℝ) ≤ 1460009 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 115. -/
theorem gammaAnalyticHigh115_logs :
    Real.log (1705300 / 37 : ℝ) ≤ 13423 / 1250 ∧ Real.log (85265 : ℝ) ≤ 7096 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1705300 / 37) 16 20 0 (13423 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 85265 17 20 0 (7096 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh115_main (hRH : RiemannHypothesis) :
    (22391 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 85265,
        Real.exp (-(n : ℝ) / (1705300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1705300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (400 / 16163) * ((1705300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1705300 / 37) * (37 / 20)) + 1) / (400 / 16163) +
        1839 / 1000 ≤
      11032 / 5 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh115_roots.2.2]
  have hs :
    Real.sqrt ((1705300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1705300 / 37) * (37 / 20)) +
        21 / 20 ≤
      3653 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh115_roots.2.2, gammaAnalyticHigh115_logs.2]
  have hz :
    Real.sqrt (1705300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1705300 / 37) + 2469 / 800 ≤
      3579 / 125 := by
    linarith only [gammaAnalyticHigh115_roots.2.1, gammaAnalyticHigh115_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1705300 / 37) (y := 37 / 20) (h := 400 / 16163) (r :=
      53671 / 250) (e := 78619 / 500000) (p := 11032 / 5) (s := 3653 / 100) (z := 3579 / 125) (F :=
      22391 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh115_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1705300 / 37 : ℝ) * (37 / 20) = 85265 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh115_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1705300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1705300 / 37 : ℝ)) ≤
      107409 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2146839 / 10000) (T := 53671 / 250) (Z := 13423 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh115_roots.1
      gammaAnalyticHigh115_roots.2.1 gammaAnalyticHigh115_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh115_power : (1705300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 239 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 115 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh115_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (13328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (53763 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (85265 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 85265) (x := 1705300 / 37) (H := 53763 / 100) (R :=
      2146839 / 10000) (W := 239 / 100000) (F := 22391 / 125) (U := 107409 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh115_power (gammaAnalyticHigh115_main hGRH.riemann)
      (gammaAnalyticHigh115_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 116. -/
theorem gammaAnalyticHigh116_roots :
    ((2164991 / 10000 : ℝ) ≤ Real.sqrt (1734260 / 37 : ℝ) ∧
      Real.sqrt (1734260 / 37 : ℝ) ≤ 135312 / 625 ∧ Real.sqrt (86713 : ℝ) ≤ 736177 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 116. -/
theorem gammaAnalyticHigh116_logs :
    Real.log (1734260 / 37 : ℝ) ≤ 6722 / 625 ∧ Real.log (86713 : ℝ) ≤ 14213 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1734260 / 37) 16 20 0 (6722 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 86713 17 20 0 (14213 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh116_main (hRH : RiemannHypothesis) :
    (45163 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 86713,
        Real.exp (-(n : ℝ) / (1734260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1734260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 162309) * ((1734260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1734260 / 37) * (37 / 20)) + 1) / (4000 / 162309) +
        1839 / 1000 ≤
      2234389 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh116_roots.2.2]
  have hs :
    Real.sqrt ((1734260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1734260 / 37) * (37 / 20)) +
        21 / 20 ≤
      9171 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh116_roots.2.2, gammaAnalyticHigh116_logs.2]
  have hz :
    Real.sqrt (1734260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1734260 / 37) + 2469 / 800 ≤
      14373 / 500 := by
    linarith only [gammaAnalyticHigh116_roots.2.1, gammaAnalyticHigh116_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1734260 / 37) (y := 37 / 20) (h := 4000 / 162309) (r :=
      135312 / 625) (e := 78619 / 500000) (p := 2234389 / 1000) (s := 9171 / 250) (z := 14373 / 500)
      (F := 45163 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh116_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1734260 / 37 : ℝ) * (37 / 20) = 86713 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh116_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1734260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1734260 / 37 : ℝ)) ≤
      27079 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2164991 / 10000) (T := 135312 / 625) (Z := 6722 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh116_roots.1
      gammaAnalyticHigh116_roots.2.1 gammaAnalyticHigh116_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh116_power : (1734260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 59 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 116 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh116_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (53763 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (27109 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (86713 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 53763 / 100)]
  apply
    reject_03_of_analytic_caps (B := 86713) (x := 1734260 / 37) (H := 27109 / 50) (R :=
      2164991 / 10000) (W := 59 / 25000) (F := 45163 / 250) (U := 27079 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh116_power (gammaAnalyticHigh116_main hGRH.riemann)
      (gammaAnalyticHigh116_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 117. -/
theorem gammaAnalyticHigh117_roots :
    ((436663 / 2000 : ℝ) ≤ Real.sqrt (1763740 / 37 : ℝ) ∧
      Real.sqrt (1763740 / 37 : ℝ) ≤ 545829 / 2500 ∧ Real.sqrt (88187 : ℝ) ≤ 296963 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 117. -/
theorem gammaAnalyticHigh117_logs :
    Real.log (1763740 / 37 : ℝ) ≤ 107721 / 10000 ∧ Real.log (88187 : ℝ) ≤ 113873 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1763740 / 37) 16 20 0 (107721 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 88187 17 20 0 (113873 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh117_main (hRH : RiemannHypothesis) :
    (18219 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 88187,
        Real.exp (-(n : ℝ) / (1763740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1763740 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 32599) * ((1763740 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1763740 / 37) * (37 / 20)) + 1) / (800 / 32599) +
        1839 / 1000 ≤
      2262759 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh117_roots.2.2]
  have hs :
    Real.sqrt ((1763740 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1763740 / 37) * (37 / 20)) +
        21 / 20 ≤
      921 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh117_roots.2.2, gammaAnalyticHigh117_logs.2]
  have hz :
    Real.sqrt (1763740 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1763740 / 37) + 2469 / 800 ≤
      28861 / 1000 := by
    linarith only [gammaAnalyticHigh117_roots.2.1, gammaAnalyticHigh117_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1763740 / 37) (y := 37 / 20) (h := 800 / 32599) (r :=
      545829 / 2500) (e := 78619 / 500000) (p := 2262759 / 1000) (s := 921 / 25) (z := 28861 / 1000)
      (F := 18219 / 100) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticHigh117_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1763740 / 37 : ℝ) * (37 / 20) = 88187 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh117_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1763740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1763740 / 37 : ℝ)) ≤
      27308 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 436663 / 2000) (T := 545829 / 2500) (Z := 107721 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh117_roots.1
      gammaAnalyticHigh117_roots.2.1 gammaAnalyticHigh117_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh117_power : (1763740 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 117 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 117 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh117_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (27109 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13669 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (88187 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 27109 / 50)]
  apply
    reject_03_of_analytic_caps (B := 88187) (x := 1763740 / 37) (H := 13669 / 25) (R :=
      436663 / 2000) (W := 117 / 50000) (F := 18219 / 100) (U := 27308 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticHigh117_power (gammaAnalyticHigh117_main hGRH.riemann)
      (gammaAnalyticHigh117_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 118. -/
theorem gammaAnalyticHigh118_roots :
    ((550439 / 2500 : ℝ) ≤ Real.sqrt (1793660 / 37 : ℝ) ∧
      Real.sqrt (1793660 / 37 : ℝ) ≤ 2201757 / 10000 ∧
      Real.sqrt (89683 : ℝ) ≤ 2994713 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 118. -/
theorem gammaAnalyticHigh118_logs :
    Real.log (1793660 / 37 : ℝ) ≤ 107889 / 10000 ∧ Real.log (89683 : ℝ) ≤ 114041 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1793660 / 37) 16 20 0 (107889 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 89683 17 20 0 (114041 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticHigh118_main (hRH : RiemannHypothesis) :
    (91869 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 89683,
        Real.exp (-(n : ℝ) / (1793660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1793660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 163681) * ((1793660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1793660 / 37) * (37 / 20)) + 1) / (4000 / 163681) +
        1839 / 1000 ≤
      2291433 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh118_roots.2.2]
  have hs :
    Real.sqrt ((1793660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1793660 / 37) * (37 / 20)) +
        21 / 20 ≤
      9249 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticHigh118_roots.2.2, gammaAnalyticHigh118_logs.2]
  have hz :
    Real.sqrt (1793660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1793660 / 37) + 2469 / 800 ≤
      3622 / 125 := by
    linarith only [gammaAnalyticHigh118_roots.2.1, gammaAnalyticHigh118_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1793660 / 37) (y := 37 / 20) (h := 4000 / 163681) (r :=
      2201757 / 10000) (e := 78619 / 500000) (p := 2291433 / 1000) (s := 9249 / 250) (z :=
      3622 / 125) (F := 91869 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticHigh118_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1793660 / 37 : ℝ) * (37 / 20) = 89683 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticHigh118_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1793660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1793660 / 37 : ℝ)) ≤
      55077 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 550439 / 2500) (T := 2201757 / 10000) (Z :=
      107889 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticHigh118_roots.1
      gammaAnalyticHigh118_roots.2.1 gammaAnalyticHigh118_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticHigh118_power : (1793660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 29 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 118 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticHigh118_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (13669 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (550 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (89683 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13669 / 25)]
  apply
    reject_03_of_analytic_caps (B := 89683) (x := 1793660 / 37) (H := 550) (R := 550439 / 2500)
      (W := 29 / 12500) (F := 91869 / 500) (U := 55077 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticHigh118_power (gammaAnalyticHigh118_main hGRH.riemann)
      (gammaAnalyticHigh118_principal hGRH.riemann)
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
