/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticNextCombined

/-! # Analytic Gamma cells after logarithmic scale 100.21 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact root caps for analytic cell 0. -/
theorem gammaAnalyticMore0_roots :
    ((202751 / 5000 : ℝ) ≤ Real.sqrt (60840 / 37 : ℝ) ∧
      Real.sqrt (60840 / 37 : ℝ) ≤ 405503 / 10000 ∧ Real.sqrt (3042 : ℝ) ≤ 68943 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 0. -/
theorem gammaAnalyticMore0_logs :
    Real.log (60840 / 37 : ℝ) ≤ 74051 / 10000 ∧ Real.log (3042 : ℝ) ≤ 80203 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (60840 / 37) 11 20 0 (74051 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3042 12 20 0 (80203 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore0_main (hRH : RiemannHypothesis) :
    (32949 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3042,
        Real.exp (-(n : ℝ) / (60840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((60840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((60840 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      18413 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore0_roots.2.2]
  have hs :
    Real.sqrt ((60840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((60840 / 37) * (37 / 20)) +
        21 / 20 ≤
      9279 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore0_roots.2.2, gammaAnalyticMore0_logs.2]
  have hz :
    Real.sqrt (60840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (60840 / 37) + 2469 / 800 ≤
      1916 / 125 := by
    linarith only [gammaAnalyticMore0_roots.2.1, gammaAnalyticMore0_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 60840 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      405503 / 10000) (e := 78619 / 500000) (p := 18413 / 100) (s := 9279 / 500) (z := 1916 / 125)
      (F := 32949 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore0_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (60840 / 37 : ℝ) * (37 / 20) = 3042 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore0_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (60840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60840 / 37 : ℝ)) ≤
      40929 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 202751 / 5000) (T := 405503 / 10000) (Z := 74051 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore0_roots.1 gammaAnalyticMore0_roots.2.1
      gammaAnalyticMore0_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore0_power : (60840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1553 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 0 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore0_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10071 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2522 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3042 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10071 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3042) (x := 60840 / 37) (H := 2522 / 25) (R := 202751 / 5000)
      (W := 1553 / 100000) (F := 32949 / 1000) (U := 40929 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore0_power (gammaAnalyticMore0_main hGRH.riemann)
      (gammaAnalyticMore0_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 1. -/
theorem gammaAnalyticMore1_roots :
    ((81247 / 2000 : ℝ) ≤ Real.sqrt (61060 / 37 : ℝ) ∧
      Real.sqrt (61060 / 37 : ℝ) ≤ 101559 / 2500 ∧ Real.sqrt (3053 : ℝ) ≤ 27627 / 500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 1. -/
theorem gammaAnalyticMore1_logs :
    Real.log (61060 / 37 : ℝ) ≤ 74087 / 10000 ∧ Real.log (3053 : ℝ) ≤ 80239 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (61060 / 37) 11 20 0 (74087 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3053 12 20 0 (80239 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore1_main (hRH : RiemannHypothesis) :
    (3301 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3053,
        Real.exp (-(n : ℝ) / (61060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61060 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((61060 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((61060 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      92311 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore1_roots.2.2]
  have hs :
    Real.sqrt ((61060 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((61060 / 37) * (37 / 20)) +
        21 / 20 ≤
      18569 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore1_roots.2.2, gammaAnalyticMore1_logs.2]
  have hz :
    Real.sqrt (61060 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (61060 / 37) + 2469 / 800 ≤
      1917 / 125 := by
    linarith only [gammaAnalyticMore1_roots.2.1, gammaAnalyticMore1_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 61060 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      101559 / 2500) (e := 78619 / 500000) (p := 92311 / 500) (s := 18569 / 1000) (z := 1917 / 125)
      (F := 3301 / 100) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore1_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (61060 / 37 : ℝ) * (37 / 20) = 3053 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore1_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (61060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61060 / 37 : ℝ)) ≤
      20501 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 81247 / 2000) (T := 101559 / 2500) (Z := 74087 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore1_roots.1 gammaAnalyticMore1_roots.2.1
      gammaAnalyticMore1_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore1_power : (61060 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 31 / 2000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 1 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore1_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2522 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5053 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3053 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2522 / 25)]
  apply
    reject_03_of_analytic_caps (B := 3053) (x := 61060 / 37) (H := 5053 / 50) (R := 81247 / 2000)
      (W := 31 / 2000) (F := 3301 / 100) (U := 20501 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore1_power (gammaAnalyticMore1_main hGRH.riemann)
      (gammaAnalyticMore1_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 2. -/
theorem gammaAnalyticMore2_roots :
    ((406899 / 10000 : ℝ) ≤ Real.sqrt (61260 / 37 : ℝ) ∧
      Real.sqrt (61260 / 37 : ℝ) ≤ 4069 / 100 ∧ Real.sqrt (3063 : ℝ) ≤ 138361 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 2. -/
theorem gammaAnalyticMore2_logs :
    Real.log (61260 / 37 : ℝ) ≤ 1853 / 250 ∧ Real.log (3063 : ℝ) ≤ 5017 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (61260 / 37) 11 20 0 (1853 / 250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3063 12 20 0 (5017 / 625) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore2_main (hRH : RiemannHypothesis) :
    (16533 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3063,
        Real.exp (-(n : ℝ) / (61260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((61260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((61260 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      185069 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore2_roots.2.2]
  have hs :
    Real.sqrt ((61260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((61260 / 37) * (37 / 20)) +
        21 / 20 ≤
      929 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore2_roots.2.2, gammaAnalyticMore2_logs.2]
  have hz :
    Real.sqrt (61260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (61260 / 37) + 2469 / 800 ≤
      1918 / 125 := by
    linarith only [gammaAnalyticMore2_roots.2.1, gammaAnalyticMore2_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 61260 / 37) (y := 37 / 20) (h := 2 / 35) (r := 4069 / 100)
      (e := 78619 / 500000) (p := 185069 / 1000) (s := 929 / 50) (z := 1918 / 125) (F :=
      16533 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore2_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (61260 / 37 : ℝ) * (37 / 20) = 3063 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore2_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (61260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61260 / 37 : ℝ)) ≤
      10267 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 406899 / 10000) (T := 4069 / 100) (Z := 1853 / 250)
      (by norm_num only) (by norm_num only) gammaAnalyticMore2_roots.1 gammaAnalyticMore2_roots.2.1
      gammaAnalyticMore2_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore2_power : (61260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1547 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 2 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore2_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5053 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10123 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3063 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5053 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3063) (x := 61260 / 37) (H := 10123 / 100) (R :=
      406899 / 10000) (W := 1547 / 100000) (F := 16533 / 500) (U := 10267 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore2_power (gammaAnalyticMore2_main hGRH.riemann)
      (gammaAnalyticMore2_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 3. -/
theorem gammaAnalyticMore3_roots :
    ((407629 / 10000 : ℝ) ≤ Real.sqrt (61480 / 37 : ℝ) ∧
      Real.sqrt (61480 / 37 : ℝ) ≤ 40763 / 1000 ∧ Real.sqrt (3074 : ℝ) ≤ 554437 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 3. -/
theorem gammaAnalyticMore3_logs :
    Real.log (61480 / 37 : ℝ) ≤ 18539 / 2500 ∧ Real.log (3074 : ℝ) ≤ 20077 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (61480 / 37) 11 20 0 (18539 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3074 12 20 0 (20077 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore3_main (hRH : RiemannHypothesis) :
    (4141 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3074,
        Real.exp (-(n : ℝ) / (61480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61480 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((61480 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((61480 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      4639 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore3_roots.2.2]
  have hs :
    Real.sqrt ((61480 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((61480 / 37) * (37 / 20)) +
        21 / 20 ≤
      18591 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore3_roots.2.2, gammaAnalyticMore3_logs.2]
  have hz :
    Real.sqrt (61480 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (61480 / 37) + 2469 / 800 ≤
      15353 / 1000 := by
    linarith only [gammaAnalyticMore3_roots.2.1, gammaAnalyticMore3_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 61480 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      40763 / 1000) (e := 78619 / 500000) (p := 4639 / 25) (s := 18591 / 1000) (z := 15353 / 1000)
      (F := 4141 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore3_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (61480 / 37 : ℝ) * (37 / 20) = 3074 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore3_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (61480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61480 / 37 : ℝ)) ≤
      2057 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 407629 / 10000) (T := 40763 / 1000) (Z := 18539 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticMore3_roots.1 gammaAnalyticMore3_roots.2.1
      gammaAnalyticMore3_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore3_power : (61480 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 193 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 3 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore3_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10123 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5071 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3074 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10123 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3074) (x := 61480 / 37) (H := 5071 / 50) (R := 407629 / 10000)
      (W := 193 / 12500) (F := 4141 / 125) (U := 2057 / 50) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore3_power (gammaAnalyticMore3_main hGRH.riemann)
      (gammaAnalyticMore3_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 4. -/
theorem gammaAnalyticMore4_roots :
    ((204179 / 5000 : ℝ) ≤ Real.sqrt (61700 / 37 : ℝ) ∧
      Real.sqrt (61700 / 37 : ℝ) ≤ 408359 / 10000 ∧ Real.sqrt (3085 : ℝ) ≤ 138857 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 4. -/
theorem gammaAnalyticMore4_logs :
    Real.log (61700 / 37 : ℝ) ≤ 4637 / 625 ∧ Real.log (3085 : ℝ) ≤ 10043 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (61700 / 37) 11 20 0 (4637 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3085 12 20 0 (10043 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore4_main (hRH : RiemannHypothesis) :
    (33189 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3085,
        Real.exp (-(n : ℝ) / (61700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((61700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((61700 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      186051 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore4_roots.2.2]
  have hs :
    Real.sqrt ((61700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((61700 / 37) * (37 / 20)) +
        21 / 20 ≤
      18603 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore4_roots.2.2, gammaAnalyticMore4_logs.2]
  have hz :
    Real.sqrt (61700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (61700 / 37) + 2469 / 800 ≤
      15361 / 1000 := by
    linarith only [gammaAnalyticMore4_roots.2.1, gammaAnalyticMore4_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 61700 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      408359 / 10000) (e := 78619 / 500000) (p := 186051 / 1000) (s := 18603 / 1000) (z :=
      15361 / 1000) (F := 33189 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore4_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (61700 / 37 : ℝ) * (37 / 20) = 3085 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore4_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (61700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61700 / 37 : ℝ)) ≤
      41213 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 204179 / 5000) (T := 408359 / 10000) (Z := 4637 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticMore4_roots.1 gammaAnalyticMore4_roots.2.1
      gammaAnalyticMore4_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore4_power : (61700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1541 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 4 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore4_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5071 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (508 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3085 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5071 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3085) (x := 61700 / 37) (H := 508 / 5) (R := 204179 / 5000)
      (W := 1541 / 100000) (F := 33189 / 1000) (U := 41213 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore4_power (gammaAnalyticMore4_main hGRH.riemann)
      (gammaAnalyticMore4_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 5. -/
theorem gammaAnalyticMore5_roots :
    ((81817 / 2000 : ℝ) ≤ Real.sqrt (61920 / 37 : ℝ) ∧
      Real.sqrt (61920 / 37 : ℝ) ≤ 204543 / 5000 ∧ Real.sqrt (3096 : ℝ) ≤ 278209 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 5. -/
theorem gammaAnalyticMore5_logs :
    Real.log (61920 / 37 : ℝ) ≤ 74227 / 10000 ∧ Real.log (3096 : ℝ) ≤ 80379 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (61920 / 37) 11 20 0 (74227 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3096 12 20 0 (80379 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore5_main (hRH : RiemannHypothesis) :
    (33251 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3096,
        Real.exp (-(n : ℝ) / (61920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61920 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((61920 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((61920 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      93271 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore5_roots.2.2]
  have hs :
    Real.sqrt ((61920 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((61920 / 37) * (37 / 20)) +
        21 / 20 ≤
      9307 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore5_roots.2.2, gammaAnalyticMore5_logs.2]
  have hz :
    Real.sqrt (61920 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (61920 / 37) + 2469 / 800 ≤
      1537 / 100 := by
    linarith only [gammaAnalyticMore5_roots.2.1, gammaAnalyticMore5_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 61920 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      204543 / 5000) (e := 78619 / 500000) (p := 93271 / 500) (s := 9307 / 500) (z := 1537 / 100)
      (F := 33251 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore5_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (61920 / 37 : ℝ) * (37 / 20) = 3096 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore5_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (61920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (61920 / 37 : ℝ)) ≤
      8257 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 81817 / 2000) (T := 204543 / 5000) (Z := 74227 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore5_roots.1 gammaAnalyticMore5_roots.2.1
      gammaAnalyticMore5_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore5_power : (61920 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 769 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 5 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore5_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (508 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10179 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3096 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 508 / 5)]
  apply
    reject_03_of_analytic_caps (B := 3096) (x := 61920 / 37) (H := 10179 / 100) (R := 81817 / 2000)
      (W := 769 / 50000) (F := 33251 / 1000) (U := 8257 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore5_power (gammaAnalyticMore5_main hGRH.riemann)
      (gammaAnalyticMore5_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 6. -/
theorem gammaAnalyticMore6_roots :
    ((204939 / 5000 : ℝ) ≤ Real.sqrt (1680 : ℝ) ∧
      Real.sqrt (1680 : ℝ) ≤ 409879 / 10000 ∧ Real.sqrt (3108 : ℝ) ≤ 111499 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 6. -/
theorem gammaAnalyticMore6_logs :
    Real.log (1680 : ℝ) ≤ 37133 / 5000 ∧ Real.log (3108 : ℝ) ≤ 40209 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1680) 11 20 0 (37133 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3108 12 20 0 (40209 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore6_main (hRH : RiemannHypothesis) :
    (33317 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3108,
        Real.exp (-(n : ℝ) / (1680)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (1680 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((1680) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1680) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      187077 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore6_roots.2.2]
  have hs :
    Real.sqrt ((1680 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((1680) * (37 / 20)) +
        21 / 20 ≤
      18627 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore6_roots.2.2, gammaAnalyticMore6_logs.2]
  have hz :
    Real.sqrt (1680 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1680) + 2469 / 800 ≤
      15379 / 1000 := by
    linarith only [gammaAnalyticMore6_roots.2.1, gammaAnalyticMore6_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1680) (y := 37 / 20) (h := 2 / 35) (r := 409879 / 10000)
      (e := 78619 / 500000) (p := 187077 / 1000) (s := 18627 / 1000) (z := 15379 / 1000) (F :=
      33317 / 1000) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore6_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1680 : ℝ) * (37 / 20) = 3108 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore6_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1680)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (1680 : ℝ)) ≤
      10341 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 204939 / 5000) (T := 409879 / 10000) (Z := 37133 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore6_roots.1 gammaAnalyticMore6_roots.2.1
      gammaAnalyticMore6_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore6_power : (1680 : ℝ) ^ (-9 / 16 : ℝ) ≤ 767 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 6 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore6_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10179 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10199 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3108 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10179 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3108) (x := 1680) (H := 10199 / 100) (R := 204939 / 5000) (W :=
      767 / 50000) (F := 33317 / 1000) (U := 10341 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore6_power (gammaAnalyticMore6_main hGRH.riemann)
      (gammaAnalyticMore6_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 7. -/
theorem gammaAnalyticMore7_roots :
    ((102667 / 2500 : ℝ) ≤ Real.sqrt (62400 / 37 : ℝ) ∧
      Real.sqrt (62400 / 37 : ℝ) ≤ 410669 / 10000 ∧ Real.sqrt (3120 : ℝ) ≤ 55857 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 7. -/
theorem gammaAnalyticMore7_logs :
    Real.log (62400 / 37 : ℝ) ≤ 14861 / 2000 ∧ Real.log (3120 : ℝ) ≤ 10057 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (62400 / 37) 11 20 0 (14861 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3120 12 20 0 (10057 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore7_main (hRH : RiemannHypothesis) :
    (4173 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3120,
        Real.exp (-(n : ℝ) / (62400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (62400 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((62400 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((62400 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      46903 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore7_roots.2.2]
  have hs :
    Real.sqrt ((62400 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((62400 / 37) * (37 / 20)) +
        21 / 20 ≤
      18639 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore7_roots.2.2, gammaAnalyticMore7_logs.2]
  have hz :
    Real.sqrt (62400 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (62400 / 37) + 2469 / 800 ≤
      15389 / 1000 := by
    linarith only [gammaAnalyticMore7_roots.2.1, gammaAnalyticMore7_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 62400 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      410669 / 10000) (e := 78619 / 500000) (p := 46903 / 250) (s := 18639 / 1000) (z :=
      15389 / 1000) (F := 4173 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore7_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (62400 / 37 : ℝ) * (37 / 20) = 3120 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore7_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (62400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (62400 / 37 : ℝ)) ≤
      20721 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 102667 / 2500) (T := 410669 / 10000) (Z := 14861 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore7_roots.1 gammaAnalyticMore7_roots.2.1
      gammaAnalyticMore7_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore7_power : (62400 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1531 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 7 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore7_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10199 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10219 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3120 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10199 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3120) (x := 62400 / 37) (H := 10219 / 100) (R := 102667 / 2500)
      (W := 1531 / 100000) (F := 4173 / 125) (U := 20721 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore7_power (gammaAnalyticMore7_main hGRH.riemann)
      (gammaAnalyticMore7_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 8. -/
theorem gammaAnalyticMore8_roots :
    ((411457 / 10000 : ℝ) ≤ Real.sqrt (62640 / 37 : ℝ) ∧
      Real.sqrt (62640 / 37 : ℝ) ≤ 205729 / 5000 ∧ Real.sqrt (3132 : ℝ) ≤ 559643 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 8. -/
theorem gammaAnalyticMore8_logs :
    Real.log (62640 / 37 : ℝ) ≤ 74343 / 10000 ∧ Real.log (3132 : ℝ) ≤ 16099 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (62640 / 37) 11 20 0 (74343 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3132 12 20 0 (16099 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore8_main (hRH : RiemannHypothesis) :
    (669 / 20 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3132,
        Real.exp (-(n : ℝ) / (62640 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (62640 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((62640 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((62640 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      94073 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore8_roots.2.2]
  have hs :
    Real.sqrt ((62640 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((62640 / 37) * (37 / 20)) +
        21 / 20 ≤
      4663 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore8_roots.2.2, gammaAnalyticMore8_logs.2]
  have hz :
    Real.sqrt (62640 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (62640 / 37) + 2469 / 800 ≤
      7699 / 500 := by
    linarith only [gammaAnalyticMore8_roots.2.1, gammaAnalyticMore8_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 62640 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      205729 / 5000) (e := 78619 / 500000) (p := 94073 / 500) (s := 4663 / 250) (z := 7699 / 500)
      (F := 669 / 20) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore8_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (62640 / 37 : ℝ) * (37 / 20) = 3132 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore8_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (62640 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (62640 / 37 : ℝ)) ≤
      41521 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 411457 / 10000) (T := 205729 / 5000) (Z := 74343 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore8_roots.1 gammaAnalyticMore8_roots.2.1
      gammaAnalyticMore8_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore8_power : (62640 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 191 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 8 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore8_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10219 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10239 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3132 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10219 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3132) (x := 62640 / 37) (H := 10239 / 100) (R :=
      411457 / 10000) (W := 191 / 12500) (F := 669 / 20) (U := 41521 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore8_power (gammaAnalyticMore8_main hGRH.riemann)
      (gammaAnalyticMore8_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 9. -/
theorem gammaAnalyticMore9_roots :
    ((41231 / 1000 : ℝ) ≤ Real.sqrt (1700 : ℝ) ∧
      Real.sqrt (1700 : ℝ) ≤ 412311 / 10000 ∧ Real.sqrt (3145 : ℝ) ≤ 560803 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 9. -/
theorem gammaAnalyticMore9_logs :
    Real.log (1700 : ℝ) ≤ 4649 / 625 ∧ Real.log (3145 : ℝ) ≤ 10067 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1700) 11 20 0 (4649 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3145 12 20 0 (10067 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore9_main (hRH : RiemannHypothesis) :
    (16761 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3145,
        Real.exp (-(n : ℝ) / (1700)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (1700 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((1700) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1700) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      7549 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore9_roots.2.2]
  have hs :
    Real.sqrt ((1700 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((1700) * (37 / 20)) +
        21 / 20 ≤
      3733 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore9_roots.2.2, gammaAnalyticMore9_logs.2]
  have hz :
    Real.sqrt (1700 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1700) + 2469 / 800 ≤ 1926 / 125 := by
    linarith only [gammaAnalyticMore9_roots.2.1, gammaAnalyticMore9_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1700) (y := 37 / 20) (h := 2 / 35) (r := 412311 / 10000)
      (e := 78619 / 500000) (p := 7549 / 40) (s := 3733 / 200) (z := 1926 / 125) (F := 16761 / 500)
      (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      gammaAnalyticMore9_roots.2.1 gamma_analytic100_exp hp hs hz (by norm_num only)
      (by norm_num only) (by norm_num only)
  norm_num only [show (1700 : ℝ) * (37 / 20) = 3145 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore9_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1700)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (1700 : ℝ)) ≤
      8321 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 41231 / 1000) (T := 412311 / 10000) (Z := 4649 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticMore9_roots.1 gammaAnalyticMore9_roots.2.1
      gammaAnalyticMore9_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore9_power : (1700 : ℝ) ^ (-9 / 16 : ℝ) ≤ 381 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 9 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore9_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10239 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10261 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3145 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10239 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3145) (x := 1700) (H := 10261 / 100) (R := 41231 / 1000) (W :=
      381 / 25000) (F := 16761 / 500) (U := 8321 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore9_power (gammaAnalyticMore9_main hGRH.riemann)
      (gammaAnalyticMore9_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 10. -/
theorem gammaAnalyticMore10_roots :
    ((413161 / 10000 : ℝ) ≤ Real.sqrt (63160 / 37 : ℝ) ∧
      Real.sqrt (63160 / 37 : ℝ) ≤ 206581 / 5000 ∧ Real.sqrt (3158 : ℝ) ≤ 561961 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 10. -/
theorem gammaAnalyticMore10_logs :
    Real.log (63160 / 37 : ℝ) ≤ 37213 / 5000 ∧ Real.log (3158 : ℝ) ≤ 80577 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (63160 / 37) 11 20 0 (37213 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3158 12 20 0 (80577 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore10_main (hRH : RiemannHypothesis) :
    (16797 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3158,
        Real.exp (-(n : ℝ) / (63160 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (63160 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((63160 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((63160 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      189303 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore10_roots.2.2]
  have hs :
    Real.sqrt ((63160 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((63160 / 37) * (37 / 20)) +
        21 / 20 ≤
      9339 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore10_roots.2.2, gammaAnalyticMore10_logs.2]
  have hz :
    Real.sqrt (63160 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (63160 / 37) + 2469 / 800 ≤
      7709 / 500 := by
    linarith only [gammaAnalyticMore10_roots.2.1, gammaAnalyticMore10_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 63160 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      206581 / 5000) (e := 78619 / 500000) (p := 189303 / 1000) (s := 9339 / 500) (z := 7709 / 500)
      (F := 16797 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore10_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (63160 / 37 : ℝ) * (37 / 20) = 3158 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore10_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (63160 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (63160 / 37 : ℝ)) ≤
      4169 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 413161 / 10000) (T := 206581 / 5000) (Z := 37213 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore10_roots.1
      gammaAnalyticMore10_roots.2.1 gammaAnalyticMore10_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore10_power : (63160 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1521 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 10 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore10_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10261 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10283 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3158 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10261 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3158) (x := 63160 / 37) (H := 10283 / 100) (R :=
      413161 / 10000) (W := 1521 / 100000) (F := 16797 / 500) (U := 4169 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore10_power (gammaAnalyticMore10_main hGRH.riemann)
      (gammaAnalyticMore10_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 11. -/
theorem gammaAnalyticMore11_roots :
    ((103519 / 2500 : ℝ) ≤ Real.sqrt (63440 / 37 : ℝ) ∧
      Real.sqrt (63440 / 37 : ℝ) ≤ 414077 / 10000 ∧ Real.sqrt (3172 : ℝ) ≤ 281603 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 11. -/
theorem gammaAnalyticMore11_logs :
    Real.log (63440 / 37 : ℝ) ≤ 7447 / 1000 ∧ Real.log (3172 : ℝ) ≤ 40311 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (63440 / 37) 11 20 0 (7447 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3172 12 20 0 (40311 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore11_main (hRH : RiemannHypothesis) :
    (33671 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3172,
        Real.exp (-(n : ℝ) / (63440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (63440 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((63440 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((63440 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      7597 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore11_roots.2.2]
  have hs :
    Real.sqrt ((63440 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((63440 / 37) * (37 / 20)) +
        21 / 20 ≤
      18693 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore11_roots.2.2, gammaAnalyticMore11_logs.2]
  have hz :
    Real.sqrt (63440 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (63440 / 37) + 2469 / 800 ≤
      3857 / 250 := by
    linarith only [gammaAnalyticMore11_roots.2.1, gammaAnalyticMore11_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 63440 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      414077 / 10000) (e := 78619 / 500000) (p := 7597 / 40) (s := 18693 / 1000) (z := 3857 / 250)
      (F := 33671 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore11_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (63440 / 37 : ℝ) * (37 / 20) = 3172 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore11_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (63440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (63440 / 37 : ℝ)) ≤
      41781 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 103519 / 2500) (T := 414077 / 10000) (Z := 7447 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore11_roots.1
      gammaAnalyticMore11_roots.2.1 gammaAnalyticMore11_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore11_power : (63440 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1517 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 11 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore11_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10283 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5153 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3172 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10283 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3172) (x := 63440 / 37) (H := 5153 / 50) (R := 103519 / 2500)
      (W := 1517 / 100000) (F := 33671 / 1000) (U := 41781 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore11_power (gammaAnalyticMore11_main hGRH.riemann)
      (gammaAnalyticMore11_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 12. -/
theorem gammaAnalyticMore12_roots :
    ((414989 / 10000 : ℝ) ≤ Real.sqrt (63720 / 37 : ℝ) ∧
      Real.sqrt (63720 / 37 : ℝ) ≤ 41499 / 1000 ∧ Real.sqrt (3186 : ℝ) ≤ 564447 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 12. -/
theorem gammaAnalyticMore12_logs :
    Real.log (63720 / 37 : ℝ) ≤ 37257 / 5000 ∧ Real.log (3186 : ℝ) ≤ 40333 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (63720 / 37) 11 20 0 (37257 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3186 12 20 0 (40333 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore12_main (hRH : RiemannHypothesis) :
    (8437 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3186,
        Real.exp (-(n : ℝ) / (63720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (63720 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((63720 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((63720 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      190547 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore12_roots.2.2]
  have hs :
    Real.sqrt ((63720 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((63720 / 37) * (37 / 20)) +
        21 / 20 ≤
      18707 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore12_roots.2.2, gammaAnalyticMore12_logs.2]
  have hz :
    Real.sqrt (63720 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (63720 / 37) + 2469 / 800 ≤
      15439 / 1000 := by
    linarith only [gammaAnalyticMore12_roots.2.1, gammaAnalyticMore12_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 63720 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      41499 / 1000) (e := 78619 / 500000) (p := 190547 / 1000) (s := 18707 / 1000) (z :=
      15439 / 1000) (F := 8437 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore12_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (63720 / 37 : ℝ) * (37 / 20) = 3186 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore12_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (63720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (63720 / 37 : ℝ)) ≤
      5234 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 414989 / 10000) (T := 41499 / 1000) (Z := 37257 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore12_roots.1
      gammaAnalyticMore12_roots.2.1 gammaAnalyticMore12_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore12_power : (63720 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1513 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 12 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore12_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5153 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10329 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3186 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5153 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3186) (x := 63720 / 37) (H := 10329 / 100) (R :=
      414989 / 10000) (W := 1513 / 100000) (F := 8437 / 250) (U := 5234 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore12_power (gammaAnalyticMore12_main hGRH.riemann)
      (gammaAnalyticMore12_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 13. -/
theorem gammaAnalyticMore13_roots :
    ((4159 / 100 : ℝ) ≤ Real.sqrt (64000 / 37 : ℝ) ∧
      Real.sqrt (64000 / 37 : ℝ) ≤ 415901 / 10000 ∧ Real.sqrt (3200 : ℝ) ≤ 282843 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 13. -/
theorem gammaAnalyticMore13_logs :
    Real.log (64000 / 37 : ℝ) ≤ 37279 / 5000 ∧ Real.log (3200 : ℝ) ≤ 8071 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (64000 / 37) 11 20 0 (37279 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3200 12 20 0 (8071 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore13_main (hRH : RiemannHypothesis) :
    (1353 / 40 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3200,
        Real.exp (-(n : ℝ) / (64000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (64000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((64000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((64000 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      191169 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore13_roots.2.2]
  have hs :
    Real.sqrt ((64000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((64000 / 37) * (37 / 20)) +
        21 / 20 ≤
      18721 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore13_roots.2.2, gammaAnalyticMore13_logs.2]
  have hz :
    Real.sqrt (64000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (64000 / 37) + 2469 / 800 ≤
      309 / 20 := by
    linarith only [gammaAnalyticMore13_roots.2.1, gammaAnalyticMore13_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 64000 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      415901 / 10000) (e := 78619 / 500000) (p := 191169 / 1000) (s := 18721 / 1000) (z := 309 / 20)
      (F := 1353 / 40) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore13_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (64000 / 37 : ℝ) * (37 / 20) = 3200 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore13_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (64000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (64000 / 37 : ℝ)) ≤
      20981 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 4159 / 100) (T := 415901 / 10000) (Z := 37279 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore13_roots.1
      gammaAnalyticMore13_roots.2.1 gammaAnalyticMore13_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore13_power : (64000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1509 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 13 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore13_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10329 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10353 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3200 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10329 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3200) (x := 64000 / 37) (H := 10353 / 100) (R := 4159 / 100)
      (W := 1509 / 100000) (F := 1353 / 40) (U := 20981 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore13_power (gammaAnalyticMore13_main hGRH.riemann)
      (gammaAnalyticMore13_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 14. -/
theorem gammaAnalyticMore14_roots :
    ((416873 / 10000 : ℝ) ≤ Real.sqrt (64300 / 37 : ℝ) ∧
      Real.sqrt (64300 / 37 : ℝ) ≤ 208437 / 5000 ∧ Real.sqrt (3215 : ℝ) ≤ 56701 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 14. -/
theorem gammaAnalyticMore14_logs :
    Real.log (64300 / 37 : ℝ) ≤ 18651 / 2500 ∧ Real.log (3215 : ℝ) ≤ 20189 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (64300 / 37) 11 20 0 (18651 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3215 12 20 0 (20189 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore14_main (hRH : RiemannHypothesis) :
    (33907 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3215,
        Real.exp (-(n : ℝ) / (64300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (64300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((64300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((64300 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      95917 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore14_roots.2.2]
  have hs :
    Real.sqrt ((64300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((64300 / 37) * (37 / 20)) +
        21 / 20 ≤
      18737 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore14_roots.2.2, gammaAnalyticMore14_logs.2]
  have hz :
    Real.sqrt (64300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (64300 / 37) + 2469 / 800 ≤
      15461 / 1000 := by
    linarith only [gammaAnalyticMore14_roots.2.1, gammaAnalyticMore14_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 64300 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      208437 / 5000) (e := 78619 / 500000) (p := 95917 / 500) (s := 18737 / 1000) (z :=
      15461 / 1000) (F := 33907 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore14_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (64300 / 37 : ℝ) * (37 / 20) = 3215 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore14_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (64300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (64300 / 37 : ℝ)) ≤
      42059 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 416873 / 10000) (T := 208437 / 5000) (Z := 18651 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticMore14_roots.1
      gammaAnalyticMore14_roots.2.1 gammaAnalyticMore14_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore14_power : (64300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 301 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 14 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore14_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10353 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10377 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3215 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10353 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3215) (x := 64300 / 37) (H := 10377 / 100) (R :=
      416873 / 10000) (W := 301 / 20000) (F := 33907 / 1000) (U := 42059 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore14_power (gammaAnalyticMore14_main hGRH.riemann)
      (gammaAnalyticMore14_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 15. -/
theorem gammaAnalyticMore15_roots :
    ((83569 / 2000 : ℝ) ≤ Real.sqrt (64600 / 37 : ℝ) ∧
      Real.sqrt (64600 / 37 : ℝ) ≤ 208923 / 5000 ∧ Real.sqrt (3230 : ℝ) ≤ 568331 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 15. -/
theorem gammaAnalyticMore15_logs :
    Real.log (64600 / 37 : ℝ) ≤ 74651 / 10000 ∧ Real.log (3230 : ℝ) ≤ 80803 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (64600 / 37) 11 20 0 (74651 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3230 12 20 0 (80803 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore15_main (hRH : RiemannHypothesis) :
    (33989 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3230,
        Real.exp (-(n : ℝ) / (64600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (64600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((64600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((64600 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      96249 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore15_roots.2.2]
  have hs :
    Real.sqrt ((64600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((64600 / 37) * (37 / 20)) +
        21 / 20 ≤
      2344 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore15_roots.2.2, gammaAnalyticMore15_logs.2]
  have hz :
    Real.sqrt (64600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (64600 / 37) + 2469 / 800 ≤
      1934 / 125 := by
    linarith only [gammaAnalyticMore15_roots.2.1, gammaAnalyticMore15_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 64600 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      208923 / 5000) (e := 78619 / 500000) (p := 96249 / 500) (s := 2344 / 125) (z := 1934 / 125)
      (F := 33989 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore15_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (64600 / 37 : ℝ) * (37 / 20) = 3230 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore15_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (64600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (64600 / 37 : ℝ)) ≤
      8431 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 83569 / 2000) (T := 208923 / 5000) (Z := 74651 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore15_roots.1
      gammaAnalyticMore15_roots.2.1 gammaAnalyticMore15_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore15_power : (64600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1501 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 15 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore15_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10377 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5201 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3230 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10377 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3230) (x := 64600 / 37) (H := 5201 / 50) (R := 83569 / 2000)
      (W := 1501 / 100000) (F := 33989 / 1000) (U := 8431 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore15_power (gammaAnalyticMore15_main hGRH.riemann)
      (gammaAnalyticMore15_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 16. -/
theorem gammaAnalyticMore16_roots :
    ((209439 / 5000 : ℝ) ≤ Real.sqrt (64920 / 37 : ℝ) ∧
      Real.sqrt (64920 / 37 : ℝ) ≤ 418879 / 10000 ∧ Real.sqrt (3246 : ℝ) ≤ 569737 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 16. -/
theorem gammaAnalyticMore16_logs :
    Real.log (64920 / 37 : ℝ) ≤ 747 / 100 ∧ Real.log (3246 : ℝ) ≤ 20213 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (64920 / 37) 11 20 0 (747 / 100) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3246 12 20 0 (20213 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore16_main (hRH : RiemannHypothesis) :
    (8519 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3246,
        Real.exp (-(n : ℝ) / (64920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (64920 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((64920 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((64920 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      193207 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore16_roots.2.2]
  have hs :
    Real.sqrt ((64920 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((64920 / 37) * (37 / 20)) +
        21 / 20 ≤
      2346 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore16_roots.2.2, gammaAnalyticMore16_logs.2]
  have hz :
    Real.sqrt (64920 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (64920 / 37) + 2469 / 800 ≤
      3871 / 250 := by
    linarith only [gammaAnalyticMore16_roots.2.1, gammaAnalyticMore16_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 64920 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      418879 / 10000) (e := 78619 / 500000) (p := 193207 / 1000) (s := 2346 / 125) (z := 3871 / 250)
      (F := 8519 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore16_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (64920 / 37 : ℝ) * (37 / 20) = 3246 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore16_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (64920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (64920 / 37 : ℝ)) ≤
      21129 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 209439 / 5000) (T := 418879 / 10000) (Z := 747 / 100)
      (by norm_num only) (by norm_num only) gammaAnalyticMore16_roots.1
      gammaAnalyticMore16_roots.2.1 gammaAnalyticMore16_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore16_power : (64920 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1497 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 16 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore16_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5201 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10429 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3246 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5201 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3246) (x := 64920 / 37) (H := 10429 / 100) (R := 209439 / 5000)
      (W := 1497 / 100000) (F := 8519 / 250) (U := 21129 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore16_power (gammaAnalyticMore16_main hGRH.riemann)
      (gammaAnalyticMore16_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 17. -/
theorem gammaAnalyticMore17_roots :
    ((419909 / 10000 : ℝ) ≤ Real.sqrt (65240 / 37 : ℝ) ∧
      Real.sqrt (65240 / 37 : ℝ) ≤ 41991 / 1000 ∧ Real.sqrt (3262 : ℝ) ≤ 28557 / 500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 17. -/
theorem gammaAnalyticMore17_logs :
    Real.log (65240 / 37 : ℝ) ≤ 299 / 40 ∧ Real.log (3262 : ℝ) ≤ 80901 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (65240 / 37) 11 20 0 (299 / 40) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3262 12 20 0 (80901 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore17_main (hRH : RiemannHypothesis) :
    (34163 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3262,
        Real.exp (-(n : ℝ) / (65240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (65240 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((65240 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((65240 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      38783 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore17_roots.2.2]
  have hs :
    Real.sqrt ((65240 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((65240 / 37) * (37 / 20)) +
        21 / 20 ≤
      2348 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore17_roots.2.2, gammaAnalyticMore17_logs.2]
  have hz :
    Real.sqrt (65240 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (65240 / 37) + 2469 / 800 ≤
      1937 / 125 := by
    linarith only [gammaAnalyticMore17_roots.2.1, gammaAnalyticMore17_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 65240 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      41991 / 1000) (e := 78619 / 500000) (p := 38783 / 200) (s := 2348 / 125) (z := 1937 / 125)
      (F := 34163 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore17_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (65240 / 37 : ℝ) * (37 / 20) = 3262 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore17_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (65240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (65240 / 37 : ℝ)) ≤
      42361 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 419909 / 10000) (T := 41991 / 1000) (Z := 299 / 40)
      (by norm_num only) (by norm_num only) gammaAnalyticMore17_roots.1
      gammaAnalyticMore17_roots.2.1 gammaAnalyticMore17_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore17_power : (65240 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1493 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 17 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore17_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10429 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2091 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3262 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10429 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3262) (x := 65240 / 37) (H := 2091 / 20) (R := 419909 / 10000)
      (W := 1493 / 100000) (F := 34163 / 1000) (U := 42361 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticMore17_power (gammaAnalyticMore17_main hGRH.riemann)
      (gammaAnalyticMore17_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 18. -/
theorem gammaAnalyticMore18_roots :
    ((210501 / 5000 : ℝ) ≤ Real.sqrt (65580 / 37 : ℝ) ∧
      Real.sqrt (65580 / 37 : ℝ) ≤ 421003 / 10000 ∧ Real.sqrt (3279 : ℝ) ≤ 286313 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 18. -/
theorem gammaAnalyticMore18_logs :
    Real.log (65580 / 37 : ℝ) ≤ 37401 / 5000 ∧ Real.log (3279 : ℝ) ≤ 80953 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (65580 / 37) 11 20 0 (37401 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3279 12 20 0 (80953 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore18_main (hRH : RiemannHypothesis) :
    (6851 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3279,
        Real.exp (-(n : ℝ) / (65580 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (65580 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((65580 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((65580 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      194667 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore18_roots.2.2]
  have hs :
    Real.sqrt ((65580 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((65580 / 37) * (37 / 20)) +
        21 / 20 ≤
      18801 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore18_roots.2.2, gammaAnalyticMore18_logs.2]
  have hz :
    Real.sqrt (65580 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (65580 / 37) + 2469 / 800 ≤
      15509 / 1000 := by
    linarith only [gammaAnalyticMore18_roots.2.1, gammaAnalyticMore18_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 65580 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      421003 / 10000) (e := 78619 / 500000) (p := 194667 / 1000) (s := 18801 / 1000) (z :=
      15509 / 1000) (F := 6851 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticMore18_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (65580 / 37 : ℝ) * (37 / 20) = 3279 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore18_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (65580 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (65580 / 37 : ℝ)) ≤
      42469 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 210501 / 5000) (T := 421003 / 10000) (Z := 37401 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore18_roots.1
      gammaAnalyticMore18_roots.2.1 gammaAnalyticMore18_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore18_power : (65580 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1489 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 18 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore18_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2091 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10483 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3279 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2091 / 20)]
  apply
    reject_03_of_analytic_caps (B := 3279) (x := 65580 / 37) (H := 10483 / 100) (R := 210501 / 5000)
      (W := 1489 / 100000) (F := 6851 / 200) (U := 42469 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore18_power (gammaAnalyticMore18_main hGRH.riemann)
      (gammaAnalyticMore18_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 19. -/
theorem gammaAnalyticMore19_roots :
    ((105523 / 2500 : ℝ) ≤ Real.sqrt (65920 / 37 : ℝ) ∧
      Real.sqrt (65920 / 37 : ℝ) ≤ 422093 / 10000 ∧ Real.sqrt (3296 : ℝ) ≤ 574109 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 19. -/
theorem gammaAnalyticMore19_logs :
    Real.log (65920 / 37 : ℝ) ≤ 74853 / 10000 ∧ Real.log (3296 : ℝ) ≤ 16201 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (65920 / 37) 11 20 0 (74853 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3296 12 20 0 (16201 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticMore19_main (hRH : RiemannHypothesis) :
    (17173 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3296,
        Real.exp (-(n : ℝ) / (65920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (65920 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((65920 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((65920 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      97709 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore19_roots.2.2]
  have hs :
    Real.sqrt ((65920 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((65920 / 37) * (37 / 20)) +
        21 / 20 ≤
      9409 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticMore19_roots.2.2, gammaAnalyticMore19_logs.2]
  have hz :
    Real.sqrt (65920 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (65920 / 37) + 2469 / 800 ≤
      15521 / 1000 := by
    linarith only [gammaAnalyticMore19_roots.2.1, gammaAnalyticMore19_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 65920 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      422093 / 10000) (e := 78619 / 500000) (p := 97709 / 500) (s := 9409 / 500) (z := 15521 / 1000)
      (F := 17173 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticMore19_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (65920 / 37 : ℝ) * (37 / 20) = 3296 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticMore19_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (65920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (65920 / 37 : ℝ)) ≤
      21289 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 105523 / 2500) (T := 422093 / 10000) (Z := 74853 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticMore19_roots.1
      gammaAnalyticMore19_roots.2.1 gammaAnalyticMore19_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticMore19_power : (65920 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 371 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 19 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticMore19_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10483 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1051 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3296 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10483 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3296) (x := 65920 / 37) (H := 1051 / 10) (R := 105523 / 2500)
      (W := 371 / 25000) (F := 17173 / 500) (U := 21289 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticMore19_power (gammaAnalyticMore19_main hGRH.riemann)
      (gammaAnalyticMore19_principal hGRH.riemann)
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
