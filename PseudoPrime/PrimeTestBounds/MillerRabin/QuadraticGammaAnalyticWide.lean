/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticMoreCombined

/-! # Analytic Gamma cells after logarithmic scale 100.21 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact root caps for analytic cell 0. -/
theorem gammaAnalyticWide0_roots :
    ((423179 / 10000 : ℝ) ≤ Real.sqrt (66260 / 37 : ℝ) ∧
      Real.sqrt (66260 / 37 : ℝ) ≤ 21159 / 500 ∧ Real.sqrt (3313 : ℝ) ≤ 575587 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 0. -/
theorem gammaAnalyticWide0_logs :
    Real.log (66260 / 37 : ℝ) ≤ 14981 / 2000 ∧ Real.log (3313 : ℝ) ≤ 81057 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (66260 / 37) 11 20 0 (14981 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3313 12 20 0 (81057 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide0_main (hRH : RiemannHypothesis) :
    (17219 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3313,
        Real.exp (-(n : ℝ) / (66260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (66260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 17941) * ((66260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((66260 / 37) * (37 / 20)) + 1) / (1000 / 17941) +
        1839 / 1000 ≤
      39221 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide0_roots.2.2]
  have hs :
    Real.sqrt ((66260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((66260 / 37) * (37 / 20)) +
        21 / 20 ≤
      3767 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide0_roots.2.2, gammaAnalyticWide0_logs.2]
  have hz :
    Real.sqrt (66260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (66260 / 37) + 2469 / 800 ≤
      7767 / 500 := by
    linarith only [gammaAnalyticWide0_roots.2.1, gammaAnalyticWide0_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 66260 / 37) (y := 37 / 20) (h := 1000 / 17941) (r :=
      21159 / 500) (e := 78619 / 500000) (p := 39221 / 200) (s := 3767 / 200) (z := 7767 / 500)
      (F := 17219 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide0_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (66260 / 37 : ℝ) * (37 / 20) = 3313 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide0_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (66260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (66260 / 37 : ℝ)) ≤
      21343 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 423179 / 10000) (T := 21159 / 500) (Z := 14981 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide0_roots.1 gammaAnalyticWide0_roots.2.1
      gammaAnalyticWide0_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide0_power : (66260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 37 / 2500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 0 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide0_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1051 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5269 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3313 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1051 / 10)]
  apply
    reject_03_of_analytic_caps (B := 3313) (x := 66260 / 37) (H := 5269 / 50) (R := 423179 / 10000)
      (W := 37 / 2500) (F := 17219 / 500) (U := 21343 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide0_power (gammaAnalyticWide0_main hGRH.riemann)
      (gammaAnalyticWide0_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 1. -/
theorem gammaAnalyticWide1_roots :
    ((424327 / 10000 : ℝ) ≤ Real.sqrt (66620 / 37 : ℝ) ∧
      Real.sqrt (66620 / 37 : ℝ) ≤ 53041 / 1250 ∧ Real.sqrt (3331 : ℝ) ≤ 577149 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 1. -/
theorem gammaAnalyticWide1_logs :
    Real.log (66620 / 37 : ℝ) ≤ 74959 / 10000 ∧ Real.log (3331 : ℝ) ≤ 81111 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (66620 / 37) 11 20 0 (74959 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3331 12 20 0 (81111 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide1_main (hRH : RiemannHypothesis) :
    (6907 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3331,
        Real.exp (-(n : ℝ) / (66620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (66620 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 35931) * ((66620 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((66620 / 37) * (37 / 20)) + 1) / (2000 / 35931) +
        1839 / 1000 ≤
      49223 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide1_roots.2.2]
  have hs :
    Real.sqrt ((66620 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((66620 / 37) * (37 / 20)) +
        21 / 20 ≤
      18853 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide1_roots.2.2, gammaAnalyticWide1_logs.2]
  have hz :
    Real.sqrt (66620 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (66620 / 37) + 2469 / 800 ≤
      15547 / 1000 := by
    linarith only [gammaAnalyticWide1_roots.2.1, gammaAnalyticWide1_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 66620 / 37) (y := 37 / 20) (h := 2000 / 35931) (r :=
      53041 / 1250) (e := 78619 / 500000) (p := 49223 / 250) (s := 18853 / 1000) (z := 15547 / 1000)
      (F := 6907 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide1_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (66620 / 37 : ℝ) * (37 / 20) = 3331 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide1_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (66620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (66620 / 37 : ℝ)) ≤
      214 / 5 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 424327 / 10000) (T := 53041 / 1250) (Z := 74959 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide1_roots.1 gammaAnalyticWide1_roots.2.1
      gammaAnalyticWide1_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide1_power : (66620 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 369 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 1 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide1_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5269 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10567 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3331 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5269 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3331) (x := 66620 / 37) (H := 10567 / 100) (R :=
      424327 / 10000) (W := 369 / 25000) (F := 6907 / 200) (U := 214 / 5) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide1_power (gammaAnalyticWide1_main hGRH.riemann)
      (gammaAnalyticWide1_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 2. -/
theorem gammaAnalyticWide2_roots :
    ((26592 / 625 : ℝ) ≤ Real.sqrt (66980 / 37 : ℝ) ∧
      Real.sqrt (66980 / 37 : ℝ) ≤ 425473 / 10000 ∧ Real.sqrt (3349 : ℝ) ≤ 289353 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 2. -/
theorem gammaAnalyticWide2_logs :
    Real.log (66980 / 37 : ℝ) ≤ 75013 / 10000 ∧ Real.log (3349 : ℝ) ≤ 16233 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (66980 / 37) 11 20 0 (75013 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3349 12 20 0 (16233 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide2_main (hRH : RiemannHypothesis) :
    (34631 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3349,
        Real.exp (-(n : ℝ) / (66980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (66980 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (100 / 1799) * ((66980 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((66980 / 37) * (37 / 20)) + 1) / (100 / 1799) +
        1839 / 1000 ≤
      197677 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide2_roots.2.2]
  have hs :
    Real.sqrt ((66980 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((66980 / 37) * (37 / 20)) +
        21 / 20 ≤
      1887 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide2_roots.2.2, gammaAnalyticWide2_logs.2]
  have hz :
    Real.sqrt (66980 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (66980 / 37) + 2469 / 800 ≤
      389 / 25 := by
    linarith only [gammaAnalyticWide2_roots.2.1, gammaAnalyticWide2_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 66980 / 37) (y := 37 / 20) (h := 100 / 1799) (r :=
      425473 / 10000) (e := 78619 / 500000) (p := 197677 / 1000) (s := 1887 / 100) (z := 389 / 25)
      (F := 34631 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide2_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (66980 / 37 : ℝ) * (37 / 20) = 3349 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide2_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (66980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (66980 / 37 : ℝ)) ≤
      21457 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 26592 / 625) (T := 425473 / 10000) (Z := 75013 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide2_roots.1 gammaAnalyticWide2_roots.2.1
      gammaAnalyticWide2_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide2_power : (66980 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1471 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 2 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide2_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10567 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2649 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3349 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10567 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3349) (x := 66980 / 37) (H := 2649 / 25) (R := 26592 / 625)
      (W := 1471 / 100000) (F := 34631 / 1000) (U := 21457 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide2_power (gammaAnalyticWide2_main hGRH.riemann)
      (gammaAnalyticWide2_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 3. -/
theorem gammaAnalyticWide3_roots :
    ((426677 / 10000 : ℝ) ≤ Real.sqrt (67360 / 37 : ℝ) ∧
      Real.sqrt (67360 / 37 : ℝ) ≤ 213339 / 5000 ∧ Real.sqrt (3368 : ℝ) ≤ 116069 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 3. -/
theorem gammaAnalyticWide3_logs :
    Real.log (67360 / 37 : ℝ) ≤ 75069 / 10000 ∧ Real.log (3368 : ℝ) ≤ 81221 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (67360 / 37) 11 20 0 (75069 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3368 12 20 0 (81221 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide3_main (hRH : RiemannHypothesis) :
    (34733 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3368,
        Real.exp (-(n : ℝ) / (67360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (67360 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 36029) * ((67360 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((67360 / 37) * (37 / 20)) + 1) / (2000 / 36029) +
        1839 / 1000 ≤
      39701 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide3_roots.2.2]
  have hs :
    Real.sqrt ((67360 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((67360 / 37) * (37 / 20)) +
        21 / 20 ≤
      18889 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide3_roots.2.2, gammaAnalyticWide3_logs.2]
  have hz :
    Real.sqrt (67360 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (67360 / 37) + 2469 / 800 ≤
      7787 / 500 := by
    linarith only [gammaAnalyticWide3_roots.2.1, gammaAnalyticWide3_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 67360 / 37) (y := 37 / 20) (h := 2000 / 36029) (r :=
      213339 / 5000) (e := 78619 / 500000) (p := 39701 / 200) (s := 18889 / 1000) (z := 7787 / 500)
      (F := 34733 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide3_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (67360 / 37 : ℝ) * (37 / 20) = 3368 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide3_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (67360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (67360 / 37 : ℝ)) ≤
      43033 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 426677 / 10000) (T := 213339 / 5000) (Z := 75069 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide3_roots.1 gammaAnalyticWide3_roots.2.1
      gammaAnalyticWide3_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide3_power : (67360 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1467 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 3 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide3_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2649 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10627 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3368 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2649 / 25)]
  apply
    reject_03_of_analytic_caps (B := 3368) (x := 67360 / 37) (H := 10627 / 100) (R :=
      426677 / 10000) (W := 1467 / 100000) (F := 34733 / 1000) (U := 43033 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide3_power (gammaAnalyticWide3_main hGRH.riemann)
      (gammaAnalyticWide3_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 4. -/
theorem gammaAnalyticWide4_roots :
    ((427879 / 10000 : ℝ) ≤ Real.sqrt (67740 / 37 : ℝ) ∧
      Real.sqrt (67740 / 37 : ℝ) ≤ 10697 / 250 ∧ Real.sqrt (3387 : ℝ) ≤ 29099 / 500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 4. -/
theorem gammaAnalyticWide4_logs :
    Real.log (67740 / 37 : ℝ) ≤ 37563 / 5000 ∧ Real.log (3387 : ℝ) ≤ 81277 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (67740 / 37) 11 20 0 (37563 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3387 12 20 0 (81277 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide4_main (hRH : RiemannHypothesis) :
    (17417 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3387,
        Real.exp (-(n : ℝ) / (67740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (67740 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 72163) * ((67740 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((67740 / 37) * (37 / 20)) + 1) / (4000 / 72163) +
        1839 / 1000 ≤
      49833 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide4_roots.2.2]
  have hs :
    Real.sqrt ((67740 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((67740 / 37) * (37 / 20)) +
        21 / 20 ≤
      18907 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide4_roots.2.2, gammaAnalyticWide4_logs.2]
  have hz :
    Real.sqrt (67740 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (67740 / 37) + 2469 / 800 ≤
      3897 / 250 := by
    linarith only [gammaAnalyticWide4_roots.2.1, gammaAnalyticWide4_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 67740 / 37) (y := 37 / 20) (h := 4000 / 72163) (r :=
      10697 / 250) (e := 78619 / 500000) (p := 49833 / 250) (s := 18907 / 1000) (z := 3897 / 250)
      (F := 17417 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide4_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (67740 / 37 : ℝ) * (37 / 20) = 3387 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide4_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (67740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (67740 / 37 : ℝ)) ≤
      43153 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 427879 / 10000) (T := 10697 / 250) (Z := 37563 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide4_roots.1 gammaAnalyticWide4_roots.2.1
      gammaAnalyticWide4_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide4_power : (67740 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 731 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 4 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide4_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10627 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5329 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3387 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10627 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3387) (x := 67740 / 37) (H := 5329 / 50) (R := 427879 / 10000)
      (W := 731 / 50000) (F := 17417 / 500) (U := 43153 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide4_power (gammaAnalyticWide4_main hGRH.riemann)
      (gammaAnalyticWide4_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 5. -/
theorem gammaAnalyticWide5_roots :
    ((429141 / 10000 : ℝ) ≤ Real.sqrt (68140 / 37 : ℝ) ∧
      Real.sqrt (68140 / 37 : ℝ) ≤ 214571 / 5000 ∧ Real.sqrt (3407 : ℝ) ≤ 36481 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 5. -/
theorem gammaAnalyticWide5_logs :
    Real.log (68140 / 37 : ℝ) ≤ 15037 / 2000 ∧ Real.log (3407 : ℝ) ≤ 10167 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (68140 / 37) 11 20 0 (15037 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3407 12 20 0 (10167 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide5_main (hRH : RiemannHypothesis) :
    (1747 / 50 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3407,
        Real.exp (-(n : ℝ) / (68140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (68140 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 18067) * ((68140 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((68140 / 37) * (37 / 20)) + 1) / (1000 / 18067) +
        1839 / 1000 ≤
      200201 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide5_roots.2.2]
  have hs :
    Real.sqrt ((68140 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((68140 / 37) * (37 / 20)) +
        21 / 20 ≤
      18927 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide5_roots.2.2, gammaAnalyticWide5_logs.2]
  have hz :
    Real.sqrt (68140 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (68140 / 37) + 2469 / 800 ≤
      7801 / 500 := by
    linarith only [gammaAnalyticWide5_roots.2.1, gammaAnalyticWide5_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 68140 / 37) (y := 37 / 20) (h := 1000 / 18067) (r :=
      214571 / 5000) (e := 78619 / 500000) (p := 200201 / 1000) (s := 18927 / 1000) (z :=
      7801 / 500) (F := 1747 / 50) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide5_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (68140 / 37 : ℝ) * (37 / 20) = 3407 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide5_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (68140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (68140 / 37 : ℝ)) ≤
      21639 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 429141 / 10000) (T := 214571 / 5000) (Z := 15037 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide5_roots.1 gammaAnalyticWide5_roots.2.1
      gammaAnalyticWide5_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide5_power : (68140 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1457 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 5 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide5_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5329 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1069 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3407 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5329 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3407) (x := 68140 / 37) (H := 1069 / 10) (R := 429141 / 10000)
      (W := 1457 / 100000) (F := 1747 / 50) (U := 21639 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide5_power (gammaAnalyticWide5_main hGRH.riemann)
      (gammaAnalyticWide5_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 6. -/
theorem gammaAnalyticWide6_roots :
    ((430461 / 10000 : ℝ) ≤ Real.sqrt (68560 / 37 : ℝ) ∧
      Real.sqrt (68560 / 37 : ℝ) ≤ 215231 / 5000 ∧ Real.sqrt (3428 : ℝ) ≤ 146373 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 6. -/
theorem gammaAnalyticWide6_logs :
    Real.log (68560 / 37 : ℝ) ≤ 37623 / 5000 ∧ Real.log (3428 : ℝ) ≤ 40699 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (68560 / 37) 11 20 0 (37623 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3428 12 20 0 (40699 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide6_main (hRH : RiemannHypothesis) :
    (8763 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3428,
        Real.exp (-(n : ℝ) / (68560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (68560 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (200 / 3619) * ((68560 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((68560 / 37) * (37 / 20)) + 1) / (200 / 3619) +
        1839 / 1000 ≤
      25139 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide6_roots.2.2]
  have hs :
    Real.sqrt ((68560 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((68560 / 37) * (37 / 20)) +
        21 / 20 ≤
      18947 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide6_roots.2.2, gammaAnalyticWide6_logs.2]
  have hz :
    Real.sqrt (68560 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (68560 / 37) + 2469 / 800 ≤
      15617 / 1000 := by
    linarith only [gammaAnalyticWide6_roots.2.1, gammaAnalyticWide6_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 68560 / 37) (y := 37 / 20) (h := 200 / 3619) (r :=
      215231 / 5000) (e := 78619 / 500000) (p := 25139 / 125) (s := 18947 / 1000) (z :=
      15617 / 1000) (F := 8763 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide6_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (68560 / 37 : ℝ) * (37 / 20) = 3428 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide6_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (68560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (68560 / 37 : ℝ)) ≤
      43409 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 430461 / 10000) (T := 215231 / 5000) (Z := 37623 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide6_roots.1 gammaAnalyticWide6_roots.2.1
      gammaAnalyticWide6_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide6_power : (68560 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 363 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 6 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide6_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1069 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2681 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3428 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1069 / 10)]
  apply
    reject_03_of_analytic_caps (B := 3428) (x := 68560 / 37) (H := 2681 / 25) (R := 430461 / 10000)
      (W := 363 / 25000) (F := 8763 / 250) (U := 43409 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide6_power (gammaAnalyticWide6_main hGRH.riemann)
      (gammaAnalyticWide6_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 7. -/
theorem gammaAnalyticWide7_roots :
    ((5398 / 125 : ℝ) ≤ Real.sqrt (69000 / 37 : ℝ) ∧
      Real.sqrt (69000 / 37 : ℝ) ≤ 431841 / 10000 ∧ Real.sqrt (3450 : ℝ) ≤ 73421 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 7. -/
theorem gammaAnalyticWide7_logs :
    Real.log (69000 / 37 : ℝ) ≤ 7531 / 1000 ∧ Real.log (3450 : ℝ) ≤ 40731 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (69000 / 37) 11 20 0 (7531 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3450 12 20 0 (40731 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide7_main (hRH : RiemannHypothesis) :
    (4396 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3450,
        Real.exp (-(n : ℝ) / (69000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (69000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 18123) * ((69000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((69000 / 37) * (37 / 20)) + 1) / (1000 / 18123) +
        1839 / 1000 ≤
      40413 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide7_roots.2.2]
  have hs :
    Real.sqrt ((69000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((69000 / 37) * (37 / 20)) +
        21 / 20 ≤
      2371 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide7_roots.2.2, gammaAnalyticWide7_logs.2]
  have hz :
    Real.sqrt (69000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (69000 / 37) + 2469 / 800 ≤
      15633 / 1000 := by
    linarith only [gammaAnalyticWide7_roots.2.1, gammaAnalyticWide7_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 69000 / 37) (y := 37 / 20) (h := 1000 / 18123) (r :=
      431841 / 10000) (e := 78619 / 500000) (p := 40413 / 200) (s := 2371 / 125) (z := 15633 / 1000)
      (F := 4396 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide7_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (69000 / 37 : ℝ) * (37 / 20) = 3450 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide7_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (69000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (69000 / 37 : ℝ)) ≤
      43547 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 5398 / 125) (T := 431841 / 10000) (Z := 7531 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide7_roots.1 gammaAnalyticWide7_roots.2.1
      gammaAnalyticWide7_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide7_power : (69000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1447 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 7 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide7_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2681 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5379 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3450 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2681 / 25)]
  apply
    reject_03_of_analytic_caps (B := 3450) (x := 69000 / 37) (H := 5379 / 50) (R := 5398 / 125)
      (W := 1447 / 100000) (F := 4396 / 125) (U := 43547 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide7_power (gammaAnalyticWide7_main hGRH.riemann)
      (gammaAnalyticWide7_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 8. -/
theorem gammaAnalyticWide8_roots :
    ((86643 / 2000 : ℝ) ≤ Real.sqrt (69440 / 37 : ℝ) ∧
      Real.sqrt (69440 / 37 : ℝ) ≤ 27076 / 625 ∧ Real.sqrt (3472 : ℝ) ≤ 589237 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 8. -/
theorem gammaAnalyticWide8_logs :
    Real.log (69440 / 37 : ℝ) ≤ 37687 / 5000 ∧ Real.log (3472 : ℝ) ≤ 3261 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (69440 / 37) 11 20 0 (37687 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3472 12 20 0 (3261 / 400) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide8_main (hRH : RiemannHypothesis) :
    (8821 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3472,
        Real.exp (-(n : ℝ) / (69440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (69440 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 72611) * ((69440 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((69440 / 37) * (37 / 20)) + 1) / (4000 / 72611) +
        1839 / 1000 ≤
      203017 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide8_roots.2.2]
  have hs :
    Real.sqrt ((69440 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((69440 / 37) * (37 / 20)) +
        21 / 20 ≤
      18989 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide8_roots.2.2, gammaAnalyticWide8_logs.2]
  have hz :
    Real.sqrt (69440 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (69440 / 37) + 2469 / 800 ≤
      15649 / 1000 := by
    linarith only [gammaAnalyticWide8_roots.2.1, gammaAnalyticWide8_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 69440 / 37) (y := 37 / 20) (h := 4000 / 72611) (r :=
      27076 / 625) (e := 78619 / 500000) (p := 203017 / 1000) (s := 18989 / 1000) (z :=
      15649 / 1000) (F := 8821 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide8_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (69440 / 37 : ℝ) * (37 / 20) = 3472 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide8_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (69440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (69440 / 37 : ℝ)) ≤
      43683 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 86643 / 2000) (T := 27076 / 625) (Z := 37687 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide8_roots.1 gammaAnalyticWide8_roots.2.1
      gammaAnalyticWide8_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide8_power : (69440 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 721 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 8 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide8_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5379 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5397 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3472 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5379 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3472) (x := 69440 / 37) (H := 5397 / 50) (R := 86643 / 2000)
      (W := 721 / 50000) (F := 8821 / 250) (U := 43683 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide8_power (gammaAnalyticWide8_main hGRH.riemann)
      (gammaAnalyticWide8_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 9. -/
theorem gammaAnalyticWide9_roots :
    ((54331 / 1250 : ℝ) ≤ Real.sqrt (69900 / 37 : ℝ) ∧
      Real.sqrt (69900 / 37 : ℝ) ≤ 434649 / 10000 ∧ Real.sqrt (3495 : ℝ) ≤ 295593 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 9. -/
theorem gammaAnalyticWide9_logs :
    Real.log (69900 / 37 : ℝ) ≤ 943 / 125 ∧ Real.log (3495 : ℝ) ≤ 81591 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (69900 / 37) 11 20 0 (943 / 125) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3495 12 20 0 (81591 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide9_main (hRH : RiemannHypothesis) :
    (8851 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3495,
        Real.exp (-(n : ℝ) / (69900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (69900 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (400 / 7273) * ((69900 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((69900 / 37) * (37 / 20)) + 1) / (400 / 7273) +
        1839 / 1000 ≤
      20401 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide9_roots.2.2]
  have hs :
    Real.sqrt ((69900 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((69900 / 37) * (37 / 20)) +
        21 / 20 ≤
      19011 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide9_roots.2.2, gammaAnalyticWide9_logs.2]
  have hz :
    Real.sqrt (69900 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (69900 / 37) + 2469 / 800 ≤
      3133 / 200 := by
    linarith only [gammaAnalyticWide9_roots.2.1, gammaAnalyticWide9_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 69900 / 37) (y := 37 / 20) (h := 400 / 7273) (r :=
      434649 / 10000) (e := 78619 / 500000) (p := 20401 / 100) (s := 19011 / 1000) (z := 3133 / 200)
      (F := 8851 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide9_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (69900 / 37 : ℝ) * (37 / 20) = 3495 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide9_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (69900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (69900 / 37 : ℝ)) ≤
      21913 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 54331 / 1250) (T := 434649 / 10000) (Z := 943 / 125)
      (by norm_num only) (by norm_num only) gammaAnalyticWide9_roots.1 gammaAnalyticWide9_roots.2.1
      gammaAnalyticWide9_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide9_power : (69900 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 359 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 9 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide9_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5397 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1083 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3495 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5397 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3495) (x := 69900 / 37) (H := 1083 / 10) (R := 54331 / 1250)
      (W := 359 / 25000) (F := 8851 / 250) (U := 21913 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide9_power (gammaAnalyticWide9_main hGRH.riemann)
      (gammaAnalyticWide9_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 10. -/
theorem gammaAnalyticWide10_roots :
    ((17443 / 400 : ℝ) ≤ Real.sqrt (70360 / 37 : ℝ) ∧
      Real.sqrt (70360 / 37 : ℝ) ≤ 109019 / 2500 ∧ Real.sqrt (3518 : ℝ) ≤ 74141 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 10. -/
theorem gammaAnalyticWide10_logs :
    Real.log (70360 / 37 : ℝ) ≤ 15101 / 2000 ∧ Real.log (3518 : ℝ) ≤ 81657 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (70360 / 37) 11 20 0 (15101 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3518 12 20 0 (81657 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide10_main (hRH : RiemannHypothesis) :
    (1421 / 40 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3518,
        Real.exp (-(n : ℝ) / (70360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (70360 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 72849) * ((70360 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((70360 / 37) * (37 / 20)) + 1) / (4000 / 72849) +
        1839 / 1000 ≤
      205001 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide10_roots.2.2]
  have hs :
    Real.sqrt ((70360 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((70360 / 37) * (37 / 20)) +
        21 / 20 ≤
      19033 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide10_roots.2.2, gammaAnalyticWide10_logs.2]
  have hz :
    Real.sqrt (70360 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (70360 / 37) + 2469 / 800 ≤
      15681 / 1000 := by
    linarith only [gammaAnalyticWide10_roots.2.1, gammaAnalyticWide10_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 70360 / 37) (y := 37 / 20) (h := 4000 / 72849) (r :=
      109019 / 2500) (e := 78619 / 500000) (p := 205001 / 1000) (s := 19033 / 1000) (z :=
      15681 / 1000) (F := 1421 / 40) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide10_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (70360 / 37 : ℝ) * (37 / 20) = 3518 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide10_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (70360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (70360 / 37 : ℝ)) ≤
      5496 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 17443 / 400) (T := 109019 / 2500) (Z := 15101 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide10_roots.1
      gammaAnalyticWide10_roots.2.1 gammaAnalyticWide10_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide10_power : (70360 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1431 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 10 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide10_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1083 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5433 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3518 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1083 / 10)]
  apply
    reject_03_of_analytic_caps (B := 3518) (x := 70360 / 37) (H := 5433 / 50) (R := 17443 / 400)
      (W := 1431 / 100000) (F := 1421 / 40) (U := 5496 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide10_power (gammaAnalyticWide10_main hGRH.riemann)
      (gammaAnalyticWide10_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 11. -/
theorem gammaAnalyticWide11_roots :
    ((10939 / 250 : ℝ) ≤ Real.sqrt (70840 / 37 : ℝ) ∧
      Real.sqrt (70840 / 37 : ℝ) ≤ 437561 / 10000 ∧ Real.sqrt (3542 : ℝ) ≤ 148787 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 11. -/
theorem gammaAnalyticWide11_logs :
    Real.log (70840 / 37 : ℝ) ≤ 75573 / 10000 ∧ Real.log (3542 : ℝ) ≤ 3269 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (70840 / 37) 11 20 0 (75573 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3542 12 20 0 (3269 / 400) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide11_main (hRH : RiemannHypothesis) :
    (713 / 20 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3542,
        Real.exp (-(n : ℝ) / (70840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (70840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (160 / 2919) * ((70840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((70840 / 37) * (37 / 20)) + 1) / (160 / 2919) +
        1839 / 1000 ≤
      103017 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide11_roots.2.2]
  have hs :
    Real.sqrt ((70840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((70840 / 37) * (37 / 20)) +
        21 / 20 ≤
      3811 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide11_roots.2.2, gammaAnalyticWide11_logs.2]
  have hz :
    Real.sqrt (70840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (70840 / 37) + 2469 / 800 ≤
      7849 / 500 := by
    linarith only [gammaAnalyticWide11_roots.2.1, gammaAnalyticWide11_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 70840 / 37) (y := 37 / 20) (h := 160 / 2919) (r :=
      437561 / 10000) (e := 78619 / 500000) (p := 103017 / 500) (s := 3811 / 200) (z := 7849 / 500)
      (F := 713 / 20) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide11_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (70840 / 37 : ℝ) * (37 / 20) = 3542 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide11_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (70840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (70840 / 37 : ℝ)) ≤
      8823 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 10939 / 250) (T := 437561 / 10000) (Z := 75573 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide11_roots.1
      gammaAnalyticWide11_roots.2.1 gammaAnalyticWide11_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide11_power : (70840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 713 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 11 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide11_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5433 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2726 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3542 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5433 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3542) (x := 70840 / 37) (H := 2726 / 25) (R := 10939 / 250)
      (W := 713 / 50000) (F := 713 / 20) (U := 8823 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide11_power (gammaAnalyticWide11_main hGRH.riemann)
      (gammaAnalyticWide11_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 12. -/
theorem gammaAnalyticWide12_roots :
    ((5488 / 125 : ℝ) ≤ Real.sqrt (71320 / 37 : ℝ) ∧
      Real.sqrt (71320 / 37 : ℝ) ≤ 439041 / 10000 ∧ Real.sqrt (3566 : ℝ) ≤ 14929 / 250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 12. -/
theorem gammaAnalyticWide12_logs :
    Real.log (71320 / 37 : ℝ) ≤ 75641 / 10000 ∧ Real.log (3566 : ℝ) ≤ 5112 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (71320 / 37) 11 20 0 (75641 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3566 12 20 0 (5112 / 625) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide12_main (hRH : RiemannHypothesis) :
    (17887 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3566,
        Real.exp (-(n : ℝ) / (71320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (71320 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 73101) * ((71320 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((71320 / 37) * (37 / 20)) + 1) / (4000 / 73101) +
        1839 / 1000 ≤
      41413 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide12_roots.2.2]
  have hs :
    Real.sqrt ((71320 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((71320 / 37) * (37 / 20)) +
        21 / 20 ≤
      9539 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide12_roots.2.2, gammaAnalyticWide12_logs.2]
  have hz :
    Real.sqrt (71320 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (71320 / 37) + 2469 / 800 ≤
      3143 / 200 := by
    linarith only [gammaAnalyticWide12_roots.2.1, gammaAnalyticWide12_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 71320 / 37) (y := 37 / 20) (h := 4000 / 73101) (r :=
      439041 / 10000) (e := 78619 / 500000) (p := 41413 / 200) (s := 9539 / 500) (z := 3143 / 200)
      (F := 17887 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide12_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (71320 / 37 : ℝ) * (37 / 20) = 3566 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide12_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (71320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (71320 / 37 : ℝ)) ≤
      44263 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 5488 / 125) (T := 439041 / 10000) (Z := 75641 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide12_roots.1
      gammaAnalyticWide12_roots.2.1 gammaAnalyticWide12_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide12_power : (71320 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 71 / 5000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 12 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide12_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2726 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10941 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3566 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2726 / 25)]
  apply
    reject_03_of_analytic_caps (B := 3566) (x := 71320 / 37) (H := 10941 / 100) (R := 5488 / 125)
      (W := 71 / 5000) (F := 17887 / 500) (U := 44263 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide12_power (gammaAnalyticWide12_main hGRH.riemann)
      (gammaAnalyticWide12_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 13. -/
theorem gammaAnalyticWide13_roots :
    ((440577 / 10000 : ℝ) ≤ Real.sqrt (71820 / 37 : ℝ) ∧
      Real.sqrt (71820 / 37 : ℝ) ≤ 220289 / 5000 ∧ Real.sqrt (3591 : ℝ) ≤ 2397 / 40) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 13. -/
theorem gammaAnalyticWide13_logs :
    Real.log (71820 / 37 : ℝ) ≤ 75711 / 10000 ∧ Real.log (3591 : ℝ) ≤ 40931 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (71820 / 37) 11 20 0 (75711 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3591 12 20 0 (40931 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide13_main (hRH : RiemannHypothesis) :
    (4488 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3591,
        Real.exp (-(n : ℝ) / (71820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (71820 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (200 / 3661) * ((71820 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((71820 / 37) * (37 / 20)) + 1) / (200 / 3661) +
        1839 / 1000 ≤
      208137 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide13_roots.2.2]
  have hs :
    Real.sqrt ((71820 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((71820 / 37) * (37 / 20)) +
        21 / 20 ≤
      19101 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide13_roots.2.2, gammaAnalyticWide13_logs.2]
  have hz :
    Real.sqrt (71820 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (71820 / 37) + 2469 / 800 ≤
      3933 / 250 := by
    linarith only [gammaAnalyticWide13_roots.2.1, gammaAnalyticWide13_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 71820 / 37) (y := 37 / 20) (h := 200 / 3661) (r :=
      220289 / 5000) (e := 78619 / 500000) (p := 208137 / 1000) (s := 19101 / 1000) (z :=
      3933 / 250) (F := 4488 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide13_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (71820 / 37 : ℝ) * (37 / 20) = 3591 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide13_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (71820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (71820 / 37 : ℝ)) ≤
      8883 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 440577 / 10000) (T := 220289 / 5000) (Z := 75711 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide13_roots.1
      gammaAnalyticWide13_roots.2.1 gammaAnalyticWide13_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide13_power : (71820 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 283 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 13 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide13_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10941 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10981 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3591 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10941 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3591) (x := 71820 / 37) (H := 10981 / 100) (R :=
      440577 / 10000) (W := 283 / 20000) (F := 4488 / 125) (U := 8883 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide13_power (gammaAnalyticWide13_main hGRH.riemann)
      (gammaAnalyticWide13_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 14. -/
theorem gammaAnalyticWide14_roots :
    ((442169 / 10000 : ℝ) ≤ Real.sqrt (72340 / 37 : ℝ) ∧
      Real.sqrt (72340 / 37 : ℝ) ≤ 44217 / 1000 ∧ Real.sqrt (3617 : ℝ) ≤ 120283 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 14. -/
theorem gammaAnalyticWide14_logs :
    Real.log (72340 / 37 : ℝ) ≤ 75783 / 10000 ∧ Real.log (3617 : ℝ) ≤ 16387 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (72340 / 37) 11 20 0 (75783 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3617 12 20 0 (16387 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide14_main (hRH : RiemannHypothesis) :
    (18019 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3617,
        Real.exp (-(n : ℝ) / (72340 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (72340 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (50 / 917) * ((72340 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((72340 / 37) * (37 / 20)) + 1) / (50 / 917) +
        1839 / 1000 ≤
      837 / 4 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide14_roots.2.2]
  have hs :
    Real.sqrt ((72340 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((72340 / 37) * (37 / 20)) +
        21 / 20 ≤
      153 / 8 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide14_roots.2.2, gammaAnalyticWide14_logs.2]
  have hz :
    Real.sqrt (72340 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (72340 / 37) + 2469 / 800 ≤
      63 / 4 := by
    linarith only [gammaAnalyticWide14_roots.2.1, gammaAnalyticWide14_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 72340 / 37) (y := 37 / 20) (h := 50 / 917) (r :=
      44217 / 1000) (e := 78619 / 500000) (p := 837 / 4) (s := 153 / 8) (z := 63 / 4) (F :=
      18019 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide14_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (72340 / 37 : ℝ) * (37 / 20) = 3617 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide14_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (72340 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (72340 / 37 : ℝ)) ≤
      22287 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 442169 / 10000) (T := 44217 / 1000) (Z := 75783 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide14_roots.1
      gammaAnalyticWide14_roots.2.1 gammaAnalyticWide14_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide14_power : (72340 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1409 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 14 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide14_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10981 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11021 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3617 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10981 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3617) (x := 72340 / 37) (H := 11021 / 100) (R :=
      442169 / 10000) (W := 1409 / 100000) (F := 18019 / 500) (U := 22287 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide14_power (gammaAnalyticWide14_main hGRH.riemann)
      (gammaAnalyticWide14_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 15. -/
theorem gammaAnalyticWide15_roots :
    ((88751 / 2000 : ℝ) ≤ Real.sqrt (72860 / 37 : ℝ) ∧
      Real.sqrt (72860 / 37 : ℝ) ≤ 110939 / 2500 ∧ Real.sqrt (3643 : ℝ) ≤ 603573 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 15. -/
theorem gammaAnalyticWide15_logs :
    Real.log (72860 / 37 : ℝ) ≤ 37927 / 5000 ∧ Real.log (3643 : ℝ) ≤ 41003 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (72860 / 37) 11 20 0 (37927 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3643 12 20 0 (41003 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide15_main (hRH : RiemannHypothesis) :
    (36171 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3643,
        Real.exp (-(n : ℝ) / (72860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (72860 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 73493) * ((72860 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((72860 / 37) * (37 / 20)) + 1) / (4000 / 73493) +
        1839 / 1000 ≤
      105181 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide15_roots.2.2]
  have hs :
    Real.sqrt ((72860 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((72860 / 37) * (37 / 20)) +
        21 / 20 ≤
      19149 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide15_roots.2.2, gammaAnalyticWide15_logs.2]
  have hz :
    Real.sqrt (72860 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (72860 / 37) + 2469 / 800 ≤
      1971 / 125 := by
    linarith only [gammaAnalyticWide15_roots.2.1, gammaAnalyticWide15_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 72860 / 37) (y := 37 / 20) (h := 4000 / 73493) (r :=
      110939 / 2500) (e := 78619 / 500000) (p := 105181 / 500) (s := 19149 / 1000) (z := 1971 / 125)
      (F := 36171 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide15_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (72860 / 37 : ℝ) * (37 / 20) = 3643 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide15_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (72860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (72860 / 37 : ℝ)) ≤
      44731 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 88751 / 2000) (T := 110939 / 2500) (Z := 37927 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide15_roots.1
      gammaAnalyticWide15_roots.2.1 gammaAnalyticWide15_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide15_power : (72860 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1403 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 15 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide15_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11021 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11061 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3643 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11021 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3643) (x := 72860 / 37) (H := 11061 / 100) (R := 88751 / 2000)
      (W := 1403 / 100000) (F := 36171 / 1000) (U := 44731 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide15_power (gammaAnalyticWide15_main hGRH.riemann)
      (gammaAnalyticWide15_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 16. -/
theorem gammaAnalyticWide16_roots :
    ((111349 / 2500 : ℝ) ≤ Real.sqrt (73400 / 37 : ℝ) ∧
      Real.sqrt (73400 / 37 : ℝ) ≤ 445397 / 10000 ∧ Real.sqrt (3670 : ℝ) ≤ 302903 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 16. -/
theorem gammaAnalyticWide16_logs :
    Real.log (73400 / 37 : ℝ) ≤ 9491 / 1250 ∧ Real.log (3670 : ℝ) ≤ 1026 / 125 := by
  have hc1 : Analysis.rationalLogIntervalCheck (73400 / 37) 11 20 0 (9491 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3670 12 20 0 (1026 / 125) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide16_main (hRH : RiemannHypothesis) :
    (36309 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3670,
        Real.exp (-(n : ℝ) / (73400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (73400 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 36813) * ((73400 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((73400 / 37) * (37 / 20)) + 1) / (2000 / 36813) +
        1839 / 1000 ≤
      211513 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide16_roots.2.2]
  have hs :
    Real.sqrt ((73400 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((73400 / 37) * (37 / 20)) +
        21 / 20 ≤
      9587 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide16_roots.2.2, gammaAnalyticWide16_logs.2]
  have hz :
    Real.sqrt (73400 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (73400 / 37) + 2469 / 800 ≤
      7893 / 500 := by
    linarith only [gammaAnalyticWide16_roots.2.1, gammaAnalyticWide16_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 73400 / 37) (y := 37 / 20) (h := 2000 / 36813) (r :=
      445397 / 10000) (e := 78619 / 500000) (p := 211513 / 1000) (s := 9587 / 500) (z := 7893 / 500)
      (F := 36309 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide16_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (73400 / 37 : ℝ) * (37 / 20) = 3670 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide16_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (73400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (73400 / 37 : ℝ)) ≤
      8979 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 111349 / 2500) (T := 445397 / 10000) (Z := 9491 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticWide16_roots.1
      gammaAnalyticWide16_roots.2.1 gammaAnalyticWide16_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide16_power : (73400 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1397 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 16 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide16_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11061 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11103 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3670 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11061 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3670) (x := 73400 / 37) (H := 11103 / 100) (R := 111349 / 2500)
      (W := 1397 / 100000) (F := 36309 / 1000) (U := 8979 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide16_power (gammaAnalyticWide16_main hGRH.riemann)
      (gammaAnalyticWide16_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 17. -/
theorem gammaAnalyticWide17_roots :
    ((111773 / 2500 : ℝ) ≤ Real.sqrt (73960 / 37 : ℝ) ∧
      Real.sqrt (73960 / 37 : ℝ) ≤ 447093 / 10000 ∧ Real.sqrt (3698 : ℝ) ≤ 38007 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 17. -/
theorem gammaAnalyticWide17_logs :
    Real.log (73960 / 37 : ℝ) ≤ 19001 / 2500 ∧ Real.log (3698 : ℝ) ≤ 20539 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (73960 / 37) 11 20 0 (19001 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3698 12 20 0 (20539 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide17_main (hRH : RiemannHypothesis) :
    (9113 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3698,
        Real.exp (-(n : ℝ) / (73960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (73960 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 36883) * ((73960 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((73960 / 37) * (37 / 20)) + 1) / (2000 / 36883) +
        1839 / 1000 ≤
      42541 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide17_roots.2.2]
  have hs :
    Real.sqrt ((73960 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((73960 / 37) * (37 / 20)) +
        21 / 20 ≤
      96 / 5 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide17_roots.2.2, gammaAnalyticWide17_logs.2]
  have hz :
    Real.sqrt (73960 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (73960 / 37) + 2469 / 800 ≤
      3161 / 200 := by
    linarith only [gammaAnalyticWide17_roots.2.1, gammaAnalyticWide17_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 73960 / 37) (y := 37 / 20) (h := 2000 / 36883) (r :=
      447093 / 10000) (e := 78619 / 500000) (p := 42541 / 200) (s := 96 / 5) (z := 3161 / 200) (F :=
      9113 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide17_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (73960 / 37 : ℝ) * (37 / 20) = 3698 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide17_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (73960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (73960 / 37 : ℝ)) ≤
      45063 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 111773 / 2500) (T := 447093 / 10000) (Z := 19001 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticWide17_roots.1
      gammaAnalyticWide17_roots.2.1 gammaAnalyticWide17_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide17_power : (73960 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1391 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 17 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide17_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11103 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5573 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3698 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11103 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3698) (x := 73960 / 37) (H := 5573 / 50) (R := 111773 / 2500)
      (W := 1391 / 100000) (F := 9113 / 250) (U := 45063 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide17_power (gammaAnalyticWide17_main hGRH.riemann)
      (gammaAnalyticWide17_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 18. -/
theorem gammaAnalyticWide18_roots :
    ((224391 / 5000 : ℝ) ≤ Real.sqrt (74520 / 37 : ℝ) ∧
      Real.sqrt (74520 / 37 : ℝ) ≤ 448783 / 10000 ∧ Real.sqrt (3726 : ℝ) ≤ 61041 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 18. -/
theorem gammaAnalyticWide18_logs :
    Real.log (74520 / 37 : ℝ) ≤ 951 / 125 ∧ Real.log (3726 : ℝ) ≤ 82231 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (74520 / 37) 11 20 0 (951 / 125) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3726 12 20 0 (82231 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide18_main (hRH : RiemannHypothesis) :
    (18297 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3726,
        Real.exp (-(n : ℝ) / (74520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (74520 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 36953) * ((74520 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((74520 / 37) * (37 / 20)) + 1) / (2000 / 36953) +
        1839 / 1000 ≤
      42779 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide18_roots.2.2]
  have hs :
    Real.sqrt ((74520 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((74520 / 37) * (37 / 20)) +
        21 / 20 ≤
      769 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide18_roots.2.2, gammaAnalyticWide18_logs.2]
  have hz :
    Real.sqrt (74520 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (74520 / 37) + 2469 / 800 ≤
      1978 / 125 := by
    linarith only [gammaAnalyticWide18_roots.2.1, gammaAnalyticWide18_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 74520 / 37) (y := 37 / 20) (h := 2000 / 36953) (r :=
      448783 / 10000) (e := 78619 / 500000) (p := 42779 / 200) (s := 769 / 40) (z := 1978 / 125)
      (F := 18297 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide18_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (74520 / 37 : ℝ) * (37 / 20) = 3726 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide18_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (74520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (74520 / 37 : ℝ)) ≤
      45231 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 224391 / 5000) (T := 448783 / 10000) (Z := 951 / 125)
      (by norm_num only) (by norm_num only) gammaAnalyticWide18_roots.1
      gammaAnalyticWide18_roots.2.1 gammaAnalyticWide18_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide18_power : (74520 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 693 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 18 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide18_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5573 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11189 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3726 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5573 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3726) (x := 74520 / 37) (H := 11189 / 100) (R := 224391 / 5000)
      (W := 693 / 50000) (F := 18297 / 500) (U := 45231 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide18_power (gammaAnalyticWide18_main hGRH.riemann)
      (gammaAnalyticWide18_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 19. -/
theorem gammaAnalyticWide19_roots :
    ((18021 / 400 : ℝ) ≤ Real.sqrt (75100 / 37 : ℝ) ∧
      Real.sqrt (75100 / 37 : ℝ) ≤ 225263 / 5000 ∧ Real.sqrt (3755 : ℝ) ≤ 612781 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 19. -/
theorem gammaAnalyticWide19_logs :
    Real.log (75100 / 37 : ℝ) ≤ 76157 / 10000 ∧ Real.log (3755 : ℝ) ≤ 82309 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (75100 / 37) 11 20 0 (76157 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3755 12 20 0 (82309 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide19_main (hRH : RiemannHypothesis) :
    (36741 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3755,
        Real.exp (-(n : ℝ) / (75100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (75100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 37023) * ((75100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((75100 / 37) * (37 / 20)) + 1) / (2000 / 37023) +
        1839 / 1000 ≤
      1721 / 8 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide19_roots.2.2]
  have hs :
    Real.sqrt ((75100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((75100 / 37) * (37 / 20)) +
        21 / 20 ≤
      19251 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide19_roots.2.2, gammaAnalyticWide19_logs.2]
  have hz :
    Real.sqrt (75100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (75100 / 37) + 2469 / 800 ≤
      15843 / 1000 := by
    linarith only [gammaAnalyticWide19_roots.2.1, gammaAnalyticWide19_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 75100 / 37) (y := 37 / 20) (h := 2000 / 37023) (r :=
      225263 / 5000) (e := 78619 / 500000) (p := 1721 / 8) (s := 19251 / 1000) (z := 15843 / 1000)
      (F := 36741 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide19_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (75100 / 37 : ℝ) * (37 / 20) = 3755 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide19_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (75100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (75100 / 37 : ℝ)) ≤
      9081 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 18021 / 400) (T := 225263 / 5000) (Z := 76157 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide19_roots.1
      gammaAnalyticWide19_roots.2.1 gammaAnalyticWide19_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide19_power : (75100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 69 / 5000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 19 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide19_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11189 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11233 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3755 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11189 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3755) (x := 75100 / 37) (H := 11233 / 100) (R := 18021 / 400)
      (W := 69 / 5000) (F := 36741 / 1000) (U := 9081 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide19_power (gammaAnalyticWide19_main hGRH.riemann)
      (gammaAnalyticWide19_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 20. -/
theorem gammaAnalyticWide20_roots :
    ((452321 / 10000 : ℝ) ≤ Real.sqrt (75700 / 37 : ℝ) ∧
      Real.sqrt (75700 / 37 : ℝ) ≤ 226161 / 5000 ∧ Real.sqrt (3785 : ℝ) ≤ 76903 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 20. -/
theorem gammaAnalyticWide20_logs :
    Real.log (75700 / 37 : ℝ) ≤ 76237 / 10000 ∧ Real.log (3785 : ℝ) ≤ 82389 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (75700 / 37) 11 20 0 (76237 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3785 12 20 0 (82389 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide20_main (hRH : RiemannHypothesis) :
    (9223 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3785,
        Real.exp (-(n : ℝ) / (75700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (75700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 74193) * ((75700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((75700 / 37) * (37 / 20)) + 1) / (4000 / 74193) +
        1839 / 1000 ≤
      43279 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide20_roots.2.2]
  have hs :
    Real.sqrt ((75700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((75700 / 37) * (37 / 20)) +
        21 / 20 ≤
      9639 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide20_roots.2.2, gammaAnalyticWide20_logs.2]
  have hz :
    Real.sqrt (75700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (75700 / 37) + 2469 / 800 ≤
      15863 / 1000 := by
    linarith only [gammaAnalyticWide20_roots.2.1, gammaAnalyticWide20_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 75700 / 37) (y := 37 / 20) (h := 4000 / 74193) (r :=
      226161 / 5000) (e := 78619 / 500000) (p := 43279 / 200) (s := 9639 / 500) (z := 15863 / 1000)
      (F := 9223 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide20_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (75700 / 37 : ℝ) * (37 / 20) = 3785 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide20_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (75700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (75700 / 37 : ℝ)) ≤
      45583 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 452321 / 10000) (T := 226161 / 5000) (Z := 76237 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide20_roots.1
      gammaAnalyticWide20_roots.2.1 gammaAnalyticWide20_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide20_power : (75700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1373 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 20 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide20_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11233 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11279 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3785 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11233 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3785) (x := 75700 / 37) (H := 11279 / 100) (R :=
      452321 / 10000) (W := 1373 / 100000) (F := 9223 / 250) (U := 45583 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide20_power (gammaAnalyticWide20_main hGRH.riemann)
      (gammaAnalyticWide20_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 21. -/
theorem gammaAnalyticWide21_roots :
    ((454169 / 10000 : ℝ) ≤ Real.sqrt (76320 / 37 : ℝ) ∧
      Real.sqrt (76320 / 37 : ℝ) ≤ 45417 / 1000 ∧ Real.sqrt (3816 : ℝ) ≤ 308869 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 21. -/
theorem gammaAnalyticWide21_logs :
    Real.log (76320 / 37 : ℝ) ≤ 38159 / 5000 ∧ Real.log (3816 : ℝ) ≤ 8247 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (76320 / 37) 12 20 0 (38159 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3816 12 20 0 (8247 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide21_main (hRH : RiemannHypothesis) :
    (4631 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3816,
        Real.exp (-(n : ℝ) / (76320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (76320 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 74347) * ((76320 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((76320 / 37) * (37 / 20)) + 1) / (4000 / 74347) +
        1839 / 1000 ≤
      43541 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide21_roots.2.2]
  have hs :
    Real.sqrt ((76320 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((76320 / 37) * (37 / 20)) +
        21 / 20 ≤
      3861 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide21_roots.2.2, gammaAnalyticWide21_logs.2]
  have hz :
    Real.sqrt (76320 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (76320 / 37) + 2469 / 800 ≤
      3971 / 250 := by
    linarith only [gammaAnalyticWide21_roots.2.1, gammaAnalyticWide21_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 76320 / 37) (y := 37 / 20) (h := 4000 / 74347) (r :=
      45417 / 1000) (e := 78619 / 500000) (p := 43541 / 200) (s := 3861 / 200) (z := 3971 / 250)
      (F := 4631 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide21_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (76320 / 37 : ℝ) * (37 / 20) = 3816 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide21_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (76320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (76320 / 37 : ℝ)) ≤
      45767 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 454169 / 10000) (T := 45417 / 1000) (Z := 38159 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide21_roots.1
      gammaAnalyticWide21_roots.2.1 gammaAnalyticWide21_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide21_power : (76320 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1367 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 21 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide21_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11279 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5663 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3816 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11279 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3816) (x := 76320 / 37) (H := 5663 / 50) (R := 454169 / 10000)
      (W := 1367 / 100000) (F := 4631 / 125) (U := 45767 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide21_power (gammaAnalyticWide21_main hGRH.riemann)
      (gammaAnalyticWide21_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 22. -/
theorem gammaAnalyticWide22_roots :
    ((45607 / 1000 : ℝ) ≤ Real.sqrt (2080 : ℝ) ∧
      Real.sqrt (2080 : ℝ) ≤ 456071 / 10000 ∧ Real.sqrt (3848 : ℝ) ≤ 620323 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 22. -/
theorem gammaAnalyticWide22_logs :
    Real.log (2080 : ℝ) ≤ 38201 / 5000 ∧ Real.log (3848 : ℝ) ≤ 41277 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2080) 12 20 0 (38201 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3848 12 20 0 (41277 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide22_main (hRH : RiemannHypothesis) :
    (4651 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3848,
        Real.exp (-(n : ℝ) / (2080)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (2080 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 74501) * ((2080) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2080) * (37 / 20)) + 1) / (4000 / 74501) +
        1839 / 1000 ≤
      109527 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide22_roots.2.2]
  have hs :
    Real.sqrt ((2080 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((2080) * (37 / 20)) +
        21 / 20 ≤
      9667 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide22_roots.2.2, gammaAnalyticWide22_logs.2]
  have hz :
    Real.sqrt (2080 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2080) + 2469 / 800 ≤ 3181 / 200 := by
    linarith only [gammaAnalyticWide22_roots.2.1, gammaAnalyticWide22_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2080) (y := 37 / 20) (h := 4000 / 74501) (r :=
      456071 / 10000) (e := 78619 / 500000) (p := 109527 / 500) (s := 9667 / 500) (z := 3181 / 200)
      (F := 4651 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide22_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2080 : ℝ) * (37 / 20) = 3848 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide22_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2080)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (2080 : ℝ)) ≤
      11489 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 45607 / 1000) (T := 456071 / 10000) (Z := 38201 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide22_roots.1
      gammaAnalyticWide22_roots.2.1 gammaAnalyticWide22_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide22_power : (2080 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1361 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 22 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide22_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5663 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5687 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3848 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5663 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3848) (x := 2080) (H := 5687 / 50) (R := 45607 / 1000) (W :=
      1361 / 100000) (F := 4651 / 125) (U := 11489 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide22_power (gammaAnalyticWide22_main hGRH.riemann)
      (gammaAnalyticWide22_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 23. -/
theorem gammaAnalyticWide23_roots :
    ((458021 / 10000 : ℝ) ≤ Real.sqrt (77620 / 37 : ℝ) ∧
      Real.sqrt (77620 / 37 : ℝ) ≤ 229011 / 5000 ∧ Real.sqrt (3881 : ℝ) ≤ 622977 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 23. -/
theorem gammaAnalyticWide23_logs :
    Real.log (77620 / 37 : ℝ) ≤ 76487 / 10000 ∧ Real.log (3881 : ℝ) ≤ 82639 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (77620 / 37) 12 20 0 (76487 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3881 12 20 0 (82639 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide23_main (hRH : RiemannHypothesis) :
    (9343 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3881,
        Real.exp (-(n : ℝ) / (77620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (77620 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 14931) * ((77620 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((77620 / 37) * (37 / 20)) + 1) / (800 / 14931) +
        1839 / 1000 ≤
      110221 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide23_roots.2.2]
  have hs :
    Real.sqrt ((77620 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((77620 / 37) * (37 / 20)) +
        21 / 20 ≤
      19363 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide23_roots.2.2, gammaAnalyticWide23_logs.2]
  have hz :
    Real.sqrt (77620 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (77620 / 37) + 2469 / 800 ≤
      7963 / 500 := by
    linarith only [gammaAnalyticWide23_roots.2.1, gammaAnalyticWide23_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 77620 / 37) (y := 37 / 20) (h := 800 / 14931) (r :=
      229011 / 5000) (e := 78619 / 500000) (p := 110221 / 500) (s := 19363 / 1000) (z := 7963 / 500)
      (F := 9343 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide23_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (77620 / 37 : ℝ) * (37 / 20) = 3881 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide23_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (77620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (77620 / 37 : ℝ)) ≤
      923 / 20 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 458021 / 10000) (T := 229011 / 5000) (Z := 76487 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide23_roots.1
      gammaAnalyticWide23_roots.2.1 gammaAnalyticWide23_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide23_power : (77620 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 677 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 23 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide23_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5687 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2856 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3881 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5687 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3881) (x := 77620 / 37) (H := 2856 / 25) (R := 458021 / 10000)
      (W := 677 / 50000) (F := 9343 / 250) (U := 923 / 20) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide23_power (gammaAnalyticWide23_main hGRH.riemann)
      (gammaAnalyticWide23_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 24. -/
theorem gammaAnalyticWide24_roots :
    ((460023 / 10000 : ℝ) ≤ Real.sqrt (78300 / 37 : ℝ) ∧
      Real.sqrt (78300 / 37 : ℝ) ≤ 57503 / 1250 ∧ Real.sqrt (3915 : ℝ) ≤ 6257 / 100) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 24. -/
theorem gammaAnalyticWide24_logs :
    Real.log (78300 / 37 : ℝ) ≤ 38287 / 5000 ∧ Real.log (3915 : ℝ) ≤ 41363 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (78300 / 37) 12 20 0 (38287 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3915 12 20 0 (41363 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide24_main (hRH : RiemannHypothesis) :
    (37541 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3915,
        Real.exp (-(n : ℝ) / (78300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (78300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 74823) * ((78300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((78300 / 37) * (37 / 20)) + 1) / (4000 / 74823) +
        1839 / 1000 ≤
      221869 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide24_roots.2.2]
  have hs :
    Real.sqrt ((78300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((78300 / 37) * (37 / 20)) +
        21 / 20 ≤
      2424 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide24_roots.2.2, gammaAnalyticWide24_logs.2]
  have hz :
    Real.sqrt (78300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (78300 / 37) + 2469 / 800 ≤
      3987 / 250 := by
    linarith only [gammaAnalyticWide24_roots.2.1, gammaAnalyticWide24_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 78300 / 37) (y := 37 / 20) (h := 4000 / 74823) (r :=
      57503 / 1250) (e := 78619 / 500000) (p := 221869 / 1000) (s := 2424 / 125) (z := 3987 / 250)
      (F := 37541 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide24_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (78300 / 37 : ℝ) * (37 / 20) = 3915 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide24_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (78300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (78300 / 37 : ℝ)) ≤
      927 / 20 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 460023 / 10000) (T := 57503 / 1250) (Z := 38287 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide24_roots.1
      gammaAnalyticWide24_roots.2.1 gammaAnalyticWide24_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide24_power : (78300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 337 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 24 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide24_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2856 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (459 / 4 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3915 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2856 / 25)]
  apply
    reject_03_of_analytic_caps (B := 3915) (x := 78300 / 37) (H := 459 / 4) (R := 460023 / 10000)
      (W := 337 / 25000) (F := 37541 / 1000) (U := 927 / 20) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide24_power (gammaAnalyticWide24_main hGRH.riemann)
      (gammaAnalyticWide24_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 25. -/
theorem gammaAnalyticWide25_roots :
    ((18483 / 400 : ℝ) ≤ Real.sqrt (79000 / 37 : ℝ) ∧
      Real.sqrt (79000 / 37 : ℝ) ≤ 115519 / 2500 ∧ Real.sqrt (3950 : ℝ) ≤ 628491 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 25. -/
theorem gammaAnalyticWide25_logs :
    Real.log (79000 / 37 : ℝ) ≤ 76663 / 10000 ∧ Real.log (3950 : ℝ) ≤ 16563 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (79000 / 37) 12 20 0 (76663 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3950 12 20 0 (16563 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide25_main (hRH : RiemannHypothesis) :
    (37713 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3950,
        Real.exp (-(n : ℝ) / (79000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (79000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 74991) * ((79000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((79000 / 37) * (37 / 20)) + 1) / (4000 / 74991) +
        1839 / 1000 ≤
      44667 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide25_roots.2.2]
  have hs :
    Real.sqrt ((79000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((79000 / 37) * (37 / 20)) +
        21 / 20 ≤
      19423 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide25_roots.2.2, gammaAnalyticWide25_logs.2]
  have hz :
    Real.sqrt (79000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (79000 / 37) + 2469 / 800 ≤
      15971 / 1000 := by
    linarith only [gammaAnalyticWide25_roots.2.1, gammaAnalyticWide25_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 79000 / 37) (y := 37 / 20) (h := 4000 / 74991) (r :=
      115519 / 2500) (e := 78619 / 500000) (p := 44667 / 200) (s := 19423 / 1000) (z :=
      15971 / 1000) (F := 37713 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide25_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (79000 / 37 : ℝ) * (37 / 20) = 3950 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide25_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (79000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (79000 / 37 : ℝ)) ≤
      23277 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 18483 / 400) (T := 115519 / 2500) (Z := 76663 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide25_roots.1
      gammaAnalyticWide25_roots.2.1 gammaAnalyticWide25_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide25_power : (79000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1341 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 25 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide25_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (459 / 4 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5763 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3950 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 459 / 4)]
  apply
    reject_03_of_analytic_caps (B := 3950) (x := 79000 / 37) (H := 5763 / 50) (R := 18483 / 400)
      (W := 1341 / 100000) (F := 37713 / 1000) (U := 23277 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide25_power (gammaAnalyticWide25_main hGRH.riemann)
      (gammaAnalyticWide25_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 26. -/
theorem gammaAnalyticWide26_roots :
    ((464117 / 10000 : ℝ) ≤ Real.sqrt (79700 / 37 : ℝ) ∧
      Real.sqrt (79700 / 37 : ℝ) ≤ 232059 / 5000 ∧ Real.sqrt (3985 : ℝ) ≤ 631269 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 26. -/
theorem gammaAnalyticWide26_logs :
    Real.log (79700 / 37 : ℝ) ≤ 4797 / 625 ∧ Real.log (3985 : ℝ) ≤ 82903 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (79700 / 37) 12 20 0 (4797 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3985 12 20 0 (82903 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide26_main (hRH : RiemannHypothesis) :
    (7577 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3985,
        Real.exp (-(n : ℝ) / (79700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (79700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (250 / 4697) * ((79700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((79700 / 37) * (37 / 20)) + 1) / (250 / 4697) +
        1839 / 1000 ≤
      112399 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide26_roots.2.2]
  have hs :
    Real.sqrt ((79700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((79700 / 37) * (37 / 20)) +
        21 / 20 ≤
      19453 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide26_roots.2.2, gammaAnalyticWide26_logs.2]
  have hz :
    Real.sqrt (79700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (79700 / 37) + 2469 / 800 ≤
      15993 / 1000 := by
    linarith only [gammaAnalyticWide26_roots.2.1, gammaAnalyticWide26_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 79700 / 37) (y := 37 / 20) (h := 250 / 4697) (r :=
      232059 / 5000) (e := 78619 / 500000) (p := 112399 / 500) (s := 19453 / 1000) (z :=
      15993 / 1000) (F := 7577 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide26_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (79700 / 37 : ℝ) * (37 / 20) = 3985 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide26_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (79700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (79700 / 37 : ℝ)) ≤
      46757 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 464117 / 10000) (T := 232059 / 5000) (Z := 4797 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticWide26_roots.1
      gammaAnalyticWide26_roots.2.1 gammaAnalyticWide26_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide26_power : (79700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 667 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 26 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide26_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5763 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5789 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3985 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5763 / 50)]
  apply
    reject_03_of_analytic_caps (B := 3985) (x := 79700 / 37) (H := 5789 / 50) (R := 464117 / 10000)
      (W := 667 / 50000) (F := 7577 / 200) (U := 46757 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide26_power (gammaAnalyticWide26_main hGRH.riemann)
      (gammaAnalyticWide26_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 27. -/
theorem gammaAnalyticWide27_roots :
    ((466209 / 10000 : ℝ) ≤ Real.sqrt (80420 / 37 : ℝ) ∧
      Real.sqrt (80420 / 37 : ℝ) ≤ 46621 / 1000 ∧ Real.sqrt (4021 : ℝ) ≤ 317057 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 27. -/
theorem gammaAnalyticWide27_logs :
    Real.log (80420 / 37 : ℝ) ≤ 38421 / 5000 ∧ Real.log (4021 : ℝ) ≤ 82993 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (80420 / 37) 12 20 0 (38421 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4021 12 20 0 (82993 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide27_main (hRH : RiemannHypothesis) :
    (38061 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4021,
        Real.exp (-(n : ℝ) / (80420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (80420 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 75327) * ((80420 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((80420 / 37) * (37 / 20)) + 1) / (4000 / 75327) +
        1839 / 1000 ≤
      226299 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide27_roots.2.2]
  have hs :
    Real.sqrt ((80420 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((80420 / 37) * (37 / 20)) +
        21 / 20 ≤
      19483 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide27_roots.2.2, gammaAnalyticWide27_logs.2]
  have hz :
    Real.sqrt (80420 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (80420 / 37) + 2469 / 800 ≤
      2002 / 125 := by
    linarith only [gammaAnalyticWide27_roots.2.1, gammaAnalyticWide27_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 80420 / 37) (y := 37 / 20) (h := 4000 / 75327) (r :=
      46621 / 1000) (e := 78619 / 500000) (p := 226299 / 1000) (s := 19483 / 1000) (z := 2002 / 125)
      (F := 38061 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide27_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (80420 / 37 : ℝ) * (37 / 20) = 4021 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide27_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (80420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (80420 / 37 : ℝ)) ≤
      9393 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 466209 / 10000) (T := 46621 / 1000) (Z := 38421 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide27_roots.1
      gammaAnalyticWide27_roots.2.1 gammaAnalyticWide27_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide27_power : (80420 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1327 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 27 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide27_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5789 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11631 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4021 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5789 / 50)]
  apply
    reject_03_of_analytic_caps (B := 4021) (x := 80420 / 37) (H := 11631 / 100) (R :=
      466209 / 10000) (W := 1327 / 100000) (F := 38061 / 1000) (U := 9393 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide27_power (gammaAnalyticWide27_main hGRH.riemann)
      (gammaAnalyticWide27_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 28. -/
theorem gammaAnalyticWide28_roots :
    ((468349 / 10000 : ℝ) ≤ Real.sqrt (81160 / 37 : ℝ) ∧
      Real.sqrt (81160 / 37 : ℝ) ≤ 9367 / 200 ∧ Real.sqrt (4058 : ℝ) ≤ 25481 / 400) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 28. -/
theorem gammaAnalyticWide28_logs :
    Real.log (81160 / 37 : ℝ) ≤ 76933 / 10000 ∧ Real.log (4058 : ℝ) ≤ 16617 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (81160 / 37) 12 20 0 (76933 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4058 12 20 0 (16617 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide28_main (hRH : RiemannHypothesis) :
    (19121 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4058,
        Real.exp (-(n : ℝ) / (81160 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (81160 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 15099) * ((81160 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((81160 / 37) * (37 / 20)) + 1) / (800 / 15099) +
        1839 / 1000 ≤
      113919 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide28_roots.2.2]
  have hs :
    Real.sqrt ((81160 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((81160 / 37) * (37 / 20)) +
        21 / 20 ≤
      3903 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide28_roots.2.2, gammaAnalyticWide28_logs.2]
  have hz :
    Real.sqrt (81160 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (81160 / 37) + 2469 / 800 ≤
      16039 / 1000 := by
    linarith only [gammaAnalyticWide28_roots.2.1, gammaAnalyticWide28_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 81160 / 37) (y := 37 / 20) (h := 800 / 15099) (r :=
      9367 / 200) (e := 78619 / 500000) (p := 113919 / 500) (s := 3903 / 200) (z := 16039 / 1000)
      (F := 19121 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide28_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (81160 / 37 : ℝ) * (37 / 20) = 4058 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide28_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (81160 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (81160 / 37 : ℝ)) ≤
      23589 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 468349 / 10000) (T := 9367 / 200) (Z := 76933 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide28_roots.1
      gammaAnalyticWide28_roots.2.1 gammaAnalyticWide28_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide28_power : (81160 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1321 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 28 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide28_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11631 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5843 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4058 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11631 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4058) (x := 81160 / 37) (H := 5843 / 50) (R := 468349 / 10000)
      (W := 1321 / 100000) (F := 19121 / 500) (U := 23589 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide28_power (gammaAnalyticWide28_main hGRH.riemann)
      (gammaAnalyticWide28_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 29. -/
theorem gammaAnalyticWide29_roots :
    ((470537 / 10000 : ℝ) ≤ Real.sqrt (81920 / 37 : ℝ) ∧
      Real.sqrt (81920 / 37 : ℝ) ≤ 235269 / 5000 ∧ Real.sqrt (4096 : ℝ) ≤ 64) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 29. -/
theorem gammaAnalyticWide29_logs :
    Real.log (81920 / 37 : ℝ) ≤ 38513 / 5000 ∧ Real.log (4096 : ℝ) ≤ 41589 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (81920 / 37) 12 20 0 (38513 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4096 12 20 0 (41589 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide29_main (hRH : RiemannHypothesis) :
    (19213 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4096,
        Real.exp (-(n : ℝ) / (81920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (81920 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 75677) * ((81920 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((81920 / 37) * (37 / 20)) + 1) / (4000 / 75677) +
        1839 / 1000 ≤
      45883 / 200 := by
    norm_num only at ⊢
  have hs :
    Real.sqrt ((81920 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((81920 / 37) * (37 / 20)) +
        21 / 20 ≤
      19547 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide29_roots.2.2, gammaAnalyticWide29_logs.2]
  have hz :
    Real.sqrt (81920 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (81920 / 37) + 2469 / 800 ≤
      16063 / 1000 := by
    linarith only [gammaAnalyticWide29_roots.2.1, gammaAnalyticWide29_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 81920 / 37) (y := 37 / 20) (h := 4000 / 75677) (r :=
      235269 / 5000) (e := 78619 / 500000) (p := 45883 / 200) (s := 19547 / 1000) (z :=
      16063 / 1000) (F := 19213 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide29_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (81920 / 37 : ℝ) * (37 / 20) = 4096 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide29_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (81920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (81920 / 37 : ℝ)) ≤
      11849 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 470537 / 10000) (T := 235269 / 5000) (Z := 38513 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide29_roots.1
      gammaAnalyticWide29_roots.2.1 gammaAnalyticWide29_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide29_power : (81920 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 657 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 29 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide29_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5843 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11741 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4096 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5843 / 50)]
  apply
    reject_03_of_analytic_caps (B := 4096) (x := 81920 / 37) (H := 11741 / 100) (R :=
      470537 / 10000) (W := 657 / 50000) (F := 19213 / 500) (U := 11849 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide29_power (gammaAnalyticWide29_main hGRH.riemann)
      (gammaAnalyticWide29_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 30. -/
theorem gammaAnalyticWide30_roots :
    ((118193 / 2500 : ℝ) ≤ Real.sqrt (82700 / 37 : ℝ) ∧
      Real.sqrt (82700 / 37 : ℝ) ≤ 472773 / 10000 ∧ Real.sqrt (4135 : ℝ) ≤ 8038 / 125) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 30. -/
theorem gammaAnalyticWide30_logs :
    Real.log (82700 / 37 : ℝ) ≤ 77121 / 10000 ∧ Real.log (4135 : ℝ) ≤ 83273 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (82700 / 37) 12 20 0 (77121 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4135 13 20 0 (83273 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide30_main (hRH : RiemannHypothesis) :
    (19307 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4135,
        Real.exp (-(n : ℝ) / (82700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (82700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 18963) * ((82700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((82700 / 37) * (37 / 20)) + 1) / (1000 / 18963) +
        1839 / 1000 ≤
      23103 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide30_roots.2.2]
  have hs :
    Real.sqrt ((82700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((82700 / 37) * (37 / 20)) +
        21 / 20 ≤
      979 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide30_roots.2.2, gammaAnalyticWide30_logs.2]
  have hz :
    Real.sqrt (82700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (82700 / 37) + 2469 / 800 ≤
      2011 / 125 := by
    linarith only [gammaAnalyticWide30_roots.2.1, gammaAnalyticWide30_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 82700 / 37) (y := 37 / 20) (h := 1000 / 18963) (r :=
      472773 / 10000) (e := 78619 / 500000) (p := 23103 / 100) (s := 979 / 50) (z := 2011 / 125)
      (F := 19307 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide30_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (82700 / 37 : ℝ) * (37 / 20) = 4135 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide30_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (82700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (82700 / 37 : ℝ)) ≤
      23809 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 118193 / 2500) (T := 472773 / 10000) (Z := 77121 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide30_roots.1
      gammaAnalyticWide30_roots.2.1 gammaAnalyticWide30_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide30_power : (82700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1307 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 30 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide30_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11741 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (5899 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4135 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11741 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4135) (x := 82700 / 37) (H := 5899 / 50) (R := 118193 / 2500)
      (W := 1307 / 100000) (F := 19307 / 500) (U := 23809 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide30_power (gammaAnalyticWide30_main hGRH.riemann)
      (gammaAnalyticWide30_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 31. -/
theorem gammaAnalyticWide31_roots :
    ((475053 / 10000 : ℝ) ≤ Real.sqrt (83500 / 37 : ℝ) ∧
      Real.sqrt (83500 / 37 : ℝ) ≤ 237527 / 5000 ∧ Real.sqrt (4175 : ℝ) ≤ 646143 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 31. -/
theorem gammaAnalyticWide31_logs :
    Real.log (83500 / 37 : ℝ) ≤ 77217 / 10000 ∧ Real.log (4175 : ℝ) ≤ 83369 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (83500 / 37) 12 20 0 (77217 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4175 13 20 0 (83369 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide31_main (hRH : RiemannHypothesis) :
    (19403 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4175,
        Real.exp (-(n : ℝ) / (83500 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (83500 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 38017) * ((83500 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((83500 / 37) * (37 / 20)) + 1) / (2000 / 38017) +
        1839 / 1000 ≤
      232683 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide31_roots.2.2]
  have hs :
    Real.sqrt ((83500 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((83500 / 37) * (37 / 20)) +
        21 / 20 ≤
      19613 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide31_roots.2.2, gammaAnalyticWide31_logs.2]
  have hz :
    Real.sqrt (83500 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (83500 / 37) + 2469 / 800 ≤
      2014 / 125 := by
    linarith only [gammaAnalyticWide31_roots.2.1, gammaAnalyticWide31_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 83500 / 37) (y := 37 / 20) (h := 2000 / 38017) (r :=
      237527 / 5000) (e := 78619 / 500000) (p := 232683 / 1000) (s := 19613 / 1000) (z :=
      2014 / 125) (F := 19403 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide31_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (83500 / 37 : ℝ) * (37 / 20) = 4175 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide31_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (83500 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (83500 / 37 : ℝ)) ≤
      9569 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 475053 / 10000) (T := 237527 / 5000) (Z := 77217 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide31_roots.1
      gammaAnalyticWide31_roots.2.1 gammaAnalyticWide31_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide31_power : (83500 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 13 / 1000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 31 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide31_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (5899 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2964 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4175 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 5899 / 50)]
  apply
    reject_03_of_analytic_caps (B := 4175) (x := 83500 / 37) (H := 2964 / 25) (R := 475053 / 10000)
      (W := 13 / 1000) (F := 19403 / 500) (U := 9569 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide31_power (gammaAnalyticWide31_main hGRH.riemann)
      (gammaAnalyticWide31_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 32. -/
theorem gammaAnalyticWide32_roots :
    ((23869 / 500 : ℝ) ≤ Real.sqrt (84320 / 37 : ℝ) ∧
      Real.sqrt (84320 / 37 : ℝ) ≤ 477381 / 10000 ∧ Real.sqrt (4216 : ℝ) ≤ 162327 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 32. -/
theorem gammaAnalyticWide32_logs :
    Real.log (84320 / 37 : ℝ) ≤ 15463 / 2000 ∧ Real.log (4216 : ℝ) ≤ 83467 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (84320 / 37) 12 20 0 (15463 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4216 13 20 0 (83467 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide32_main (hRH : RiemannHypothesis) :
    (19501 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4216,
        Real.exp (-(n : ℝ) / (84320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (84320 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 76223) * ((84320 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((84320 / 37) * (37 / 20)) + 1) / (4000 / 76223) +
        1839 / 1000 ≤
      58593 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide32_roots.2.2]
  have hs :
    Real.sqrt ((84320 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((84320 / 37) * (37 / 20)) +
        21 / 20 ≤
      19647 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide32_roots.2.2, gammaAnalyticWide32_logs.2]
  have hz :
    Real.sqrt (84320 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (84320 / 37) + 2469 / 800 ≤
      16137 / 1000 := by
    linarith only [gammaAnalyticWide32_roots.2.1, gammaAnalyticWide32_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 84320 / 37) (y := 37 / 20) (h := 4000 / 76223) (r :=
      477381 / 10000) (e := 78619 / 500000) (p := 58593 / 250) (s := 19647 / 1000) (z :=
      16137 / 1000) (F := 19501 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide32_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (84320 / 37 : ℝ) * (37 / 20) = 4216 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide32_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (84320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (84320 / 37 : ℝ)) ≤
      48077 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 23869 / 500) (T := 477381 / 10000) (Z := 15463 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide32_roots.1
      gammaAnalyticWide32_roots.2.1 gammaAnalyticWide32_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide32_power : (84320 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1293 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 32 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide32_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2964 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2383 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4216 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2964 / 25)]
  apply
    reject_03_of_analytic_caps (B := 4216) (x := 84320 / 37) (H := 2383 / 20) (R := 23869 / 500)
      (W := 1293 / 100000) (F := 19501 / 500) (U := 48077 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide32_power (gammaAnalyticWide32_main hGRH.riemann)
      (gammaAnalyticWide32_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 33. -/
theorem gammaAnalyticWide33_roots :
    ((29988 / 625 : ℝ) ≤ Real.sqrt (85180 / 37 : ℝ) ∧
      Real.sqrt (85180 / 37 : ℝ) ≤ 479809 / 10000 ∧ Real.sqrt (4259 : ℝ) ≤ 652611 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 33. -/
theorem gammaAnalyticWide33_logs :
    Real.log (85180 / 37 : ℝ) ≤ 77417 / 10000 ∧ Real.log (4259 : ℝ) ≤ 5223 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (85180 / 37) 12 20 0 (77417 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4259 13 20 0 (5223 / 625) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide33_main (hRH : RiemannHypothesis) :
    (19603 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4259,
        Real.exp (-(n : ℝ) / (85180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (85180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 19103) * ((85180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((85180 / 37) * (37 / 20)) + 1) / (1000 / 19103) +
        1839 / 1000 ≤
      11807 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide33_roots.2.2]
  have hs :
    Real.sqrt ((85180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((85180 / 37) * (37 / 20)) +
        21 / 20 ≤
      9841 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide33_roots.2.2, gammaAnalyticWide33_logs.2]
  have hz :
    Real.sqrt (85180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (85180 / 37) + 2469 / 800 ≤
      4041 / 250 := by
    linarith only [gammaAnalyticWide33_roots.2.1, gammaAnalyticWide33_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 85180 / 37) (y := 37 / 20) (h := 1000 / 19103) (r :=
      479809 / 10000) (e := 78619 / 500000) (p := 11807 / 50) (s := 9841 / 500) (z := 4041 / 250)
      (F := 19603 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide33_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (85180 / 37 : ℝ) * (37 / 20) = 4259 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide33_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (85180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (85180 / 37 : ℝ)) ≤
      24159 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 29988 / 625) (T := 479809 / 10000) (Z := 77417 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide33_roots.1
      gammaAnalyticWide33_roots.2.1 gammaAnalyticWide33_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide33_power : (85180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 257 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 33 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide33_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2383 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11977 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4259 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2383 / 20)]
  apply
    reject_03_of_analytic_caps (B := 4259) (x := 85180 / 37) (H := 11977 / 100) (R := 29988 / 625)
      (W := 257 / 20000) (F := 19603 / 500) (U := 24159 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide33_power (gammaAnalyticWide33_main hGRH.riemann)
      (gammaAnalyticWide33_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 34. -/
theorem gammaAnalyticWide34_roots :
    ((12057 / 250 : ℝ) ≤ Real.sqrt (86060 / 37 : ℝ) ∧
      Real.sqrt (86060 / 37 : ℝ) ≤ 482281 / 10000 ∧ Real.sqrt (4303 : ℝ) ≤ 655973 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 34. -/
theorem gammaAnalyticWide34_logs :
    Real.log (86060 / 37 : ℝ) ≤ 77519 / 10000 ∧ Real.log (4303 : ℝ) ≤ 83671 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (86060 / 37) 12 20 0 (77519 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4303 13 20 0 (83671 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide34_main (hRH : RiemannHypothesis) :
    (19707 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4303,
        Real.exp (-(n : ℝ) / (86060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (86060 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (125 / 2394) * ((86060 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((86060 / 37) * (37 / 20)) + 1) / (125 / 2394) +
        1839 / 1000 ≤
      29743 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide34_roots.2.2]
  have hs :
    Real.sqrt ((86060 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((86060 / 37) * (37 / 20)) +
        21 / 20 ≤
      19717 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide34_roots.2.2, gammaAnalyticWide34_logs.2]
  have hz :
    Real.sqrt (86060 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (86060 / 37) + 2469 / 800 ≤
      1619 / 100 := by
    linarith only [gammaAnalyticWide34_roots.2.1, gammaAnalyticWide34_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 86060 / 37) (y := 37 / 20) (h := 125 / 2394) (r :=
      482281 / 10000) (e := 78619 / 500000) (p := 29743 / 125) (s := 19717 / 1000) (z := 1619 / 100)
      (F := 19707 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide34_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (86060 / 37 : ℝ) * (37 / 20) = 4303 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide34_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (86060 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (86060 / 37 : ℝ)) ≤
      12141 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 12057 / 250) (T := 482281 / 10000) (Z := 77519 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide34_roots.1
      gammaAnalyticWide34_roots.2.1 gammaAnalyticWide34_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide34_power : (86060 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 639 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 34 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide34_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11977 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12039 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4303 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11977 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4303) (x := 86060 / 37) (H := 12039 / 100) (R := 12057 / 250)
      (W := 639 / 50000) (F := 19707 / 500) (U := 12141 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide34_power (gammaAnalyticWide34_main hGRH.riemann)
      (gammaAnalyticWide34_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 35. -/
theorem gammaAnalyticWide35_roots :
    ((96959 / 2000 : ℝ) ≤ Real.sqrt (86960 / 37 : ℝ) ∧
      Real.sqrt (86960 / 37 : ℝ) ≤ 121199 / 2500 ∧ Real.sqrt (4348 : ℝ) ≤ 329697 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 35. -/
theorem gammaAnalyticWide35_logs :
    Real.log (86960 / 37 : ℝ) ≤ 77623 / 10000 ∧ Real.log (4348 : ℝ) ≤ 3351 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (86960 / 37) 12 20 0 (77623 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4348 13 20 0 (3351 / 400) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide35_main (hRH : RiemannHypothesis) :
    (317 / 8 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4348,
        Real.exp (-(n : ℝ) / (86960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (86960 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 76811) * ((86960 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((86960 / 37) * (37 / 20)) + 1) / (4000 / 76811) +
        1839 / 1000 ≤
      29973 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide35_roots.2.2]
  have hs :
    Real.sqrt ((86960 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((86960 / 37) * (37 / 20)) +
        21 / 20 ≤
      9877 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide35_roots.2.2, gammaAnalyticWide35_logs.2]
  have hz :
    Real.sqrt (86960 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (86960 / 37) + 2469 / 800 ≤
      16217 / 1000 := by
    linarith only [gammaAnalyticWide35_roots.2.1, gammaAnalyticWide35_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 86960 / 37) (y := 37 / 20) (h := 4000 / 76811) (r :=
      121199 / 2500) (e := 78619 / 500000) (p := 29973 / 125) (s := 9877 / 500) (z := 16217 / 1000)
      (F := 317 / 8) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide35_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (86960 / 37 : ℝ) * (37 / 20) = 4348 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide35_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (86960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (86960 / 37 : ℝ)) ≤
      9763 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 96959 / 2000) (T := 121199 / 2500) (Z := 77623 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide35_roots.1
      gammaAnalyticWide35_roots.2.1 gammaAnalyticWide35_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide35_power : (86960 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 127 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 35 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide35_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12039 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12103 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4348 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12039 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4348) (x := 86960 / 37) (H := 12103 / 100) (R := 96959 / 2000)
      (W := 127 / 10000) (F := 317 / 8) (U := 9763 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide35_power (gammaAnalyticWide35_main hGRH.riemann)
      (gammaAnalyticWide35_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 36. -/
theorem gammaAnalyticWide36_roots :
    ((487353 / 10000 : ℝ) ≤ Real.sqrt (87880 / 37 : ℝ) ∧
      Real.sqrt (87880 / 37 : ℝ) ≤ 243677 / 5000 ∧ Real.sqrt (4394 : ℝ) ≤ 662873 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 36. -/
theorem gammaAnalyticWide36_logs :
    Real.log (87880 / 37 : ℝ) ≤ 77729 / 10000 ∧ Real.log (4394 : ℝ) ≤ 2097 / 250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (87880 / 37) 12 20 0 (77729 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4394 13 20 0 (2097 / 250) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide36_main (hRH : RiemannHypothesis) :
    (39841 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4394,
        Real.exp (-(n : ℝ) / (87880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (87880 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 38507) * ((87880 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((87880 / 37) * (37 / 20)) + 1) / (2000 / 38507) +
        1839 / 1000 ≤
      12083 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide36_roots.2.2]
  have hs :
    Real.sqrt ((87880 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((87880 / 37) * (37 / 20)) +
        21 / 20 ≤
      1979 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide36_roots.2.2, gammaAnalyticWide36_logs.2]
  have hz :
    Real.sqrt (87880 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (87880 / 37) + 2469 / 800 ≤
      4061 / 250 := by
    linarith only [gammaAnalyticWide36_roots.2.1, gammaAnalyticWide36_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 87880 / 37) (y := 37 / 20) (h := 2000 / 38507) (r :=
      243677 / 5000) (e := 78619 / 500000) (p := 12083 / 50) (s := 1979 / 100) (z := 4061 / 250)
      (F := 39841 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide36_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (87880 / 37 : ℝ) * (37 / 20) = 4394 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide36_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (87880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (87880 / 37 : ℝ)) ≤
      49069 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 487353 / 10000) (T := 243677 / 5000) (Z := 77729 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide36_roots.1
      gammaAnalyticWide36_roots.2.1 gammaAnalyticWide36_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide36_power : (87880 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1263 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 36 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide36_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12103 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3042 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4394 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12103 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4394) (x := 87880 / 37) (H := 3042 / 25) (R := 487353 / 10000)
      (W := 1263 / 100000) (F := 39841 / 1000) (U := 49069 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide36_power (gammaAnalyticWide36_main hGRH.riemann)
      (gammaAnalyticWide36_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 37. -/
theorem gammaAnalyticWide37_roots :
    ((489953 / 10000 : ℝ) ≤ Real.sqrt (88820 / 37 : ℝ) ∧
      Real.sqrt (88820 / 37 : ℝ) ≤ 244977 / 5000 ∧ Real.sqrt (4441 : ℝ) ≤ 666409 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 37. -/
theorem gammaAnalyticWide37_logs :
    Real.log (88820 / 37 : ℝ) ≤ 15567 / 2000 ∧ Real.log (4441 : ℝ) ≤ 83987 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (88820 / 37) 12 20 0 (15567 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4441 13 20 0 (83987 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide37_main (hRH : RiemannHypothesis) :
    (40059 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4441,
        Real.exp (-(n : ℝ) / (88820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (88820 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 77217) * ((88820 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((88820 / 37) * (37 / 20)) + 1) / (4000 / 77217) +
        1839 / 1000 ≤
      60893 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide37_roots.2.2]
  have hs :
    Real.sqrt ((88820 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((88820 / 37) * (37 / 20)) +
        21 / 20 ≤
      4957 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide37_roots.2.2, gammaAnalyticWide37_logs.2]
  have hz :
    Real.sqrt (88820 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (88820 / 37) + 2469 / 800 ≤
      2034 / 125 := by
    linarith only [gammaAnalyticWide37_roots.2.1, gammaAnalyticWide37_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 88820 / 37) (y := 37 / 20) (h := 4000 / 77217) (r :=
      244977 / 5000) (e := 78619 / 500000) (p := 60893 / 250) (s := 4957 / 250) (z := 2034 / 125)
      (F := 40059 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide37_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (88820 / 37 : ℝ) * (37 / 20) = 4441 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide37_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (88820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (88820 / 37 : ℝ)) ≤
      6166 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 489953 / 10000) (T := 244977 / 5000) (Z := 15567 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide37_roots.1
      gammaAnalyticWide37_roots.2.1 gammaAnalyticWide37_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide37_power : (88820 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 251 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 37 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide37_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3042 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12233 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4441 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3042 / 25)]
  apply
    reject_03_of_analytic_caps (B := 4441) (x := 88820 / 37) (H := 12233 / 100) (R :=
      489953 / 10000) (W := 251 / 20000) (F := 40059 / 1000) (U := 6166 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide37_power (gammaAnalyticWide37_main hGRH.riemann)
      (gammaAnalyticWide37_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 38. -/
theorem gammaAnalyticWide38_roots :
    ((492593 / 10000 : ℝ) ≤ Real.sqrt (89780 / 37 : ℝ) ∧
      Real.sqrt (89780 / 37 : ℝ) ≤ 246297 / 5000 ∧ Real.sqrt (4489 : ℝ) ≤ 67) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 38. -/
theorem gammaAnalyticWide38_logs :
    Real.log (89780 / 37 : ℝ) ≤ 38971 / 5000 ∧ Real.log (4489 : ℝ) ≤ 42047 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (89780 / 37) 12 20 0 (38971 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4489 13 20 0 (42047 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide38_main (hRH : RiemannHypothesis) :
    (20141 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4489,
        Real.exp (-(n : ℝ) / (89780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (89780 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 77427) * ((89780 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((89780 / 37) * (37 / 20)) + 1) / (4000 / 77427) +
        1839 / 1000 ≤
      245519 / 1000 := by
    norm_num only at ⊢
  have hs :
    Real.sqrt ((89780 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((89780 / 37) * (37 / 20)) +
        21 / 20 ≤
      3973 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide38_roots.2.2, gammaAnalyticWide38_logs.2]
  have hz :
    Real.sqrt (89780 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (89780 / 37) + 2469 / 800 ≤
      163 / 10 := by
    linarith only [gammaAnalyticWide38_roots.2.1, gammaAnalyticWide38_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 89780 / 37) (y := 37 / 20) (h := 4000 / 77427) (r :=
      246297 / 5000) (e := 78619 / 500000) (p := 245519 / 1000) (s := 3973 / 200) (z := 163 / 10)
      (F := 20141 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide38_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (89780 / 37 : ℝ) * (37 / 20) = 4489 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide38_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (89780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (89780 / 37 : ℝ)) ≤
      49591 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 492593 / 10000) (T := 246297 / 5000) (Z := 38971 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide38_roots.1
      gammaAnalyticWide38_roots.2.1 gammaAnalyticWide38_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide38_power : (89780 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 39 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 38 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide38_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12233 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12301 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4489 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12233 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4489) (x := 89780 / 37) (H := 12301 / 100) (R :=
      492593 / 10000) (W := 39 / 3125) (F := 20141 / 500) (U := 49591 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide38_power (gammaAnalyticWide38_main hGRH.riemann)
      (gammaAnalyticWide38_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 39. -/
theorem gammaAnalyticWide39_roots :
    ((495329 / 10000 : ℝ) ≤ Real.sqrt (90780 / 37 : ℝ) ∧
      Real.sqrt (90780 / 37 : ℝ) ≤ 49533 / 1000 ∧ Real.sqrt (4539 : ℝ) ≤ 336861 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 39. -/
theorem gammaAnalyticWide39_logs :
    Real.log (90780 / 37 : ℝ) ≤ 78053 / 10000 ∧ Real.log (4539 : ℝ) ≤ 16841 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (90780 / 37) 12 20 0 (78053 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4539 13 20 0 (16841 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide39_main (hRH : RiemannHypothesis) :
    (5064 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4539,
        Real.exp (-(n : ℝ) / (90780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (90780 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 77637) * ((90780 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((90780 / 37) * (37 / 20)) + 1) / (4000 / 77637) +
        1839 / 1000 ≤
      123771 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide39_roots.2.2]
  have hs :
    Real.sqrt ((90780 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((90780 / 37) * (37 / 20)) +
        21 / 20 ≤
      2488 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide39_roots.2.2, gammaAnalyticWide39_logs.2]
  have hz :
    Real.sqrt (90780 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (90780 / 37) + 2469 / 800 ≤
      16329 / 1000 := by
    linarith only [gammaAnalyticWide39_roots.2.1, gammaAnalyticWide39_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 90780 / 37) (y := 37 / 20) (h := 4000 / 77637) (r :=
      49533 / 1000) (e := 78619 / 500000) (p := 123771 / 500) (s := 2488 / 125) (z := 16329 / 1000)
      (F := 5064 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide39_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (90780 / 37 : ℝ) * (37 / 20) = 4539 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide39_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (90780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (90780 / 37 : ℝ)) ≤
      49863 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 495329 / 10000) (T := 49533 / 1000) (Z := 78053 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide39_roots.1
      gammaAnalyticWide39_roots.2.1 gammaAnalyticWide39_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide39_power : (90780 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 31 / 2500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 39 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide39_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12301 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1237 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4539 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12301 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4539) (x := 90780 / 37) (H := 1237 / 10) (R := 495329 / 10000)
      (W := 31 / 2500) (F := 5064 / 125) (U := 49863 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide39_power (gammaAnalyticWide39_main hGRH.riemann)
      (gammaAnalyticWide39_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 40. -/
theorem gammaAnalyticWide40_roots :
    ((62263 / 1250 : ℝ) ≤ Real.sqrt (91800 / 37 : ℝ) ∧
      Real.sqrt (91800 / 37 : ℝ) ≤ 99621 / 2000 ∧ Real.sqrt (4590 : ℝ) ≤ 84687 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 40. -/
theorem gammaAnalyticWide40_logs :
    Real.log (91800 / 37 : ℝ) ≤ 15633 / 2000 ∧ Real.log (4590 : ℝ) ≤ 84317 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (91800 / 37) 12 20 0 (15633 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4590 13 20 0 (84317 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide40_main (hRH : RiemannHypothesis) :
    (8149 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4590,
        Real.exp (-(n : ℝ) / (91800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (91800 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 77861) * ((91800 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((91800 / 37) * (37 / 20)) + 1) / (4000 / 77861) +
        1839 / 1000 ≤
      1248 / 5 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide40_roots.2.2]
  have hs :
    Real.sqrt ((91800 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((91800 / 37) * (37 / 20)) +
        21 / 20 ≤
      2493 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide40_roots.2.2, gammaAnalyticWide40_logs.2]
  have hz :
    Real.sqrt (91800 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (91800 / 37) + 2469 / 800 ≤
      8179 / 500 := by
    linarith only [gammaAnalyticWide40_roots.2.1, gammaAnalyticWide40_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 91800 / 37) (y := 37 / 20) (h := 4000 / 77861) (r :=
      99621 / 2000) (e := 78619 / 500000) (p := 1248 / 5) (s := 2493 / 125) (z := 8179 / 500) (F :=
      8149 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide40_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (91800 / 37 : ℝ) * (37 / 20) = 4590 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide40_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (91800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (91800 / 37 : ℝ)) ≤
      50139 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 62263 / 1250) (T := 99621 / 2000) (Z := 15633 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide40_roots.1
      gammaAnalyticWide40_roots.2.1 gammaAnalyticWide40_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide40_power : (91800 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 77 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 40 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide40_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1237 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (622 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4590 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1237 / 10)]
  apply
    reject_03_of_analytic_caps (B := 4590) (x := 91800 / 37) (H := 622 / 5) (R := 62263 / 1250)
      (W := 77 / 6250) (F := 8149 / 200) (U := 50139 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide40_power (gammaAnalyticWide40_main hGRH.riemann)
      (gammaAnalyticWide40_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 41. -/
theorem gammaAnalyticWide41_roots :
    ((250459 / 5000 : ℝ) ≤ Real.sqrt (92840 / 37 : ℝ) ∧
      Real.sqrt (92840 / 37 : ℝ) ≤ 500919 / 10000 ∧ Real.sqrt (4642 : ℝ) ≤ 681323 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 41. -/
theorem gammaAnalyticWide41_logs :
    Real.log (92840 / 37 : ℝ) ≤ 39139 / 5000 ∧ Real.log (4642 : ℝ) ≤ 8443 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (92840 / 37) 12 20 0 (39139 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4642 13 20 0 (8443 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide41_main (hRH : RiemannHypothesis) :
    (20491 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4642,
        Real.exp (-(n : ℝ) / (92840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (92840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 39039) * ((92840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((92840 / 37) * (37 / 20)) + 1) / (2000 / 39039) +
        1839 / 1000 ≤
      62923 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide41_roots.2.2]
  have hs :
    Real.sqrt ((92840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((92840 / 37) * (37 / 20)) +
        21 / 20 ≤
      2498 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide41_roots.2.2, gammaAnalyticWide41_logs.2]
  have hz :
    Real.sqrt (92840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (92840 / 37) + 2469 / 800 ≤
      4097 / 250 := by
    linarith only [gammaAnalyticWide41_roots.2.1, gammaAnalyticWide41_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 92840 / 37) (y := 37 / 20) (h := 2000 / 39039) (r :=
      500919 / 10000) (e := 78619 / 500000) (p := 62923 / 250) (s := 2498 / 125) (z := 4097 / 250)
      (F := 20491 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide41_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (92840 / 37 : ℝ) * (37 / 20) = 4642 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide41_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (92840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (92840 / 37 : ℝ)) ≤
      2521 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 250459 / 5000) (T := 500919 / 10000) (Z := 39139 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide41_roots.1
      gammaAnalyticWide41_roots.2.1 gammaAnalyticWide41_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide41_power : (92840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 153 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 41 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide41_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (622 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12511 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4642 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 622 / 5)]
  apply
    reject_03_of_analytic_caps (B := 4642) (x := 92840 / 37) (H := 12511 / 100) (R := 250459 / 5000)
      (W := 153 / 12500) (F := 20491 / 500) (U := 2521 / 50) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide41_power (gammaAnalyticWide41_main hGRH.riemann)
      (gammaAnalyticWide41_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 42. -/
theorem gammaAnalyticWide42_roots :
    ((503769 / 10000 : ℝ) ≤ Real.sqrt (93900 / 37 : ℝ) ∧
      Real.sqrt (93900 / 37 : ℝ) ≤ 50377 / 1000 ∧ Real.sqrt (4695 : ℝ) ≤ 685201 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 42. -/
theorem gammaAnalyticWide42_logs :
    Real.log (93900 / 37 : ℝ) ≤ 78391 / 10000 ∧ Real.log (4695 : ℝ) ≤ 84543 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (93900 / 37) 12 20 0 (78391 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4695 13 20 0 (84543 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide42_main (hRH : RiemannHypothesis) :
    (41221 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4695,
        Real.exp (-(n : ℝ) / (93900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (93900 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 39151) * ((93900 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((93900 / 37) * (37 / 20)) + 1) / (2000 / 39151) +
        1839 / 1000 ≤
      126909 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide42_roots.2.2]
  have hs :
    Real.sqrt ((93900 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((93900 / 37) * (37 / 20)) +
        21 / 20 ≤
      2503 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide42_roots.2.2, gammaAnalyticWide42_logs.2]
  have hz :
    Real.sqrt (93900 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (93900 / 37) + 2469 / 800 ≤
      8209 / 500 := by
    linarith only [gammaAnalyticWide42_roots.2.1, gammaAnalyticWide42_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 93900 / 37) (y := 37 / 20) (h := 2000 / 39151) (r :=
      50377 / 1000) (e := 78619 / 500000) (p := 126909 / 500) (s := 2503 / 125) (z := 8209 / 500)
      (F := 41221 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide42_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (93900 / 37 : ℝ) * (37 / 20) = 4695 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide42_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (93900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (93900 / 37 : ℝ)) ≤
      50703 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 503769 / 10000) (T := 50377 / 1000) (Z := 78391 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide42_roots.1
      gammaAnalyticWide42_roots.2.1 gammaAnalyticWide42_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide42_power : (93900 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1217 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 42 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide42_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12511 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12583 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4695 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12511 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4695) (x := 93900 / 37) (H := 12583 / 100) (R :=
      503769 / 10000) (W := 1217 / 100000) (F := 41221 / 1000) (U := 50703 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide42_power (gammaAnalyticWide42_main hGRH.riemann)
      (gammaAnalyticWide42_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 43. -/
theorem gammaAnalyticWide43_roots :
    ((253329 / 5000 : ℝ) ≤ Real.sqrt (94980 / 37 : ℝ) ∧
      Real.sqrt (94980 / 37 : ℝ) ≤ 506659 / 10000 ∧ Real.sqrt (4749 : ℝ) ≤ 68913 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 43. -/
theorem gammaAnalyticWide43_logs :
    Real.log (94980 / 37 : ℝ) ≤ 39253 / 5000 ∧ Real.log (4749 : ℝ) ≤ 84657 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (94980 / 37) 12 20 0 (39253 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4749 13 20 0 (84657 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide43_main (hRH : RiemannHypothesis) :
    (5183 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4749,
        Real.exp (-(n : ℝ) / (94980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (94980 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 39263) * ((94980 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((94980 / 37) * (37 / 20)) + 1) / (2000 / 39263) +
        1839 / 1000 ≤
      127989 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide43_roots.2.2]
  have hs :
    Real.sqrt ((94980 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((94980 / 37) * (37 / 20)) +
        21 / 20 ≤
      4013 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide43_roots.2.2, gammaAnalyticWide43_logs.2]
  have hz :
    Real.sqrt (94980 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (94980 / 37) + 2469 / 800 ≤
      2056 / 125 := by
    linarith only [gammaAnalyticWide43_roots.2.1, gammaAnalyticWide43_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 94980 / 37) (y := 37 / 20) (h := 2000 / 39263) (r :=
      506659 / 10000) (e := 78619 / 500000) (p := 127989 / 500) (s := 4013 / 200) (z := 2056 / 125)
      (F := 5183 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide43_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (94980 / 37 : ℝ) * (37 / 20) = 4749 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide43_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (94980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (94980 / 37 : ℝ)) ≤
      50991 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 253329 / 5000) (T := 506659 / 10000) (Z := 39253 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide43_roots.1
      gammaAnalyticWide43_roots.2.1 gammaAnalyticWide43_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide43_power : (94980 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1209 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 43 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide43_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12583 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3164 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4749 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12583 / 100)]
  apply
    reject_03_of_analytic_caps (B := 4749) (x := 94980 / 37) (H := 3164 / 25) (R := 253329 / 5000)
      (W := 1209 / 100000) (F := 5183 / 125) (U := 50991 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide43_power (gammaAnalyticWide43_main hGRH.riemann)
      (gammaAnalyticWide43_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 44. -/
theorem gammaAnalyticWide44_roots :
    ((127409 / 2500 : ℝ) ≤ Real.sqrt (96100 / 37 : ℝ) ∧
      Real.sqrt (96100 / 37 : ℝ) ≤ 509637 / 10000 ∧ Real.sqrt (4805 : ℝ) ≤ 346591 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 44. -/
theorem gammaAnalyticWide44_logs :
    Real.log (96100 / 37 : ℝ) ≤ 78623 / 10000 ∧ Real.log (4805 : ℝ) ≤ 3391 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (96100 / 37) 12 20 0 (78623 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4805 13 20 0 (3391 / 400) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide44_main (hRH : RiemannHypothesis) :
    (8343 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4805,
        Real.exp (-(n : ℝ) / (96100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (96100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (16 / 315) * ((96100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((96100 / 37) * (37 / 20)) + 1) / (16 / 315) +
        1839 / 1000 ≤
      64553 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide44_roots.2.2]
  have hs :
    Real.sqrt ((96100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((96100 / 37) * (37 / 20)) +
        21 / 20 ≤
      20107 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide44_roots.2.2, gammaAnalyticWide44_logs.2]
  have hz :
    Real.sqrt (96100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (96100 / 37) + 2469 / 800 ≤
      16479 / 1000 := by
    linarith only [gammaAnalyticWide44_roots.2.1, gammaAnalyticWide44_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 96100 / 37) (y := 37 / 20) (h := 16 / 315) (r :=
      509637 / 10000) (e := 78619 / 500000) (p := 64553 / 250) (s := 20107 / 1000) (z :=
      16479 / 1000) (F := 8343 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide44_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (96100 / 37 : ℝ) * (37 / 20) = 4805 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide44_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (96100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (96100 / 37 : ℝ)) ≤
      6411 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 127409 / 2500) (T := 509637 / 10000) (Z := 78623 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide44_roots.1
      gammaAnalyticWide44_roots.2.1 gammaAnalyticWide44_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide44_power : (96100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1201 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 44 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide44_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3164 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3183 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4805 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3164 / 25)]
  apply
    reject_03_of_analytic_caps (B := 4805) (x := 96100 / 37) (H := 3183 / 25) (R := 127409 / 2500)
      (W := 1201 / 100000) (F := 8343 / 200) (U := 6411 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide44_power (gammaAnalyticWide44_main hGRH.riemann)
      (gammaAnalyticWide44_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 45. -/
theorem gammaAnalyticWide45_roots :
    ((512703 / 10000 : ℝ) ≤ Real.sqrt (97260 / 37 : ℝ) ∧
      Real.sqrt (97260 / 37 : ℝ) ≤ 32044 / 625 ∧ Real.sqrt (4863 : ℝ) ≤ 697353 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 45. -/
theorem gammaAnalyticWide45_logs :
    Real.log (97260 / 37 : ℝ) ≤ 78743 / 10000 ∧ Real.log (4863 : ℝ) ≤ 16979 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (97260 / 37) 12 20 0 (78743 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4863 13 20 0 (16979 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide45_main (hRH : RiemannHypothesis) :
    (41973 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4863,
        Real.exp (-(n : ℝ) / (97260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (97260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 19747) * ((97260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((97260 / 37) * (37 / 20)) + 1) / (1000 / 19747) +
        1839 / 1000 ≤
      130259 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide45_roots.2.2]
  have hs :
    Real.sqrt ((97260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((97260 / 37) * (37 / 20)) +
        21 / 20 ≤
      20149 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide45_roots.2.2, gammaAnalyticWide45_logs.2]
  have hz :
    Real.sqrt (97260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (97260 / 37) + 2469 / 800 ≤
      16511 / 1000 := by
    linarith only [gammaAnalyticWide45_roots.2.1, gammaAnalyticWide45_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 97260 / 37) (y := 37 / 20) (h := 1000 / 19747) (r :=
      32044 / 625) (e := 78619 / 500000) (p := 130259 / 500) (s := 20149 / 1000) (z := 16511 / 1000)
      (F := 41973 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide45_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (97260 / 37 : ℝ) * (37 / 20) = 4863 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide45_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (97260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (97260 / 37 : ℝ)) ≤
      51593 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 512703 / 10000) (T := 32044 / 625) (Z := 78743 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide45_roots.1
      gammaAnalyticWide45_roots.2.1 gammaAnalyticWide45_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide45_power : (97260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1193 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 45 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide45_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3183 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1281 / 10 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4863 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3183 / 25)]
  apply
    reject_03_of_analytic_caps (B := 4863) (x := 97260 / 37) (H := 1281 / 10) (R := 512703 / 10000)
      (W := 1193 / 100000) (F := 41973 / 1000) (U := 51593 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide45_power (gammaAnalyticWide45_main hGRH.riemann)
      (gammaAnalyticWide45_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 46. -/
theorem gammaAnalyticWide46_roots :
    ((128951 / 2500 : ℝ) ≤ Real.sqrt (98440 / 37 : ℝ) ∧
      Real.sqrt (98440 / 37 : ℝ) ≤ 103161 / 2000 ∧ Real.sqrt (4922 : ℝ) ≤ 70157 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 46. -/
theorem gammaAnalyticWide46_logs :
    Real.log (98440 / 37 : ℝ) ≤ 78863 / 10000 ∧ Real.log (4922 : ℝ) ≤ 17003 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (98440 / 37) 12 20 0 (78863 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4922 13 20 0 (17003 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide46_main (hRH : RiemannHypothesis) :
    (21117 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4922,
        Real.exp (-(n : ℝ) / (98440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (98440 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 79233) * ((98440 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((98440 / 37) * (37 / 20)) + 1) / (4000 / 79233) +
        1839 / 1000 ≤
      262857 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide46_roots.2.2]
  have hs :
    Real.sqrt ((98440 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((98440 / 37) * (37 / 20)) +
        21 / 20 ≤
      20193 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide46_roots.2.2, gammaAnalyticWide46_logs.2]
  have hz :
    Real.sqrt (98440 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (98440 / 37) + 2469 / 800 ≤
      16543 / 1000 := by
    linarith only [gammaAnalyticWide46_roots.2.1, gammaAnalyticWide46_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 98440 / 37) (y := 37 / 20) (h := 4000 / 79233) (r :=
      103161 / 2000) (e := 78619 / 500000) (p := 262857 / 1000) (s := 20193 / 1000) (z :=
      16543 / 1000) (F := 21117 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide46_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (98440 / 37 : ℝ) * (37 / 20) = 4922 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide46_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (98440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (98440 / 37 : ℝ)) ≤
      25951 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 128951 / 2500) (T := 103161 / 2000) (Z := 78863 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide46_roots.1
      gammaAnalyticWide46_roots.2.1 gammaAnalyticWide46_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide46_power : (98440 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 237 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 46 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide46_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (1281 / 10 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3222 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4922 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 1281 / 10)]
  apply
    reject_03_of_analytic_caps (B := 4922) (x := 98440 / 37) (H := 3222 / 25) (R := 128951 / 2500)
      (W := 237 / 20000) (F := 21117 / 500) (U := 25951 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide46_power (gammaAnalyticWide46_main hGRH.riemann)
      (gammaAnalyticWide46_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 47. -/
theorem gammaAnalyticWide47_roots :
    ((51899 / 1000 : ℝ) ≤ Real.sqrt (99660 / 37 : ℝ) ∧
      Real.sqrt (99660 / 37 : ℝ) ≤ 518991 / 10000 ∧ Real.sqrt (4983 : ℝ) ≤ 44119 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 47. -/
theorem gammaAnalyticWide47_logs :
    Real.log (99660 / 37 : ℝ) ≤ 78987 / 10000 ∧ Real.log (4983 : ℝ) ≤ 42569 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (99660 / 37) 12 20 0 (78987 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 4983 13 20 0 (42569 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide47_main (hRH : RiemannHypothesis) :
    (21251 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 4983,
        Real.exp (-(n : ℝ) / (99660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (99660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 79471) * ((99660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((99660 / 37) * (37 / 20)) + 1) / (4000 / 79471) +
        1839 / 1000 ≤
      66317 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide47_roots.2.2]
  have hs :
    Real.sqrt ((99660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((99660 / 37) * (37 / 20)) +
        21 / 20 ≤
      20237 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide47_roots.2.2, gammaAnalyticWide47_logs.2]
  have hz :
    Real.sqrt (99660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (99660 / 37) + 2469 / 800 ≤
      2072 / 125 := by
    linarith only [gammaAnalyticWide47_roots.2.1, gammaAnalyticWide47_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 99660 / 37) (y := 37 / 20) (h := 4000 / 79471) (r :=
      518991 / 10000) (e := 78619 / 500000) (p := 66317 / 250) (s := 20237 / 1000) (z := 2072 / 125)
      (F := 21251 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide47_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (99660 / 37 : ℝ) * (37 / 20) = 4983 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide47_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (99660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (99660 / 37 : ℝ)) ≤
      52219 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 51899 / 1000) (T := 518991 / 10000) (Z := 78987 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide47_roots.1
      gammaAnalyticWide47_roots.2.1 gammaAnalyticWide47_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide47_power : (99660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1177 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 47 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide47_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3222 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (12969 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (4983 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3222 / 25)]
  apply
    reject_03_of_analytic_caps (B := 4983) (x := 99660 / 37) (H := 12969 / 100) (R := 51899 / 1000)
      (W := 1177 / 100000) (F := 21251 / 500) (U := 52219 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide47_power (gammaAnalyticWide47_main hGRH.riemann)
      (gammaAnalyticWide47_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 48. -/
theorem gammaAnalyticWide48_roots :
    ((522209 / 10000 : ℝ) ≤ Real.sqrt (100900 / 37 : ℝ) ∧
      Real.sqrt (100900 / 37 : ℝ) ≤ 52221 / 1000 ∧ Real.sqrt (5045 : ℝ) ≤ 355141 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 48. -/
theorem gammaAnalyticWide48_logs :
    Real.log (100900 / 37 : ℝ) ≤ 7911 / 1000 ∧ Real.log (5045 : ℝ) ≤ 42631 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (100900 / 37) 12 20 0 (7911 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5045 13 20 0 (42631 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide48_main (hRH : RiemannHypothesis) :
    (10693 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5045,
        Real.exp (-(n : ℝ) / (100900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (100900 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 79723) * ((100900 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((100900 / 37) * (37 / 20)) + 1) / (4000 / 79723) +
        1839 / 1000 ≤
      267711 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide48_roots.2.2]
  have hs :
    Real.sqrt ((100900 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((100900 / 37) * (37 / 20)) +
        21 / 20 ≤
      10141 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide48_roots.2.2, gammaAnalyticWide48_logs.2]
  have hz :
    Real.sqrt (100900 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (100900 / 37) + 2469 / 800 ≤
      16609 / 1000 := by
    linarith only [gammaAnalyticWide48_roots.2.1, gammaAnalyticWide48_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 100900 / 37) (y := 37 / 20) (h := 4000 / 79723) (r :=
      52221 / 1000) (e := 78619 / 500000) (p := 267711 / 1000) (s := 10141 / 500) (z :=
      16609 / 1000) (F := 10693 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide48_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (100900 / 37 : ℝ) * (37 / 20) = 5045 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide48_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (100900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (100900 / 37 : ℝ)) ≤
      2627 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 522209 / 10000) (T := 52221 / 1000) (Z := 7911 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide48_roots.1
      gammaAnalyticWide48_roots.2.1 gammaAnalyticWide48_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide48_power : (100900 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 73 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 48 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide48_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (12969 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (261 / 2 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5045 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 12969 / 100)]
  apply
    reject_03_of_analytic_caps (B := 5045) (x := 100900 / 37) (H := 261 / 2) (R := 522209 / 10000)
      (W := 73 / 6250) (F := 10693 / 250) (U := 2627 / 50) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide48_power (gammaAnalyticWide48_main hGRH.riemann)
      (gammaAnalyticWide48_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 49. -/
theorem gammaAnalyticWide49_roots :
    ((525511 / 10000 : ℝ) ≤ Real.sqrt (102180 / 37 : ℝ) ∧
      Real.sqrt (102180 / 37 : ℝ) ≤ 65689 / 1250 ∧ Real.sqrt (5109 : ℝ) ≤ 714773 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 49. -/
theorem gammaAnalyticWide49_logs :
    Real.log (102180 / 37 : ℝ) ≤ 19809 / 2500 ∧ Real.log (5109 : ℝ) ≤ 21347 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (102180 / 37) 12 20 0 (19809 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5109 13 20 0 (21347 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide49_main (hRH : RiemannHypothesis) :
    (861 / 20 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5109,
        Real.exp (-(n : ℝ) / (102180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (102180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (125 / 2499) * ((102180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((102180 / 37) * (37 / 20)) + 1) / (125 / 2499) +
        1839 / 1000 ≤
      10809 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide49_roots.2.2]
  have hs :
    Real.sqrt ((102180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((102180 / 37) * (37 / 20)) +
        21 / 20 ≤
      20327 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide49_roots.2.2, gammaAnalyticWide49_logs.2]
  have hz :
    Real.sqrt (102180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (102180 / 37) + 2469 / 800 ≤
      16643 / 1000 := by
    linarith only [gammaAnalyticWide49_roots.2.1, gammaAnalyticWide49_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 102180 / 37) (y := 37 / 20) (h := 125 / 2499) (r :=
      65689 / 1250) (e := 78619 / 500000) (p := 10809 / 40) (s := 20327 / 1000) (z := 16643 / 1000)
      (F := 861 / 20) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide49_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (102180 / 37 : ℝ) * (37 / 20) = 5109 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide49_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (102180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (102180 / 37 : ℝ)) ≤
      13217 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 525511 / 10000) (T := 65689 / 1250) (Z := 19809 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticWide49_roots.1
      gammaAnalyticWide49_roots.2.1 gammaAnalyticWide49_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide49_power : (102180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 29 / 2500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 49 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide49_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (261 / 2 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (6567 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5109 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 261 / 2)]
  apply
    reject_03_of_analytic_caps (B := 5109) (x := 102180 / 37) (H := 6567 / 50) (R := 525511 / 10000)
      (W := 29 / 2500) (F := 861 / 20) (U := 13217 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide49_power (gammaAnalyticWide49_main hGRH.riemann)
      (gammaAnalyticWide49_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 50. -/
theorem gammaAnalyticWide50_roots :
    ((264447 / 5000 : ℝ) ≤ Real.sqrt (103500 / 37 : ℝ) ∧
      Real.sqrt (103500 / 37 : ℝ) ≤ 105779 / 2000 ∧ Real.sqrt (5175 : ℝ) ≤ 1151 / 16) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 50. -/
theorem gammaAnalyticWide50_logs :
    Real.log (103500 / 37 : ℝ) ≤ 15873 / 2000 ∧ Real.log (5175 : ℝ) ≤ 21379 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (103500 / 37) 12 20 0 (15873 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5175 13 20 0 (21379 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide50_main (hRH : RiemannHypothesis) :
    (21667 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5175,
        Real.exp (-(n : ℝ) / (103500 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (103500 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 80227) * ((103500 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((103500 / 37) * (37 / 20)) + 1) / (4000 / 80227) +
        1839 / 1000 ≤
      272809 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide50_roots.2.2]
  have hs :
    Real.sqrt ((103500 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((103500 / 37) * (37 / 20)) +
        21 / 20 ≤
      10187 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide50_roots.2.2, gammaAnalyticWide50_logs.2]
  have hz :
    Real.sqrt (103500 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (103500 / 37) + 2469 / 800 ≤
      8339 / 500 := by
    linarith only [gammaAnalyticWide50_roots.2.1, gammaAnalyticWide50_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 103500 / 37) (y := 37 / 20) (h := 4000 / 80227) (r :=
      105779 / 2000) (e := 78619 / 500000) (p := 272809 / 1000) (s := 10187 / 500) (z := 8339 / 500)
      (F := 21667 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide50_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (103500 / 37 : ℝ) * (37 / 20) = 5175 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide50_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (103500 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (103500 / 37 : ℝ)) ≤
      10641 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 264447 / 5000) (T := 105779 / 2000) (Z := 15873 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide50_roots.1
      gammaAnalyticWide50_roots.2.1 gammaAnalyticWide50_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide50_power : (103500 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 36 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 50 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide50_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (6567 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13219 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5175 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 6567 / 50)]
  apply
    reject_03_of_analytic_caps (B := 5175) (x := 103500 / 37) (H := 13219 / 100) (R :=
      264447 / 5000) (W := 36 / 3125) (F := 21667 / 500) (U := 10641 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide50_power (gammaAnalyticWide50_main hGRH.riemann)
      (gammaAnalyticWide50_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 51. -/
theorem gammaAnalyticWide51_roots :
    ((532307 / 10000 : ℝ) ≤ Real.sqrt (104840 / 37 : ℝ) ∧
      Real.sqrt (104840 / 37 : ℝ) ≤ 133077 / 2500 ∧ Real.sqrt (5242 : ℝ) ≤ 724017 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 51. -/
theorem gammaAnalyticWide51_logs :
    Real.log (104840 / 37 : ℝ) ≤ 79493 / 10000 ∧ Real.log (5242 : ℝ) ≤ 17129 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (104840 / 37) 12 20 0 (79493 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5242 13 20 0 (17129 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide51_main (hRH : RiemannHypothesis) :
    (43621 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5242,
        Real.exp (-(n : ℝ) / (104840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (104840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 40243) * ((104840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((104840 / 37) * (37 / 20)) + 1) / (2000 / 40243) +
        1839 / 1000 ≤
      34428 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide51_roots.2.2]
  have hs :
    Real.sqrt ((104840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((104840 / 37) * (37 / 20)) +
        21 / 20 ≤
      20421 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide51_roots.2.2, gammaAnalyticWide51_logs.2]
  have hz :
    Real.sqrt (104840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (104840 / 37) + 2469 / 800 ≤
      2089 / 125 := by
    linarith only [gammaAnalyticWide51_roots.2.1, gammaAnalyticWide51_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 104840 / 37) (y := 37 / 20) (h := 2000 / 40243) (r :=
      133077 / 2500) (e := 78619 / 500000) (p := 34428 / 125) (s := 20421 / 1000) (z := 2089 / 125)
      (F := 43621 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide51_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (104840 / 37 : ℝ) * (37 / 20) = 5242 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide51_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (104840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (104840 / 37 : ℝ)) ≤
      10709 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 532307 / 10000) (T := 133077 / 2500) (Z := 79493 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide51_roots.1
      gammaAnalyticWide51_roots.2.1 gammaAnalyticWide51_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide51_power : (104840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 143 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 51 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide51_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (13219 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2661 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5242 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13219 / 100)]
  apply
    reject_03_of_analytic_caps (B := 5242) (x := 104840 / 37) (H := 2661 / 20) (R := 532307 / 10000)
      (W := 143 / 12500) (F := 43621 / 1000) (U := 10709 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide51_power (gammaAnalyticWide51_main hGRH.riemann)
      (gammaAnalyticWide51_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 52. -/
theorem gammaAnalyticWide52_roots :
    ((535749 / 10000 : ℝ) ≤ Real.sqrt (106200 / 37 : ℝ) ∧
      Real.sqrt (106200 / 37 : ℝ) ≤ 2143 / 40 ∧ Real.sqrt (5310 : ℝ) ≤ 364349 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 52. -/
theorem gammaAnalyticWide52_logs :
    Real.log (106200 / 37 : ℝ) ≤ 39811 / 5000 ∧ Real.log (5310 : ℝ) ≤ 42887 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (106200 / 37) 12 20 0 (39811 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5310 13 20 0 (42887 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide52_main (hRH : RiemannHypothesis) :
    (4391 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5310,
        Real.exp (-(n : ℝ) / (106200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (106200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 16149) * ((106200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((106200 / 37) * (37 / 20)) + 1) / (800 / 16149) +
        1839 / 1000 ≤
      27807 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide52_roots.2.2]
  have hs :
    Real.sqrt ((106200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((106200 / 37) * (37 / 20)) +
        21 / 20 ≤
      5117 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide52_roots.2.2, gammaAnalyticWide52_logs.2]
  have hz :
    Real.sqrt (106200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (106200 / 37) + 2469 / 800 ≤
      16747 / 1000 := by
    linarith only [gammaAnalyticWide52_roots.2.1, gammaAnalyticWide52_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 106200 / 37) (y := 37 / 20) (h := 800 / 16149) (r :=
      2143 / 40) (e := 78619 / 500000) (p := 27807 / 100) (s := 5117 / 250) (z := 16747 / 1000)
      (F := 4391 / 100) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide52_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (106200 / 37 : ℝ) * (37 / 20) = 5310 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide52_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (106200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (106200 / 37 : ℝ)) ≤
      6736 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 535749 / 10000) (T := 2143 / 40) (Z := 39811 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide52_roots.1
      gammaAnalyticWide52_roots.2.1 gammaAnalyticWide52_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide52_power : (106200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 227 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 52 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide52_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2661 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3348 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5310 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2661 / 20)]
  apply
    reject_03_of_analytic_caps (B := 5310) (x := 106200 / 37) (H := 3348 / 25) (R := 535749 / 10000)
      (W := 227 / 20000) (F := 4391 / 100) (U := 6736 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide52_power (gammaAnalyticWide52_main hGRH.riemann)
      (gammaAnalyticWide52_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 53. -/
theorem gammaAnalyticWide53_roots :
    ((134817 / 2500 : ℝ) ≤ Real.sqrt (107600 / 37 : ℝ) ∧
      Real.sqrt (107600 / 37 : ℝ) ≤ 539269 / 10000 ∧ Real.sqrt (5380 : ℝ) ≤ 146697 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 53. -/
theorem gammaAnalyticWide53_logs :
    Real.log (107600 / 37 : ℝ) ≤ 79753 / 10000 ∧ Real.log (5380 : ℝ) ≤ 17181 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (107600 / 37) 12 20 0 (79753 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5380 13 20 0 (17181 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide53_main (hRH : RiemannHypothesis) :
    (22103 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5380,
        Real.exp (-(n : ℝ) / (107600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (107600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 81011) * ((107600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((107600 / 37) * (37 / 20)) + 1) / (4000 / 81011) +
        1839 / 1000 ≤
      35098 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide53_roots.2.2]
  have hs :
    Real.sqrt ((107600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((107600 / 37) * (37 / 20)) +
        21 / 20 ≤
      5129 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide53_roots.2.2, gammaAnalyticWide53_logs.2]
  have hz :
    Real.sqrt (107600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (107600 / 37) + 2469 / 800 ≤
      16783 / 1000 := by
    linarith only [gammaAnalyticWide53_roots.2.1, gammaAnalyticWide53_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 107600 / 37) (y := 37 / 20) (h := 4000 / 81011) (r :=
      539269 / 10000) (e := 78619 / 500000) (p := 35098 / 125) (s := 5129 / 250) (z := 16783 / 1000)
      (F := 22103 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide53_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (107600 / 37 : ℝ) * (37 / 20) = 5380 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide53_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (107600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (107600 / 37 : ℝ)) ≤
      54239 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 134817 / 2500) (T := 539269 / 10000) (Z := 79753 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide53_roots.1
      gammaAnalyticWide53_roots.2.1 gammaAnalyticWide53_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide53_power : (107600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1127 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 53 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide53_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3348 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13481 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5380 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3348 / 25)]
  apply
    reject_03_of_analytic_caps (B := 5380) (x := 107600 / 37) (H := 13481 / 100) (R :=
      134817 / 2500) (W := 1127 / 100000) (F := 22103 / 500) (U := 54239 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide53_power (gammaAnalyticWide53_main hGRH.riemann)
      (gammaAnalyticWide53_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 54. -/
theorem gammaAnalyticWide54_roots :
    ((108573 / 2000 : ℝ) ≤ Real.sqrt (109040 / 37 : ℝ) ∧
      Real.sqrt (109040 / 37 : ℝ) ≤ 271433 / 5000 ∧ Real.sqrt (5452 : ℝ) ≤ 738377 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 54. -/
theorem gammaAnalyticWide54_logs :
    Real.log (109040 / 37 : ℝ) ≤ 39943 / 5000 ∧ Real.log (5452 : ℝ) ≤ 43019 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (109040 / 37) 12 20 0 (39943 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5452 13 20 0 (43019 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide54_main (hRH : RiemannHypothesis) :
    (44509 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5452,
        Real.exp (-(n : ℝ) / (109040 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (109040 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 81277) * ((109040 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((109040 / 37) * (37 / 20)) + 1) / (4000 / 81277) +
        1839 / 1000 ≤
      283567 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide54_roots.2.2]
  have hs :
    Real.sqrt ((109040 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((109040 / 37) * (37 / 20)) +
        21 / 20 ≤
      4113 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide54_roots.2.2, gammaAnalyticWide54_logs.2]
  have hz :
    Real.sqrt (109040 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (109040 / 37) + 2469 / 800 ≤
      16819 / 1000 := by
    linarith only [gammaAnalyticWide54_roots.2.1, gammaAnalyticWide54_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 109040 / 37) (y := 37 / 20) (h := 4000 / 81277) (r :=
      271433 / 5000) (e := 78619 / 500000) (p := 283567 / 1000) (s := 4113 / 200) (z :=
      16819 / 1000) (F := 44509 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide54_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (109040 / 37 : ℝ) * (37 / 20) = 5452 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide54_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (109040 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (109040 / 37 : ℝ)) ≤
      54597 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 108573 / 2000) (T := 271433 / 5000) (Z := 39943 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide54_roots.1
      gammaAnalyticWide54_roots.2.1 gammaAnalyticWide54_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide54_power : (109040 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1119 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 54 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide54_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (13481 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3393 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5452 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13481 / 100)]
  apply
    reject_03_of_analytic_caps (B := 5452) (x := 109040 / 37) (H := 3393 / 25) (R := 108573 / 2000)
      (W := 1119 / 100000) (F := 44509 / 1000) (U := 54597 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide54_power (gammaAnalyticWide54_main hGRH.riemann)
      (gammaAnalyticWide54_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 55. -/
theorem gammaAnalyticWide55_roots :
    ((546487 / 10000 : ℝ) ≤ Real.sqrt (110500 / 37 : ℝ) ∧
      Real.sqrt (110500 / 37 : ℝ) ≤ 68311 / 1250 ∧ Real.sqrt (5525 : ℝ) ≤ 92913 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 55. -/
theorem gammaAnalyticWide55_logs :
    Real.log (110500 / 37 : ℝ) ≤ 80019 / 10000 ∧ Real.log (5525 : ℝ) ≤ 86171 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (110500 / 37) 12 20 0 (80019 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5525 13 20 0 (86171 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide55_main (hRH : RiemannHypothesis) :
    (44813 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5525,
        Real.exp (-(n : ℝ) / (110500 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (110500 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (80 / 1631) * ((110500 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((110500 / 37) * (37 / 20)) + 1) / (80 / 1631) +
        1839 / 1000 ≤
      286379 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide55_roots.2.2]
  have hs :
    Real.sqrt ((110500 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((110500 / 37) * (37 / 20)) +
        21 / 20 ≤
      10307 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide55_roots.2.2, gammaAnalyticWide55_logs.2]
  have hz :
    Real.sqrt (110500 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (110500 / 37) + 2469 / 800 ≤
      2107 / 125 := by
    linarith only [gammaAnalyticWide55_roots.2.1, gammaAnalyticWide55_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 110500 / 37) (y := 37 / 20) (h := 80 / 1631) (r :=
      68311 / 1250) (e := 78619 / 500000) (p := 286379 / 1000) (s := 10307 / 500) (z := 2107 / 125)
      (F := 44813 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide55_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (110500 / 37 : ℝ) * (37 / 20) = 5525 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide55_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (110500 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (110500 / 37 : ℝ)) ≤
      27479 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 546487 / 10000) (T := 68311 / 1250) (Z := 80019 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide55_roots.1
      gammaAnalyticWide55_roots.2.1 gammaAnalyticWide55_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide55_power : (110500 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 111 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 55 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide55_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3393 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13663 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5525 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3393 / 25)]
  apply
    reject_03_of_analytic_caps (B := 5525) (x := 110500 / 37) (H := 13663 / 100) (R :=
      546487 / 10000) (W := 111 / 10000) (F := 44813 / 1000) (U := 27479 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide55_power (gammaAnalyticWide55_main hGRH.riemann)
      (gammaAnalyticWide55_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 56. -/
theorem gammaAnalyticWide56_roots :
    ((68773 / 1250 : ℝ) ≤ Real.sqrt (112000 / 37 : ℝ) ∧
      Real.sqrt (112000 / 37 : ℝ) ≤ 110037 / 2000 ∧ Real.sqrt (5600 : ℝ) ≤ 187083 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 56. -/
theorem gammaAnalyticWide56_logs :
    Real.log (112000 / 37 : ℝ) ≤ 40077 / 5000 ∧ Real.log (5600 : ℝ) ≤ 43153 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (112000 / 37) 12 20 0 (40077 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5600 13 20 0 (43153 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide56_main (hRH : RiemannHypothesis) :
    (11281 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5600,
        Real.exp (-(n : ℝ) / (112000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (112000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 81823) * ((112000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((112000 / 37) * (37 / 20)) + 1) / (4000 / 81823) +
        1839 / 1000 ≤
      144629 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide56_roots.2.2]
  have hs :
    Real.sqrt ((112000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((112000 / 37) * (37 / 20)) +
        21 / 20 ≤
      2583 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide56_roots.2.2, gammaAnalyticWide56_logs.2]
  have hz :
    Real.sqrt (112000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (112000 / 37) + 2469 / 800 ≤
      16893 / 1000 := by
    linarith only [gammaAnalyticWide56_roots.2.1, gammaAnalyticWide56_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 112000 / 37) (y := 37 / 20) (h := 4000 / 81823) (r :=
      110037 / 2000) (e := 78619 / 500000) (p := 144629 / 500) (s := 2583 / 125) (z := 16893 / 1000)
      (F := 11281 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide56_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (112000 / 37 : ℝ) * (37 / 20) = 5600 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide56_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (112000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (112000 / 37 : ℝ)) ≤
      27663 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 68773 / 1250) (T := 110037 / 2000) (Z := 40077 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide56_roots.1
      gammaAnalyticWide56_roots.2.1 gammaAnalyticWide56_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide56_power : (112000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 551 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 56 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide56_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (13663 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13757 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5600 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13663 / 100)]
  apply
    reject_03_of_analytic_caps (B := 5600) (x := 112000 / 37) (H := 13757 / 100) (R := 68773 / 1250)
      (W := 551 / 50000) (F := 11281 / 250) (U := 27663 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide56_power (gammaAnalyticWide56_main hGRH.riemann)
      (gammaAnalyticWide56_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 57. -/
theorem gammaAnalyticWide57_roots :
    ((553953 / 10000 : ℝ) ≤ Real.sqrt (113540 / 37 : ℝ) ∧
      Real.sqrt (113540 / 37 : ℝ) ≤ 276977 / 5000 ∧ Real.sqrt (5677 : ℝ) ≤ 753459 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 57. -/
theorem gammaAnalyticWide57_logs :
    Real.log (113540 / 37 : ℝ) ≤ 8029 / 1000 ∧ Real.log (5677 : ℝ) ≤ 43221 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (113540 / 37) 12 20 0 (8029 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5677 13 20 0 (43221 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide57_main (hRH : RiemannHypothesis) :
    (45441 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5677,
        Real.exp (-(n : ℝ) / (113540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (113540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (400 / 8211) * ((113540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((113540 / 37) * (37 / 20)) + 1) / (400 / 8211) +
        1839 / 1000 ≤
      73051 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide57_roots.2.2]
  have hs :
    Real.sqrt ((113540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((113540 / 37) * (37 / 20)) +
        21 / 20 ≤
      10357 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide57_roots.2.2, gammaAnalyticWide57_logs.2]
  have hz :
    Real.sqrt (113540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (113540 / 37) + 2469 / 800 ≤
      16931 / 1000 := by
    linarith only [gammaAnalyticWide57_roots.2.1, gammaAnalyticWide57_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 113540 / 37) (y := 37 / 20) (h := 400 / 8211) (r :=
      276977 / 5000) (e := 78619 / 500000) (p := 73051 / 250) (s := 10357 / 500) (z := 16931 / 1000)
      (F := 45441 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide57_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (113540 / 37 : ℝ) * (37 / 20) = 5677 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide57_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (113540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (113540 / 37 : ℝ)) ≤
      27851 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 553953 / 10000) (T := 276977 / 5000) (Z := 8029 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide57_roots.1
      gammaAnalyticWide57_roots.2.1 gammaAnalyticWide57_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide57_power : (113540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1093 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 57 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide57_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (13757 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3463 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5677 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13757 / 100)]
  apply
    reject_03_of_analytic_caps (B := 5677) (x := 113540 / 37) (H := 3463 / 25) (R := 553953 / 10000)
      (W := 1093 / 100000) (F := 45441 / 1000) (U := 27851 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide57_power (gammaAnalyticWide57_main hGRH.riemann)
      (gammaAnalyticWide57_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 58. -/
theorem gammaAnalyticWide58_roots :
    ((278897 / 5000 : ℝ) ≤ Real.sqrt (115120 / 37 : ℝ) ∧
      Real.sqrt (115120 / 37 : ℝ) ≤ 111559 / 2000 ∧ Real.sqrt (5756 : ℝ) ≤ 189671 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 58. -/
theorem gammaAnalyticWide58_logs :
    Real.log (115120 / 37 : ℝ) ≤ 80429 / 10000 ∧ Real.log (5756 : ℝ) ≤ 4329 / 500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (115120 / 37) 12 20 0 (80429 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5756 13 20 0 (4329 / 500) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide58_main (hRH : RiemannHypothesis) :
    (11441 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5756,
        Real.exp (-(n : ℝ) / (115120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (115120 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (400 / 8239) * ((115120 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((115120 / 37) * (37 / 20)) + 1) / (400 / 8239) +
        1839 / 1000 ≤
      36902 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide58_roots.2.2]
  have hs :
    Real.sqrt ((115120 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((115120 / 37) * (37 / 20)) +
        21 / 20 ≤
      10383 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide58_roots.2.2, gammaAnalyticWide58_logs.2]
  have hz :
    Real.sqrt (115120 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (115120 / 37) + 2469 / 800 ≤
      16969 / 1000 := by
    linarith only [gammaAnalyticWide58_roots.2.1, gammaAnalyticWide58_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 115120 / 37) (y := 37 / 20) (h := 400 / 8239) (r :=
      111559 / 2000) (e := 78619 / 500000) (p := 36902 / 125) (s := 10383 / 500) (z := 16969 / 1000)
      (F := 11441 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide58_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (115120 / 37 : ℝ) * (37 / 20) = 5756 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide58_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (115120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (115120 / 37 : ℝ)) ≤
      14021 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 278897 / 5000) (T := 111559 / 2000) (Z := 80429 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide58_roots.1
      gammaAnalyticWide58_roots.2.1 gammaAnalyticWide58_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide58_power : (115120 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 217 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 58 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide58_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3463 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (13949 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5756 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3463 / 25)]
  apply
    reject_03_of_analytic_caps (B := 5756) (x := 115120 / 37) (H := 13949 / 100) (R :=
      278897 / 5000) (W := 217 / 20000) (F := 11441 / 250) (U := 14021 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide58_power (gammaAnalyticWide58_main hGRH.riemann)
      (gammaAnalyticWide58_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 59. -/
theorem gammaAnalyticWide59_roots :
    ((112341 / 2000 : ℝ) ≤ Real.sqrt (116740 / 37 : ℝ) ∧
      Real.sqrt (116740 / 37 : ℝ) ≤ 280853 / 5000 ∧ Real.sqrt (5837 : ℝ) ≤ 764003 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 59. -/
theorem gammaAnalyticWide59_logs :
    Real.log (116740 / 37 : ℝ) ≤ 10071 / 1250 ∧ Real.log (5837 : ℝ) ≤ 1084 / 125 := by
  have hc1 : Analysis.rationalLogIntervalCheck (116740 / 37) 12 20 0 (10071 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5837 13 20 0 (1084 / 125) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide59_main (hRH : RiemannHypothesis) :
    (11523 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5837,
        Real.exp (-(n : ℝ) / (116740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (116740 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 82677) * ((116740 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((116740 / 37) * (37 / 20)) + 1) / (4000 / 82677) +
        1839 / 1000 ≤
      298293 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide59_roots.2.2]
  have hs :
    Real.sqrt ((116740 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((116740 / 37) * (37 / 20)) +
        21 / 20 ≤
      10409 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide59_roots.2.2, gammaAnalyticWide59_logs.2]
  have hz :
    Real.sqrt (116740 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (116740 / 37) + 2469 / 800 ≤
      2126 / 125 := by
    linarith only [gammaAnalyticWide59_roots.2.1, gammaAnalyticWide59_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 116740 / 37) (y := 37 / 20) (h := 4000 / 82677) (r :=
      280853 / 5000) (e := 78619 / 500000) (p := 298293 / 1000) (s := 10409 / 500) (z := 2126 / 125)
      (F := 11523 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide59_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (116740 / 37 : ℝ) * (37 / 20) = 5837 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide59_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (116740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (116740 / 37 : ℝ)) ≤
      28237 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 112341 / 2000) (T := 280853 / 5000) (Z := 10071 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticWide59_roots.1
      gammaAnalyticWide59_roots.2.1 gammaAnalyticWide59_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide59_power : (116740 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 269 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 59 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide59_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (13949 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3512 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5837 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 13949 / 100)]
  apply
    reject_03_of_analytic_caps (B := 5837) (x := 116740 / 37) (H := 3512 / 25) (R := 112341 / 2000)
      (W := 269 / 25000) (F := 11523 / 250) (U := 28237 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide59_power (gammaAnalyticWide59_main hGRH.riemann)
      (gammaAnalyticWide59_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 60. -/
theorem gammaAnalyticWide60_roots :
    ((113137 / 2000 : ℝ) ≤ Real.sqrt (3200 : ℝ) ∧
      Real.sqrt (3200 : ℝ) ≤ 282843 / 5000 ∧ Real.sqrt (5920 : ℝ) ≤ 96177 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 60. -/
theorem gammaAnalyticWide60_logs :
    Real.log (3200 : ℝ) ≤ 8071 / 1000 ∧ Real.log (5920 : ℝ) ≤ 86861 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3200) 12 20 0 (8071 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 5920 13 20 0 (86861 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide60_main (hRH : RiemannHypothesis) :
    (46427 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 5920,
        Real.exp (-(n : ℝ) / (3200)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (3200 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 82971) * ((3200) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3200) * (37 / 20)) + 1) / (4000 / 82971) +
        1839 / 1000 ≤
      75359 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide60_roots.2.2]
  have hs :
    Real.sqrt ((3200 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((3200) * (37 / 20)) +
        21 / 20 ≤
      20871 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide60_roots.2.2, gammaAnalyticWide60_logs.2]
  have hz :
    Real.sqrt (3200 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3200) + 2469 / 800 ≤
      17047 / 1000 := by
    linarith only [gammaAnalyticWide60_roots.2.1, gammaAnalyticWide60_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3200) (y := 37 / 20) (h := 4000 / 82971) (r :=
      282843 / 5000) (e := 78619 / 500000) (p := 75359 / 250) (s := 20871 / 1000) (z :=
      17047 / 1000) (F := 46427 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide60_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3200 : ℝ) * (37 / 20) = 5920 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide60_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3200)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (3200 : ℝ)) ≤
      5687 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 113137 / 2000) (T := 282843 / 5000) (Z := 8071 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide60_roots.1
      gammaAnalyticWide60_roots.2.1 gammaAnalyticWide60_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide60_power : (3200 : ℝ) ^ (-9 / 16 : ℝ) ≤ 267 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 60 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide60_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3512 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3537 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (5920 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3512 / 25)]
  apply
    reject_03_of_analytic_caps (B := 5920) (x := 3200) (H := 3537 / 25) (R := 113137 / 2000) (W :=
      267 / 25000) (F := 46427 / 1000) (U := 5687 / 100) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide60_power (gammaAnalyticWide60_main hGRH.riemann)
      (gammaAnalyticWide60_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 61. -/
theorem gammaAnalyticWide61_roots :
    ((142421 / 2500 : ℝ) ≤ Real.sqrt (120080 / 37 : ℝ) ∧
      Real.sqrt (120080 / 37 : ℝ) ≤ 113937 / 2000 ∧ Real.sqrt (6004 : ℝ) ≤ 154971 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 61. -/
theorem gammaAnalyticWide61_logs :
    Real.log (120080 / 37 : ℝ) ≤ 1617 / 200 ∧ Real.log (6004 : ℝ) ≤ 43501 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (120080 / 37) 12 20 0 (1617 / 200) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6004 13 20 0 (43501 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide61_main (hRH : RiemannHypothesis) :
    (46763 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6004,
        Real.exp (-(n : ℝ) / (120080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (120080 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 16653) * ((120080 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((120080 / 37) * (37 / 20)) + 1) / (800 / 16653) +
        1839 / 1000 ≤
      60921 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide61_roots.2.2]
  have hs :
    Real.sqrt ((120080 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((120080 / 37) * (37 / 20)) +
        21 / 20 ≤
      5231 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide61_roots.2.2, gammaAnalyticWide61_logs.2]
  have hz :
    Real.sqrt (120080 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (120080 / 37) + 2469 / 800 ≤
      8543 / 500 := by
    linarith only [gammaAnalyticWide61_roots.2.1, gammaAnalyticWide61_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 120080 / 37) (y := 37 / 20) (h := 800 / 16653) (r :=
      113937 / 2000) (e := 78619 / 500000) (p := 60921 / 200) (s := 5231 / 250) (z := 8543 / 500)
      (F := 46763 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide61_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (120080 / 37 : ℝ) * (37 / 20) = 6004 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide61_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (120080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (120080 / 37 : ℝ)) ≤
      57269 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 142421 / 2500) (T := 113937 / 2000) (Z := 1617 / 200)
      (by norm_num only) (by norm_num only) gammaAnalyticWide61_roots.1
      gammaAnalyticWide61_roots.2.1 gammaAnalyticWide61_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide61_power : (120080 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 53 / 5000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 61 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide61_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3537 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (14249 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6004 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3537 / 25)]
  apply
    reject_03_of_analytic_caps (B := 6004) (x := 120080 / 37) (H := 14249 / 100) (R :=
      142421 / 2500) (W := 53 / 5000) (F := 46763 / 1000) (U := 57269 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide61_power (gammaAnalyticWide61_main hGRH.riemann)
      (gammaAnalyticWide61_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 62. -/
theorem gammaAnalyticWide62_roots :
    ((573797 / 10000 : ℝ) ≤ Real.sqrt (121820 / 37 : ℝ) ∧
      Real.sqrt (121820 / 37 : ℝ) ≤ 286899 / 5000 ∧ Real.sqrt (6091 : ℝ) ≤ 780449 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 62. -/
theorem gammaAnalyticWide62_logs :
    Real.log (121820 / 37 : ℝ) ≤ 40497 / 5000 ∧ Real.log (6091 : ℝ) ≤ 43573 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (121820 / 37) 12 20 0 (40497 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6091 13 20 0 (43573 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide62_main (hRH : RiemannHypothesis) :
    (11777 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6091,
        Real.exp (-(n : ℝ) / (121820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (121820 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 83559) * ((121820 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((121820 / 37) * (37 / 20)) + 1) / (4000 / 83559) +
        1839 / 1000 ≤
      2463 / 8 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide62_roots.2.2]
  have hs :
    Real.sqrt ((121820 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((121820 / 37) * (37 / 20)) +
        21 / 20 ≤
      20979 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide62_roots.2.2, gammaAnalyticWide62_logs.2]
  have hz :
    Real.sqrt (121820 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (121820 / 37) + 2469 / 800 ≤
      17127 / 1000 := by
    linarith only [gammaAnalyticWide62_roots.2.1, gammaAnalyticWide62_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 121820 / 37) (y := 37 / 20) (h := 4000 / 83559) (r :=
      286899 / 5000) (e := 78619 / 500000) (p := 2463 / 8) (s := 20979 / 1000) (z := 17127 / 1000)
      (F := 11777 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide62_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (121820 / 37 : ℝ) * (37 / 20) = 6091 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide62_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (121820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (121820 / 37 : ℝ)) ≤
      57679 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 573797 / 10000) (T := 286899 / 5000) (Z := 40497 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide62_roots.1
      gammaAnalyticWide62_roots.2.1 gammaAnalyticWide62_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide62_power : (121820 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1051 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 62 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide62_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (14249 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (14353 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6091 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 14249 / 100)]
  apply
    reject_03_of_analytic_caps (B := 6091) (x := 121820 / 37) (H := 14353 / 100) (R :=
      573797 / 10000) (W := 1051 / 100000) (F := 11777 / 250) (U := 57679 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide62_power (gammaAnalyticWide62_main hGRH.riemann)
      (gammaAnalyticWide62_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 63. -/
theorem gammaAnalyticWide63_roots :
    ((288987 / 5000 : ℝ) ≤ Real.sqrt (123600 / 37 : ℝ) ∧
      Real.sqrt (123600 / 37 : ℝ) ≤ 23119 / 400 ∧ Real.sqrt (6180 : ℝ) ≤ 78613 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 63. -/
theorem gammaAnalyticWide63_logs :
    Real.log (123600 / 37 : ℝ) ≤ 81139 / 10000 ∧ Real.log (6180 : ℝ) ≤ 87291 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (123600 / 37) 12 20 0 (81139 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6180 13 20 0 (87291 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide63_main (hRH : RiemannHypothesis) :
    (47459 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6180,
        Real.exp (-(n : ℝ) / (123600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (123600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 83867) * ((123600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((123600 / 37) * (37 / 20)) + 1) / (4000 / 83867) +
        1839 / 1000 ≤
      311209 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide63_roots.2.2]
  have hs :
    Real.sqrt ((123600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((123600 / 37) * (37 / 20)) +
        21 / 20 ≤
      10517 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide63_roots.2.2, gammaAnalyticWide63_logs.2]
  have hz :
    Real.sqrt (123600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (123600 / 37) + 2469 / 800 ≤
      2146 / 125 := by
    linarith only [gammaAnalyticWide63_roots.2.1, gammaAnalyticWide63_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 123600 / 37) (y := 37 / 20) (h := 4000 / 83867) (r :=
      23119 / 400) (e := 78619 / 500000) (p := 311209 / 1000) (s := 10517 / 500) (z := 2146 / 125)
      (F := 47459 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide63_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (123600 / 37 : ℝ) * (37 / 20) = 6180 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide63_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (123600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (123600 / 37 : ℝ)) ≤
      11619 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 288987 / 5000) (T := 23119 / 400) (Z := 81139 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide63_roots.1
      gammaAnalyticWide63_roots.2.1 gammaAnalyticWide63_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide63_power : (123600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 521 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 63 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide63_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (14353 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (7229 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6180 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 14353 / 100)]
  apply
    reject_03_of_analytic_caps (B := 6180) (x := 123600 / 37) (H := 7229 / 50) (R := 288987 / 5000)
      (W := 521 / 50000) (F := 47459 / 1000) (U := 11619 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide63_power (gammaAnalyticWide63_main hGRH.riemann)
      (gammaAnalyticWide63_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 64. -/
theorem gammaAnalyticWide64_roots :
    ((582213 / 10000 : ℝ) ≤ Real.sqrt (125420 / 37 : ℝ) ∧
      Real.sqrt (125420 / 37 : ℝ) ≤ 291107 / 5000 ∧ Real.sqrt (6271 : ℝ) ≤ 791897 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 64. -/
theorem gammaAnalyticWide64_logs :
    Real.log (125420 / 37 : ℝ) ≤ 40643 / 5000 ∧ Real.log (6271 : ℝ) ≤ 87437 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (125420 / 37) 12 20 0 (40643 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6271 13 20 0 (87437 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide64_main (hRH : RiemannHypothesis) :
    (5977 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6271,
        Real.exp (-(n : ℝ) / (125420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (125420 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (160 / 3367) * ((125420 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((125420 / 37) * (37 / 20)) + 1) / (160 / 3367) +
        1839 / 1000 ≤
      62921 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide64_roots.2.2]
  have hs :
    Real.sqrt ((125420 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((125420 / 37) * (37 / 20)) +
        21 / 20 ≤
      2109 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide64_roots.2.2, gammaAnalyticWide64_logs.2]
  have hz :
    Real.sqrt (125420 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (125420 / 37) + 2469 / 800 ≤
      17209 / 1000 := by
    linarith only [gammaAnalyticWide64_roots.2.1, gammaAnalyticWide64_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 125420 / 37) (y := 37 / 20) (h := 160 / 3367) (r :=
      291107 / 5000) (e := 78619 / 500000) (p := 62921 / 200) (s := 2109 / 100) (z := 17209 / 1000)
      (F := 5977 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide64_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (125420 / 37 : ℝ) * (37 / 20) = 6271 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide64_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (125420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (125420 / 37 : ℝ)) ≤
      58517 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 582213 / 10000) (T := 291107 / 5000) (Z := 40643 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide64_roots.1
      gammaAnalyticWide64_roots.2.1 gammaAnalyticWide64_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide64_power : (125420 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 517 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 64 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide64_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (7229 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2913 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6271 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 7229 / 50)]
  apply
    reject_03_of_analytic_caps (B := 6271) (x := 125420 / 37) (H := 2913 / 20) (R := 582213 / 10000)
      (W := 517 / 50000) (F := 5977 / 125) (U := 58517 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide64_power (gammaAnalyticWide64_main hGRH.riemann)
      (gammaAnalyticWide64_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 65. -/
theorem gammaAnalyticWide65_roots :
    ((117303 / 2000 : ℝ) ≤ Real.sqrt (3440 : ℝ) ∧
      Real.sqrt (3440 : ℝ) ≤ 146629 / 2500 ∧ Real.sqrt (6364 : ℝ) ≤ 797747 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 65. -/
theorem gammaAnalyticWide65_logs :
    Real.log (3440 : ℝ) ≤ 81433 / 10000 ∧ Real.log (6364 : ℝ) ≤ 17517 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3440) 12 20 0 (81433 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6364 13 20 0 (17517 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide65_main (hRH : RiemannHypothesis) :
    (48177 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6364,
        Real.exp (-(n : ℝ) / (3440)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (3440 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 84483) * ((3440) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3440) * (37 / 20)) + 1) / (4000 / 84483) +
        1839 / 1000 ≤
      318063 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide65_roots.2.2]
  have hs :
    Real.sqrt ((3440 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((3440) * (37 / 20)) +
        21 / 20 ≤
      10573 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide65_roots.2.2, gammaAnalyticWide65_logs.2]
  have hz :
    Real.sqrt (3440 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3440) + 2469 / 800 ≤
      17251 / 1000 := by
    linarith only [gammaAnalyticWide65_roots.2.1, gammaAnalyticWide65_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3440) (y := 37 / 20) (h := 4000 / 84483) (r :=
      146629 / 2500) (e := 78619 / 500000) (p := 318063 / 1000) (s := 10573 / 500) (z :=
      17251 / 1000) (F := 48177 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide65_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3440 : ℝ) * (37 / 20) = 6364 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide65_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3440)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (3440 : ℝ)) ≤
      29473 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 117303 / 2000) (T := 146629 / 2500) (Z := 81433 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide65_roots.1
      gammaAnalyticWide65_roots.2.1 gammaAnalyticWide65_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide65_power : (3440 : ℝ) ^ (-9 / 16 : ℝ) ≤ 41 / 4000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 65 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide65_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2913 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (7337 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6364 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2913 / 20)]
  apply
    reject_03_of_analytic_caps (B := 6364) (x := 3440) (H := 7337 / 50) (R := 117303 / 2000) (W :=
      41 / 4000) (F := 48177 / 1000) (U := 29473 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide65_power (gammaAnalyticWide65_main hGRH.riemann)
      (gammaAnalyticWide65_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 66. -/
theorem gammaAnalyticWide66_roots :
    ((147719 / 2500 : ℝ) ≤ Real.sqrt (129180 / 37 : ℝ) ∧
      Real.sqrt (129180 / 37 : ℝ) ≤ 590877 / 10000 ∧ Real.sqrt (6459 : ℝ) ≤ 10046 / 125) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 66. -/
theorem gammaAnalyticWide66_logs :
    Real.log (129180 / 37 : ℝ) ≤ 81581 / 10000 ∧ Real.log (6459 : ℝ) ≤ 87733 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (129180 / 37) 12 20 0 (81581 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6459 13 20 0 (87733 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide66_main (hRH : RiemannHypothesis) :
    (48543 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6459,
        Real.exp (-(n : ℝ) / (129180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (129180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 42399) * ((129180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((129180 / 37) * (37 / 20)) + 1) / (2000 / 42399) +
        1839 / 1000 ≤
      160791 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide66_roots.2.2]
  have hs :
    Real.sqrt ((129180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((129180 / 37) * (37 / 20)) +
        21 / 20 ≤
      21203 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide66_roots.2.2, gammaAnalyticWide66_logs.2]
  have hz :
    Real.sqrt (129180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (129180 / 37) + 2469 / 800 ≤
      17293 / 1000 := by
    linarith only [gammaAnalyticWide66_roots.2.1, gammaAnalyticWide66_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 129180 / 37) (y := 37 / 20) (h := 2000 / 42399) (r :=
      590877 / 10000) (e := 78619 / 500000) (p := 160791 / 500) (s := 21203 / 1000) (z :=
      17293 / 1000) (F := 48543 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide66_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (129180 / 37 : ℝ) * (37 / 20) = 6459 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide66_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (129180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (129180 / 37 : ℝ)) ≤
      59381 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 147719 / 2500) (T := 590877 / 10000) (Z := 81581 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide66_roots.1
      gammaAnalyticWide66_roots.2.1 gammaAnalyticWide66_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide66_power : (129180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1017 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 66 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide66_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (7337 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (14783 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6459 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 7337 / 50)]
  apply
    reject_03_of_analytic_caps (B := 6459) (x := 129180 / 37) (H := 14783 / 100) (R :=
      147719 / 2500) (W := 1017 / 100000) (F := 48543 / 1000) (U := 59381 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide66_power (gammaAnalyticWide66_main hGRH.riemann)
      (gammaAnalyticWide66_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 67. -/
theorem gammaAnalyticWide67_roots :
    ((37206 / 625 : ℝ) ≤ Real.sqrt (131120 / 37 : ℝ) ∧
      Real.sqrt (131120 / 37 : ℝ) ≤ 595297 / 10000 ∧ Real.sqrt (6556 : ℝ) ≤ 202423 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 67. -/
theorem gammaAnalyticWide67_logs :
    Real.log (131120 / 37 : ℝ) ≤ 8173 / 1000 ∧ Real.log (6556 : ℝ) ≤ 43941 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (131120 / 37) 12 20 0 (8173 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6556 13 20 0 (43941 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide67_main (hRH : RiemannHypothesis) :
    (9783 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6556,
        Real.exp (-(n : ℝ) / (131120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (131120 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 85113) * ((131120 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((131120 / 37) * (37 / 20)) + 1) / (4000 / 85113) +
        1839 / 1000 ≤
      162581 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide67_roots.2.2]
  have hs :
    Real.sqrt ((131120 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((131120 / 37) * (37 / 20)) +
        21 / 20 ≤
      1063 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide67_roots.2.2, gammaAnalyticWide67_logs.2]
  have hz :
    Real.sqrt (131120 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (131120 / 37) + 2469 / 800 ≤
      2167 / 125 := by
    linarith only [gammaAnalyticWide67_roots.2.1, gammaAnalyticWide67_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 131120 / 37) (y := 37 / 20) (h := 4000 / 85113) (r :=
      595297 / 10000) (e := 78619 / 500000) (p := 162581 / 500) (s := 1063 / 50) (z := 2167 / 125)
      (F := 9783 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide67_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (131120 / 37 : ℝ) * (37 / 20) = 6556 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide67_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (131120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (131120 / 37 : ℝ)) ≤
      59821 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 37206 / 625) (T := 595297 / 10000) (Z := 8173 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide67_roots.1
      gammaAnalyticWide67_roots.2.1 gammaAnalyticWide67_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide67_power : (131120 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 63 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 67 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide67_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (14783 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2979 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6556 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 14783 / 100)]
  apply
    reject_03_of_analytic_caps (B := 6556) (x := 131120 / 37) (H := 2979 / 20) (R := 37206 / 625)
      (W := 63 / 6250) (F := 9783 / 200) (U := 59821 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide67_power (gammaAnalyticWide67_main hGRH.riemann)
      (gammaAnalyticWide67_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 68. -/
theorem gammaAnalyticWide68_roots :
    ((299887 / 5000 : ℝ) ≤ Real.sqrt (133100 / 37 : ℝ) ∧
      Real.sqrt (133100 / 37 : ℝ) ≤ 23991 / 400 ∧ Real.sqrt (6655 : ℝ) ≤ 407891 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 68. -/
theorem gammaAnalyticWide68_logs :
    Real.log (133100 / 37 : ℝ) ≤ 2047 / 250 ∧ Real.log (6655 : ℝ) ≤ 5502 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (133100 / 37) 12 20 0 (2047 / 250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6655 13 20 0 (5502 / 625) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide68_main (hRH : RiemannHypothesis) :
    (49291 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6655,
        Real.exp (-(n : ℝ) / (133100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (133100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 17087) * ((133100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((133100 / 37) * (37 / 20)) + 1) / (800 / 17087) +
        1839 / 1000 ≤
      164401 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide68_roots.2.2]
  have hs :
    Real.sqrt ((133100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((133100 / 37) * (37 / 20)) +
        21 / 20 ≤
      10659 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide68_roots.2.2, gammaAnalyticWide68_logs.2]
  have hz :
    Real.sqrt (133100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (133100 / 37) + 2469 / 800 ≤
      17379 / 1000 := by
    linarith only [gammaAnalyticWide68_roots.2.1, gammaAnalyticWide68_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 133100 / 37) (y := 37 / 20) (h := 800 / 17087) (r :=
      23991 / 400) (e := 78619 / 500000) (p := 164401 / 500) (s := 10659 / 500) (z := 17379 / 1000)
      (F := 49291 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide68_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (133100 / 37 : ℝ) * (37 / 20) = 6655 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide68_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (133100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (133100 / 37 : ℝ)) ≤
      15067 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 299887 / 5000) (T := 23991 / 400) (Z := 2047 / 250)
      (by norm_num only) (by norm_num only) gammaAnalyticWide68_roots.1
      gammaAnalyticWide68_roots.2.1 gammaAnalyticWide68_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide68_power : (133100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1 / 100 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 68 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide68_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2979 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3752 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6655 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2979 / 20)]
  apply
    reject_03_of_analytic_caps (B := 6655) (x := 133100 / 37) (H := 3752 / 25) (R := 299887 / 5000)
      (W := 1 / 100) (F := 49291 / 1000) (U := 15067 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide68_power (gammaAnalyticWide68_main hGRH.riemann)
      (gammaAnalyticWide68_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 69. -/
theorem gammaAnalyticWide69_roots :
    ((604353 / 10000 : ℝ) ≤ Real.sqrt (135140 / 37 : ℝ) ∧
      Real.sqrt (135140 / 37 : ℝ) ≤ 302177 / 5000 ∧ Real.sqrt (6757 : ℝ) ≤ 82201 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 69. -/
theorem gammaAnalyticWide69_logs :
    Real.log (135140 / 37 : ℝ) ≤ 5127 / 625 ∧ Real.log (6757 : ℝ) ≤ 11023 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (135140 / 37) 12 20 0 (5127 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6757 13 20 0 (11023 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide69_main (hRH : RiemannHypothesis) :
    (12419 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6757,
        Real.exp (-(n : ℝ) / (135140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (135140 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 85757) * ((135140 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((135140 / 37) * (37 / 20)) + 1) / (4000 / 85757) +
        1839 / 1000 ≤
      166269 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide69_roots.2.2]
  have hs :
    Real.sqrt ((135140 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((135140 / 37) * (37 / 20)) +
        21 / 20 ≤
      10689 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide69_roots.2.2, gammaAnalyticWide69_logs.2]
  have hz :
    Real.sqrt (135140 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (135140 / 37) + 2469 / 800 ≤
      17423 / 1000 := by
    linarith only [gammaAnalyticWide69_roots.2.1, gammaAnalyticWide69_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 135140 / 37) (y := 37 / 20) (h := 4000 / 85757) (r :=
      302177 / 5000) (e := 78619 / 500000) (p := 166269 / 500) (s := 10689 / 500) (z :=
      17423 / 1000) (F := 12419 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide69_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (135140 / 37 : ℝ) * (37 / 20) = 6757 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide69_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (135140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (135140 / 37 : ℝ)) ≤
      15181 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 604353 / 10000) (T := 302177 / 5000) (Z := 5127 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticWide69_roots.1
      gammaAnalyticWide69_roots.2.1 gammaAnalyticWide69_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide69_power : (135140 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 991 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 69 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide69_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3752 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15123 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6757 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3752 / 25)]
  apply
    reject_03_of_analytic_caps (B := 6757) (x := 135140 / 37) (H := 15123 / 100) (R :=
      604353 / 10000) (W := 991 / 100000) (F := 12419 / 250) (U := 15181 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide69_power (gammaAnalyticWide69_main hGRH.riemann)
      (gammaAnalyticWide69_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 70. -/
theorem gammaAnalyticWide70_roots :
    ((304493 / 5000 : ℝ) ≤ Real.sqrt (137220 / 37 : ℝ) ∧
      Real.sqrt (137220 / 37 : ℝ) ≤ 608987 / 10000 ∧ Real.sqrt (6861 : ℝ) ≤ 103539 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 70. -/
theorem gammaAnalyticWide70_logs :
    Real.log (137220 / 37 : ℝ) ≤ 16437 / 2000 ∧ Real.log (6861 : ℝ) ≤ 88337 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (137220 / 37) 12 20 0 (16437 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6861 13 20 0 (88337 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide70_main (hRH : RiemannHypothesis) :
    (10013 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6861,
        Real.exp (-(n : ℝ) / (137220 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (137220 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 43043) * ((137220 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((137220 / 37) * (37 / 20)) + 1) / (2000 / 43043) +
        1839 / 1000 ≤
      336333 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide70_roots.2.2]
  have hs :
    Real.sqrt ((137220 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((137220 / 37) * (37 / 20)) +
        21 / 20 ≤
      21437 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide70_roots.2.2, gammaAnalyticWide70_logs.2]
  have hz :
    Real.sqrt (137220 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (137220 / 37) + 2469 / 800 ≤
      17467 / 1000 := by
    linarith only [gammaAnalyticWide70_roots.2.1, gammaAnalyticWide70_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 137220 / 37) (y := 37 / 20) (h := 2000 / 43043) (r :=
      608987 / 10000) (e := 78619 / 500000) (p := 336333 / 1000) (s := 21437 / 1000) (z :=
      17467 / 1000) (F := 10013 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide70_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (137220 / 37 : ℝ) * (37 / 20) = 6861 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide70_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (137220 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (137220 / 37 : ℝ)) ≤
      30593 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 304493 / 5000) (T := 608987 / 10000) (Z := 16437 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide70_roots.1
      gammaAnalyticWide70_roots.2.1 gammaAnalyticWide70_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide70_power : (137220 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 983 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 70 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide70_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15123 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (762 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6861 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15123 / 100)]
  apply
    reject_03_of_analytic_caps (B := 6861) (x := 137220 / 37) (H := 762 / 5) (R := 304493 / 5000)
      (W := 983 / 100000) (F := 10013 / 200) (U := 30593 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide70_power (gammaAnalyticWide70_main hGRH.riemann)
      (gammaAnalyticWide70_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 71. -/
theorem gammaAnalyticWide71_roots :
    ((613673 / 10000 : ℝ) ≤ Real.sqrt (139340 / 37 : ℝ) ∧
      Real.sqrt (139340 / 37 : ℝ) ≤ 306837 / 5000 ∧ Real.sqrt (6967 : ℝ) ≤ 417343 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 71. -/
theorem gammaAnalyticWide71_logs :
    Real.log (139340 / 37 : ℝ) ≤ 41169 / 5000 ∧ Real.log (6967 : ℝ) ≤ 8849 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (139340 / 37) 12 20 0 (41169 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 6967 13 20 0 (8849 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide71_main (hRH : RiemannHypothesis) :
    (50459 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 6967,
        Real.exp (-(n : ℝ) / (139340 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (139340 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 43211) * ((139340 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((139340 / 37) * (37 / 20)) + 1) / (2000 / 43211) +
        1839 / 1000 ≤
      170093 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide71_roots.2.2]
  have hs :
    Real.sqrt ((139340 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((139340 / 37) * (37 / 20)) +
        21 / 20 ≤
      21497 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide71_roots.2.2, gammaAnalyticWide71_logs.2]
  have hz :
    Real.sqrt (139340 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (139340 / 37) + 2469 / 800 ≤
      2189 / 125 := by
    linarith only [gammaAnalyticWide71_roots.2.1, gammaAnalyticWide71_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 139340 / 37) (y := 37 / 20) (h := 2000 / 43211) (r :=
      306837 / 5000) (e := 78619 / 500000) (p := 170093 / 500) (s := 21497 / 1000) (z := 2189 / 125)
      (F := 50459 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide71_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (139340 / 37 : ℝ) * (37 / 20) = 6967 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide71_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (139340 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (139340 / 37 : ℝ)) ≤
      61653 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 613673 / 10000) (T := 306837 / 5000) (Z := 41169 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide71_roots.1
      gammaAnalyticWide71_roots.2.1 gammaAnalyticWide71_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide71_power : (139340 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 39 / 4000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 71 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide71_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (762 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (7679 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (6967 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 762 / 5)]
  apply
    reject_03_of_analytic_caps (B := 6967) (x := 139340 / 37) (H := 7679 / 50) (R := 613673 / 10000)
      (W := 39 / 4000) (F := 50459 / 1000) (U := 61653 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide71_power (gammaAnalyticWide71_main hGRH.riemann)
      (gammaAnalyticWide71_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 72. -/
theorem gammaAnalyticWide72_roots :
    ((309227 / 5000 : ℝ) ≤ Real.sqrt (141520 / 37 : ℝ) ∧
      Real.sqrt (141520 / 37 : ℝ) ≤ 123691 / 2000 ∧ Real.sqrt (7076 : ℝ) ≤ 84119 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 72. -/
theorem gammaAnalyticWide72_logs :
    Real.log (141520 / 37 : ℝ) ≤ 82493 / 10000 ∧ Real.log (7076 : ℝ) ≤ 17729 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (141520 / 37) 12 20 0 (82493 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 7076 13 20 0 (17729 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide72_main (hRH : RiemannHypothesis) :
    (2543 / 50 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 7076,
        Real.exp (-(n : ℝ) / (141520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (141520 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 86751) * ((141520 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((141520 / 37) * (37 / 20)) + 1) / (4000 / 86751) +
        1839 / 1000 ≤
      344133 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide72_roots.2.2]
  have hs :
    Real.sqrt ((141520 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((141520 / 37) * (37 / 20)) +
        21 / 20 ≤
      10779 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide72_roots.2.2, gammaAnalyticWide72_logs.2]
  have hz :
    Real.sqrt (141520 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (141520 / 37) + 2469 / 800 ≤
      17557 / 1000 := by
    linarith only [gammaAnalyticWide72_roots.2.1, gammaAnalyticWide72_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 141520 / 37) (y := 37 / 20) (h := 4000 / 86751) (r :=
      123691 / 2000) (e := 78619 / 500000) (p := 344133 / 1000) (s := 10779 / 500) (z :=
      17557 / 1000) (F := 2543 / 50) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide72_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (141520 / 37 : ℝ) * (37 / 20) = 7076 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide72_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (141520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (141520 / 37 : ℝ)) ≤
      6213 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 309227 / 5000) (T := 123691 / 2000) (Z := 82493 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide72_roots.1
      gammaAnalyticWide72_roots.2.1 gammaAnalyticWide72_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide72_power : (141520 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 483 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 72 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide72_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (7679 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15479 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (7076 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 7679 / 50)]
  apply
    reject_03_of_analytic_caps (B := 7076) (x := 141520 / 37) (H := 15479 / 100) (R :=
      309227 / 5000) (W := 483 / 50000) (F := 2543 / 50) (U := 6213 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide72_power (gammaAnalyticWide72_main hGRH.riemann)
      (gammaAnalyticWide72_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 73. -/
theorem gammaAnalyticWide73_roots :
    ((311643 / 5000 : ℝ) ≤ Real.sqrt (143740 / 37 : ℝ) ∧
      Real.sqrt (143740 / 37 : ℝ) ≤ 623287 / 10000 ∧ Real.sqrt (7187 : ℝ) ≤ 423881 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 73. -/
theorem gammaAnalyticWide73_logs :
    Real.log (143740 / 37 : ℝ) ≤ 82649 / 10000 ∧ Real.log (7187 : ℝ) ≤ 88801 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (143740 / 37) 12 20 0 (82649 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 7187 13 20 0 (88801 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide73_main (hRH : RiemannHypothesis) :
    (25633 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 7187,
        Real.exp (-(n : ℝ) / (143740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (143740 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 43547) * ((143740 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((143740 / 37) * (37 / 20)) + 1) / (2000 / 43547) +
        1839 / 1000 ≤
      348137 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide73_roots.2.2]
  have hs :
    Real.sqrt ((143740 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((143740 / 37) * (37 / 20)) +
        21 / 20 ≤
      1081 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide73_roots.2.2, gammaAnalyticWide73_logs.2]
  have hz :
    Real.sqrt (143740 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (143740 / 37) + 2469 / 800 ≤
      17603 / 1000 := by
    linarith only [gammaAnalyticWide73_roots.2.1, gammaAnalyticWide73_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 143740 / 37) (y := 37 / 20) (h := 2000 / 43547) (r :=
      623287 / 10000) (e := 78619 / 500000) (p := 348137 / 1000) (s := 1081 / 50) (z :=
      17603 / 1000) (F := 25633 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide73_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (143740 / 37 : ℝ) * (37 / 20) = 7187 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide73_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (143740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (143740 / 37 : ℝ)) ≤
      15653 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 311643 / 5000) (T := 623287 / 10000) (Z := 82649 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide73_roots.1
      gammaAnalyticWide73_roots.2.1 gammaAnalyticWide73_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide73_power : (143740 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 479 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 73 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide73_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15479 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (156 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (7187 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15479 / 100)]
  apply
    reject_03_of_analytic_caps (B := 7187) (x := 143740 / 37) (H := 156) (R := 311643 / 5000) (W :=
      479 / 50000) (F := 25633 / 500) (U := 15653 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide73_power (gammaAnalyticWide73_main hGRH.riemann)
      (gammaAnalyticWide73_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 74. -/
theorem gammaAnalyticWide74_roots :
    ((628167 / 10000 : ℝ) ≤ Real.sqrt (146000 / 37 : ℝ) ∧
      Real.sqrt (146000 / 37 : ℝ) ≤ 78521 / 1250 ∧ Real.sqrt (7300 : ℝ) ≤ 854401 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 74. -/
theorem gammaAnalyticWide74_logs :
    Real.log (146000 / 37 : ℝ) ≤ 16561 / 2000 ∧ Real.log (7300 : ℝ) ≤ 88957 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (146000 / 37) 12 20 0 (16561 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 7300 13 20 0 (88957 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide74_main (hRH : RiemannHypothesis) :
    (12919 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 7300,
        Real.exp (-(n : ℝ) / (146000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (146000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (400 / 8743) * ((146000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((146000 / 37) * (37 / 20)) + 1) / (400 / 8743) +
        1839 / 1000 ≤
      352197 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide74_roots.2.2]
  have hs :
    Real.sqrt ((146000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((146000 / 37) * (37 / 20)) +
        21 / 20 ≤
      10841 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide74_roots.2.2, gammaAnalyticWide74_logs.2]
  have hz :
    Real.sqrt (146000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (146000 / 37) + 2469 / 800 ≤
      2206 / 125 := by
    linarith only [gammaAnalyticWide74_roots.2.1, gammaAnalyticWide74_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 146000 / 37) (y := 37 / 20) (h := 400 / 8743) (r :=
      78521 / 1250) (e := 78619 / 500000) (p := 352197 / 1000) (s := 10841 / 500) (z := 2206 / 125)
      (F := 12919 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide74_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (146000 / 37 : ℝ) * (37 / 20) = 7300 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide74_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (146000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (146000 / 37 : ℝ)) ≤
      31549 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 628167 / 10000) (T := 78521 / 1250) (Z := 16561 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide74_roots.1
      gammaAnalyticWide74_roots.2.1 gammaAnalyticWide74_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide74_power : (146000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 949 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 74 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide74_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (156 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15723 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (7300 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 156)]
  apply
    reject_03_of_analytic_caps (B := 7300) (x := 146000 / 37) (H := 15723 / 100) (R :=
      628167 / 10000) (W := 949 / 100000) (F := 12919 / 250) (U := 31549 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide74_power (gammaAnalyticWide74_main hGRH.riemann)
      (gammaAnalyticWide74_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 75. -/
theorem gammaAnalyticWide75_roots :
    ((316569 / 5000 : ℝ) ≤ Real.sqrt (148320 / 37 : ℝ) ∧
      Real.sqrt (148320 / 37 : ℝ) ≤ 633139 / 10000 ∧ Real.sqrt (7416 : ℝ) ≤ 861163 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 75. -/
theorem gammaAnalyticWide75_logs :
    Real.log (148320 / 37 : ℝ) ≤ 82963 / 10000 ∧ Real.log (7416 : ℝ) ≤ 44557 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (148320 / 37) 12 20 0 (82963 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 7416 13 20 0 (44557 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide75_main (hRH : RiemannHypothesis) :
    (26047 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 7416,
        Real.exp (-(n : ℝ) / (148320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (148320 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (200 / 4389) * ((148320 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((148320 / 37) * (37 / 20)) + 1) / (200 / 4389) +
        1839 / 1000 ≤
      89087 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide75_roots.2.2]
  have hs :
    Real.sqrt ((148320 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((148320 / 37) * (37 / 20)) +
        21 / 20 ≤
      2718 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide75_roots.2.2, gammaAnalyticWide75_logs.2]
  have hz :
    Real.sqrt (148320 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (148320 / 37) + 2469 / 800 ≤
      3539 / 200 := by
    linarith only [gammaAnalyticWide75_roots.2.1, gammaAnalyticWide75_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 148320 / 37) (y := 37 / 20) (h := 200 / 4389) (r :=
      633139 / 10000) (e := 78619 / 500000) (p := 89087 / 250) (s := 2718 / 125) (z := 3539 / 200)
      (F := 26047 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide75_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (148320 / 37 : ℝ) * (37 / 20) = 7416 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide75_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (148320 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (148320 / 37 : ℝ)) ≤
      31797 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 316569 / 5000) (T := 633139 / 10000) (Z := 82963 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide75_roots.1
      gammaAnalyticWide75_roots.2.1 gammaAnalyticWide75_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide75_power : (148320 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 941 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 75 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide75_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15723 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15849 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (7416 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15723 / 100)]
  apply
    reject_03_of_analytic_caps (B := 7416) (x := 148320 / 37) (H := 15849 / 100) (R :=
      316569 / 5000) (W := 941 / 100000) (F := 26047 / 500) (U := 31797 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide75_power (gammaAnalyticWide75_main hGRH.riemann)
      (gammaAnalyticWide75_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 76. -/
theorem gammaAnalyticWide76_roots :
    ((319099 / 5000 : ℝ) ≤ Real.sqrt (150700 / 37 : ℝ) ∧
      Real.sqrt (150700 / 37 : ℝ) ≤ 638199 / 10000 ∧ Real.sqrt (7535 : ℝ) ≤ 217011 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 76. -/
theorem gammaAnalyticWide76_logs :
    Real.log (150700 / 37 : ℝ) ≤ 41561 / 5000 ∧ Real.log (7535 : ℝ) ≤ 44637 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (150700 / 37) 12 20 0 (41561 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 7535 13 20 0 (44637 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide76_main (hRH : RiemannHypothesis) :
    (52519 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 7535,
        Real.exp (-(n : ℝ) / (150700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (150700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (400 / 8813) * ((150700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((150700 / 37) * (37 / 20)) + 1) / (400 / 8813) +
        1839 / 1000 ≤
      360589 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide76_roots.2.2]
  have hs :
    Real.sqrt ((150700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((150700 / 37) * (37 / 20)) +
        21 / 20 ≤
      2726 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide76_roots.2.2, gammaAnalyticWide76_logs.2]
  have hz :
    Real.sqrt (150700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (150700 / 37) + 2469 / 800 ≤
      8871 / 500 := by
    linarith only [gammaAnalyticWide76_roots.2.1, gammaAnalyticWide76_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 150700 / 37) (y := 37 / 20) (h := 400 / 8813) (r :=
      638199 / 10000) (e := 78619 / 500000) (p := 360589 / 1000) (s := 2726 / 125) (z := 8871 / 500)
      (F := 52519 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide76_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (150700 / 37 : ℝ) * (37 / 20) = 7535 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide76_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (150700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (150700 / 37 : ℝ)) ≤
      32049 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 319099 / 5000) (T := 638199 / 10000) (Z := 41561 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide76_roots.1
      gammaAnalyticWide76_roots.2.1 gammaAnalyticWide76_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide76_power : (150700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 933 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 76 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide76_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15849 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3994 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (7535 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15849 / 100)]
  apply
    reject_03_of_analytic_caps (B := 7535) (x := 150700 / 37) (H := 3994 / 25) (R := 319099 / 5000)
      (W := 933 / 100000) (F := 52519 / 1000) (U := 32049 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide76_power (gammaAnalyticWide76_main hGRH.riemann)
      (gammaAnalyticWide76_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 77. -/
theorem gammaAnalyticWide77_roots :
    ((321651 / 5000 : ℝ) ≤ Real.sqrt (153120 / 37 : ℝ) ∧
      Real.sqrt (153120 / 37 : ℝ) ≤ 643303 / 10000 ∧ Real.sqrt (7656 : ℝ) ≤ 437493 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 77. -/
theorem gammaAnalyticWide77_logs :
    Real.log (153120 / 37 : ℝ) ≤ 83281 / 10000 ∧ Real.log (7656 : ℝ) ≤ 89433 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (153120 / 37) 13 20 0 (83281 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 7656 13 20 0 (89433 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide77_main (hRH : RiemannHypothesis) :
    (52947 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 7656,
        Real.exp (-(n : ℝ) / (153120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (153120 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (25 / 553) * ((153120 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((153120 / 37) * (37 / 20)) + 1) / (25 / 553) +
        1839 / 1000 ≤
      72977 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide77_roots.2.2]
  have hs :
    Real.sqrt ((153120 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((153120 / 37) * (37 / 20)) +
        21 / 20 ≤
      2734 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide77_roots.2.2, gammaAnalyticWide77_logs.2]
  have hz :
    Real.sqrt (153120 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (153120 / 37) + 2469 / 800 ≤
      1779 / 100 := by
    linarith only [gammaAnalyticWide77_roots.2.1, gammaAnalyticWide77_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 153120 / 37) (y := 37 / 20) (h := 25 / 553) (r :=
      643303 / 10000) (e := 78619 / 500000) (p := 72977 / 200) (s := 2734 / 125) (z := 1779 / 100)
      (F := 52947 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide77_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (153120 / 37 : ℝ) * (37 / 20) = 7656 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide77_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (153120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (153120 / 37 : ℝ)) ≤
      64607 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 321651 / 5000) (T := 643303 / 10000) (Z := 83281 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide77_roots.1
      gammaAnalyticWide77_roots.2.1 gammaAnalyticWide77_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide77_power : (153120 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 231 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 77 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide77_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3994 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4026 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (7656 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3994 / 25)]
  apply
    reject_03_of_analytic_caps (B := 7656) (x := 153120 / 37) (H := 4026 / 25) (R := 321651 / 5000)
      (W := 231 / 25000) (F := 52947 / 1000) (U := 64607 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide77_power (gammaAnalyticWide77_main hGRH.riemann)
      (gammaAnalyticWide77_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 78. -/
theorem gammaAnalyticWide78_roots :
    ((64849 / 1000 : ℝ) ≤ Real.sqrt (155600 / 37 : ℝ) ∧
      Real.sqrt (155600 / 37 : ℝ) ≤ 648491 / 10000 ∧ Real.sqrt (7780 : ℝ) ≤ 220511 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 78. -/
theorem gammaAnalyticWide78_logs :
    Real.log (155600 / 37 : ℝ) ≤ 41721 / 5000 ∧ Real.log (7780 : ℝ) ≤ 44797 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (155600 / 37) 13 20 0 (41721 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 7780 13 20 0 (44797 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide78_main (hRH : RiemannHypothesis) :
    (53383 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 7780,
        Real.exp (-(n : ℝ) / (155600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (155600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 88837) * ((155600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((155600 / 37) * (37 / 20)) + 1) / (4000 / 88837) +
        1839 / 1000 ≤
      36927 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide78_roots.2.2]
  have hs :
    Real.sqrt ((155600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((155600 / 37) * (37 / 20)) +
        21 / 20 ≤
      21937 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide78_roots.2.2, gammaAnalyticWide78_logs.2]
  have hz :
    Real.sqrt (155600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (155600 / 37) + 2469 / 800 ≤
      8919 / 500 := by
    linarith only [gammaAnalyticWide78_roots.2.1, gammaAnalyticWide78_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 155600 / 37) (y := 37 / 20) (h := 4000 / 88837) (r :=
      648491 / 10000) (e := 78619 / 500000) (p := 36927 / 100) (s := 21937 / 1000) (z := 8919 / 500)
      (F := 53383 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide78_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (155600 / 37 : ℝ) * (37 / 20) = 7780 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide78_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (155600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (155600 / 37 : ℝ)) ≤
      521 / 8 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 64849 / 1000) (T := 648491 / 10000) (Z := 41721 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide78_roots.1
      gammaAnalyticWide78_roots.2.1 gammaAnalyticWide78_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide78_power : (155600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 229 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 78 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide78_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (4026 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3247 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (7780 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 4026 / 25)]
  apply
    reject_03_of_analytic_caps (B := 7780) (x := 155600 / 37) (H := 3247 / 20) (R := 64849 / 1000)
      (W := 229 / 25000) (F := 53383 / 1000) (U := 521 / 8) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide78_power (gammaAnalyticWide78_main hGRH.riemann)
      (gammaAnalyticWide78_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 79. -/
theorem gammaAnalyticWide79_roots :
    ((326881 / 5000 : ℝ) ≤ Real.sqrt (158140 / 37 : ℝ) ∧
      Real.sqrt (158140 / 37 : ℝ) ≤ 653763 / 10000 ∧ Real.sqrt (7907 : ℝ) ≤ 444607 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 79. -/
theorem gammaAnalyticWide79_logs :
    Real.log (158140 / 37 : ℝ) ≤ 20901 / 2500 ∧ Real.log (7907 : ℝ) ≤ 22439 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (158140 / 37) 13 20 0 (20901 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 7907 13 20 0 (22439 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide79_main (hRH : RiemannHypothesis) :
    (26913 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 7907,
        Real.exp (-(n : ℝ) / (158140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (158140 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 44597) * ((158140 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((158140 / 37) * (37 / 20)) + 1) / (2000 / 44597) +
        1839 / 1000 ≤
      186871 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide79_roots.2.2]
  have hs :
    Real.sqrt ((158140 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((158140 / 37) * (37 / 20)) +
        21 / 20 ≤
      22003 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide79_roots.2.2, gammaAnalyticWide79_logs.2]
  have hz :
    Real.sqrt (158140 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (158140 / 37) + 2469 / 800 ≤
      17887 / 1000 := by
    linarith only [gammaAnalyticWide79_roots.2.1, gammaAnalyticWide79_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 158140 / 37) (y := 37 / 20) (h := 2000 / 44597) (r :=
      653763 / 10000) (e := 78619 / 500000) (p := 186871 / 500) (s := 22003 / 1000) (z :=
      17887 / 1000) (F := 26913 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide79_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (158140 / 37 : ℝ) * (37 / 20) = 7907 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide79_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (158140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (158140 / 37 : ℝ)) ≤
      1313 / 20 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 326881 / 5000) (T := 653763 / 10000) (Z := 20901 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticWide79_roots.1
      gammaAnalyticWide79_roots.2.1 gammaAnalyticWide79_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide79_power : (158140 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 227 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 79 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide79_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3247 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4092 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (7907 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3247 / 20)]
  apply
    reject_03_of_analytic_caps (B := 7907) (x := 158140 / 37) (H := 4092 / 25) (R := 326881 / 5000)
      (W := 227 / 25000) (F := 26913 / 500) (U := 1313 / 20) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide79_power (gammaAnalyticWide79_main hGRH.riemann)
      (gammaAnalyticWide79_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 80. -/
theorem gammaAnalyticWide80_roots :
    ((329557 / 5000 : ℝ) ≤ Real.sqrt (160740 / 37 : ℝ) ∧
      Real.sqrt (160740 / 37 : ℝ) ≤ 131823 / 2000 ∧ Real.sqrt (8037 : ℝ) ≤ 448247 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 80. -/
theorem gammaAnalyticWide80_logs :
    Real.log (160740 / 37 : ℝ) ≤ 83767 / 10000 ∧ Real.log (8037 : ℝ) ≤ 89919 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (160740 / 37) 13 20 0 (83767 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 8037 13 20 0 (89919 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide80_main (hRH : RiemannHypothesis) :
    (2171 / 40 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 8037,
        Real.exp (-(n : ℝ) / (160740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (160740 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 44779) * ((160740 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((160740 / 37) * (37 / 20)) + 1) / (2000 / 44779) +
        1839 / 1000 ≤
      189151 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide80_roots.2.2]
  have hs :
    Real.sqrt ((160740 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((160740 / 37) * (37 / 20)) +
        21 / 20 ≤
      22069 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide80_roots.2.2, gammaAnalyticWide80_logs.2]
  have hz :
    Real.sqrt (160740 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (160740 / 37) + 2469 / 800 ≤
      2242 / 125 := by
    linarith only [gammaAnalyticWide80_roots.2.1, gammaAnalyticWide80_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 160740 / 37) (y := 37 / 20) (h := 2000 / 44779) (r :=
      131823 / 2000) (e := 78619 / 500000) (p := 189151 / 500) (s := 22069 / 1000) (z := 2242 / 125)
      (F := 2171 / 40) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide80_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (160740 / 37 : ℝ) * (37 / 20) = 8037 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide80_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (160740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (160740 / 37 : ℝ)) ≤
      8273 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 329557 / 5000) (T := 131823 / 2000) (Z := 83767 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide80_roots.1
      gammaAnalyticWide80_roots.2.1 gammaAnalyticWide80_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide80_power : (160740 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 899 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 80 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide80_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (4092 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8251 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (8037 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 4092 / 25)]
  apply
    reject_03_of_analytic_caps (B := 8037) (x := 160740 / 37) (H := 8251 / 50) (R := 329557 / 5000)
      (W := 899 / 100000) (F := 2171 / 40) (U := 8273 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide80_power (gammaAnalyticWide80_main hGRH.riemann)
      (gammaAnalyticWide80_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 81. -/
theorem gammaAnalyticWide81_roots :
    ((132901 / 2000 : ℝ) ≤ Real.sqrt (163380 / 37 : ℝ) ∧
      Real.sqrt (163380 / 37 : ℝ) ≤ 332253 / 5000 ∧ Real.sqrt (8169 : ℝ) ≤ 451913 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 81. -/
theorem gammaAnalyticWide81_logs :
    Real.log (163380 / 37 : ℝ) ≤ 8393 / 1000 ∧ Real.log (8169 : ℝ) ≤ 45041 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (163380 / 37) 13 20 0 (8393 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 8169 13 20 0 (45041 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide81_main (hRH : RiemannHypothesis) :
    (6841 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 8169,
        Real.exp (-(n : ℝ) / (163380 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (163380 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 89929) * ((163380 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((163380 / 37) * (37 / 20)) + 1) / (4000 / 89929) +
        1839 / 1000 ≤
      382913 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide81_roots.2.2]
  have hs :
    Real.sqrt ((163380 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((163380 / 37) * (37 / 20)) +
        21 / 20 ≤
      2767 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide81_roots.2.2, gammaAnalyticWide81_logs.2]
  have hz :
    Real.sqrt (163380 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (163380 / 37) + 2469 / 800 ≤
      3597 / 200 := by
    linarith only [gammaAnalyticWide81_roots.2.1, gammaAnalyticWide81_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 163380 / 37) (y := 37 / 20) (h := 4000 / 89929) (r :=
      332253 / 5000) (e := 78619 / 500000) (p := 382913 / 1000) (s := 2767 / 125) (z := 3597 / 200)
      (F := 6841 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide81_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (163380 / 37 : ℝ) * (37 / 20) = 8169 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide81_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (163380 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (163380 / 37 : ℝ)) ≤
      33361 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 132901 / 2000) (T := 332253 / 5000) (Z := 8393 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide81_roots.1
      gammaAnalyticWide81_roots.2.1 gammaAnalyticWide81_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide81_power : (163380 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 891 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 81 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide81_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (8251 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8319 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (8169 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 8251 / 50)]
  apply
    reject_03_of_analytic_caps (B := 8169) (x := 163380 / 37) (H := 8319 / 50) (R := 132901 / 2000)
      (W := 891 / 100000) (F := 6841 / 125) (U := 33361 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide81_power (gammaAnalyticWide81_main hGRH.riemann)
      (gammaAnalyticWide81_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 82. -/
theorem gammaAnalyticWide82_roots :
    ((669973 / 10000 : ℝ) ≤ Real.sqrt (166080 / 37 : ℝ) ∧
      Real.sqrt (166080 / 37 : ℝ) ≤ 334987 / 5000 ∧ Real.sqrt (8304 : ℝ) ≤ 911263 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 82. -/
theorem gammaAnalyticWide82_logs :
    Real.log (166080 / 37 : ℝ) ≤ 42047 / 5000 ∧ Real.log (8304 : ℝ) ≤ 18049 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (166080 / 37) 13 20 0 (42047 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 8304 14 20 0 (18049 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide82_main (hRH : RiemannHypothesis) :
    (55187 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 8304,
        Real.exp (-(n : ℝ) / (166080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (166080 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 90293) * ((166080 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((166080 / 37) * (37 / 20)) + 1) / (4000 / 90293) +
        1839 / 1000 ≤
      387609 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide82_roots.2.2]
  have hs :
    Real.sqrt ((166080 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((166080 / 37) * (37 / 20)) +
        21 / 20 ≤
      22203 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide82_roots.2.2, gammaAnalyticWide82_logs.2]
  have hz :
    Real.sqrt (166080 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (166080 / 37) + 2469 / 800 ≤
      3607 / 200 := by
    linarith only [gammaAnalyticWide82_roots.2.1, gammaAnalyticWide82_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 166080 / 37) (y := 37 / 20) (h := 4000 / 90293) (r :=
      334987 / 5000) (e := 78619 / 500000) (p := 387609 / 1000) (s := 22203 / 1000) (z :=
      3607 / 200) (F := 55187 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide82_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (166080 / 37 : ℝ) * (37 / 20) = 8304 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide82_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (166080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (166080 / 37 : ℝ)) ≤
      67267 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 669973 / 10000) (T := 334987 / 5000) (Z := 42047 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide82_roots.1
      gammaAnalyticWide82_roots.2.1 gammaAnalyticWide82_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide82_power : (166080 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 883 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 82 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide82_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (8319 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4194 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (8304 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 8319 / 50)]
  apply
    reject_03_of_analytic_caps (B := 8304) (x := 166080 / 37) (H := 4194 / 25) (R := 669973 / 10000)
      (W := 883 / 100000) (F := 55187 / 1000) (U := 67267 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide82_power (gammaAnalyticWide82_main hGRH.riemann)
      (gammaAnalyticWide82_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 83. -/
theorem gammaAnalyticWide83_roots :
    ((675557 / 10000 : ℝ) ≤ Real.sqrt (168860 / 37 : ℝ) ∧
      Real.sqrt (168860 / 37 : ℝ) ≤ 337779 / 5000 ∧ Real.sqrt (8443 : ℝ) ≤ 459429 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 83. -/
theorem gammaAnalyticWide83_logs :
    Real.log (168860 / 37 : ℝ) ≤ 4213 / 500 ∧ Real.log (8443 : ℝ) ≤ 90411 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (168860 / 37) 13 20 0 (4213 / 500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 8443 14 20 0 (90411 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide83_main (hRH : RiemannHypothesis) :
    (6957 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 8443,
        Real.exp (-(n : ℝ) / (168860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (168860 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 90671) * ((168860 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((168860 / 37) * (37 / 20)) + 1) / (4000 / 90671) +
        1839 / 1000 ≤
      49053 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide83_roots.2.2]
  have hs :
    Real.sqrt ((168860 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((168860 / 37) * (37 / 20)) +
        21 / 20 ≤
      22271 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide83_roots.2.2, gammaAnalyticWide83_logs.2]
  have hz :
    Real.sqrt (168860 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (168860 / 37) + 2469 / 800 ≤
      9043 / 500 := by
    linarith only [gammaAnalyticWide83_roots.2.1, gammaAnalyticWide83_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 168860 / 37) (y := 37 / 20) (h := 4000 / 90671) (r :=
      337779 / 5000) (e := 78619 / 500000) (p := 49053 / 125) (s := 22271 / 1000) (z := 9043 / 500)
      (F := 6957 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide83_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (168860 / 37 : ℝ) * (37 / 20) = 8443 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide83_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (168860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (168860 / 37 : ℝ)) ≤
      8478 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 675557 / 10000) (T := 337779 / 5000) (Z := 4213 / 500)
      (by norm_num only) (by norm_num only) gammaAnalyticWide83_roots.1
      gammaAnalyticWide83_roots.2.1 gammaAnalyticWide83_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide83_power : (168860 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 7 / 800 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 83 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide83_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (4194 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (4229 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (8443 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 4194 / 25)]
  apply
    reject_03_of_analytic_caps (B := 8443) (x := 168860 / 37) (H := 4229 / 25) (R := 675557 / 10000)
      (W := 7 / 800) (F := 6957 / 125) (U := 8478 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide83_power (gammaAnalyticWide83_main hGRH.riemann)
      (gammaAnalyticWide83_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 84. -/
theorem gammaAnalyticWide84_roots :
    ((27247 / 400 : ℝ) ≤ Real.sqrt (4640 : ℝ) ∧
      Real.sqrt (4640 : ℝ) ≤ 85147 / 1250 ∧ Real.sqrt (8584 : ℝ) ≤ 926499 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 84. -/
theorem gammaAnalyticWide84_logs :
    Real.log (4640 : ℝ) ≤ 3377 / 400 ∧ Real.log (8584 : ℝ) ≤ 90577 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4640) 13 20 0 (3377 / 400) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 8584 14 20 0 (90577 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide84_main (hRH : RiemannHypothesis) :
    (7016 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 8584,
        Real.exp (-(n : ℝ) / (4640)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (4640 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 91049) * ((4640) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4640) * (37 / 20)) + 1) / (4000 / 91049) +
        1839 / 1000 ≤
      397289 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide84_roots.2.2]
  have hs :
    Real.sqrt ((4640 : ℝ) * (37 / 20)) / 20 + (1839 / 1000 : ℝ) * Real.log ((4640) * (37 / 20)) +
        21 / 20 ≤
      1117 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide84_roots.2.2, gammaAnalyticWide84_logs.2]
  have hz :
    Real.sqrt (4640 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4640) + 2469 / 800 ≤
      18137 / 1000 := by
    linarith only [gammaAnalyticWide84_roots.2.1, gammaAnalyticWide84_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4640) (y := 37 / 20) (h := 4000 / 91049) (r :=
      85147 / 1250) (e := 78619 / 500000) (p := 397289 / 1000) (s := 1117 / 50) (z := 18137 / 1000)
      (F := 7016 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide84_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4640 : ℝ) * (37 / 20) = 8584 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide84_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4640)) * ArithmeticFunction.vonMangoldt n / Real.sqrt (4640 : ℝ)) ≤
      8548 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 27247 / 400) (T := 85147 / 1250) (Z := 3377 / 400)
      (by norm_num only) (by norm_num only) gammaAnalyticWide84_roots.1
      gammaAnalyticWide84_roots.2.1 gammaAnalyticWide84_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide84_power : (4640 : ℝ) ^ (-9 / 16 : ℝ) ≤ 867 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 84 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide84_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (4229 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8529 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (8584 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 4229 / 25)]
  apply
    reject_03_of_analytic_caps (B := 8584) (x := 4640) (H := 8529 / 50) (R := 27247 / 400) (W :=
      867 / 100000) (F := 7016 / 125) (U := 8548 / 125) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide84_power (gammaAnalyticWide84_main hGRH.riemann)
      (gammaAnalyticWide84_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 85. -/
theorem gammaAnalyticWide85_roots :
    ((85863 / 1250 : ℝ) ≤ Real.sqrt (174580 / 37 : ℝ) ∧
      Real.sqrt (174580 / 37 : ℝ) ≤ 137381 / 2000 ∧ Real.sqrt (8729 : ℝ) ≤ 233573 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 85. -/
theorem gammaAnalyticWide85_logs :
    Real.log (174580 / 37 : ℝ) ≤ 84593 / 10000 ∧ Real.log (8729 : ℝ) ≤ 18149 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (174580 / 37) 13 20 0 (84593 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 8729 14 20 0 (18149 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide85_main (hRH : RiemannHypothesis) :
    (56609 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 8729,
        Real.exp (-(n : ℝ) / (174580 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (174580 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 91427) * ((174580 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((174580 / 37) * (37 / 20)) + 1) / (4000 / 91427) +
        1839 / 1000 ≤
      402271 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide85_roots.2.2]
  have hs :
    Real.sqrt ((174580 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((174580 / 37) * (37 / 20)) +
        21 / 20 ≤
      2241 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide85_roots.2.2, gammaAnalyticWide85_logs.2]
  have hz :
    Real.sqrt (174580 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (174580 / 37) + 2469 / 800 ≤
      18189 / 1000 := by
    linarith only [gammaAnalyticWide85_roots.2.1, gammaAnalyticWide85_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 174580 / 37) (y := 37 / 20) (h := 4000 / 91427) (r :=
      137381 / 2000) (e := 78619 / 500000) (p := 402271 / 1000) (s := 2241 / 100) (z :=
      18189 / 1000) (F := 56609 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide85_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (174580 / 37 : ℝ) * (37 / 20) = 8729 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide85_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (174580 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (174580 / 37 : ℝ)) ≤
      17239 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 85863 / 1250) (T := 137381 / 2000) (Z := 84593 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide85_roots.1
      gammaAnalyticWide85_roots.2.1 gammaAnalyticWide85_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide85_power : (174580 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 859 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 85 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide85_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (8529 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8601 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (8729 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 8529 / 50)]
  apply
    reject_03_of_analytic_caps (B := 8729) (x := 174580 / 37) (H := 8601 / 50) (R := 85863 / 1250)
      (W := 859 / 100000) (F := 56609 / 1000) (U := 17239 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide85_power (gammaAnalyticWide85_main hGRH.riemann)
      (gammaAnalyticWide85_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 86. -/
theorem gammaAnalyticWide86_roots :
    ((692703 / 10000 : ℝ) ≤ Real.sqrt (177540 / 37 : ℝ) ∧
      Real.sqrt (177540 / 37 : ℝ) ≤ 43294 / 625 ∧ Real.sqrt (8877 : ℝ) ≤ 942179 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 86. -/
theorem gammaAnalyticWide86_logs :
    Real.log (177540 / 37 : ℝ) ≤ 84761 / 10000 ∧ Real.log (8877 : ℝ) ≤ 90913 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (177540 / 37) 13 20 0 (84761 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 8877 14 20 0 (90913 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide86_main (hRH : RiemannHypothesis) :
    (11419 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 8877,
        Real.exp (-(n : ℝ) / (177540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (177540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 22953) * ((177540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((177540 / 37) * (37 / 20)) + 1) / (1000 / 22953) +
        1839 / 1000 ≤
      203667 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide86_roots.2.2]
  have hs :
    Real.sqrt ((177540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((177540 / 37) * (37 / 20)) +
        21 / 20 ≤
      562 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide86_roots.2.2, gammaAnalyticWide86_logs.2]
  have hz :
    Real.sqrt (177540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (177540 / 37) + 2469 / 800 ≤
      18241 / 1000 := by
    linarith only [gammaAnalyticWide86_roots.2.1, gammaAnalyticWide86_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 177540 / 37) (y := 37 / 20) (h := 1000 / 22953) (r :=
      43294 / 625) (e := 78619 / 500000) (p := 203667 / 500) (s := 562 / 25) (z := 18241 / 1000)
      (F := 11419 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide86_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (177540 / 37 : ℝ) * (37 / 20) = 8877 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide86_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (177540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (177540 / 37 : ℝ)) ≤
      34767 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 692703 / 10000) (T := 43294 / 625) (Z := 84761 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide86_roots.1
      gammaAnalyticWide86_roots.2.1 gammaAnalyticWide86_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide86_power : (177540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 17 / 2000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 86 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide86_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (8601 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17347 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (8877 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 8601 / 50)]
  apply
    reject_03_of_analytic_caps (B := 8877) (x := 177540 / 37) (H := 17347 / 100) (R :=
      692703 / 10000) (W := 17 / 2000) (F := 11419 / 200) (U := 34767 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide86_power (gammaAnalyticWide86_main hGRH.riemann)
      (gammaAnalyticWide86_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 87. -/
theorem gammaAnalyticWide87_roots :
    ((698531 / 10000 : ℝ) ≤ Real.sqrt (180540 / 37 : ℝ) ∧
      Real.sqrt (180540 / 37 : ℝ) ≤ 174633 / 2500 ∧ Real.sqrt (9027 : ℝ) ≤ 475053 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 87. -/
theorem gammaAnalyticWide87_logs :
    Real.log (180540 / 37 : ℝ) ≤ 5308 / 625 ∧ Real.log (9027 : ℝ) ≤ 2277 / 250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (180540 / 37) 13 20 0 (5308 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 9027 14 20 0 (2277 / 250) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide87_main (hRH : RiemannHypothesis) :
    (11517 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 9027,
        Real.exp (-(n : ℝ) / (180540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (180540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 92197) * ((180540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((180540 / 37) * (37 / 20)) + 1) / (4000 / 92197) +
        1839 / 1000 ≤
      103111 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide87_roots.2.2]
  have hs :
    Real.sqrt ((180540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((180540 / 37) * (37 / 20)) +
        21 / 20 ≤
      22551 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide87_roots.2.2, gammaAnalyticWide87_logs.2]
  have hz :
    Real.sqrt (180540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (180540 / 37) + 2469 / 800 ≤
      18293 / 1000 := by
    linarith only [gammaAnalyticWide87_roots.2.1, gammaAnalyticWide87_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 180540 / 37) (y := 37 / 20) (h := 4000 / 92197) (r :=
      174633 / 2500) (e := 78619 / 500000) (p := 103111 / 250) (s := 22551 / 1000) (z :=
      18293 / 1000) (F := 11517 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide87_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (180540 / 37 : ℝ) * (37 / 20) = 9027 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide87_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (180540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (180540 / 37 : ℝ)) ≤
      17529 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 698531 / 10000) (T := 174633 / 2500) (Z := 5308 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticWide87_roots.1
      gammaAnalyticWide87_roots.2.1 gammaAnalyticWide87_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide87_power : (180540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 421 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 87 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide87_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17347 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (8747 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (9027 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17347 / 100)]
  apply
    reject_03_of_analytic_caps (B := 9027) (x := 180540 / 37) (H := 8747 / 50) (R := 698531 / 10000)
      (W := 421 / 50000) (F := 11517 / 200) (U := 17529 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide87_power (gammaAnalyticWide87_main hGRH.riemann)
      (gammaAnalyticWide87_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 88. -/
theorem gammaAnalyticWide88_roots :
    ((44029 / 625 : ℝ) ≤ Real.sqrt (183620 / 37 : ℝ) ∧
      Real.sqrt (183620 / 37 : ℝ) ≤ 140893 / 2000 ∧ Real.sqrt (9181 : ℝ) ≤ 59886 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 88. -/
theorem gammaAnalyticWide88_logs :
    Real.log (183620 / 37 : ℝ) ≤ 42549 / 5000 ∧ Real.log (9181 : ℝ) ≤ 91249 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (183620 / 37) 13 20 0 (42549 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 9181 14 20 0 (91249 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide88_main (hRH : RiemannHypothesis) :
    (58083 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 9181,
        Real.exp (-(n : ℝ) / (183620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (183620 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 92589) * ((183620 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((183620 / 37) * (37 / 20)) + 1) / (4000 / 92589) +
        1839 / 1000 ≤
      417669 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide88_roots.2.2]
  have hs :
    Real.sqrt ((183620 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((183620 / 37) * (37 / 20)) +
        21 / 20 ≤
      11311 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide88_roots.2.2, gammaAnalyticWide88_logs.2]
  have hz :
    Real.sqrt (183620 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (183620 / 37) + 2469 / 800 ≤
      9173 / 500 := by
    linarith only [gammaAnalyticWide88_roots.2.1, gammaAnalyticWide88_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 183620 / 37) (y := 37 / 20) (h := 4000 / 92589) (r :=
      140893 / 2000) (e := 78619 / 500000) (p := 417669 / 1000) (s := 11311 / 500) (z := 9173 / 500)
      (F := 58083 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide88_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (183620 / 37 : ℝ) * (37 / 20) = 9181 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide88_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (183620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (183620 / 37 : ℝ)) ≤
      70707 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 44029 / 625) (T := 140893 / 2000) (Z := 42549 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide88_roots.1
      gammaAnalyticWide88_roots.2.1 gammaAnalyticWide88_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide88_power : (183620 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 417 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 88 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide88_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (8747 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17643 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (9181 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 8747 / 50)]
  apply
    reject_03_of_analytic_caps (B := 9181) (x := 183620 / 37) (H := 17643 / 100) (R := 44029 / 625)
      (W := 417 / 50000) (F := 58083 / 1000) (U := 70707 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide88_power (gammaAnalyticWide88_main hGRH.riemann)
      (gammaAnalyticWide88_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 89. -/
theorem gammaAnalyticWide89_roots :
    ((355231 / 5000 : ℝ) ≤ Real.sqrt (186760 / 37 : ℝ) ∧
      Real.sqrt (186760 / 37 : ℝ) ≤ 710463 / 10000 ∧ Real.sqrt (9338 : ℝ) ≤ 483167 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 89. -/
theorem gammaAnalyticWide89_logs :
    Real.log (186760 / 37 : ℝ) ≤ 85267 / 10000 ∧ Real.log (9338 : ℝ) ≤ 91419 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (186760 / 37) 13 20 0 (85267 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 9338 14 20 0 (91419 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide89_main (hRH : RiemannHypothesis) :
    (29293 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 9338,
        Real.exp (-(n : ℝ) / (186760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (186760 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 92981) * ((186760 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((186760 / 37) * (37 / 20)) + 1) / (4000 / 92981) +
        1839 / 1000 ≤
      105743 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide89_roots.2.2]
  have hs :
    Real.sqrt ((186760 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((186760 / 37) * (37 / 20)) +
        21 / 20 ≤
      11347 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide89_roots.2.2, gammaAnalyticWide89_logs.2]
  have hz :
    Real.sqrt (186760 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (186760 / 37) + 2469 / 800 ≤
      92 / 5 := by
    linarith only [gammaAnalyticWide89_roots.2.1, gammaAnalyticWide89_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 186760 / 37) (y := 37 / 20) (h := 4000 / 92981) (r :=
      710463 / 10000) (e := 78619 / 500000) (p := 105743 / 250) (s := 11347 / 500) (z := 92 / 5)
      (F := 29293 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide89_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (186760 / 37 : ℝ) * (37 / 20) = 9338 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide89_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (186760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (186760 / 37 : ℝ)) ≤
      35653 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 355231 / 5000) (T := 710463 / 10000) (Z := 85267 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide89_roots.1
      gammaAnalyticWide89_roots.2.1 gammaAnalyticWide89_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide89_power : (186760 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 827 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 89 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide89_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17643 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17793 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (9338 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17643 / 100)]
  apply
    reject_03_of_analytic_caps (B := 9338) (x := 186760 / 37) (H := 17793 / 100) (R :=
      355231 / 5000) (W := 827 / 100000) (F := 29293 / 500) (U := 35653 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide89_power (gammaAnalyticWide89_main hGRH.riemann)
      (gammaAnalyticWide89_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 90. -/
theorem gammaAnalyticWide90_roots :
    ((143297 / 2000 : ℝ) ≤ Real.sqrt (189940 / 37 : ℝ) ∧
      Real.sqrt (189940 / 37 : ℝ) ≤ 358243 / 5000 ∧ Real.sqrt (9497 : ℝ) ≤ 487263 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 90. -/
theorem gammaAnalyticWide90_logs :
    Real.log (189940 / 37 : ℝ) ≤ 21359 / 2500 ∧ Real.log (9497 : ℝ) ≤ 22897 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (189940 / 37) 13 20 0 (21359 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 9497 14 20 0 (22897 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide90_main (hRH : RiemannHypothesis) :
    (14773 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 9497,
        Real.exp (-(n : ℝ) / (189940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (189940 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (200 / 4669) * ((189940 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((189940 / 37) * (37 / 20)) + 1) / (200 / 4669) +
        1839 / 1000 ≤
      10708 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide90_roots.2.2]
  have hs :
    Real.sqrt ((189940 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((189940 / 37) * (37 / 20)) +
        21 / 20 ≤
      11383 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide90_roots.2.2, gammaAnalyticWide90_logs.2]
  have hz :
    Real.sqrt (189940 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (189940 / 37) + 2469 / 800 ≤
      18453 / 1000 := by
    linarith only [gammaAnalyticWide90_roots.2.1, gammaAnalyticWide90_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 189940 / 37) (y := 37 / 20) (h := 200 / 4669) (r :=
      358243 / 5000) (e := 78619 / 500000) (p := 10708 / 25) (s := 11383 / 500) (z := 18453 / 1000)
      (F := 14773 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide90_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (189940 / 37 : ℝ) * (37 / 20) = 9497 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide90_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (189940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (189940 / 37 : ℝ)) ≤
      71907 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 143297 / 2000) (T := 358243 / 5000) (Z := 21359 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticWide90_roots.1
      gammaAnalyticWide90_roots.2.1 gammaAnalyticWide90_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide90_power : (189940 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 819 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 90 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide90_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17793 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3589 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (9497 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17793 / 100)]
  apply
    reject_03_of_analytic_caps (B := 9497) (x := 189940 / 37) (H := 3589 / 20) (R := 143297 / 2000)
      (W := 819 / 100000) (F := 14773 / 250) (U := 71907 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide90_power (gammaAnalyticWide90_main hGRH.riemann)
      (gammaAnalyticWide90_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 91. -/
theorem gammaAnalyticWide91_roots :
    ((722607 / 10000 : ℝ) ≤ Real.sqrt (193200 / 37 : ℝ) ∧
      Real.sqrt (193200 / 37 : ℝ) ≤ 45163 / 625 ∧ Real.sqrt (9660 : ℝ) ≤ 982853 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 91. -/
theorem gammaAnalyticWide91_logs :
    Real.log (193200 / 37 : ℝ) ≤ 42803 / 5000 ∧ Real.log (9660 : ℝ) ≤ 45879 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (193200 / 37) 13 20 0 (42803 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 9660 14 20 0 (45879 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide91_main (hRH : RiemannHypothesis) :
    (29803 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 9660,
        Real.exp (-(n : ℝ) / (193200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (193200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 23443) * ((193200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((193200 / 37) * (37 / 20)) + 1) / (1000 / 23443) +
        1839 / 1000 ≤
      21689 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide91_roots.2.2]
  have hs :
    Real.sqrt ((193200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((193200 / 37) * (37 / 20)) +
        21 / 20 ≤
      22839 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide91_roots.2.2, gammaAnalyticWide91_logs.2]
  have hz :
    Real.sqrt (193200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (193200 / 37) + 2469 / 800 ≤
      18507 / 1000 := by
    linarith only [gammaAnalyticWide91_roots.2.1, gammaAnalyticWide91_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 193200 / 37) (y := 37 / 20) (h := 1000 / 23443) (r :=
      45163 / 625) (e := 78619 / 500000) (p := 21689 / 50) (s := 22839 / 1000) (z := 18507 / 1000)
      (F := 29803 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide91_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (193200 / 37 : ℝ) * (37 / 20) = 9660 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide91_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (193200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (193200 / 37 : ℝ)) ≤
      72517 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 722607 / 10000) (T := 45163 / 625) (Z := 42803 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide91_roots.1
      gammaAnalyticWide91_roots.2.1 gammaAnalyticWide91_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide91_power : (193200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 811 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 91 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide91_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3589 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18099 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (9660 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3589 / 20)]
  apply
    reject_03_of_analytic_caps (B := 9660) (x := 193200 / 37) (H := 18099 / 100) (R :=
      722607 / 10000) (W := 811 / 100000) (F := 29803 / 500) (U := 72517 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide91_power (gammaAnalyticWide91_main hGRH.riemann)
      (gammaAnalyticWide91_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 92. -/
theorem gammaAnalyticWide92_roots :
    ((728827 / 10000 : ℝ) ≤ Real.sqrt (196540 / 37 : ℝ) ∧
      Real.sqrt (196540 / 37 : ℝ) ≤ 182207 / 2500 ∧ Real.sqrt (9827 : ℝ) ≤ 991313 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 92. -/
theorem gammaAnalyticWide92_logs :
    Real.log (196540 / 37 : ℝ) ≤ 42889 / 5000 ∧ Real.log (9827 : ℝ) ≤ 91929 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (196540 / 37) 13 20 0 (42889 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 9827 14 20 0 (91929 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide92_main (hRH : RiemannHypothesis) :
    (7516 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 9827,
        Real.exp (-(n : ℝ) / (196540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (196540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 47089) * ((196540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((196540 / 37) * (37 / 20)) + 1) / (2000 / 47089) +
        1839 / 1000 ≤
      8787 / 20 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide92_roots.2.2]
  have hs :
    Real.sqrt ((196540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((196540 / 37) * (37 / 20)) +
        21 / 20 ≤
      22913 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide92_roots.2.2, gammaAnalyticWide92_logs.2]
  have hz :
    Real.sqrt (196540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (196540 / 37) + 2469 / 800 ≤
      9281 / 500 := by
    linarith only [gammaAnalyticWide92_roots.2.1, gammaAnalyticWide92_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 196540 / 37) (y := 37 / 20) (h := 2000 / 47089) (r :=
      182207 / 2500) (e := 78619 / 500000) (p := 8787 / 20) (s := 22913 / 1000) (z := 9281 / 500)
      (F := 7516 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide92_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (196540 / 37 : ℝ) * (37 / 20) = 9827 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide92_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (196540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (196540 / 37 : ℝ)) ≤
      36569 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 728827 / 10000) (T := 182207 / 2500) (Z := 42889 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide92_roots.1
      gammaAnalyticWide92_roots.2.1 gammaAnalyticWide92_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide92_power : (196540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 803 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 92 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide92_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18099 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (3651 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (9827 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18099 / 100)]
  apply
    reject_03_of_analytic_caps (B := 9827) (x := 196540 / 37) (H := 3651 / 20) (R := 728827 / 10000)
      (W := 803 / 100000) (F := 7516 / 125) (U := 36569 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide92_power (gammaAnalyticWide92_main hGRH.riemann)
      (gammaAnalyticWide92_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 93. -/
theorem gammaAnalyticWide93_roots :
    ((45944 / 625 : ℝ) ≤ Real.sqrt (199940 / 37 : ℝ) ∧
      Real.sqrt (199940 / 37 : ℝ) ≤ 147021 / 2000 ∧ Real.sqrt (9997 : ℝ) ≤ 19997 / 200) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 93. -/
theorem gammaAnalyticWide93_logs :
    Real.log (199940 / 37 : ℝ) ≤ 85949 / 10000 ∧ Real.log (9997 : ℝ) ≤ 92101 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (199940 / 37) 13 20 0 (85949 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 9997 14 20 0 (92101 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide93_main (hRH : RiemannHypothesis) :
    (12131 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 9997,
        Real.exp (-(n : ℝ) / (199940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (199940 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 11823) * ((199940 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((199940 / 37) * (37 / 20)) + 1) / (500 / 11823) +
        1839 / 1000 ≤
      88999 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide93_roots.2.2]
  have hs :
    Real.sqrt ((199940 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((199940 / 37) * (37 / 20)) +
        21 / 20 ≤
      22987 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide93_roots.2.2, gammaAnalyticWide93_logs.2]
  have hz :
    Real.sqrt (199940 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (199940 / 37) + 2469 / 800 ≤
      18617 / 1000 := by
    linarith only [gammaAnalyticWide93_roots.2.1, gammaAnalyticWide93_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 199940 / 37) (y := 37 / 20) (h := 500 / 11823) (r :=
      147021 / 2000) (e := 78619 / 500000) (p := 88999 / 200) (s := 22987 / 1000) (z :=
      18617 / 1000) (F := 12131 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide93_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (199940 / 37 : ℝ) * (37 / 20) = 9997 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide93_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (199940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (199940 / 37 : ℝ)) ≤
      18441 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 45944 / 625) (T := 147021 / 2000) (Z := 85949 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide93_roots.1
      gammaAnalyticWide93_roots.2.1 gammaAnalyticWide93_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide93_power : (199940 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 159 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 93 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide93_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (3651 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18413 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (9997 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 3651 / 20)]
  apply
    reject_03_of_analytic_caps (B := 9997) (x := 199940 / 37) (H := 18413 / 100) (R := 45944 / 625)
      (W := 159 / 20000) (F := 12131 / 200) (U := 18441 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide93_power (gammaAnalyticWide93_main hGRH.riemann)
      (gammaAnalyticWide93_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 94. -/
theorem gammaAnalyticWide94_roots :
    ((370737 / 5000 : ℝ) ≤ Real.sqrt (203420 / 37 : ℝ) ∧
      Real.sqrt (203420 / 37 : ℝ) ≤ 29659 / 400 ∧ Real.sqrt (10171 : ℝ) ≤ 504257 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 94. -/
theorem gammaAnalyticWide94_logs :
    Real.log (203420 / 37 : ℝ) ≤ 43061 / 5000 ∧ Real.log (10171 : ℝ) ≤ 92273 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (203420 / 37) 13 20 0 (43061 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 10171 14 20 0 (92273 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide94_main (hRH : RiemannHypothesis) :
    (6119 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 10171,
        Real.exp (-(n : ℝ) / (203420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (203420 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (400 / 9499) * ((203420 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((203420 / 37) * (37 / 20)) + 1) / (400 / 9499) +
        1839 / 1000 ≤
      450749 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide94_roots.2.2]
  have hs :
    Real.sqrt ((203420 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((203420 / 37) * (37 / 20)) +
        21 / 20 ≤
      11531 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide94_roots.2.2, gammaAnalyticWide94_logs.2]
  have hz :
    Real.sqrt (203420 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (203420 / 37) + 2469 / 800 ≤
      18673 / 1000 := by
    linarith only [gammaAnalyticWide94_roots.2.1, gammaAnalyticWide94_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 203420 / 37) (y := 37 / 20) (h := 400 / 9499) (r :=
      29659 / 400) (e := 78619 / 500000) (p := 450749 / 1000) (s := 11531 / 500) (z := 18673 / 1000)
      (F := 6119 / 100) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticWide94_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (203420 / 37 : ℝ) * (37 / 20) = 10171 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide94_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (203420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (203420 / 37 : ℝ)) ≤
      372 / 5 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 370737 / 5000) (T := 29659 / 400) (Z := 43061 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide94_roots.1
      gammaAnalyticWide94_roots.2.1 gammaAnalyticWide94_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide94_power : (203420 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 197 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 94 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide94_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18413 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18573 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (10171 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18413 / 100)]
  apply
    reject_03_of_analytic_caps (B := 10171) (x := 203420 / 37) (H := 18573 / 100) (R :=
      370737 / 5000) (W := 197 / 25000) (F := 6119 / 100) (U := 372 / 5) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide94_power (gammaAnalyticWide94_main hGRH.riemann)
      (gammaAnalyticWide94_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 95. -/
theorem gammaAnalyticWide95_roots :
    ((747897 / 10000 : ℝ) ≤ Real.sqrt (206960 / 37 : ℝ) ∧
      Real.sqrt (206960 / 37 : ℝ) ≤ 373949 / 5000 ∧ Real.sqrt (10348 : ℝ) ≤ 254313 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 95. -/
theorem gammaAnalyticWide95_logs :
    Real.log (206960 / 37 : ℝ) ≤ 43147 / 5000 ∧ Real.log (10348 : ℝ) ≤ 46223 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (206960 / 37) 13 20 0 (43147 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 10348 14 20 0 (46223 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide95_main (hRH : RiemannHypothesis) :
    (61729 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 10348,
        Real.exp (-(n : ℝ) / (206960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (206960 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 95403) * ((206960 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((206960 / 37) * (37 / 20)) + 1) / (4000 / 95403) +
        1839 / 1000 ≤
      57072 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide95_roots.2.2]
  have hs :
    Real.sqrt ((206960 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((206960 / 37) * (37 / 20)) +
        21 / 20 ≤
      11569 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide95_roots.2.2, gammaAnalyticWide95_logs.2]
  have hz :
    Real.sqrt (206960 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (206960 / 37) + 2469 / 800 ≤
      2341 / 125 := by
    linarith only [gammaAnalyticWide95_roots.2.1, gammaAnalyticWide95_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 206960 / 37) (y := 37 / 20) (h := 4000 / 95403) (r :=
      373949 / 5000) (e := 78619 / 500000) (p := 57072 / 125) (s := 11569 / 500) (z := 2341 / 125)
      (F := 61729 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide95_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (206960 / 37 : ℝ) * (37 / 20) = 10348 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide95_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (206960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (206960 / 37 : ℝ)) ≤
      75041 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 747897 / 10000) (T := 373949 / 5000) (Z := 43147 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide95_roots.1
      gammaAnalyticWide95_roots.2.1 gammaAnalyticWide95_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide95_power : (206960 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 39 / 5000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 95 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide95_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18573 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (9367 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (10348 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18573 / 100)]
  apply
    reject_03_of_analytic_caps (B := 10348) (x := 206960 / 37) (H := 9367 / 50) (R :=
      747897 / 10000) (W := 39 / 5000) (F := 61729 / 1000) (U := 75041 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide95_power (gammaAnalyticWide95_main hGRH.riemann)
      (gammaAnalyticWide95_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 96. -/
theorem gammaAnalyticWide96_roots :
    ((377187 / 5000 : ℝ) ≤ Real.sqrt (210560 / 37 : ℝ) ∧
      Real.sqrt (210560 / 37 : ℝ) ≤ 1207 / 16 ∧ Real.sqrt (10528 : ℝ) ≤ 1026061 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 96. -/
theorem gammaAnalyticWide96_logs :
    Real.log (210560 / 37 : ℝ) ≤ 86467 / 10000 ∧ Real.log (10528 : ℝ) ≤ 46309 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (210560 / 37) 13 20 0 (86467 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 10528 14 20 0 (46309 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide96_main (hRH : RiemannHypothesis) :
    (62273 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 10528,
        Real.exp (-(n : ℝ) / (210560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (210560 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 11977) * ((210560 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((210560 / 37) * (37 / 20)) + 1) / (500 / 11977) +
        1839 / 1000 ≤
      462477 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide96_roots.2.2]
  have hs :
    Real.sqrt ((210560 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((210560 / 37) * (37 / 20)) +
        21 / 20 ≤
      23213 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide96_roots.2.2, gammaAnalyticWide96_logs.2]
  have hz :
    Real.sqrt (210560 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (210560 / 37) + 2469 / 800 ≤
      3757 / 200 := by
    linarith only [gammaAnalyticWide96_roots.2.1, gammaAnalyticWide96_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 210560 / 37) (y := 37 / 20) (h := 500 / 11977) (r :=
      1207 / 16) (e := 78619 / 500000) (p := 462477 / 1000) (s := 23213 / 1000) (z := 3757 / 200)
      (F := 62273 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide96_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (210560 / 37 : ℝ) * (37 / 20) = 10528 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide96_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (210560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (210560 / 37 : ℝ)) ≤
      75687 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 377187 / 5000) (T := 1207 / 16) (Z := 86467 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide96_roots.1
      gammaAnalyticWide96_roots.2.1 gammaAnalyticWide96_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide96_power : (210560 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 773 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 96 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide96_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (9367 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18897 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (10528 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 9367 / 50)]
  apply
    reject_03_of_analytic_caps (B := 10528) (x := 210560 / 37) (H := 18897 / 100) (R :=
      377187 / 5000) (W := 773 / 100000) (F := 62273 / 1000) (U := 75687 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide96_power (gammaAnalyticWide96_main hGRH.riemann)
      (gammaAnalyticWide96_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 97. -/
theorem gammaAnalyticWide97_roots :
    ((380469 / 5000 : ℝ) ≤ Real.sqrt (214240 / 37 : ℝ) ∧
      Real.sqrt (214240 / 37 : ℝ) ≤ 760939 / 10000 ∧ Real.sqrt (10712 : ℝ) ≤ 258747 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 97. -/
theorem gammaAnalyticWide97_logs :
    Real.log (214240 / 37 : ℝ) ≤ 1083 / 125 ∧ Real.log (10712 : ℝ) ≤ 11599 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (214240 / 37) 13 20 0 (1083 / 125) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 10712 14 20 0 (11599 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide97_main (hRH : RiemannHypothesis) :
    (7853 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 10712,
        Real.exp (-(n : ℝ) / (214240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (214240 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 96229) * ((214240 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((214240 / 37) * (37 / 20)) + 1) / (4000 / 96229) +
        1839 / 1000 ≤
      234241 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide97_roots.2.2]
  have hs :
    Real.sqrt ((214240 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((214240 / 37) * (37 / 20)) +
        21 / 20 ≤
      2329 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide97_roots.2.2, gammaAnalyticWide97_logs.2]
  have hz :
    Real.sqrt (214240 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (214240 / 37) + 2469 / 800 ≤
      18841 / 1000 := by
    linarith only [gammaAnalyticWide97_roots.2.1, gammaAnalyticWide97_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 214240 / 37) (y := 37 / 20) (h := 4000 / 96229) (r :=
      760939 / 10000) (e := 78619 / 500000) (p := 234241 / 500) (s := 2329 / 100) (z :=
      18841 / 1000) (F := 7853 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide97_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (214240 / 37 : ℝ) * (37 / 20) = 10712 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide97_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (214240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (214240 / 37 : ℝ)) ≤
      38171 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 380469 / 5000) (T := 760939 / 10000) (Z := 1083 / 125)
      (by norm_num only) (by norm_num only) gammaAnalyticWide97_roots.1
      gammaAnalyticWide97_roots.2.1 gammaAnalyticWide97_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide97_power : (214240 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 153 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 97 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide97_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18897 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (9531 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (10712 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18897 / 100)]
  apply
    reject_03_of_analytic_caps (B := 10712) (x := 214240 / 37) (H := 9531 / 50) (R := 380469 / 5000)
      (W := 153 / 20000) (F := 7853 / 125) (U := 38171 / 500) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticWide97_power (gammaAnalyticWide97_main hGRH.riemann)
      (gammaAnalyticWide97_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 98. -/
theorem gammaAnalyticWide98_roots :
    ((383793 / 5000 : ℝ) ≤ Real.sqrt (218000 / 37 : ℝ) ∧
      Real.sqrt (218000 / 37 : ℝ) ≤ 767587 / 10000 ∧ Real.sqrt (10900 : ℝ) ≤ 1044031 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 98. -/
theorem gammaAnalyticWide98_logs :
    Real.log (218000 / 37 : ℝ) ≤ 43407 / 5000 ∧ Real.log (10900 : ℝ) ≤ 46483 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (218000 / 37) 13 20 0 (43407 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 10900 14 20 0 (46483 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide98_main (hRH : RiemannHypothesis) :
    (31691 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 10900,
        Real.exp (-(n : ℝ) / (218000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (218000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 96649) * ((218000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((218000 / 37) * (37 / 20)) + 1) / (4000 / 96649) +
        1839 / 1000 ≤
      59324 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide98_roots.2.2]
  have hs :
    Real.sqrt ((218000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((218000 / 37) * (37 / 20)) +
        21 / 20 ≤
      23367 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide98_roots.2.2, gammaAnalyticWide98_logs.2]
  have hz :
    Real.sqrt (218000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (218000 / 37) + 2469 / 800 ≤
      18899 / 1000 := by
    linarith only [gammaAnalyticWide98_roots.2.1, gammaAnalyticWide98_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 218000 / 37) (y := 37 / 20) (h := 4000 / 96649) (r :=
      767587 / 10000) (e := 78619 / 500000) (p := 59324 / 125) (s := 23367 / 1000) (z :=
      18899 / 1000) (F := 31691 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide98_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (218000 / 37 : ℝ) * (37 / 20) = 10900 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide98_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (218000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (218000 / 37 : ℝ)) ≤
      15401 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 383793 / 5000) (T := 767587 / 10000) (Z := 43407 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticWide98_roots.1
      gammaAnalyticWide98_roots.2.1 gammaAnalyticWide98_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide98_power : (218000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 379 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 98 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide98_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (9531 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19229 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (10900 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 9531 / 50)]
  apply
    reject_03_of_analytic_caps (B := 10900) (x := 218000 / 37) (H := 19229 / 100) (R :=
      383793 / 5000) (W := 379 / 50000) (F := 31691 / 500) (U := 15401 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide98_power (gammaAnalyticWide98_main hGRH.riemann)
      (gammaAnalyticWide98_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 99. -/
theorem gammaAnalyticWide99_roots :
    ((774317 / 10000 : ℝ) ≤ Real.sqrt (221840 / 37 : ℝ) ∧
      Real.sqrt (221840 / 37 : ℝ) ≤ 387159 / 5000 ∧ Real.sqrt (11092 : ℝ) ≤ 526593 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 99. -/
theorem gammaAnalyticWide99_logs :
    Real.log (221840 / 37 : ℝ) ≤ 21747 / 2500 ∧ Real.log (11092 : ℝ) ≤ 4657 / 500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (221840 / 37) 13 20 0 (21747 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 11092 14 20 0 (4657 / 500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticWide99_main (hRH : RiemannHypothesis) :
    (63947 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 11092,
        Real.exp (-(n : ℝ) / (221840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (221840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 97069) * ((221840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((221840 / 37) * (37 / 20)) + 1) / (4000 / 97069) +
        1839 / 1000 ≤
      120201 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide99_roots.2.2]
  have hs :
    Real.sqrt ((221840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((221840 / 37) * (37 / 20)) +
        21 / 20 ≤
      4689 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticWide99_roots.2.2, gammaAnalyticWide99_logs.2]
  have hz :
    Real.sqrt (221840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (221840 / 37) + 2469 / 800 ≤
      4739 / 250 := by
    linarith only [gammaAnalyticWide99_roots.2.1, gammaAnalyticWide99_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 221840 / 37) (y := 37 / 20) (h := 4000 / 97069) (r :=
      387159 / 5000) (e := 78619 / 500000) (p := 120201 / 250) (s := 4689 / 200) (z := 4739 / 250)
      (F := 63947 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticWide99_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (221840 / 37 : ℝ) * (37 / 20) = 11092 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticWide99_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (221840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (221840 / 37 : ℝ)) ≤
      77677 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 774317 / 10000) (T := 387159 / 5000) (Z := 21747 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticWide99_roots.1
      gammaAnalyticWide99_roots.2.1 gammaAnalyticWide99_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticWide99_power : (221840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 3 / 400 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 99 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticWide99_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19229 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (9699 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (11092 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19229 / 100)]
  apply
    reject_03_of_analytic_caps (B := 11092) (x := 221840 / 37) (H := 9699 / 50) (R :=
      774317 / 10000) (W := 3 / 400) (F := 63947 / 1000) (U := 77677 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticWide99_power (gammaAnalyticWide99_main hGRH.riemann)
      (gammaAnalyticWide99_principal hGRH.riemann)
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
