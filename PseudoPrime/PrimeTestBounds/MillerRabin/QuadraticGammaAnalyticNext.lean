/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticShared

/-! # Analytic Gamma cells after logarithmic scale 100.21 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact root caps for analytic cell 0. -/
theorem gammaAnalyticNext0_roots :
    ((201749 / 5000 : ℝ) ≤ Real.sqrt (60240 / 37 : ℝ) ∧
      Real.sqrt (60240 / 37 : ℝ) ≤ 403499 / 10000 ∧ Real.sqrt (3012 : ℝ) ≤ 548817 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 0. -/
theorem gammaAnalyticNext0_logs :
    Real.log (60240 / 37 : ℝ) ≤ 4622 / 625 ∧ Real.log (3012 : ℝ) ≤ 10013 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (60240 / 37) 11 20 0 (4622 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3012 12 20 0 (10013 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticNext0_main (hRH : RiemannHypothesis) :
    (1639 / 50 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3012,
        Real.exp (-(n : ℝ) / (60240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60240 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((60240 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((60240 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      182787 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext0_roots.2.2]
  have hs :
    Real.sqrt ((60240 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((60240 / 37) * (37 / 20)) +
        21 / 20 ≤
      9263 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext0_roots.2.2, gammaAnalyticNext0_logs.2]
  have hz :
    Real.sqrt (60240 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (60240 / 37) + 2469 / 800 ≤
      1913 / 125 := by
    linarith only [gammaAnalyticNext0_roots.2.1, gammaAnalyticNext0_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 60240 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      403499 / 10000) (e := 78619 / 500000) (p := 182787 / 1000) (s := 9263 / 500) (z := 1913 / 125)
      (F := 1639 / 50) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticNext0_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (60240 / 37 : ℝ) * (37 / 20) = 3012 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticNext0_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (60240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60240 / 37 : ℝ)) ≤
      4073 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 201749 / 5000) (T := 403499 / 10000) (Z := 4622 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticNext0_roots.1 gammaAnalyticNext0_roots.2.1
      gammaAnalyticNext0_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticNext0_power : (60240 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 781 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 0 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticNext0_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10021 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10031 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3012 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10021 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3012) (x := 60240 / 37) (H := 10031 / 100) (R := 201749 / 5000)
      (W := 781 / 50000) (F := 1639 / 50) (U := 4073 / 100) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticNext0_power (gammaAnalyticNext0_main hGRH.riemann)
      (gammaAnalyticNext0_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 1. -/
theorem gammaAnalyticNext1_roots :
    ((403899 / 10000 : ℝ) ≤ Real.sqrt (60360 / 37 : ℝ) ∧
      Real.sqrt (60360 / 37 : ℝ) ≤ 4039 / 100 ∧ Real.sqrt (3018 : ℝ) ≤ 137341 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 1. -/
theorem gammaAnalyticNext1_logs :
    Real.log (60360 / 37 : ℝ) ≤ 18493 / 2500 ∧ Real.log (3018 : ℝ) ≤ 20031 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (60360 / 37) 11 20 0 (18493 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3018 12 20 0 (20031 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticNext1_main (hRH : RiemannHypothesis) :
    (16407 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3018,
        Real.exp (-(n : ℝ) / (60360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60360 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((60360 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((60360 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      22882 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext1_roots.2.2]
  have hs :
    Real.sqrt ((60360 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((60360 / 37) * (37 / 20)) +
        21 / 20 ≤
      4633 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext1_roots.2.2, gammaAnalyticNext1_logs.2]
  have hz :
    Real.sqrt (60360 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (60360 / 37) + 2469 / 800 ≤
      15309 / 1000 := by
    linarith only [gammaAnalyticNext1_roots.2.1, gammaAnalyticNext1_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 60360 / 37) (y := 37 / 20) (h := 2 / 35) (r := 4039 / 100)
      (e := 78619 / 500000) (p := 22882 / 125) (s := 4633 / 250) (z := 15309 / 1000) (F :=
      16407 / 500) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticNext1_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (60360 / 37 : ℝ) * (37 / 20) = 3018 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticNext1_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (60360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60360 / 37 : ℝ)) ≤
      4077 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 403899 / 10000) (T := 4039 / 100) (Z := 18493 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticNext1_roots.1 gammaAnalyticNext1_roots.2.1
      gammaAnalyticNext1_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticNext1_power : (60360 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 39 / 2500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 1 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticNext1_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10031 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10041 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3018 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10031 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3018) (x := 60360 / 37) (H := 10041 / 100) (R :=
      403899 / 10000) (W := 39 / 2500) (F := 16407 / 500) (U := 4077 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticNext1_power (gammaAnalyticNext1_main hGRH.riemann)
      (gammaAnalyticNext1_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 2. -/
theorem gammaAnalyticNext2_roots :
    ((404301 / 10000 : ℝ) ≤ Real.sqrt (60480 / 37 : ℝ) ∧
      Real.sqrt (60480 / 37 : ℝ) ≤ 202151 / 5000 ∧ Real.sqrt (3024 : ℝ) ≤ 54991 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 2. -/
theorem gammaAnalyticNext2_logs :
    Real.log (60480 / 37 : ℝ) ≤ 9249 / 1250 ∧ Real.log (3024 : ℝ) ≤ 5009 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (60480 / 37) 11 20 0 (9249 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3024 12 20 0 (5009 / 625) = true := by decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticNext2_main (hRH : RiemannHypothesis) :
    (32847 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3024,
        Real.exp (-(n : ℝ) / (60480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60480 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((60480 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((60480 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      45831 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext2_roots.2.2]
  have hs :
    Real.sqrt ((60480 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((60480 / 37) * (37 / 20)) +
        21 / 20 ≤
      18539 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext2_roots.2.2, gammaAnalyticNext2_logs.2]
  have hz :
    Real.sqrt (60480 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (60480 / 37) + 2469 / 800 ≤
      7657 / 500 := by
    linarith only [gammaAnalyticNext2_roots.2.1, gammaAnalyticNext2_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 60480 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      202151 / 5000) (e := 78619 / 500000) (p := 45831 / 250) (s := 18539 / 1000) (z := 7657 / 500)
      (F := 32847 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticNext2_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (60480 / 37 : ℝ) * (37 / 20) = 3024 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticNext2_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (60480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60480 / 37 : ℝ)) ≤
      40809 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 404301 / 10000) (T := 202151 / 5000) (Z := 9249 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticNext2_roots.1 gammaAnalyticNext2_roots.2.1
      gammaAnalyticNext2_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticNext2_power : (60480 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 779 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 2 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticNext2_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10041 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10051 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3024 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10041 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3024) (x := 60480 / 37) (H := 10051 / 100) (R :=
      404301 / 10000) (W := 779 / 50000) (F := 32847 / 1000) (U := 40809 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticNext2_power (gammaAnalyticNext2_main hGRH.riemann)
      (gammaAnalyticNext2_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 3. -/
theorem gammaAnalyticNext3_roots :
    ((202351 / 5000 : ℝ) ≤ Real.sqrt (60600 / 37 : ℝ) ∧
      Real.sqrt (60600 / 37 : ℝ) ≤ 404703 / 10000 ∧ Real.sqrt (3030 : ℝ) ≤ 110091 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 3. -/
theorem gammaAnalyticNext3_logs :
    Real.log (60600 / 37 : ℝ) ≤ 18503 / 2500 ∧ Real.log (3030 : ℝ) ≤ 20041 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (60600 / 37) 11 20 0 (18503 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3030 12 20 0 (20041 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticNext3_main (hRH : RiemannHypothesis) :
    (32881 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3030,
        Real.exp (-(n : ℝ) / (60600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((60600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((60600 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      183593 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext3_roots.2.2]
  have hs :
    Real.sqrt ((60600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((60600 / 37) * (37 / 20)) +
        21 / 20 ≤
      3709 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext3_roots.2.2, gammaAnalyticNext3_logs.2]
  have hz :
    Real.sqrt (60600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (60600 / 37) + 2469 / 800 ≤
      7659 / 500 := by
    linarith only [gammaAnalyticNext3_roots.2.1, gammaAnalyticNext3_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 60600 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      404703 / 10000) (e := 78619 / 500000) (p := 183593 / 1000) (s := 3709 / 200) (z := 7659 / 500)
      (F := 32881 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticNext3_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (60600 / 37 : ℝ) * (37 / 20) = 3030 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticNext3_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (60600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60600 / 37 : ℝ)) ≤
      40849 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 202351 / 5000) (T := 404703 / 10000) (Z := 18503 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticNext3_roots.1 gammaAnalyticNext3_roots.2.1
      gammaAnalyticNext3_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticNext3_power : (60600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 389 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 3 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticNext3_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10051 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10061 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3030 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10051 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3030) (x := 60600 / 37) (H := 10061 / 100) (R := 202351 / 5000)
      (W := 389 / 25000) (F := 32881 / 1000) (U := 40849 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticNext3_power (gammaAnalyticNext3_main hGRH.riemann)
      (gammaAnalyticNext3_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 4. -/
theorem gammaAnalyticNext4_roots :
    ((202551 / 5000 : ℝ) ≤ Real.sqrt (60720 / 37 : ℝ) ∧
      Real.sqrt (60720 / 37 : ℝ) ≤ 405103 / 10000 ∧ Real.sqrt (3036 : ℝ) ≤ 551 / 10) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 4. -/
theorem gammaAnalyticNext4_logs :
    Real.log (60720 / 37 : ℝ) ≤ 4627 / 625 ∧ Real.log (3036 : ℝ) ≤ 80183 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (60720 / 37) 11 20 0 (4627 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 3036 12 20 0 (80183 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticNext4_main (hRH : RiemannHypothesis) :
    (6583 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 3036,
        Real.exp (-(n : ℝ) / (60720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60720 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2 / 35) * ((60720 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((60720 / 37) * (37 / 20)) + 1) / (2 / 35) +
        1839 / 1000 ≤
      183861 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext4_roots.2.2]
  have hs :
    Real.sqrt ((60720 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((60720 / 37) * (37 / 20)) +
        21 / 20 ≤
      18551 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticNext4_roots.2.2, gammaAnalyticNext4_logs.2]
  have hz :
    Real.sqrt (60720 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (60720 / 37) + 2469 / 800 ≤
      15323 / 1000 := by
    linarith only [gammaAnalyticNext4_roots.2.1, gammaAnalyticNext4_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 60720 / 37) (y := 37 / 20) (h := 2 / 35) (r :=
      405103 / 10000) (e := 78619 / 500000) (p := 183861 / 1000) (s := 18551 / 1000) (z :=
      15323 / 1000) (F := 6583 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticNext4_roots.2.1 gamma_analytic100_exp hp hs
      hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (60720 / 37 : ℝ) * (37 / 20) = 3036 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticNext4_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (60720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (60720 / 37 : ℝ)) ≤
      40889 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 202551 / 5000) (T := 405103 / 10000) (Z := 4627 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticNext4_roots.1 gammaAnalyticNext4_roots.2.1
      gammaAnalyticNext4_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticNext4_power : (60720 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 311 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 4 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticNext4_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (10061 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (10071 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (3036 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 10061 / 100)]
  apply
    reject_03_of_analytic_caps (B := 3036) (x := 60720 / 37) (H := 10071 / 100) (R := 202551 / 5000)
      (W := 311 / 20000) (F := 6583 / 200) (U := 40889 / 1000) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticNext4_power (gammaAnalyticNext4_main hGRH.riemann)
      (gammaAnalyticNext4_principal hGRH.riemann)
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
