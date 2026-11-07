/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaAnalyticHighCombined

/-! # Analytic Gamma cells after logarithmic scale 100.21 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exact root caps for analytic cell 0. -/
theorem gammaAnalyticBridge0_roots :
    ((1107407 / 5000 : ℝ) ≤ Real.sqrt (1815000 / 37 : ℝ) ∧
      Real.sqrt (1815000 / 37 : ℝ) ≤ 442963 / 2000 ∧ Real.sqrt (90750 : ℝ) ≤ 120499 / 400) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 0. -/
theorem gammaAnalyticBridge0_logs :
    Real.log (1815000 / 37 : ℝ) ≤ 108007 / 10000 ∧ Real.log (90750 : ℝ) ≤ 114159 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1815000 / 37) 16 20 0 (108007 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 90750 17 20 0 (114159 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge0_main (hRH : RiemannHypothesis) :
    (36967 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 90750,
        Real.exp (-(n : ℝ) / (1815000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1815000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 164171) * ((1815000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1815000 / 37) * (37 / 20)) + 1) / (4000 / 164171) +
        1839 / 1000 ≤
      2311809 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge0_roots.2.2]
  have hs :
    Real.sqrt ((1815000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1815000 / 37) * (37 / 20)) +
        21 / 20 ≤
      37107 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge0_roots.2.2, gammaAnalyticBridge0_logs.2]
  have hz :
    Real.sqrt (1815000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1815000 / 37) + 2469 / 800 ≤
      14529 / 500 := by
    linarith only [gammaAnalyticBridge0_roots.2.1, gammaAnalyticBridge0_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1815000 / 37) (y := 37 / 20) (h := 4000 / 164171) (r :=
      442963 / 2000) (e := 78619 / 500000) (p := 2311809 / 1000) (s := 37107 / 1000) (z :=
      14529 / 500) (F := 36967 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge0_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1815000 / 37 : ℝ) * (37 / 20) = 90750 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge0_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1815000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1815000 / 37 : ℝ)) ≤
      221613 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1107407 / 5000) (T := 442963 / 2000) (Z :=
      108007 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge0_roots.1
      gammaAnalyticBridge0_roots.2.1 gammaAnalyticBridge0_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge0_power : (1815000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 23 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 0 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge0_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (550 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11093 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (90750 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 550)]
  apply
    reject_03_of_analytic_caps (B := 90750) (x := 1815000 / 37) (H := 11093 / 20) (R :=
      1107407 / 5000) (W := 23 / 10000) (F := 36967 / 200) (U := 221613 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge0_power (gammaAnalyticBridge0_main hGRH.riemann)
      (gammaAnalyticBridge0_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 1. -/
theorem gammaAnalyticBridge1_roots :
    ((279191 / 1250 : ℝ) ≤ Real.sqrt (1845800 / 37 : ℝ) ∧
      Real.sqrt (1845800 / 37 : ℝ) ≤ 2233529 / 10000 ∧
      Real.sqrt (92290 : ℝ) ≤ 3037927 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 1. -/
theorem gammaAnalyticBridge1_logs :
    Real.log (1845800 / 37 : ℝ) ≤ 6761 / 625 ∧ Real.log (92290 : ℝ) ≤ 114327 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1845800 / 37) 16 20 0 (6761 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 92290 17 20 0 (114327 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge1_main (hRH : RiemannHypothesis) :
    (37281 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 92290,
        Real.exp (-(n : ℝ) / (1845800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1845800 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (125 / 5152) * ((1845800 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1845800 / 37) * (37 / 20)) + 1) / (125 / 5152) +
        1839 / 1000 ≤
      468223 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge1_roots.2.2]
  have hs :
    Real.sqrt ((1845800 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1845800 / 37) * (37 / 20)) +
        21 / 20 ≤
      7453 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge1_roots.2.2, gammaAnalyticBridge1_logs.2]
  have hz :
    Real.sqrt (1845800 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1845800 / 37) + 2469 / 800 ≤
      1167 / 40 := by
    linarith only [gammaAnalyticBridge1_roots.2.1, gammaAnalyticBridge1_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1845800 / 37) (y := 37 / 20) (h := 125 / 5152) (r :=
      2233529 / 10000) (e := 78619 / 500000) (p := 468223 / 200) (s := 7453 / 200) (z := 1167 / 40)
      (F := 37281 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge1_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1845800 / 37 : ℝ) * (37 / 20) = 92290 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge1_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1845800 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1845800 / 37 : ℝ)) ≤
      55871 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 279191 / 1250) (T := 2233529 / 10000) (Z := 6761 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge1_roots.1
      gammaAnalyticBridge1_roots.2.1 gammaAnalyticBridge1_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge1_power : (1845800 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 57 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 1 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge1_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11093 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (55933 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (92290 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11093 / 20)]
  apply
    reject_03_of_analytic_caps (B := 92290) (x := 1845800 / 37) (H := 55933 / 100) (R :=
      279191 / 1250) (W := 57 / 25000) (F := 37281 / 200) (U := 55871 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge1_power (gammaAnalyticBridge1_main hGRH.riemann)
      (gammaAnalyticBridge1_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 2. -/
theorem gammaAnalyticBridge2_roots :
    ((1126193 / 5000 : ℝ) ≤ Real.sqrt (1877100 / 37 : ℝ) ∧
      Real.sqrt (1877100 / 37 : ℝ) ≤ 2252387 / 10000 ∧
      Real.sqrt (93855 : ℝ) ≤ 3063577 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 2. -/
theorem gammaAnalyticBridge2_logs :
    Real.log (1877100 / 37 : ℝ) ≤ 13543 / 1250 ∧ Real.log (93855 : ℝ) ≤ 7156 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1877100 / 37) 16 20 0 (13543 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 93855 17 20 0 (7156 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge2_main (hRH : RiemannHypothesis) :
    (187989 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 93855,
        Real.exp (-(n : ℝ) / (1877100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1877100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 165557) * ((1877100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1877100 / 37) * (37 / 20)) + 1) / (4000 / 165557) +
        1839 / 1000 ≤
      2370771 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge2_roots.2.2]
  have hs :
    Real.sqrt ((1877100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1877100 / 37) * (37 / 20)) +
        21 / 20 ≤
      4678 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge2_roots.2.2, gammaAnalyticBridge2_logs.2]
  have hz :
    Real.sqrt (1877100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1877100 / 37) + 2469 / 800 ≤
      7323 / 250 := by
    linarith only [gammaAnalyticBridge2_roots.2.1, gammaAnalyticBridge2_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1877100 / 37) (y := 37 / 20) (h := 4000 / 165557) (r :=
      2252387 / 10000) (e := 78619 / 500000) (p := 2370771 / 1000) (s := 4678 / 125) (z :=
      7323 / 250) (F := 187989 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge2_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1877100 / 37 : ℝ) * (37 / 20) = 93855 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge2_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1877100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1877100 / 37 : ℝ)) ≤
      225369 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1126193 / 5000) (T := 2252387 / 10000) (Z :=
      13543 / 1250) (by norm_num only) (by norm_num only) gammaAnalyticBridge2_roots.1
      gammaAnalyticBridge2_roots.2.1 gammaAnalyticBridge2_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge2_power : (1877100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 113 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 2 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge2_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (55933 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (11281 / 20 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (93855 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 55933 / 100)]
  apply
    reject_03_of_analytic_caps (B := 93855) (x := 1877100 / 37) (H := 11281 / 20) (R :=
      1126193 / 5000) (W := 113 / 50000) (F := 187989 / 1000) (U := 225369 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge2_power (gammaAnalyticBridge2_main hGRH.riemann)
      (gammaAnalyticBridge2_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 3. -/
theorem gammaAnalyticBridge3_roots :
    ((283923 / 1250 : ℝ) ≤ Real.sqrt (1908900 / 37 : ℝ) ∧
      Real.sqrt (1908900 / 37 : ℝ) ≤ 454277 / 2000 ∧ Real.sqrt (95445 : ℝ) ≤ 1544709 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 3. -/
theorem gammaAnalyticBridge3_logs :
    Real.log (1908900 / 37 : ℝ) ≤ 6782 / 625 ∧ Real.log (95445 : ℝ) ≤ 14333 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1908900 / 37) 16 20 0 (6782 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 95445 17 20 0 (14333 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge3_main (hRH : RiemannHypothesis) :
    (23698 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 95445,
        Real.exp (-(n : ℝ) / (1908900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1908900 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (16 / 665) * ((1908900 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1908900 / 37) * (37 / 20)) + 1) / (16 / 665) +
        1839 / 1000 ≤
      96031 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge3_roots.2.2]
  have hs :
    Real.sqrt ((1908900 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1908900 / 37) * (37 / 20)) +
        21 / 20 ≤
      4698 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge3_roots.2.2, gammaAnalyticBridge3_logs.2]
  have hz :
    Real.sqrt (1908900 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1908900 / 37) + 2469 / 800 ≤
      2941 / 100 := by
    linarith only [gammaAnalyticBridge3_roots.2.1, gammaAnalyticBridge3_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1908900 / 37) (y := 37 / 20) (h := 16 / 665) (r :=
      454277 / 2000) (e := 78619 / 500000) (p := 96031 / 40) (s := 4698 / 125) (z := 2941 / 100)
      (F := 23698 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge3_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1908900 / 37 : ℝ) * (37 / 20) = 95445 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge3_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1908900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1908900 / 37 : ℝ)) ≤
      56817 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 283923 / 1250) (T := 454277 / 2000) (Z := 6782 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge3_roots.1
      gammaAnalyticBridge3_roots.2.1 gammaAnalyticBridge3_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge3_power : (1908900 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 7 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 3 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge3_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (11281 / 20 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (56881 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (95445 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 11281 / 20)]
  apply
    reject_03_of_analytic_caps (B := 95445) (x := 1908900 / 37) (H := 56881 / 100) (R :=
      283923 / 1250) (W := 7 / 3125) (F := 23698 / 125) (U := 56817 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge3_power (gammaAnalyticBridge3_main hGRH.riemann)
      (gammaAnalyticBridge3_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 4. -/
theorem gammaAnalyticBridge4_roots :
    ((572639 / 2500 : ℝ) ≤ Real.sqrt (1941260 / 37 : ℝ) ∧
      Real.sqrt (1941260 / 37 : ℝ) ≤ 2290557 / 10000 ∧ Real.sqrt (97063 : ℝ) ≤ 1557747 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 4. -/
theorem gammaAnalyticBridge4_logs :
    Real.log (1941260 / 37 : ℝ) ≤ 2717 / 250 ∧ Real.log (97063 : ℝ) ≤ 7177 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1941260 / 37) 16 20 0 (2717 / 250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 97063 17 20 0 (7177 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge4_main (hRH : RiemannHypothesis) :
    (191193 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 97063,
        Real.exp (-(n : ℝ) / (1941260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1941260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (80 / 3339) * ((1941260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1941260 / 37) * (37 / 20)) + 1) / (80 / 3339) +
        1839 / 1000 ≤
      2431179 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge4_roots.2.2]
  have hs :
    Real.sqrt ((1941260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1941260 / 37) * (37 / 20)) +
        21 / 20 ≤
      18873 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge4_roots.2.2, gammaAnalyticBridge4_logs.2]
  have hz :
    Real.sqrt (1941260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1941260 / 37) + 2469 / 800 ≤
      29529 / 1000 := by
    linarith only [gammaAnalyticBridge4_roots.2.1, gammaAnalyticBridge4_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1941260 / 37) (y := 37 / 20) (h := 80 / 3339) (r :=
      2290557 / 10000) (e := 78619 / 500000) (p := 2431179 / 1000) (s := 18873 / 500) (z :=
      29529 / 1000) (F := 191193 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge4_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1941260 / 37 : ℝ) * (37 / 20) = 97063 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge4_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1941260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1941260 / 37 : ℝ)) ≤
      45837 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 572639 / 2500) (T := 2290557 / 10000) (Z := 2717 / 250)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge4_roots.1
      gammaAnalyticBridge4_roots.2.1 gammaAnalyticBridge4_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge4_power : (1941260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 111 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 4 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge4_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (56881 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2868 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (97063 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 56881 / 100)]
  apply
    reject_03_of_analytic_caps (B := 97063) (x := 1941260 / 37) (H := 2868 / 5) (R := 572639 / 2500)
      (W := 111 / 50000) (F := 191193 / 1000) (U := 45837 / 200) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticBridge4_power (gammaAnalyticBridge4_main hGRH.riemann)
      (gammaAnalyticBridge4_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 5. -/
theorem gammaAnalyticBridge5_roots :
    ((2309849 / 10000 : ℝ) ≤ Real.sqrt (1974100 / 37 : ℝ) ∧
      Real.sqrt (1974100 / 37 : ℝ) ≤ 46197 / 200 ∧ Real.sqrt (98705 : ℝ) ≤ 392717 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 5. -/
theorem gammaAnalyticBridge5_logs :
    Real.log (1974100 / 37 : ℝ) ≤ 6803 / 625 ∧ Real.log (98705 : ℝ) ≤ 114999 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (1974100 / 37) 16 20 0 (6803 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 98705 17 20 0 (114999 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge5_main (hRH : RiemannHypothesis) :
    (192813 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 98705,
        Real.exp (-(n : ℝ) / (1974100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1974100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (80 / 3353) * ((1974100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((1974100 / 37) * (37 / 20)) + 1) / (80 / 3353) +
        1839 / 1000 ≤
      307738 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge5_roots.2.2]
  have hs :
    Real.sqrt ((1974100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((1974100 / 37) * (37 / 20)) +
        21 / 20 ≤
      37907 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge5_roots.2.2, gammaAnalyticBridge5_logs.2]
  have hz :
    Real.sqrt (1974100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (1974100 / 37) + 2469 / 800 ≤
      29649 / 1000 := by
    linarith only [gammaAnalyticBridge5_roots.2.1, gammaAnalyticBridge5_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 1974100 / 37) (y := 37 / 20) (h := 80 / 3353) (r :=
      46197 / 200) (e := 78619 / 500000) (p := 307738 / 125) (s := 37907 / 1000) (z := 29649 / 1000)
      (F := 192813 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge5_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (1974100 / 37 : ℝ) * (37 / 20) = 98705 by norm_num only, Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge5_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (1974100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (1974100 / 37 : ℝ)) ≤
      115557 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2309849 / 10000) (T := 46197 / 200) (Z := 6803 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge5_roots.1
      gammaAnalyticBridge5_roots.2.1 gammaAnalyticBridge5_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge5_power : (1974100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 11 / 5000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 5 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge5_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2868 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (57843 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (98705 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2868 / 5)]
  apply
    reject_03_of_analytic_caps (B := 98705) (x := 1974100 / 37) (H := 57843 / 100) (R :=
      2309849 / 10000) (W := 11 / 5000) (F := 192813 / 1000) (U := 115557 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge5_power (gammaAnalyticBridge5_main hGRH.riemann)
      (gammaAnalyticBridge5_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 6. -/
theorem gammaAnalyticBridge6_roots :
    ((145581 / 625 : ℝ) ≤ Real.sqrt (2007480 / 37 : ℝ) ∧
      Real.sqrt (2007480 / 37 : ℝ) ≤ 2329297 / 10000 ∧
      Real.sqrt (100374 : ℝ) ≤ 1584093 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 6. -/
theorem gammaAnalyticBridge6_logs :
    Real.log (2007480 / 37 : ℝ) ≤ 21803 / 2000 ∧ Real.log (100374 : ℝ) ≤ 115167 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2007480 / 37) 16 20 0 (21803 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 100374 17 20 0 (115167 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge6_main (hRH : RiemannHypothesis) :
    (38889 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 100374,
        Real.exp (-(n : ℝ) / (2007480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2007480 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 168357) * ((2007480 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2007480 / 37) * (37 / 20)) + 1) / (4000 / 168357) +
        1839 / 1000 ≤
      2493003 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge6_roots.2.2]
  have hs :
    Real.sqrt ((2007480 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2007480 / 37) * (37 / 20)) +
        21 / 20 ≤
      38071 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge6_roots.2.2, gammaAnalyticBridge6_logs.2]
  have hz :
    Real.sqrt (2007480 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2007480 / 37) + 2469 / 800 ≤
      29769 / 1000 := by
    linarith only [gammaAnalyticBridge6_roots.2.1, gammaAnalyticBridge6_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2007480 / 37) (y := 37 / 20) (h := 4000 / 168357) (r :=
      2329297 / 10000) (e := 78619 / 500000) (p := 2493003 / 1000) (s := 38071 / 1000) (z :=
      29769 / 1000) (F := 38889 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge6_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2007480 / 37 : ℝ) * (37 / 20) = 100374 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge6_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2007480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2007480 / 37 : ℝ)) ≤
      116529 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 145581 / 625) (T := 2329297 / 10000) (Z := 21803 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge6_roots.1
      gammaAnalyticBridge6_roots.2.1 gammaAnalyticBridge6_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge6_power : (2007480 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 109 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 6 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge6_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (57843 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (58329 / 100 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (100374 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 57843 / 100)]
  apply
    reject_03_of_analytic_caps (B := 100374) (x := 2007480 / 37) (H := 58329 / 100) (R :=
      145581 / 625) (W := 109 / 50000) (F := 38889 / 200) (U := 116529 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge6_power (gammaAnalyticBridge6_main hGRH.riemann)
      (gammaAnalyticBridge6_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 7. -/
theorem gammaAnalyticBridge7_roots :
    ((2348869 / 10000 : ℝ) ≤ Real.sqrt (2041360 / 37 : ℝ) ∧
      Real.sqrt (2041360 / 37 : ℝ) ≤ 234887 / 1000 ∧ Real.sqrt (102068 : ℝ) ≤ 3194809 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 7. -/
theorem gammaAnalyticBridge7_logs :
    Real.log (2041360 / 37 : ℝ) ≤ 109183 / 10000 ∧ Real.log (102068 : ℝ) ≤ 57667 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2041360 / 37) 16 20 0 (109183 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 102068 17 20 0 (57667 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge7_main (hRH : RiemannHypothesis) :
    (196089 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 102068,
        Real.exp (-(n : ℝ) / (2041360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2041360 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 21133) * ((2041360 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2041360 / 37) * (37 / 20)) + 1) / (500 / 21133) +
        1839 / 1000 ≤
      2524437 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge7_roots.2.2]
  have hs :
    Real.sqrt ((2041360 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2041360 / 37) * (37 / 20)) +
        21 / 20 ≤
      19117 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge7_roots.2.2, gammaAnalyticBridge7_logs.2]
  have hz :
    Real.sqrt (2041360 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2041360 / 37) + 2469 / 800 ≤
      2989 / 100 := by
    linarith only [gammaAnalyticBridge7_roots.2.1, gammaAnalyticBridge7_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2041360 / 37) (y := 37 / 20) (h := 500 / 21133) (r :=
      234887 / 1000) (e := 78619 / 500000) (p := 2524437 / 1000) (s := 19117 / 500) (z :=
      2989 / 100) (F := 196089 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge7_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2041360 / 37 : ℝ) * (37 / 20) = 102068 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge7_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2041360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2041360 / 37 : ℝ)) ≤
      47003 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2348869 / 10000) (T := 234887 / 1000) (Z :=
      109183 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge7_roots.1
      gammaAnalyticBridge7_roots.2.1 gammaAnalyticBridge7_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge7_power : (2041360 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 27 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 7 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge7_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (58329 / 100 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (2941 / 5 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (102068 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 58329 / 100)]
  apply
    reject_03_of_analytic_caps (B := 102068) (x := 2041360 / 37) (H := 2941 / 5) (R :=
      2348869 / 10000) (W := 27 / 12500) (F := 196089 / 1000) (U := 47003 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge7_power (gammaAnalyticBridge7_main hGRH.riemann)
      (gammaAnalyticBridge7_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 8. -/
theorem gammaAnalyticBridge8_roots :
    ((473727 / 2000 : ℝ) ≤ Real.sqrt (2075860 / 37 : ℝ) ∧
      Real.sqrt (2075860 / 37 : ℝ) ≤ 592159 / 2500 ∧ Real.sqrt (103793 : ℝ) ≤ 3221693 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 8. -/
theorem gammaAnalyticBridge8_logs :
    Real.log (2075860 / 37 : ℝ) ≤ 2187 / 200 ∧ Real.log (103793 : ℝ) ≤ 57751 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2075860 / 37) 16 20 0 (2187 / 200) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 103793 17 20 0 (57751 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge8_main (hRH : RiemannHypothesis) :
    (49437 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 103793,
        Real.exp (-(n : ℝ) / (2075860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2075860 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 169771) * ((2075860 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2075860 / 37) * (37 / 20)) + 1) / (4000 / 169771) +
        1839 / 1000 ≤
      319539 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge8_roots.2.2]
  have hs :
    Real.sqrt ((2075860 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2075860 / 37) * (37 / 20)) +
        21 / 20 ≤
      192 / 5 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge8_roots.2.2, gammaAnalyticBridge8_logs.2]
  have hz :
    Real.sqrt (2075860 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2075860 / 37) + 2469 / 800 ≤
      7503 / 250 := by
    linarith only [gammaAnalyticBridge8_roots.2.1, gammaAnalyticBridge8_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2075860 / 37) (y := 37 / 20) (h := 4000 / 169771) (r :=
      592159 / 2500) (e := 78619 / 500000) (p := 319539 / 125) (s := 192 / 5) (z := 7503 / 250)
      (F := 49437 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge8_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2075860 / 37 : ℝ) * (37 / 20) = 103793 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge8_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2075860 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2075860 / 37 : ℝ)) ≤
      236991 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 473727 / 2000) (T := 592159 / 2500) (Z := 2187 / 200)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge8_roots.1
      gammaAnalyticBridge8_roots.2.1 gammaAnalyticBridge8_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge8_power : (2075860 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 107 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 8 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge8_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (2941 / 5 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (29657 / 50 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (103793 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 2941 / 5)]
  apply
    reject_03_of_analytic_caps (B := 103793) (x := 2075860 / 37) (H := 29657 / 50) (R :=
      473727 / 2000) (W := 107 / 50000) (F := 49437 / 250) (U := 236991 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge8_power (gammaAnalyticBridge8_main hGRH.riemann)
      (gammaAnalyticBridge8_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 9. -/
theorem gammaAnalyticBridge9_roots :
    ((2388531 / 10000 : ℝ) ≤ Real.sqrt (2110880 / 37 : ℝ) ∧
      Real.sqrt (2110880 / 37 : ℝ) ≤ 597133 / 2500 ∧ Real.sqrt (105544 : ℝ) ≤ 1624377 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 9. -/
theorem gammaAnalyticBridge9_logs :
    Real.log (2110880 / 37 : ℝ) ≤ 109517 / 10000 ∧ Real.log (105544 : ℝ) ≤ 115669 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2110880 / 37) 16 20 0 (109517 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 105544 17 20 0 (115669 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge9_main (hRH : RiemannHypothesis) :
    (199419 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 105544,
        Real.exp (-(n : ℝ) / (2110880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2110880 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 34097) * ((2110880 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2110880 / 37) * (37 / 20)) + 1) / (800 / 34097) +
        1839 / 1000 ≤
      2588531 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge9_roots.2.2]
  have hs :
    Real.sqrt ((2110880 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2110880 / 37) * (37 / 20)) +
        21 / 20 ≤
      19283 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge9_roots.2.2, gammaAnalyticBridge9_logs.2]
  have hz :
    Real.sqrt (2110880 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2110880 / 37) + 2469 / 800 ≤
      6027 / 200 := by
    linarith only [gammaAnalyticBridge9_roots.2.1, gammaAnalyticBridge9_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2110880 / 37) (y := 37 / 20) (h := 800 / 34097) (r :=
      597133 / 2500) (e := 78619 / 500000) (p := 2588531 / 1000) (s := 19283 / 500) (z :=
      6027 / 200) (F := 199419 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge9_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2110880 / 37 : ℝ) * (37 / 20) = 105544 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge9_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2110880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2110880 / 37 : ℝ)) ≤
      11949 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2388531 / 10000) (T := 597133 / 2500) (Z :=
      109517 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge9_roots.1
      gammaAnalyticBridge9_roots.2.1 gammaAnalyticBridge9_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge9_power : (2110880 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 53 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 9 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge9_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (29657 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (14953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (105544 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 29657 / 50)]
  apply
    reject_03_of_analytic_caps (B := 105544) (x := 2110880 / 37) (H := 14953 / 25) (R :=
      2388531 / 10000) (W := 53 / 25000) (F := 199419 / 1000) (U := 11949 / 50) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge9_power (gammaAnalyticBridge9_main hGRH.riemann)
      (gammaAnalyticBridge9_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 10. -/
theorem gammaAnalyticBridge10_roots :
    ((602147 / 2500 : ℝ) ≤ Real.sqrt (2146480 / 37 : ℝ) ∧
      Real.sqrt (2146480 / 37 : ℝ) ≤ 2408589 / 10000 ∧ Real.sqrt (107324 : ℝ) ≤ 655207 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 10. -/
theorem gammaAnalyticBridge10_logs :
    Real.log (2146480 / 37 : ℝ) ≤ 21937 / 2000 ∧ Real.log (107324 : ℝ) ≤ 115837 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2146480 / 37) 16 20 0 (21937 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 107324 17 20 0 (115837 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge10_main (hRH : RiemannHypothesis) :
    (201103 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 107324,
        Real.exp (-(n : ℝ) / (2146480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2146480 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 171199) * ((2146480 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2146480 / 37) * (37 / 20)) + 1) / (4000 / 171199) +
        1839 / 1000 ≤
      655287 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge10_roots.2.2]
  have hs :
    Real.sqrt ((2146480 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2146480 / 37) * (37 / 20)) +
        21 / 20 ≤
      38733 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge10_roots.2.2, gammaAnalyticBridge10_logs.2]
  have hz :
    Real.sqrt (2146480 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2146480 / 37) + 2469 / 800 ≤
      15129 / 500 := by
    linarith only [gammaAnalyticBridge10_roots.2.1, gammaAnalyticBridge10_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2146480 / 37) (y := 37 / 20) (h := 4000 / 171199) (r :=
      2408589 / 10000) (e := 78619 / 500000) (p := 655287 / 250) (s := 38733 / 1000) (z :=
      15129 / 500) (F := 201103 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge10_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2146480 / 37 : ℝ) * (37 / 20) = 107324 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge10_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2146480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2146480 / 37 : ℝ)) ≤
      48197 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 602147 / 2500) (T := 2408589 / 10000) (Z := 21937 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge10_roots.1
      gammaAnalyticBridge10_roots.2.1 gammaAnalyticBridge10_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge10_power : (2146480 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 21 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 10 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge10_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (14953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (107324 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 14953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 107324) (x := 2146480 / 37) (H := 15078 / 25) (R :=
      602147 / 2500) (W := 21 / 10000) (F := 201103 / 1000) (U := 48197 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge10_power (gammaAnalyticBridge10_main hGRH.riemann)
      (gammaAnalyticBridge10_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 11. -/
theorem gammaAnalyticBridge11_roots :
    ((607181 / 2500 : ℝ) ≤ Real.sqrt (2182520 / 37 : ℝ) ∧
      Real.sqrt (2182520 / 37 : ℝ) ≤ 97149 / 400 ∧ Real.sqrt (109126 : ℝ) ≤ 3303423 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 11. -/
theorem gammaAnalyticBridge11_logs :
    Real.log (2182520 / 37 : ℝ) ≤ 109851 / 10000 ∧ Real.log (109126 : ℝ) ≤ 116003 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2182520 / 37) 16 20 0 (109851 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 109126 17 20 0 (116003 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge11_main (hRH : RiemannHypothesis) :
    (202793 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 109126,
        Real.exp (-(n : ℝ) / (2182520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2182520 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 171913) * ((2182520 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2182520 / 37) * (37 / 20)) + 1) / (4000 / 171913) +
        1839 / 1000 ≤
      265403 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge11_roots.2.2]
  have hs :
    Real.sqrt ((2182520 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2182520 / 37) * (37 / 20)) +
        21 / 20 ≤
      38901 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge11_roots.2.2, gammaAnalyticBridge11_logs.2]
  have hz :
    Real.sqrt (2182520 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2182520 / 37) + 2469 / 800 ≤
      15191 / 500 := by
    linarith only [gammaAnalyticBridge11_roots.2.1, gammaAnalyticBridge11_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2182520 / 37) (y := 37 / 20) (h := 4000 / 171913) (r :=
      97149 / 400) (e := 78619 / 500000) (p := 265403 / 100) (s := 38901 / 1000) (z := 15191 / 500)
      (F := 202793 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge11_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2182520 / 37 : ℝ) * (37 / 20) = 109126 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge11_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2182520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2182520 / 37 : ℝ)) ≤
      121499 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 607181 / 2500) (T := 97149 / 400) (Z := 109851 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge11_roots.1
      gammaAnalyticBridge11_roots.2.1 gammaAnalyticBridge11_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge11_power : (2182520 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 13 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 11 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge11_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (109126 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 109126) (x := 2182520 / 37) (H := 15203 / 25) (R :=
      607181 / 2500) (W := 13 / 6250) (F := 202793 / 1000) (U := 121499 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge11_power (gammaAnalyticBridge11_main hGRH.riemann)
      (gammaAnalyticBridge11_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 12. -/
theorem gammaAnalyticBridge12_roots :
    ((2448849 / 10000 : ℝ) ≤ Real.sqrt (2218840 / 37 : ℝ) ∧
      Real.sqrt (2218840 / 37 : ℝ) ≤ 48977 / 200 ∧ Real.sqrt (110942 : ℝ) ≤ 832699 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 12. -/
theorem gammaAnalyticBridge12_logs :
    Real.log (2218840 / 37 : ℝ) ≤ 6876 / 625 ∧ Real.log (110942 : ℝ) ≤ 14521 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2218840 / 37) 16 20 0 (6876 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 110942 17 20 0 (14521 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge12_main (hRH : RiemannHypothesis) :
    (204483 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 110942,
        Real.exp (-(n : ℝ) / (2218840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2218840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 172627) * ((2218840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2218840 / 37) * (37 / 20)) + 1) / (4000 / 172627) +
        1839 / 1000 ≤
      268703 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge12_roots.2.2]
  have hs :
    Real.sqrt ((2218840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2218840 / 37) * (37 / 20)) +
        21 / 20 ≤
      9767 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge12_roots.2.2, gammaAnalyticBridge12_logs.2]
  have hz :
    Real.sqrt (2218840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2218840 / 37) + 2469 / 800 ≤
      6101 / 200 := by
    linarith only [gammaAnalyticBridge12_roots.2.1, gammaAnalyticBridge12_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2218840 / 37) (y := 37 / 20) (h := 4000 / 172627) (r :=
      48977 / 200) (e := 78619 / 500000) (p := 268703 / 100) (s := 9767 / 250) (z := 6101 / 200)
      (F := 204483 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge12_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2218840 / 37 : ℝ) * (37 / 20) = 110942 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge12_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2218840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2218840 / 37 : ℝ)) ≤
      24501 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2448849 / 10000) (T := 48977 / 200) (Z := 6876 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge12_roots.1
      gammaAnalyticBridge12_roots.2.1 gammaAnalyticBridge12_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge12_power : (2218840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 103 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 12 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge12_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (110942 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 110942) (x := 2218840 / 37) (H := 15328 / 25) (R :=
      2448849 / 10000) (W := 103 / 50000) (F := 204483 / 1000) (U := 24501 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge12_power (gammaAnalyticBridge12_main hGRH.riemann)
      (gammaAnalyticBridge12_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 13. -/
theorem gammaAnalyticBridge13_roots :
    ((1234493 / 5000 : ℝ) ≤ Real.sqrt (2255480 / 37 : ℝ) ∧
      Real.sqrt (2255480 / 37 : ℝ) ≤ 2468987 / 10000 ∧ Real.sqrt (112774 : ℝ) ≤ 671637 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 13. -/
theorem gammaAnalyticBridge13_logs :
    Real.log (2255480 / 37 : ℝ) ≤ 5509 / 500 ∧ Real.log (112774 : ℝ) ≤ 29083 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2255480 / 37) 16 20 0 (5509 / 500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 112774 17 20 0 (29083 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge13_main (hRH : RiemannHypothesis) :
    (103087 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 112774,
        Real.exp (-(n : ℝ) / (2255480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2255480 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 86667) * ((2255480 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2255480 / 37) * (37 / 20)) + 1) / (2000 / 86667) +
        1839 / 1000 ≤
      544037 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge13_roots.2.2]
  have hs :
    Real.sqrt ((2255480 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2255480 / 37) * (37 / 20)) +
        21 / 20 ≤
      7847 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge13_roots.2.2, gammaAnalyticBridge13_logs.2]
  have hz :
    Real.sqrt (2255480 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2255480 / 37) + 2469 / 800 ≤
      7657 / 250 := by
    linarith only [gammaAnalyticBridge13_roots.2.1, gammaAnalyticBridge13_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2255480 / 37) (y := 37 / 20) (h := 2000 / 86667) (r :=
      2468987 / 10000) (e := 78619 / 500000) (p := 544037 / 200) (s := 7847 / 200) (z := 7657 / 250)
      (F := 103087 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge13_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2255480 / 37 : ℝ) * (37 / 20) = 112774 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge13_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2255480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2255480 / 37 : ℝ)) ≤
      247023 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1234493 / 5000) (T := 2468987 / 10000) (Z := 5509 / 500)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge13_roots.1
      gammaAnalyticBridge13_roots.2.1 gammaAnalyticBridge13_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge13_power : (2255480 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 51 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 13 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge13_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (112774 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 112774) (x := 2255480 / 37) (H := 15453 / 25) (R :=
      1234493 / 5000) (W := 51 / 25000) (F := 103087 / 500) (U := 247023 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge13_power (gammaAnalyticBridge13_main hGRH.riemann)
      (gammaAnalyticBridge13_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 14. -/
theorem gammaAnalyticBridge14_roots :
    ((1244561 / 5000 : ℝ) ≤ Real.sqrt (2292420 / 37 : ℝ) ∧
      Real.sqrt (2292420 / 37 : ℝ) ≤ 2489123 / 10000 ∧
      Real.sqrt (114621 : ℝ) ≤ 3385573 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 14. -/
theorem gammaAnalyticBridge14_logs :
    Real.log (2292420 / 37 : ℝ) ≤ 110343 / 10000 ∧ Real.log (114621 : ℝ) ≤ 58247 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2292420 / 37) 16 20 0 (110343 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 114621 17 20 0 (58247 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge14_main (hRH : RiemannHypothesis) :
    (25983 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 114621,
        Real.exp (-(n : ℝ) / (2292420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2292420 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 174041) * ((2292420 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2292420 / 37) * (37 / 20)) + 1) / (4000 / 174041) +
        1839 / 1000 ≤
      110139 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge14_roots.2.2]
  have hs :
    Real.sqrt ((2292420 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2292420 / 37) * (37 / 20)) +
        21 / 20 ≤
      19701 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge14_roots.2.2, gammaAnalyticBridge14_logs.2]
  have hz :
    Real.sqrt (2292420 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2292420 / 37) + 2469 / 800 ≤
      30751 / 1000 := by
    linarith only [gammaAnalyticBridge14_roots.2.1, gammaAnalyticBridge14_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2292420 / 37) (y := 37 / 20) (h := 4000 / 174041) (r :=
      2489123 / 10000) (e := 78619 / 500000) (p := 110139 / 40) (s := 19701 / 500) (z :=
      30751 / 1000) (F := 25983 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge14_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2292420 / 37 : ℝ) * (37 / 20) = 114621 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge14_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2292420 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2292420 / 37 : ℝ)) ≤
      62259 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1244561 / 5000) (T := 2489123 / 10000) (Z :=
      110343 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge14_roots.1
      gammaAnalyticBridge14_roots.2.1 gammaAnalyticBridge14_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge14_power : (2292420 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 101 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 14 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge14_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (114621 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 114621) (x := 2292420 / 37) (H := 15578 / 25) (R :=
      1244561 / 5000) (W := 101 / 50000) (F := 25983 / 125) (U := 62259 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge14_power (gammaAnalyticBridge14_main hGRH.riemann)
      (gammaAnalyticBridge14_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 15. -/
theorem gammaAnalyticBridge15_roots :
    ((1254629 / 5000 : ℝ) ≤ Real.sqrt (2329660 / 37 : ℝ) ∧
      Real.sqrt (2329660 / 37 : ℝ) ≤ 2509259 / 10000 ∧
      Real.sqrt (116483 : ℝ) ≤ 3412961 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 15. -/
theorem gammaAnalyticBridge15_logs :
    Real.log (2329660 / 37 : ℝ) ≤ 13813 / 1250 ∧ Real.log (116483 : ℝ) ≤ 7291 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2329660 / 37) 16 20 0 (13813 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 116483 17 20 0 (7291 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge15_main (hRH : RiemannHypothesis) :
    (41911 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 116483,
        Real.exp (-(n : ℝ) / (2329660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2329660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 174741) * ((2329660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2329660 / 37) * (37 / 20)) + 1) / (4000 / 174741) +
        1839 / 1000 ≤
      27869 / 10 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge15_roots.2.2]
  have hs :
    Real.sqrt ((2329660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2329660 / 37) * (37 / 20)) +
        21 / 20 ≤
      4946 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge15_roots.2.2, gammaAnalyticBridge15_logs.2]
  have hz :
    Real.sqrt (2329660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2329660 / 37) + 2469 / 800 ≤
      15437 / 500 := by
    linarith only [gammaAnalyticBridge15_roots.2.1, gammaAnalyticBridge15_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2329660 / 37) (y := 37 / 20) (h := 4000 / 174741) (r :=
      2509259 / 10000) (e := 78619 / 500000) (p := 27869 / 10) (s := 4946 / 125) (z := 15437 / 500)
      (F := 41911 / 200) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge15_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2329660 / 37 : ℝ) * (37 / 20) = 116483 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge15_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2329660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2329660 / 37 : ℝ)) ≤
      251049 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1254629 / 5000) (T := 2509259 / 10000) (Z :=
      13813 / 1250) (by norm_num only) (by norm_num only) gammaAnalyticBridge15_roots.1
      gammaAnalyticBridge15_roots.2.1 gammaAnalyticBridge15_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge15_power : (2329660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1 / 500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 15 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge15_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (116483 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 116483) (x := 2329660 / 37) (H := 15703 / 25) (R :=
      1254629 / 5000) (W := 1 / 500) (F := 41911 / 200) (U := 251049 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge15_power (gammaAnalyticBridge15_main hGRH.riemann)
      (gammaAnalyticBridge15_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 16. -/
theorem gammaAnalyticBridge16_roots :
    ((1264697 / 5000 : ℝ) ≤ Real.sqrt (2367200 / 37 : ℝ) ∧
      Real.sqrt (2367200 / 37 : ℝ) ≤ 505879 / 2000 ∧ Real.sqrt (118360 : ℝ) ≤ 3440349 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 16. -/
theorem gammaAnalyticBridge16_logs :
    Real.log (2367200 / 37 : ℝ) ≤ 13833 / 1250 ∧ Real.log (118360 : ℝ) ≤ 23363 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2367200 / 37) 16 20 0 (13833 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 118360 17 20 0 (23363 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge16_main (hRH : RiemannHypothesis) :
    (105623 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 118360,
        Real.exp (-(n : ℝ) / (2367200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2367200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 175441) * ((2367200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2367200 / 37) * (37 / 20)) + 1) / (4000 / 175441) +
        1839 / 1000 ≤
      2820459 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge16_roots.2.2]
  have hs :
    Real.sqrt ((2367200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2367200 / 37) * (37 / 20)) +
        21 / 20 ≤
      7947 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge16_roots.2.2, gammaAnalyticBridge16_logs.2]
  have hz :
    Real.sqrt (2367200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2367200 / 37) + 2469 / 800 ≤
      30997 / 1000 := by
    linarith only [gammaAnalyticBridge16_roots.2.1, gammaAnalyticBridge16_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2367200 / 37) (y := 37 / 20) (h := 4000 / 175441) (r :=
      505879 / 2000) (e := 78619 / 500000) (p := 2820459 / 1000) (s := 7947 / 200) (z :=
      30997 / 1000) (F := 105623 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge16_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2367200 / 37 : ℝ) * (37 / 20) = 118360 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge16_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2367200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2367200 / 37 : ℝ)) ≤
      253063 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1264697 / 5000) (T := 505879 / 2000) (Z := 13833 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge16_roots.1
      gammaAnalyticBridge16_roots.2.1 gammaAnalyticBridge16_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge16_power : (2367200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 99 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 16 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge16_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (118360 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 118360) (x := 2367200 / 37) (H := 15828 / 25) (R :=
      1264697 / 5000) (W := 99 / 50000) (F := 105623 / 500) (U := 253063 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge16_power (gammaAnalyticBridge16_main hGRH.riemann)
      (gammaAnalyticBridge16_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 17. -/
theorem gammaAnalyticBridge17_roots :
    ((254953 / 1000 : ℝ) ≤ Real.sqrt (2405040 / 37 : ℝ) ∧
      Real.sqrt (2405040 / 37 : ℝ) ≤ 2549531 / 10000 ∧
      Real.sqrt (120252 : ℝ) ≤ 1733869 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 17. -/
theorem gammaAnalyticBridge17_logs :
    Real.log (2405040 / 37 : ℝ) ≤ 55411 / 5000 ∧ Real.log (120252 : ℝ) ≤ 58487 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2405040 / 37) 16 20 0 (55411 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 120252 17 20 0 (58487 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge17_main (hRH : RiemannHypothesis) :
    (26617 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 120252,
        Real.exp (-(n : ℝ) / (2405040 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2405040 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 88067) * ((2405040 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2405040 / 37) * (37 / 20)) + 1) / (2000 / 88067) +
        1839 / 1000 ≤
      356769 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge17_roots.2.2]
  have hs :
    Real.sqrt ((2405040 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2405040 / 37) * (37 / 20)) +
        21 / 20 ≤
      39901 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge17_roots.2.2, gammaAnalyticBridge17_logs.2]
  have hz :
    Real.sqrt (2405040 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2405040 / 37) + 2469 / 800 ≤
      778 / 25 := by
    linarith only [gammaAnalyticBridge17_roots.2.1, gammaAnalyticBridge17_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2405040 / 37) (y := 37 / 20) (h := 2000 / 88067) (r :=
      2549531 / 10000) (e := 78619 / 500000) (p := 356769 / 125) (s := 39901 / 1000) (z := 778 / 25)
      (F := 26617 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge17_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2405040 / 37 : ℝ) * (37 / 20) = 120252 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge17_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2405040 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2405040 / 37 : ℝ)) ≤
      63769 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 254953 / 1000) (T := 2549531 / 10000) (Z := 55411 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge17_roots.1
      gammaAnalyticBridge17_roots.2.1 gammaAnalyticBridge17_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge17_power : (2405040 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 197 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 17 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge17_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (15953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (120252 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 120252) (x := 2405040 / 37) (H := 15953 / 25) (R :=
      254953 / 1000) (W := 197 / 100000) (F := 26617 / 125) (U := 63769 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge17_power (gammaAnalyticBridge17_main hGRH.riemann)
      (gammaAnalyticBridge17_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 18. -/
theorem gammaAnalyticBridge18_roots :
    ((2569667 / 10000 : ℝ) ≤ Real.sqrt (2443180 / 37 : ℝ) ∧
      Real.sqrt (2443180 / 37 : ℝ) ≤ 642417 / 2500 ∧ Real.sqrt (122159 : ℝ) ≤ 1747563 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 18. -/
theorem gammaAnalyticBridge18_logs :
    Real.log (2443180 / 37 : ℝ) ≤ 110979 / 10000 ∧ Real.log (122159 : ℝ) ≤ 117131 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2443180 / 37) 17 20 0 (110979 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 122159 17 20 0 (117131 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge18_main (hRH : RiemannHypothesis) :
    (214627 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 122159,
        Real.exp (-(n : ℝ) / (2443180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2443180 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 88417) * ((2443180 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2443180 / 37) * (37 / 20)) + 1) / (2000 / 88417) +
        1839 / 1000 ≤
      2887977 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge18_roots.2.2]
  have hs :
    Real.sqrt ((2443180 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2443180 / 37) * (37 / 20)) +
        21 / 20 ≤
      40067 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge18_roots.2.2, gammaAnalyticBridge18_logs.2]
  have hz :
    Real.sqrt (2443180 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2443180 / 37) + 2469 / 800 ≤
      15621 / 500 := by
    linarith only [gammaAnalyticBridge18_roots.2.1, gammaAnalyticBridge18_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2443180 / 37) (y := 37 / 20) (h := 2000 / 88417) (r :=
      642417 / 2500) (e := 78619 / 500000) (p := 2887977 / 1000) (s := 40067 / 1000) (z :=
      15621 / 500) (F := 214627 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge18_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2443180 / 37 : ℝ) * (37 / 20) = 122159 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge18_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2443180 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2443180 / 37 : ℝ)) ≤
      257089 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2569667 / 10000) (T := 642417 / 2500) (Z :=
      110979 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge18_roots.1
      gammaAnalyticBridge18_roots.2.1 gammaAnalyticBridge18_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge18_power : (2443180 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 39 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 18 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge18_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (15953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (122159 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 15953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 122159) (x := 2443180 / 37) (H := 16078 / 25) (R :=
      2569667 / 10000) (W := 39 / 20000) (F := 214627 / 1000) (U := 257089 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge18_power (gammaAnalyticBridge18_main hGRH.riemann)
      (gammaAnalyticBridge18_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 19. -/
theorem gammaAnalyticBridge19_roots :
    ((2589803 / 10000 : ℝ) ≤ Real.sqrt (2481620 / 37 : ℝ) ∧
      Real.sqrt (2481620 / 37 : ℝ) ≤ 647451 / 2500 ∧ Real.sqrt (124081 : ℝ) ≤ 1761257 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 19. -/
theorem gammaAnalyticBridge19_logs :
    Real.log (2481620 / 37 : ℝ) ≤ 6946 / 625 ∧ Real.log (124081 : ℝ) ≤ 117287 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2481620 / 37) 17 20 0 (6946 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 124081 17 20 0 (117287 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge19_main (hRH : RiemannHypothesis) :
    (108159 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 124081,
        Real.exp (-(n : ℝ) / (2481620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2481620 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (50 / 2219) * ((2481620 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2481620 / 37) * (37 / 20)) + 1) / (50 / 2219) +
        1839 / 1000 ≤
      365242 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge19_roots.2.2]
  have hs :
    Real.sqrt ((2481620 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2481620 / 37) * (37 / 20)) +
        21 / 20 ≤
      5029 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge19_roots.2.2, gammaAnalyticBridge19_logs.2]
  have hz :
    Real.sqrt (2481620 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2481620 / 37) + 2469 / 800 ≤
      7841 / 250 := by
    linarith only [gammaAnalyticBridge19_roots.2.1, gammaAnalyticBridge19_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2481620 / 37) (y := 37 / 20) (h := 50 / 2219) (r :=
      647451 / 2500) (e := 78619 / 500000) (p := 365242 / 125) (s := 5029 / 125) (z := 7841 / 250)
      (F := 108159 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge19_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2481620 / 37 : ℝ) * (37 / 20) = 124081 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge19_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2481620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2481620 / 37 : ℝ)) ≤
      129551 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2589803 / 10000) (T := 647451 / 2500) (Z := 6946 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge19_roots.1
      gammaAnalyticBridge19_roots.2.1 gammaAnalyticBridge19_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge19_power : (2481620 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 193 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 19 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge19_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (124081 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 124081) (x := 2481620 / 37) (H := 16203 / 25) (R :=
      2589803 / 10000) (W := 193 / 100000) (F := 108159 / 500) (U := 129551 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge19_power (gammaAnalyticBridge19_main hGRH.riemann)
      (gammaAnalyticBridge19_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 20. -/
theorem gammaAnalyticBridge20_roots :
    ((2609929 / 10000 : ℝ) ≤ Real.sqrt (2520340 / 37 : ℝ) ∧
      Real.sqrt (2520340 / 37 : ℝ) ≤ 260993 / 1000 ∧ Real.sqrt (126017 : ℝ) ≤ 221868 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 20. -/
theorem gammaAnalyticBridge20_logs :
    Real.log (2520340 / 37 : ℝ) ≤ 11129 / 1000 ∧ Real.log (126017 : ℝ) ≤ 58721 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2520340 / 37) 17 20 0 (11129 / 1000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 126017 17 20 0 (58721 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge20_main (hRH : RiemannHypothesis) :
    (27251 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 126017,
        Real.exp (-(n : ℝ) / (2520340 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2520340 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 178213) * ((2520340 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2520340 / 37) * (37 / 20)) + 1) / (4000 / 178213) +
        1839 / 1000 ≤
      369501 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge20_roots.2.2]
  have hs :
    Real.sqrt ((2520340 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2520340 / 37) * (37 / 20)) +
        21 / 20 ≤
      20199 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge20_roots.2.2, gammaAnalyticBridge20_logs.2]
  have hz :
    Real.sqrt (2520340 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2520340 / 37) + 2469 / 800 ≤
      15743 / 500 := by
    linarith only [gammaAnalyticBridge20_roots.2.1, gammaAnalyticBridge20_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2520340 / 37) (y := 37 / 20) (h := 4000 / 178213) (r :=
      260993 / 1000) (e := 78619 / 500000) (p := 369501 / 125) (s := 20199 / 500) (z := 15743 / 500)
      (F := 27251 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge20_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2520340 / 37 : ℝ) * (37 / 20) = 126017 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge20_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2520340 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2520340 / 37 : ℝ)) ≤
      130557 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2609929 / 10000) (T := 260993 / 1000) (Z := 11129 / 1000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge20_roots.1
      gammaAnalyticBridge20_roots.2.1 gammaAnalyticBridge20_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge20_power : (2520340 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 6 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 20 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge20_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (126017 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 126017) (x := 2520340 / 37) (H := 16328 / 25) (R :=
      2609929 / 10000) (W := 6 / 3125) (F := 27251 / 125) (U := 130557 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge20_power (gammaAnalyticBridge20_main hGRH.riemann)
      (gammaAnalyticBridge20_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 21. -/
theorem gammaAnalyticBridge21_roots :
    ((526013 / 2000 : ℝ) ≤ Real.sqrt (2559380 / 37 : ℝ) ∧
      Real.sqrt (2559380 / 37 : ℝ) ≤ 1315033 / 5000 ∧ Real.sqrt (127969 : ℝ) ≤ 894319 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 21. -/
theorem gammaAnalyticBridge21_logs :
    Real.log (2559380 / 37 : ℝ) ≤ 27861 / 2500 ∧ Real.log (127969 : ℝ) ≤ 29399 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2559380 / 37) 17 20 0 (27861 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 127969 17 20 0 (29399 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge21_main (hRH : RiemannHypothesis) :
    (219699 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 127969,
        Real.exp (-(n : ℝ) / (2559380 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2559380 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 178899) * ((2559380 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2559380 / 37) * (37 / 20)) + 1) / (4000 / 178899) +
        1839 / 1000 ≤
      299023 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge21_roots.2.2]
  have hs :
    Real.sqrt ((2559380 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2559380 / 37) * (37 / 20)) +
        21 / 20 ≤
      40563 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge21_roots.2.2, gammaAnalyticBridge21_logs.2]
  have hz :
    Real.sqrt (2559380 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2559380 / 37) + 2469 / 800 ≤
      3951 / 125 := by
    linarith only [gammaAnalyticBridge21_roots.2.1, gammaAnalyticBridge21_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2559380 / 37) (y := 37 / 20) (h := 4000 / 178899) (r :=
      1315033 / 5000) (e := 78619 / 500000) (p := 299023 / 100) (s := 40563 / 1000) (z :=
      3951 / 125) (F := 219699 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge21_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2559380 / 37 : ℝ) * (37 / 20) = 127969 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge21_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2559380 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2559380 / 37 : ℝ)) ≤
      263127 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 526013 / 2000) (T := 1315033 / 5000) (Z := 27861 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge21_roots.1
      gammaAnalyticBridge21_roots.2.1 gammaAnalyticBridge21_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge21_power : (2559380 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 19 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 21 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge21_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (127969 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 127969) (x := 2559380 / 37) (H := 16453 / 25) (R :=
      526013 / 2000) (W := 19 / 10000) (F := 219699 / 1000) (U := 263127 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge21_power (gammaAnalyticBridge21_main hGRH.riemann)
      (gammaAnalyticBridge21_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 22. -/
theorem gammaAnalyticBridge22_roots :
    ((2650201 / 10000 : ℝ) ≤ Real.sqrt (2598720 / 37 : ℝ) ∧
      Real.sqrt (2598720 / 37 : ℝ) ≤ 1325101 / 5000 ∧ Real.sqrt (129936 : ℝ) ≤ 450583 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 22. -/
theorem gammaAnalyticBridge22_logs :
    Real.log (2598720 / 37 : ℝ) ≤ 111597 / 10000 ∧ Real.log (129936 : ℝ) ≤ 29437 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2598720 / 37) 17 20 0 (111597 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 129936 17 20 0 (29437 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge22_main (hRH : RiemannHypothesis) :
    (221389 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 129936,
        Real.exp (-(n : ℝ) / (2598720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2598720 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 89789) * ((2598720 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2598720 / 37) * (37 / 20)) + 1) / (2000 / 89789) +
        1839 / 1000 ≤
      378073 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge22_roots.2.2]
  have hs :
    Real.sqrt ((2598720 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2598720 / 37) * (37 / 20)) +
        21 / 20 ≤
      5091 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge22_roots.2.2, gammaAnalyticBridge22_logs.2]
  have hz :
    Real.sqrt (2598720 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2598720 / 37) + 2469 / 800 ≤
      3173 / 100 := by
    linarith only [gammaAnalyticBridge22_roots.2.1, gammaAnalyticBridge22_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2598720 / 37) (y := 37 / 20) (h := 2000 / 89789) (r :=
      1325101 / 5000) (e := 78619 / 500000) (p := 378073 / 125) (s := 5091 / 125) (z := 3173 / 100)
      (F := 221389 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge22_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2598720 / 37 : ℝ) * (37 / 20) = 129936 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge22_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2598720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2598720 / 37 : ℝ)) ≤
      13257 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2650201 / 10000) (T := 1325101 / 5000) (Z :=
      111597 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge22_roots.1
      gammaAnalyticBridge22_roots.2.1 gammaAnalyticBridge22_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge22_power : (2598720 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 47 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 22 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge22_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (129936 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 129936) (x := 2598720 / 37) (H := 16578 / 25) (R :=
      2650201 / 10000) (W := 47 / 25000) (F := 221389 / 1000) (U := 13257 / 50) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge22_power (gammaAnalyticBridge22_main hGRH.riemann)
      (gammaAnalyticBridge22_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 23. -/
theorem gammaAnalyticBridge23_roots :
    ((2670337 / 10000 : ℝ) ≤ Real.sqrt (2638360 / 37 : ℝ) ∧
      Real.sqrt (2638360 / 37 : ℝ) ≤ 1335169 / 5000 ∧ Real.sqrt (131918 : ℝ) ≤ 908013 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 23. -/
theorem gammaAnalyticBridge23_logs :
    Real.log (2638360 / 37 : ℝ) ≤ 27937 / 2500 ∧ Real.log (131918 : ℝ) ≤ 1179 / 100 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2638360 / 37) 17 20 0 (27937 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 131918 18 20 0 (1179 / 100) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge23_main (hRH : RiemannHypothesis) :
    (5577 / 25 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 131918,
        Real.exp (-(n : ℝ) / (2638360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2638360 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 22533) * ((2638360 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2638360 / 37) * (37 / 20)) + 1) / (500 / 22533) +
        1839 / 1000 ≤
      3059067 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge23_roots.2.2]
  have hs :
    Real.sqrt ((2638360 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2638360 / 37) * (37 / 20)) +
        21 / 20 ≤
      40893 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge23_roots.2.2, gammaAnalyticBridge23_logs.2]
  have hz :
    Real.sqrt (2638360 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2638360 / 37) + 2469 / 800 ≤
      31851 / 1000 := by
    linarith only [gammaAnalyticBridge23_roots.2.1, gammaAnalyticBridge23_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2638360 / 37) (y := 37 / 20) (h := 500 / 22533) (r :=
      1335169 / 5000) (e := 78619 / 500000) (p := 3059067 / 1000) (s := 40893 / 1000) (z :=
      31851 / 1000) (F := 5577 / 25) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge23_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2638360 / 37 : ℝ) * (37 / 20) = 131918 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge23_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2638360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2638360 / 37 : ℝ)) ≤
      133577 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2670337 / 10000) (T := 1335169 / 5000) (Z :=
      27937 / 2500) (by norm_num only) (by norm_num only) gammaAnalyticBridge23_roots.1
      gammaAnalyticBridge23_roots.2.1 gammaAnalyticBridge23_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge23_power : (2638360 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 187 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 23 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge23_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (131918 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 131918) (x := 2638360 / 37) (H := 16703 / 25) (R :=
      2670337 / 10000) (W := 187 / 100000) (F := 5577 / 25) (U := 133577 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge23_power (gammaAnalyticBridge23_main hGRH.riemann)
      (gammaAnalyticBridge23_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 24. -/
theorem gammaAnalyticBridge24_roots :
    ((2690473 / 10000 : ℝ) ≤ Real.sqrt (2678300 / 37 : ℝ) ∧
      Real.sqrt (2678300 / 37 : ℝ) ≤ 1345237 / 5000 ∧ Real.sqrt (133915 : ℝ) ≤ 45743 / 125) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 24. -/
theorem gammaAnalyticBridge24_logs :
    Real.log (2678300 / 37 : ℝ) ≤ 55949 / 5000 ∧ Real.log (133915 : ℝ) ≤ 2361 / 200 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2678300 / 37) 17 20 0 (55949 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 133915 18 20 0 (2361 / 200) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge24_main (hRH : RiemannHypothesis) :
    (224771 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 133915,
        Real.exp (-(n : ℝ) / (2678300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2678300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 180943) * ((2678300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2678300 / 37) * (37 / 20)) + 1) / (4000 / 180943) +
        1839 / 1000 ≤
      3093681 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge24_roots.2.2]
  have hs :
    Real.sqrt ((2678300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2678300 / 37) * (37 / 20)) +
        21 / 20 ≤
      41057 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge24_roots.2.2, gammaAnalyticBridge24_logs.2]
  have hz :
    Real.sqrt (2678300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2678300 / 37) + 2469 / 800 ≤
      31973 / 1000 := by
    linarith only [gammaAnalyticBridge24_roots.2.1, gammaAnalyticBridge24_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2678300 / 37) (y := 37 / 20) (h := 4000 / 180943) (r :=
      1345237 / 5000) (e := 78619 / 500000) (p := 3093681 / 1000) (s := 41057 / 1000) (z :=
      31973 / 1000) (F := 224771 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge24_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2678300 / 37 : ℝ) * (37 / 20) = 133915 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge24_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2678300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2678300 / 37 : ℝ)) ≤
      269167 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2690473 / 10000) (T := 1345237 / 5000) (Z :=
      55949 / 5000) (by norm_num only) (by norm_num only) gammaAnalyticBridge24_roots.1
      gammaAnalyticBridge24_roots.2.1 gammaAnalyticBridge24_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge24_power : (2678300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 37 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 24 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge24_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (133915 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 133915) (x := 2678300 / 37) (H := 16828 / 25) (R :=
      2690473 / 10000) (W := 37 / 20000) (F := 224771 / 1000) (U := 269167 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge24_power (gammaAnalyticBridge24_main hGRH.riemann)
      (gammaAnalyticBridge24_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 25. -/
theorem gammaAnalyticBridge25_roots :
    ((2710609 / 10000 : ℝ) ≤ Real.sqrt (2718540 / 37 : ℝ) ∧
      Real.sqrt (2718540 / 37 : ℝ) ≤ 271061 / 1000 ∧ Real.sqrt (135927 : ℝ) ≤ 921707 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 25. -/
theorem gammaAnalyticBridge25_logs :
    Real.log (2718540 / 37 : ℝ) ≤ 112047 / 10000 ∧ Real.log (135927 : ℝ) ≤ 118199 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2718540 / 37) 17 20 0 (112047 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 135927 18 20 0 (118199 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge25_main (hRH : RiemannHypothesis) :
    (113231 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 135927,
        Real.exp (-(n : ℝ) / (2718540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2718540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 36323) * ((2718540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2718540 / 37) * (37 / 20)) + 1) / (800 / 36323) +
        1839 / 1000 ≤
      125137 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge25_roots.2.2]
  have hs :
    Real.sqrt ((2718540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2718540 / 37) * (37 / 20)) +
        21 / 20 ≤
      41221 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge25_roots.2.2, gammaAnalyticBridge25_logs.2]
  have hz :
    Real.sqrt (2718540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2718540 / 37) + 2469 / 800 ≤
      16047 / 500 := by
    linarith only [gammaAnalyticBridge25_roots.2.1, gammaAnalyticBridge25_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2718540 / 37) (y := 37 / 20) (h := 800 / 36323) (r :=
      271061 / 1000) (e := 78619 / 500000) (p := 125137 / 40) (s := 41221 / 1000) (z := 16047 / 500)
      (F := 113231 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge25_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2718540 / 37 : ℝ) * (37 / 20) = 135927 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge25_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2718540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2718540 / 37 : ℝ)) ≤
      13559 / 50 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2710609 / 10000) (T := 271061 / 1000) (Z :=
      112047 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge25_roots.1
      gammaAnalyticBridge25_roots.2.1 gammaAnalyticBridge25_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge25_power : (2718540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 23 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 25 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge25_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (16953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (135927 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 135927) (x := 2718540 / 37) (H := 16953 / 25) (R :=
      2710609 / 10000) (W := 23 / 12500) (F := 113231 / 500) (U := 13559 / 50) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge25_power (gammaAnalyticBridge25_main hGRH.riemann)
      (gammaAnalyticBridge25_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 26. -/
theorem gammaAnalyticBridge26_roots :
    ((546149 / 2000 : ℝ) ≤ Real.sqrt (2759080 / 37 : ℝ) ∧
      Real.sqrt (2759080 / 37 : ℝ) ≤ 1365373 / 5000 ∧ Real.sqrt (137954 : ℝ) ≤ 464277 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 26. -/
theorem gammaAnalyticBridge26_logs :
    Real.log (2759080 / 37 : ℝ) ≤ 22439 / 2000 ∧ Real.log (137954 : ℝ) ≤ 118347 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2759080 / 37) 17 20 0 (22439 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 137954 18 20 0 (118347 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge26_main (hRH : RiemannHypothesis) :
    (228153 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 137954,
        Real.exp (-(n : ℝ) / (2759080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2759080 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 182287) * ((2759080 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2759080 / 37) * (37 / 20)) + 1) / (4000 / 182287) +
        1839 / 1000 ≤
      3163297 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge26_roots.2.2]
  have hs :
    Real.sqrt ((2759080 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2759080 / 37) * (37 / 20)) +
        21 / 20 ≤
      20693 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge26_roots.2.2, gammaAnalyticBridge26_logs.2]
  have hz :
    Real.sqrt (2759080 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2759080 / 37) + 2469 / 800 ≤
      6443 / 200 := by
    linarith only [gammaAnalyticBridge26_roots.2.1, gammaAnalyticBridge26_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2759080 / 37) (y := 37 / 20) (h := 4000 / 182287) (r :=
      1365373 / 5000) (e := 78619 / 500000) (p := 3163297 / 1000) (s := 20693 / 500) (z :=
      6443 / 200) (F := 228153 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge26_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2759080 / 37 : ℝ) * (37 / 20) = 137954 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge26_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2759080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2759080 / 37 : ℝ)) ≤
      273193 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 546149 / 2000) (T := 1365373 / 5000) (Z := 22439 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge26_roots.1
      gammaAnalyticBridge26_roots.2.1 gammaAnalyticBridge26_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge26_power : (2759080 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 91 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 26 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge26_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (16953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (137954 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 16953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 137954) (x := 2759080 / 37) (H := 17078 / 25) (R :=
      546149 / 2000) (W := 91 / 50000) (F := 228153 / 1000) (U := 273193 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge26_power (gammaAnalyticBridge26_main hGRH.riemann)
      (gammaAnalyticBridge26_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 27. -/
theorem gammaAnalyticBridge27_roots :
    ((343859 / 1250 : ℝ) ≤ Real.sqrt (2799900 / 37 : ℝ) ∧
      Real.sqrt (2799900 / 37 : ℝ) ≤ 2750873 / 10000 ∧
      Real.sqrt (139995 : ℝ) ≤ 3741591 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 27. -/
theorem gammaAnalyticBridge27_logs :
    Real.log (2799900 / 37 : ℝ) ≤ 56171 / 5000 ∧ Real.log (139995 : ℝ) ≤ 59247 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2799900 / 37) 17 20 0 (56171 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 139995 18 20 0 (59247 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge27_main (hRH : RiemannHypothesis) :
    (229843 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 139995,
        Real.exp (-(n : ℝ) / (2799900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2799900 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 182959) * ((2799900 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2799900 / 37) * (37 / 20)) + 1) / (4000 / 182959) +
        1839 / 1000 ≤
      3198281 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge27_roots.2.2]
  have hs :
    Real.sqrt ((2799900 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2799900 / 37) * (37 / 20)) +
        21 / 20 ≤
      831 / 20 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge27_roots.2.2, gammaAnalyticBridge27_logs.2]
  have hz :
    Real.sqrt (2799900 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2799900 / 37) + 2469 / 800 ≤
      4042 / 125 := by
    linarith only [gammaAnalyticBridge27_roots.2.1, gammaAnalyticBridge27_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2799900 / 37) (y := 37 / 20) (h := 4000 / 182959) (r :=
      2750873 / 10000) (e := 78619 / 500000) (p := 3198281 / 1000) (s := 831 / 20) (z := 4042 / 125)
      (F := 229843 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge27_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2799900 / 37 : ℝ) * (37 / 20) = 139995 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge27_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2799900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2799900 / 37 : ℝ)) ≤
      55041 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 343859 / 1250) (T := 2750873 / 10000) (Z := 56171 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge27_roots.1
      gammaAnalyticBridge27_roots.2.1 gammaAnalyticBridge27_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge27_power : (2799900 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 181 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 27 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge27_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (139995 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 139995) (x := 2799900 / 37) (H := 17203 / 25) (R :=
      343859 / 1250) (W := 181 / 100000) (F := 229843 / 1000) (U := 55041 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge27_power (gammaAnalyticBridge27_main hGRH.riemann)
      (gammaAnalyticBridge27_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 28. -/
theorem gammaAnalyticBridge28_roots :
    ((173188 / 625 : ℝ) ≤ Real.sqrt (2841040 / 37 : ℝ) ∧
      Real.sqrt (2841040 / 37 : ℝ) ≤ 2771009 / 10000 ∧
      Real.sqrt (142052 : ℝ) ≤ 3768979 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 28. -/
theorem gammaAnalyticBridge28_logs :
    Real.log (2841040 / 37 : ℝ) ≤ 14061 / 1250 ∧ Real.log (142052 : ℝ) ≤ 1483 / 125 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2841040 / 37) 17 20 0 (14061 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 142052 18 20 0 (1483 / 125) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge28_main (hRH : RiemannHypothesis) :
    (115767 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 142052,
        Real.exp (-(n : ℝ) / (2841040 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2841040 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 183631) * ((2841040 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2841040 / 37) * (37 / 20)) + 1) / (4000 / 183631) +
        1839 / 1000 ≤
      323341 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge28_roots.2.2]
  have hs :
    Real.sqrt ((2841040 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2841040 / 37) * (37 / 20)) +
        21 / 20 ≤
      41713 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge28_roots.2.2, gammaAnalyticBridge28_logs.2]
  have hz :
    Real.sqrt (2841040 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2841040 / 37) + 2469 / 800 ≤
      32457 / 1000 := by
    linarith only [gammaAnalyticBridge28_roots.2.1, gammaAnalyticBridge28_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2841040 / 37) (y := 37 / 20) (h := 4000 / 183631) (r :=
      2771009 / 10000) (e := 78619 / 500000) (p := 323341 / 100) (s := 41713 / 1000) (z :=
      32457 / 1000) (F := 115767 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge28_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2841040 / 37 : ℝ) * (37 / 20) = 142052 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge28_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2841040 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2841040 / 37 : ℝ)) ≤
      277219 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 173188 / 625) (T := 2771009 / 10000) (Z := 14061 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge28_roots.1
      gammaAnalyticBridge28_roots.2.1 gammaAnalyticBridge28_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge28_power : (2841040 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 179 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 28 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge28_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (142052 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 142052) (x := 2841040 / 37) (H := 17328 / 25) (R :=
      173188 / 625) (W := 179 / 100000) (F := 115767 / 500) (U := 277219 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge28_power (gammaAnalyticBridge28_main hGRH.riemann)
      (gammaAnalyticBridge28_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 29. -/
theorem gammaAnalyticBridge29_roots :
    ((348893 / 1250 : ℝ) ≤ Real.sqrt (2882480 / 37 : ℝ) ∧
      Real.sqrt (2882480 / 37 : ℝ) ≤ 558229 / 2000 ∧ Real.sqrt (144124 : ℝ) ≤ 3796367 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 29. -/
theorem gammaAnalyticBridge29_logs :
    Real.log (2882480 / 37 : ℝ) ≤ 112633 / 10000 ∧ Real.log (144124 : ℝ) ≤ 23757 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2882480 / 37) 17 20 0 (112633 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 144124 18 20 0 (23757 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge29_main (hRH : RiemannHypothesis) :
    (9329 / 40 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 144124,
        Real.exp (-(n : ℝ) / (2882480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2882480 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 23037) * ((2882480 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2882480 / 37) * (37 / 20)) + 1) / (500 / 23037) +
        1839 / 1000 ≤
      817167 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge29_roots.2.2]
  have hs :
    Real.sqrt ((2882480 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2882480 / 37) * (37 / 20)) +
        21 / 20 ≤
      41877 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge29_roots.2.2, gammaAnalyticBridge29_logs.2]
  have hz :
    Real.sqrt (2882480 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2882480 / 37) + 2469 / 800 ≤
      32577 / 1000 := by
    linarith only [gammaAnalyticBridge29_roots.2.1, gammaAnalyticBridge29_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2882480 / 37) (y := 37 / 20) (h := 500 / 23037) (r :=
      558229 / 2000) (e := 78619 / 500000) (p := 817167 / 250) (s := 41877 / 1000) (z :=
      32577 / 1000) (F := 9329 / 40) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge29_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2882480 / 37 : ℝ) * (37 / 20) = 144124 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge29_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2882480 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2882480 / 37 : ℝ)) ≤
      34904 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 348893 / 1250) (T := 558229 / 2000) (Z := 112633 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge29_roots.1
      gammaAnalyticBridge29_roots.2.1 gammaAnalyticBridge29_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge29_power : (2882480 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 89 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 29 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge29_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (144124 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 144124) (x := 2882480 / 37) (H := 17453 / 25) (R :=
      348893 / 1250) (W := 89 / 50000) (F := 9329 / 40) (U := 34904 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge29_power (gammaAnalyticBridge29_main hGRH.riemann)
      (gammaAnalyticBridge29_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 30. -/
theorem gammaAnalyticBridge30_roots :
    ((35141 / 125 : ℝ) ≤ Real.sqrt (2924220 / 37 : ℝ) ∧
      Real.sqrt (2924220 / 37 : ℝ) ≤ 2811281 / 10000 ∧ Real.sqrt (146211 : ℝ) ≤ 764751 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 30. -/
theorem gammaAnalyticBridge30_logs :
    Real.log (2924220 / 37 : ℝ) ≤ 112777 / 10000 ∧ Real.log (146211 : ℝ) ≤ 118929 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2924220 / 37) 17 20 0 (112777 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 146211 18 20 0 (118929 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge30_main (hRH : RiemannHypothesis) :
    (58729 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 146211,
        Real.exp (-(n : ℝ) / (2924220 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2924220 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 92477) * ((2924220 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2924220 / 37) * (37 / 20)) + 1) / (2000 / 92477) +
        1839 / 1000 ≤
      3304053 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge30_roots.2.2]
  have hs :
    Real.sqrt ((2924220 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2924220 / 37) * (37 / 20)) +
        21 / 20 ≤
      1051 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge30_roots.2.2, gammaAnalyticBridge30_logs.2]
  have hz :
    Real.sqrt (2924220 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2924220 / 37) + 2469 / 800 ≤
      16349 / 500 := by
    linarith only [gammaAnalyticBridge30_roots.2.1, gammaAnalyticBridge30_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2924220 / 37) (y := 37 / 20) (h := 2000 / 92477) (r :=
      2811281 / 10000) (e := 78619 / 500000) (p := 3304053 / 1000) (s := 1051 / 25) (z :=
      16349 / 500) (F := 58729 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge30_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2924220 / 37 : ℝ) * (37 / 20) = 146211 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge30_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2924220 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2924220 / 37 : ℝ)) ≤
      56249 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 35141 / 125) (T := 2811281 / 10000) (Z := 112777 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge30_roots.1
      gammaAnalyticBridge30_roots.2.1 gammaAnalyticBridge30_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge30_power : (2924220 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 11 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 30 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge30_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (146211 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 146211) (x := 2924220 / 37) (H := 17578 / 25) (R :=
      35141 / 125) (W := 11 / 6250) (F := 58729 / 250) (U := 56249 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge30_power (gammaAnalyticBridge30_main hGRH.riemann)
      (gammaAnalyticBridge30_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 31. -/
theorem gammaAnalyticBridge31_roots :
    ((353927 / 1250 : ℝ) ≤ Real.sqrt (2966260 / 37 : ℝ) ∧
      Real.sqrt (2966260 / 37 : ℝ) ≤ 2831417 / 10000 ∧
      Real.sqrt (148313 : ℝ) ≤ 3851143 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 31. -/
theorem gammaAnalyticBridge31_logs :
    Real.log (2966260 / 37 : ℝ) ≤ 112919 / 10000 ∧ Real.log (148313 : ℝ) ≤ 119071 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (2966260 / 37) 17 20 0 (112919 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 148313 18 20 0 (119071 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge31_main (hRH : RiemannHypothesis) :
    (236607 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 148313,
        Real.exp (-(n : ℝ) / (2966260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2966260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 185619) * ((2966260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((2966260 / 37) * (37 / 20)) + 1) / (4000 / 185619) +
        1839 / 1000 ≤
      834891 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge31_roots.2.2]
  have hs :
    Real.sqrt ((2966260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((2966260 / 37) * (37 / 20)) +
        21 / 20 ≤
      42203 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge31_roots.2.2, gammaAnalyticBridge31_logs.2]
  have hz :
    Real.sqrt (2966260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (2966260 / 37) + 2469 / 800 ≤
      16409 / 500 := by
    linarith only [gammaAnalyticBridge31_roots.2.1, gammaAnalyticBridge31_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 2966260 / 37) (y := 37 / 20) (h := 4000 / 185619) (r :=
      2831417 / 10000) (e := 78619 / 500000) (p := 834891 / 250) (s := 42203 / 1000) (z :=
      16409 / 500) (F := 236607 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge31_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (2966260 / 37 : ℝ) * (37 / 20) = 148313 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge31_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (2966260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (2966260 / 37 : ℝ)) ≤
      141629 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 353927 / 1250) (T := 2831417 / 10000) (Z :=
      112919 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge31_roots.1
      gammaAnalyticBridge31_roots.2.1 gammaAnalyticBridge31_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge31_power : (2966260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 7 / 4000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 31 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge31_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (148313 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 148313) (x := 2966260 / 37) (H := 17703 / 25) (R :=
      353927 / 1250) (W := 7 / 4000) (F := 236607 / 1000) (U := 141629 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge31_power (gammaAnalyticBridge31_main hGRH.riemann)
      (gammaAnalyticBridge31_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 32. -/
theorem gammaAnalyticBridge32_roots :
    ((178222 / 625 : ℝ) ≤ Real.sqrt (3008600 / 37 : ℝ) ∧
      Real.sqrt (3008600 / 37 : ℝ) ≤ 2851553 / 10000 ∧
      Real.sqrt (150430 : ℝ) ≤ 3878531 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 32. -/
theorem gammaAnalyticBridge32_logs :
    Real.log (3008600 / 37 : ℝ) ≤ 113061 / 10000 ∧ Real.log (150430 : ℝ) ≤ 119213 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3008600 / 37) 17 20 0 (113061 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 150430 18 20 0 (119213 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge32_main (hRH : RiemannHypothesis) :
    (119149 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 150430,
        Real.exp (-(n : ℝ) / (3008600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3008600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 186277) * ((3008600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3008600 / 37) * (37 / 20)) + 1) / (4000 / 186277) +
        1839 / 1000 ≤
      1687601 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge32_roots.2.2]
  have hs :
    Real.sqrt ((3008600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3008600 / 37) * (37 / 20)) +
        21 / 20 ≤
      21183 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge32_roots.2.2, gammaAnalyticBridge32_logs.2]
  have hz :
    Real.sqrt (3008600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3008600 / 37) + 2469 / 800 ≤
      16469 / 500 := by
    linarith only [gammaAnalyticBridge32_roots.2.1, gammaAnalyticBridge32_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3008600 / 37) (y := 37 / 20) (h := 4000 / 186277) (r :=
      2851553 / 10000) (e := 78619 / 500000) (p := 1687601 / 500) (s := 21183 / 500) (z :=
      16469 / 500) (F := 119149 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge32_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3008600 / 37 : ℝ) * (37 / 20) = 150430 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge32_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3008600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3008600 / 37 : ℝ)) ≤
      285271 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 178222 / 625) (T := 2851553 / 10000) (Z :=
      113061 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge32_roots.1
      gammaAnalyticBridge32_roots.2.1 gammaAnalyticBridge32_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge32_power : (3008600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 173 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 32 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge32_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (150430 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 150430) (x := 3008600 / 37) (H := 17828 / 25) (R :=
      178222 / 625) (W := 173 / 100000) (F := 119149 / 500) (U := 285271 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge32_power (gammaAnalyticBridge32_main hGRH.riemann)
      (gammaAnalyticBridge32_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 33. -/
theorem gammaAnalyticBridge33_roots :
    ((358961 / 1250 : ℝ) ≤ Real.sqrt (3051240 / 37 : ℝ) ∧
      Real.sqrt (3051240 / 37 : ℝ) ≤ 2871689 / 10000 ∧
      Real.sqrt (152562 : ℝ) ≤ 3905919 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 33. -/
theorem gammaAnalyticBridge33_logs :
    Real.log (3051240 / 37 : ℝ) ≤ 56601 / 5000 ∧ Real.log (152562 : ℝ) ≤ 59677 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3051240 / 37) 17 20 0 (56601 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 152562 18 20 0 (59677 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge33_main (hRH : RiemannHypothesis) :
    (239989 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 152562,
        Real.exp (-(n : ℝ) / (3051240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3051240 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 37387) * ((3051240 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3051240 / 37) * (37 / 20)) + 1) / (800 / 37387) +
        1839 / 1000 ≤
      682193 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge33_roots.2.2]
  have hs :
    Real.sqrt ((3051240 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3051240 / 37) * (37 / 20)) +
        21 / 20 ≤
      42529 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge33_roots.2.2, gammaAnalyticBridge33_logs.2]
  have hz :
    Real.sqrt (3051240 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3051240 / 37) + 2469 / 800 ≤
      33059 / 1000 := by
    linarith only [gammaAnalyticBridge33_roots.2.1, gammaAnalyticBridge33_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3051240 / 37) (y := 37 / 20) (h := 800 / 37387) (r :=
      2871689 / 10000) (e := 78619 / 500000) (p := 682193 / 200) (s := 42529 / 1000) (z :=
      33059 / 1000) (F := 239989 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge33_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3051240 / 37 : ℝ) * (37 / 20) = 152562 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge33_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3051240 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3051240 / 37 : ℝ)) ≤
      57457 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 358961 / 1250) (T := 2871689 / 10000) (Z := 56601 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge33_roots.1
      gammaAnalyticBridge33_roots.2.1 gammaAnalyticBridge33_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge33_power : (3051240 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 43 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 33 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge33_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (17953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (152562 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 152562) (x := 3051240 / 37) (H := 17953 / 25) (R :=
      358961 / 1250) (W := 43 / 25000) (F := 239989 / 1000) (U := 57457 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge33_power (gammaAnalyticBridge33_main hGRH.riemann)
      (gammaAnalyticBridge33_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 34. -/
theorem gammaAnalyticBridge34_roots :
    ((578363 / 2000 : ℝ) ≤ Real.sqrt (3094160 / 37 : ℝ) ∧
      Real.sqrt (3094160 / 37 : ℝ) ≤ 361477 / 1250 ∧ Real.sqrt (154708 : ℝ) ≤ 1966647 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 34. -/
theorem gammaAnalyticBridge34_logs :
    Real.log (3094160 / 37 : ℝ) ≤ 56671 / 5000 ∧ Real.log (154708 : ℝ) ≤ 119493 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3094160 / 37) 17 20 0 (56671 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 154708 18 20 0 (119493 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge34_main (hRH : RiemannHypothesis) :
    (241679 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 154708,
        Real.exp (-(n : ℝ) / (3094160 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3094160 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 93793) * ((3094160 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3094160 / 37) * (37 / 20)) + 1) / (2000 / 93793) +
        1839 / 1000 ≤
      1723419 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge34_roots.2.2]
  have hs :
    Real.sqrt ((3094160 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3094160 / 37) * (37 / 20)) +
        21 / 20 ≤
      10673 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge34_roots.2.2, gammaAnalyticBridge34_logs.2]
  have hz :
    Real.sqrt (3094160 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3094160 / 37) + 2469 / 800 ≤
      33179 / 1000 := by
    linarith only [gammaAnalyticBridge34_roots.2.1, gammaAnalyticBridge34_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3094160 / 37) (y := 37 / 20) (h := 2000 / 93793) (r :=
      361477 / 1250) (e := 78619 / 500000) (p := 1723419 / 500) (s := 10673 / 250) (z :=
      33179 / 1000) (F := 241679 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge34_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3094160 / 37 : ℝ) * (37 / 20) = 154708 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge34_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3094160 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3094160 / 37 : ℝ)) ≤
      289297 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 578363 / 2000) (T := 361477 / 1250) (Z := 56671 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge34_roots.1
      gammaAnalyticBridge34_roots.2.1 gammaAnalyticBridge34_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge34_power : (3094160 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 171 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 34 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge34_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (17953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (154708 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 17953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 154708) (x := 3094160 / 37) (H := 18078 / 25) (R :=
      578363 / 2000) (W := 171 / 100000) (F := 241679 / 1000) (U := 289297 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge34_power (gammaAnalyticBridge34_main hGRH.riemann)
      (gammaAnalyticBridge34_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 35. -/
theorem gammaAnalyticBridge35_roots :
    ((2911951 / 10000 : ℝ) ≤ Real.sqrt (3137400 / 37 : ℝ) ∧
      Real.sqrt (3137400 / 37 : ℝ) ≤ 181997 / 625 ∧ Real.sqrt (156870 : ℝ) ≤ 1980341 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 35. -/
theorem gammaAnalyticBridge35_logs :
    Real.log (3137400 / 37 : ℝ) ≤ 2837 / 250 ∧ Real.log (156870 : ℝ) ≤ 7477 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3137400 / 37) 17 20 0 (2837 / 250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 156870 18 20 0 (7477 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge35_main (hRH : RiemannHypothesis) :
    (24337 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 156870,
        Real.exp (-(n : ℝ) / (3137400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3137400 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 188237) * ((3137400 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3137400 / 37) * (37 / 20)) + 1) / (4000 / 188237) +
        1839 / 1000 ≤
      870713 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge35_roots.2.2]
  have hs :
    Real.sqrt ((3137400 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3137400 / 37) * (37 / 20)) +
        21 / 20 ≤
      21427 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge35_roots.2.2, gammaAnalyticBridge35_logs.2]
  have hz :
    Real.sqrt (3137400 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3137400 / 37) + 2469 / 800 ≤
      16649 / 500 := by
    linarith only [gammaAnalyticBridge35_roots.2.1, gammaAnalyticBridge35_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3137400 / 37) (y := 37 / 20) (h := 4000 / 188237) (r :=
      181997 / 625) (e := 78619 / 500000) (p := 870713 / 250) (s := 21427 / 500) (z := 16649 / 500)
      (F := 24337 / 100) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge35_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3137400 / 37 : ℝ) * (37 / 20) = 156870 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge35_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3137400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3137400 / 37 : ℝ)) ≤
      29131 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2911951 / 10000) (T := 181997 / 625) (Z := 2837 / 250)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge35_roots.1
      gammaAnalyticBridge35_roots.2.1 gammaAnalyticBridge35_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge35_power : (3137400 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 169 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 35 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge35_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (156870 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 156870) (x := 3137400 / 37) (H := 18203 / 25) (R :=
      2911951 / 10000) (W := 169 / 100000) (F := 24337 / 100) (U := 29131 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge35_power (gammaAnalyticBridge35_main hGRH.riemann)
      (gammaAnalyticBridge35_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 36. -/
theorem gammaAnalyticBridge36_roots :
    ((2932087 / 10000 : ℝ) ≤ Real.sqrt (3180940 / 37 : ℝ) ∧
      Real.sqrt (3180940 / 37 : ℝ) ≤ 366511 / 1250 ∧ Real.sqrt (159047 : ℝ) ≤ 398807 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 36. -/
theorem gammaAnalyticBridge36_logs :
    Real.log (3180940 / 37 : ℝ) ≤ 56809 / 5000 ∧ Real.log (159047 : ℝ) ≤ 11977 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3180940 / 37) 17 20 0 (56809 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 159047 18 20 0 (11977 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge36_main (hRH : RiemannHypothesis) :
    (245061 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 159047,
        Real.exp (-(n : ℝ) / (3180940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3180940 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 23611) * ((3180940 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3180940 / 37) * (37 / 20)) + 1) / (500 / 23611) +
        1839 / 1000 ≤
      3518991 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge36_roots.2.2]
  have hs :
    Real.sqrt ((3180940 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3180940 / 37) * (37 / 20)) +
        21 / 20 ≤
      43017 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge36_roots.2.2, gammaAnalyticBridge36_logs.2]
  have hz :
    Real.sqrt (3180940 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3180940 / 37) + 2469 / 800 ≤
      16709 / 500 := by
    linarith only [gammaAnalyticBridge36_roots.2.1, gammaAnalyticBridge36_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3180940 / 37) (y := 37 / 20) (h := 500 / 23611) (r :=
      366511 / 1250) (e := 78619 / 500000) (p := 3518991 / 1000) (s := 43017 / 1000) (z :=
      16709 / 500) (F := 245061 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge36_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3180940 / 37 : ℝ) * (37 / 20) = 159047 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge36_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3180940 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3180940 / 37 : ℝ)) ≤
      293323 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2932087 / 10000) (T := 366511 / 1250) (Z := 56809 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge36_roots.1
      gammaAnalyticBridge36_roots.2.1 gammaAnalyticBridge36_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge36_power : (3180940 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 21 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 36 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge36_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (159047 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 159047) (x := 3180940 / 37) (H := 18328 / 25) (R :=
      2932087 / 10000) (W := 21 / 12500) (F := 245061 / 1000) (U := 293323 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge36_power (gammaAnalyticBridge36_main hGRH.riemann)
      (gammaAnalyticBridge36_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 37. -/
theorem gammaAnalyticBridge37_roots :
    ((2952223 / 10000 : ℝ) ≤ Real.sqrt (3224780 / 37 : ℝ) ∧
      Real.sqrt (3224780 / 37 : ℝ) ≤ 184514 / 625 ∧ Real.sqrt (161239 : ℝ) ≤ 2007729 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 37. -/
theorem gammaAnalyticBridge37_logs :
    Real.log (3224780 / 37 : ℝ) ≤ 22751 / 2000 ∧ Real.log (161239 : ℝ) ≤ 119907 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3224780 / 37) 17 20 0 (22751 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 161239 18 20 0 (119907 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge37_main (hRH : RiemannHypothesis) :
    (30844 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 161239,
        Real.exp (-(n : ℝ) / (3224780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3224780 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 189539) * ((3224780 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3224780 / 37) * (37 / 20)) + 1) / (4000 / 189539) +
        1839 / 1000 ≤
      3555253 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge37_roots.2.2]
  have hs :
    Real.sqrt ((3224780 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3224780 / 37) * (37 / 20)) +
        21 / 20 ≤
      43179 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge37_roots.2.2, gammaAnalyticBridge37_logs.2]
  have hz :
    Real.sqrt (3224780 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3224780 / 37) + 2469 / 800 ≤
      16769 / 500 := by
    linarith only [gammaAnalyticBridge37_roots.2.1, gammaAnalyticBridge37_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3224780 / 37) (y := 37 / 20) (h := 4000 / 189539) (r :=
      184514 / 625) (e := 78619 / 500000) (p := 3555253 / 1000) (s := 43179 / 1000) (z :=
      16769 / 500) (F := 30844 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge37_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3224780 / 37 : ℝ) * (37 / 20) = 161239 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge37_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3224780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3224780 / 37 : ℝ)) ≤
      36917 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2952223 / 10000) (T := 184514 / 625) (Z := 22751 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge37_roots.1
      gammaAnalyticBridge37_roots.2.1 gammaAnalyticBridge37_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge37_power : (3224780 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 167 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 37 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge37_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (161239 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 161239) (x := 3224780 / 37) (H := 18453 / 25) (R :=
      2952223 / 10000) (W := 167 / 100000) (F := 30844 / 125) (U := 36917 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge37_power (gammaAnalyticBridge37_main hGRH.riemann)
      (gammaAnalyticBridge37_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 38. -/
theorem gammaAnalyticBridge38_roots :
    ((2972359 / 10000 : ℝ) ≤ Real.sqrt (3268920 / 37 : ℝ) ∧
      Real.sqrt (3268920 / 37 : ℝ) ≤ 74309 / 250 ∧ Real.sqrt (163446 : ℝ) ≤ 2021423 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 38. -/
theorem gammaAnalyticBridge38_logs :
    Real.log (3268920 / 37 : ℝ) ≤ 113891 / 10000 ∧ Real.log (163446 : ℝ) ≤ 120043 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3268920 / 37) 17 20 0 (113891 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 163446 18 20 0 (120043 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge38_main (hRH : RiemannHypothesis) :
    (248443 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 163446,
        Real.exp (-(n : ℝ) / (3268920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3268920 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 190183) * ((3268920 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3268920 / 37) * (37 / 20)) + 1) / (4000 / 190183) +
        1839 / 1000 ≤
      89791 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge38_roots.2.2]
  have hs :
    Real.sqrt ((3268920 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3268920 / 37) * (37 / 20)) +
        21 / 20 ≤
      43341 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge38_roots.2.2, gammaAnalyticBridge38_logs.2]
  have hz :
    Real.sqrt (3268920 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3268920 / 37) + 2469 / 800 ≤
      33657 / 1000 := by
    linarith only [gammaAnalyticBridge38_roots.2.1, gammaAnalyticBridge38_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3268920 / 37) (y := 37 / 20) (h := 4000 / 190183) (r :=
      74309 / 250) (e := 78619 / 500000) (p := 89791 / 25) (s := 43341 / 1000) (z := 33657 / 1000)
      (F := 248443 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge38_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3268920 / 37 : ℝ) * (37 / 20) = 163446 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge38_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3268920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3268920 / 37 : ℝ)) ≤
      5947 / 20 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 2972359 / 10000) (T := 74309 / 250) (Z := 113891 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge38_roots.1
      gammaAnalyticBridge38_roots.2.1 gammaAnalyticBridge38_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge38_power : (3268920 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 83 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 38 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge38_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (163446 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 163446) (x := 3268920 / 37) (H := 18578 / 25) (R :=
      2972359 / 10000) (W := 83 / 50000) (F := 248443 / 1000) (U := 5947 / 20) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge38_power (gammaAnalyticBridge38_main hGRH.riemann)
      (gammaAnalyticBridge38_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 39. -/
theorem gammaAnalyticBridge39_roots :
    ((598499 / 2000 : ℝ) ≤ Real.sqrt (3313360 / 37 : ℝ) ∧
      Real.sqrt (3313360 / 37 : ℝ) ≤ 187031 / 625 ∧ Real.sqrt (165668 : ℝ) ≤ 2035117 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 39. -/
theorem gammaAnalyticBridge39_logs :
    Real.log (3313360 / 37 : ℝ) ≤ 57013 / 5000 ∧ Real.log (165668 : ℝ) ≤ 60089 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3313360 / 37) 17 20 0 (57013 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 165668 18 20 0 (60089 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge39_main (hRH : RiemannHypothesis) :
    (125067 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 165668,
        Real.exp (-(n : ℝ) / (3313360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3313360 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 190827) * ((3313360 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3313360 / 37) * (37 / 20)) + 1) / (4000 / 190827) +
        1839 / 1000 ≤
      72563 / 20 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge39_roots.2.2]
  have hs :
    Real.sqrt ((3313360 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3313360 / 37) * (37 / 20)) +
        21 / 20 ≤
      21751 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge39_roots.2.2, gammaAnalyticBridge39_logs.2]
  have hz :
    Real.sqrt (3313360 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3313360 / 37) + 2469 / 800 ≤
      4222 / 125 := by
    linarith only [gammaAnalyticBridge39_roots.2.1, gammaAnalyticBridge39_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3313360 / 37) (y := 37 / 20) (h := 4000 / 190827) (r :=
      187031 / 625) (e := 78619 / 500000) (p := 72563 / 20) (s := 21751 / 500) (z := 4222 / 125)
      (F := 125067 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge39_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3313360 / 37 : ℝ) * (37 / 20) = 165668 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge39_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3313360 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3313360 / 37 : ℝ)) ≤
      299363 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 598499 / 2000) (T := 187031 / 625) (Z := 57013 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge39_roots.1
      gammaAnalyticBridge39_roots.2.1 gammaAnalyticBridge39_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge39_power : (3313360 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 41 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 39 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge39_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (165668 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 165668) (x := 3313360 / 37) (H := 18703 / 25) (R :=
      598499 / 2000) (W := 41 / 25000) (F := 125067 / 500) (U := 299363 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge39_power (gammaAnalyticBridge39_main hGRH.riemann)
      (gammaAnalyticBridge39_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 40. -/
theorem gammaAnalyticBridge40_roots :
    ((3012631 / 10000 : ℝ) ≤ Real.sqrt (3358100 / 37 : ℝ) ∧
      Real.sqrt (3358100 / 37 : ℝ) ≤ 376579 / 1250 ∧ Real.sqrt (167905 : ℝ) ≤ 2048811 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 40. -/
theorem gammaAnalyticBridge40_logs :
    Real.log (3358100 / 37 : ℝ) ≤ 1427 / 125 ∧ Real.log (167905 : ℝ) ≤ 15039 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3358100 / 37) 17 20 0 (1427 / 125) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 167905 18 20 0 (15039 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge40_main (hRH : RiemannHypothesis) :
    (10073 / 40 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 167905,
        Real.exp (-(n : ℝ) / (3358100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3358100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 23933) * ((3358100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3358100 / 37) * (37 / 20)) + 1) / (500 / 23933) +
        1839 / 1000 ≤
      458098 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge40_roots.2.2]
  have hs :
    Real.sqrt ((3358100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3358100 / 37) * (37 / 20)) +
        21 / 20 ≤
      5458 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge40_roots.2.2, gammaAnalyticBridge40_logs.2]
  have hz :
    Real.sqrt (3358100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3358100 / 37) + 2469 / 800 ≤
      6779 / 200 := by
    linarith only [gammaAnalyticBridge40_roots.2.1, gammaAnalyticBridge40_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3358100 / 37) (y := 37 / 20) (h := 500 / 23933) (r :=
      376579 / 1250) (e := 78619 / 500000) (p := 458098 / 125) (s := 5458 / 125) (z := 6779 / 200)
      (F := 10073 / 40) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge40_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3358100 / 37 : ℝ) * (37 / 20) = 167905 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge40_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3358100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3358100 / 37 : ℝ)) ≤
      37672 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3012631 / 10000) (T := 376579 / 1250) (Z := 1427 / 125)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge40_roots.1
      gammaAnalyticBridge40_roots.2.1 gammaAnalyticBridge40_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge40_power : (3358100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 163 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 40 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge40_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (167905 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 167905) (x := 3358100 / 37) (H := 18828 / 25) (R :=
      3012631 / 10000) (W := 163 / 100000) (F := 10073 / 40) (U := 37672 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge40_power (gammaAnalyticBridge40_main hGRH.riemann)
      (gammaAnalyticBridge40_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 41. -/
theorem gammaAnalyticBridge41_roots :
    ((1516379 / 5000 : ℝ) ≤ Real.sqrt (3403120 / 37 : ℝ) ∧
      Real.sqrt (3403120 / 37 : ℝ) ≤ 3032759 / 10000 ∧
      Real.sqrt (170156 : ℝ) ≤ 4124997 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 41. -/
theorem gammaAnalyticBridge41_logs :
    Real.log (3403120 / 37 : ℝ) ≤ 114293 / 10000 ∧ Real.log (170156 : ℝ) ≤ 24089 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3403120 / 37) 17 20 0 (114293 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 170156 18 20 0 (24089 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge41_main (hRH : RiemannHypothesis) :
    (50703 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 170156,
        Real.exp (-(n : ℝ) / (3403120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3403120 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 48027) * ((3403120 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3403120 / 37) * (37 / 20)) + 1) / (1000 / 48027) +
        1839 / 1000 ≤
      1850761 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge41_roots.2.2]
  have hs :
    Real.sqrt ((3403120 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3403120 / 37) * (37 / 20)) +
        21 / 20 ≤
      1753 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge41_roots.2.2, gammaAnalyticBridge41_logs.2]
  have hz :
    Real.sqrt (3403120 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3403120 / 37) + 2469 / 800 ≤
      17007 / 500 := by
    linarith only [gammaAnalyticBridge41_roots.2.1, gammaAnalyticBridge41_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3403120 / 37) (y := 37 / 20) (h := 1000 / 48027) (r :=
      3032759 / 10000) (e := 78619 / 500000) (p := 1850761 / 500) (s := 1753 / 40) (z :=
      17007 / 500) (F := 50703 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge41_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3403120 / 37 : ℝ) * (37 / 20) = 170156 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge41_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3403120 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3403120 / 37 : ℝ)) ≤
      303389 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1516379 / 5000) (T := 3032759 / 10000) (Z :=
      114293 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge41_roots.1
      gammaAnalyticBridge41_roots.2.1 gammaAnalyticBridge41_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge41_power : (3403120 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 81 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 41 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge41_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (18953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (170156 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 170156) (x := 3403120 / 37) (H := 18953 / 25) (R :=
      1516379 / 5000) (W := 81 / 50000) (F := 50703 / 200) (U := 303389 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge41_power (gammaAnalyticBridge41_main hGRH.riemann)
      (gammaAnalyticBridge41_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 42. -/
theorem gammaAnalyticBridge42_roots :
    ((1526447 / 5000 : ℝ) ≤ Real.sqrt (3448460 / 37 : ℝ) ∧
      Real.sqrt (3448460 / 37 : ℝ) ≤ 610579 / 2000 ∧ Real.sqrt (172423 : ℝ) ≤ 830477 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 42. -/
theorem gammaAnalyticBridge42_logs :
    Real.log (3448460 / 37 : ℝ) ≤ 57213 / 5000 ∧ Real.log (172423 : ℝ) ≤ 60289 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3448460 / 37) 17 20 0 (57213 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 172423 18 20 0 (60289 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge42_main (hRH : RiemannHypothesis) :
    (255207 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 172423,
        Real.exp (-(n : ℝ) / (3448460 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3448460 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 96369) * ((3448460 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3448460 / 37) * (37 / 20)) + 1) / (2000 / 96369) +
        1839 / 1000 ≤
      18692 / 5 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge42_roots.2.2]
  have hs :
    Real.sqrt ((3448460 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3448460 / 37) * (37 / 20)) +
        21 / 20 ≤
      43987 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge42_roots.2.2, gammaAnalyticBridge42_logs.2]
  have hz :
    Real.sqrt (3448460 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3448460 / 37) + 2469 / 800 ≤
      34133 / 1000 := by
    linarith only [gammaAnalyticBridge42_roots.2.1, gammaAnalyticBridge42_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3448460 / 37) (y := 37 / 20) (h := 2000 / 96369) (r :=
      610579 / 2000) (e := 78619 / 500000) (p := 18692 / 5) (s := 43987 / 1000) (z := 34133 / 1000)
      (F := 255207 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge42_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3448460 / 37 : ℝ) * (37 / 20) = 172423 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge42_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3448460 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3448460 / 37 : ℝ)) ≤
      152701 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1526447 / 5000) (T := 610579 / 2000) (Z := 57213 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge42_roots.1
      gammaAnalyticBridge42_roots.2.1 gammaAnalyticBridge42_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge42_power : (3448460 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 161 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 42 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge42_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (18953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (172423 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 18953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 172423) (x := 3448460 / 37) (H := 19078 / 25) (R :=
      1526447 / 5000) (W := 161 / 100000) (F := 255207 / 1000) (U := 152701 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge42_power (gammaAnalyticBridge42_main hGRH.riemann)
      (gammaAnalyticBridge42_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 43. -/
theorem gammaAnalyticBridge43_roots :
    ((307303 / 1000 : ℝ) ≤ Real.sqrt (3494100 / 37 : ℝ) ∧
      Real.sqrt (3494100 / 37 : ℝ) ≤ 3073031 / 10000 ∧
      Real.sqrt (174705 : ℝ) ≤ 4179773 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 43. -/
theorem gammaAnalyticBridge43_logs :
    Real.log (3494100 / 37 : ℝ) ≤ 114557 / 10000 ∧ Real.log (174705 : ℝ) ≤ 120709 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3494100 / 37) 17 20 0 (114557 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 174705 18 20 0 (120709 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge43_main (hRH : RiemannHypothesis) :
    (128449 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 174705,
        Real.exp (-(n : ℝ) / (3494100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3494100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (32 / 1547) * ((3494100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3494100 / 37) * (37 / 20)) + 1) / (32 / 1547) +
        1839 / 1000 ≤
      3775399 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge43_roots.2.2]
  have hs :
    Real.sqrt ((3494100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3494100 / 37) * (37 / 20)) +
        21 / 20 ≤
      11037 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge43_roots.2.2, gammaAnalyticBridge43_logs.2]
  have hz :
    Real.sqrt (3494100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3494100 / 37) + 2469 / 800 ≤
      8563 / 250 := by
    linarith only [gammaAnalyticBridge43_roots.2.1, gammaAnalyticBridge43_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3494100 / 37) (y := 37 / 20) (h := 32 / 1547) (r :=
      3073031 / 10000) (e := 78619 / 500000) (p := 3775399 / 1000) (s := 11037 / 250) (z :=
      8563 / 250) (F := 128449 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge43_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3494100 / 37 : ℝ) * (37 / 20) = 174705 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge43_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3494100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3494100 / 37 : ℝ)) ≤
      61483 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 307303 / 1000) (T := 3073031 / 10000) (Z :=
      114557 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge43_roots.1
      gammaAnalyticBridge43_roots.2.1 gammaAnalyticBridge43_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge43_power : (3494100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1 / 625 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 43 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge43_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (174705 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 174705) (x := 3494100 / 37) (H := 19203 / 25) (R :=
      307303 / 1000) (W := 1 / 625) (F := 128449 / 500) (U := 61483 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge43_power (gammaAnalyticBridge43_main hGRH.riemann)
      (gammaAnalyticBridge43_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 44. -/
theorem gammaAnalyticBridge44_roots :
    ((618633 / 2000 : ℝ) ≤ Real.sqrt (3540040 / 37 : ℝ) ∧
      Real.sqrt (3540040 / 37 : ℝ) ≤ 1546583 / 5000 ∧
      Real.sqrt (177002 : ℝ) ≤ 4207161 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 44. -/
theorem gammaAnalyticBridge44_logs :
    Real.log (3540040 / 37 : ℝ) ≤ 7168 / 625 ∧ Real.log (177002 : ℝ) ≤ 3021 / 250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3540040 / 37) 17 20 0 (7168 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 177002 18 20 0 (3021 / 250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge44_main (hRH : RiemannHypothesis) :
    (258589 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 177002,
        Real.exp (-(n : ℝ) / (3540040 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3540040 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 38801) * ((3540040 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3540040 / 37) * (37 / 20)) + 1) / (800 / 38801) +
        1839 / 1000 ≤
      95313 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge44_roots.2.2]
  have hs :
    Real.sqrt ((3540040 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3540040 / 37) * (37 / 20)) +
        21 / 20 ≤
      44309 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge44_roots.2.2, gammaAnalyticBridge44_logs.2]
  have hz :
    Real.sqrt (3540040 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3540040 / 37) + 2469 / 800 ≤
      34371 / 1000 := by
    linarith only [gammaAnalyticBridge44_roots.2.1, gammaAnalyticBridge44_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3540040 / 37) (y := 37 / 20) (h := 800 / 38801) (r :=
      1546583 / 5000) (e := 78619 / 500000) (p := 95313 / 25) (s := 44309 / 1000) (z :=
      34371 / 1000) (F := 258589 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge44_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3540040 / 37 : ℝ) * (37 / 20) = 177002 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge44_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3540040 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3540040 / 37 : ℝ)) ≤
      77357 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 618633 / 2000) (T := 1546583 / 5000) (Z := 7168 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge44_roots.1
      gammaAnalyticBridge44_roots.2.1 gammaAnalyticBridge44_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge44_power : (3540040 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 79 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 44 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge44_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (177002 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 177002) (x := 3540040 / 37) (H := 19328 / 25) (R :=
      618633 / 2000) (W := 79 / 50000) (F := 258589 / 1000) (U := 77357 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge44_power (gammaAnalyticBridge44_main hGRH.riemann)
      (gammaAnalyticBridge44_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 45. -/
theorem gammaAnalyticBridge45_roots :
    ((3113301 / 10000 : ℝ) ≤ Real.sqrt (3586280 / 37 : ℝ) ∧
      Real.sqrt (3586280 / 37 : ℝ) ≤ 1556651 / 5000 ∧
      Real.sqrt (179314 : ℝ) ≤ 4234549 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 45. -/
theorem gammaAnalyticBridge45_logs :
    Real.log (3586280 / 37 : ℝ) ≤ 57409 / 5000 ∧ Real.log (179314 : ℝ) ≤ 120969 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3586280 / 37) 17 20 0 (57409 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 179314 18 20 0 (120969 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge45_main (hRH : RiemannHypothesis) :
    (6507 / 25 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 179314,
        Real.exp (-(n : ℝ) / (3586280 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3586280 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 97321) * ((3586280 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3586280 / 37) * (37 / 20)) + 1) / (2000 / 97321) +
        1839 / 1000 ≤
      3849761 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge45_roots.2.2]
  have hs :
    Real.sqrt ((3586280 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3586280 / 37) * (37 / 20)) +
        21 / 20 ≤
      44469 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge45_roots.2.2, gammaAnalyticBridge45_logs.2]
  have hz :
    Real.sqrt (3586280 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3586280 / 37) + 2469 / 800 ≤
      3449 / 100 := by
    linarith only [gammaAnalyticBridge45_roots.2.1, gammaAnalyticBridge45_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3586280 / 37) (y := 37 / 20) (h := 2000 / 97321) (r :=
      1556651 / 5000) (e := 78619 / 500000) (p := 3849761 / 1000) (s := 44469 / 1000) (z :=
      3449 / 100) (F := 6507 / 25) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge45_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3586280 / 37 : ℝ) * (37 / 20) = 179314 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge45_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3586280 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3586280 / 37 : ℝ)) ≤
      311441 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3113301 / 10000) (T := 1556651 / 5000) (Z :=
      57409 / 5000) (by norm_num only) (by norm_num only) gammaAnalyticBridge45_roots.1
      gammaAnalyticBridge45_roots.2.1 gammaAnalyticBridge45_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge45_power : (3586280 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 157 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 45 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge45_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (179314 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 179314) (x := 3586280 / 37) (H := 19453 / 25) (R :=
      3113301 / 10000) (W := 157 / 100000) (F := 6507 / 25) (U := 311441 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge45_power (gammaAnalyticBridge45_main hGRH.riemann)
      (gammaAnalyticBridge45_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 46. -/
theorem gammaAnalyticBridge46_roots :
    ((3133437 / 10000 : ℝ) ≤ Real.sqrt (3632820 / 37 : ℝ) ∧
      Real.sqrt (3632820 / 37 : ℝ) ≤ 1566719 / 5000 ∧
      Real.sqrt (181641 : ℝ) ≤ 4261937 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 46. -/
theorem gammaAnalyticBridge46_logs :
    Real.log (3632820 / 37 : ℝ) ≤ 114947 / 10000 ∧ Real.log (181641 : ℝ) ≤ 60549 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3632820 / 37) 17 20 0 (114947 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 181641 18 20 0 (60549 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge46_main (hRH : RiemannHypothesis) :
    (261971 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 181641,
        Real.exp (-(n : ℝ) / (3632820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3632820 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 39053) * ((3632820 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3632820 / 37) * (37 / 20)) + 1) / (800 / 39053) +
        1839 / 1000 ≤
      971781 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge46_roots.2.2]
  have hs :
    Real.sqrt ((3632820 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3632820 / 37) * (37 / 20)) +
        21 / 20 ≤
      4463 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge46_roots.2.2, gammaAnalyticBridge46_logs.2]
  have hz :
    Real.sqrt (3632820 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3632820 / 37) + 2469 / 800 ≤
      4326 / 125 := by
    linarith only [gammaAnalyticBridge46_roots.2.1, gammaAnalyticBridge46_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3632820 / 37) (y := 37 / 20) (h := 800 / 39053) (r :=
      1566719 / 5000) (e := 78619 / 500000) (p := 971781 / 250) (s := 4463 / 100) (z := 4326 / 125)
      (F := 261971 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge46_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3632820 / 37 : ℝ) * (37 / 20) = 181641 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge46_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3632820 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3632820 / 37 : ℝ)) ≤
      62691 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3133437 / 10000) (T := 1566719 / 5000) (Z :=
      114947 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge46_roots.1
      gammaAnalyticBridge46_roots.2.1 gammaAnalyticBridge46_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge46_power : (3632820 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 39 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 46 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge46_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (181641 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 181641) (x := 3632820 / 37) (H := 19578 / 25) (R :=
      3133437 / 10000) (W := 39 / 25000) (F := 261971 / 1000) (U := 62691 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge46_power (gammaAnalyticBridge46_main hGRH.riemann)
      (gammaAnalyticBridge46_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 47. -/
theorem gammaAnalyticBridge47_roots :
    ((3153573 / 10000 : ℝ) ≤ Real.sqrt (3679660 / 37 : ℝ) ∧
      Real.sqrt (3679660 / 37 : ℝ) ≤ 1576787 / 5000 ∧ Real.sqrt (183983 : ℝ) ≤ 1072331 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 47. -/
theorem gammaAnalyticBridge47_logs :
    Real.log (3679660 / 37 : ℝ) ≤ 4603 / 400 ∧ Real.log (183983 : ℝ) ≤ 60613 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3679660 / 37) 17 20 0 (4603 / 400) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 183983 18 20 0 (60613 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge47_main (hRH : RiemannHypothesis) :
    (131831 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 183983,
        Real.exp (-(n : ℝ) / (3679660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3679660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 39179) * ((3679660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3679660 / 37) * (37 / 20)) + 1) / (800 / 39179) +
        1839 / 1000 ≤
      784921 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge47_roots.2.2]
  have hs :
    Real.sqrt ((3679660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3679660 / 37) * (37 / 20)) +
        21 / 20 ≤
      44791 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge47_roots.2.2, gammaAnalyticBridge47_logs.2]
  have hz :
    Real.sqrt (3679660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3679660 / 37) + 2469 / 800 ≤
      17363 / 500 := by
    linarith only [gammaAnalyticBridge47_roots.2.1, gammaAnalyticBridge47_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3679660 / 37) (y := 37 / 20) (h := 800 / 39179) (r :=
      1576787 / 5000) (e := 78619 / 500000) (p := 784921 / 200) (s := 44791 / 1000) (z :=
      17363 / 500) (F := 131831 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge47_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3679660 / 37 : ℝ) * (37 / 20) = 183983 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge47_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3679660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3679660 / 37 : ℝ)) ≤
      78867 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3153573 / 10000) (T := 1576787 / 5000) (Z := 4603 / 400)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge47_roots.1
      gammaAnalyticBridge47_roots.2.1 gammaAnalyticBridge47_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge47_power : (3679660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 31 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 47 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge47_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (183983 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 183983) (x := 3679660 / 37) (H := 19703 / 25) (R :=
      3153573 / 10000) (W := 31 / 20000) (F := 131831 / 500) (U := 78867 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge47_power (gammaAnalyticBridge47_main hGRH.riemann)
      (gammaAnalyticBridge47_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 48. -/
theorem gammaAnalyticBridge48_roots :
    ((3173701 / 10000 : ℝ) ≤ Real.sqrt (3726780 / 37 : ℝ) ∧
      Real.sqrt (3726780 / 37 : ℝ) ≤ 1586851 / 5000 ∧
      Real.sqrt (186339 : ℝ) ≤ 4316701 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 48. -/
theorem gammaAnalyticBridge48_logs :
    Real.log (3726780 / 37 : ℝ) ≤ 57601 / 5000 ∧ Real.log (186339 : ℝ) ≤ 60677 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3726780 / 37) 17 20 0 (57601 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 186339 18 20 0 (60677 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge48_main (hRH : RiemannHypothesis) :
    (265353 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 186339,
        Real.exp (-(n : ℝ) / (3726780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3726780 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 98259) * ((3726780 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3726780 / 37) * (37 / 20)) + 1) / (2000 / 98259) +
        1839 / 1000 ≤
      3962191 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge48_roots.2.2]
  have hs :
    Real.sqrt ((3726780 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3726780 / 37) * (37 / 20)) +
        21 / 20 ≤
      44951 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge48_roots.2.2, gammaAnalyticBridge48_logs.2]
  have hz :
    Real.sqrt (3726780 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3726780 / 37) + 2469 / 800 ≤
      8711 / 250 := by
    linarith only [gammaAnalyticBridge48_roots.2.1, gammaAnalyticBridge48_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3726780 / 37) (y := 37 / 20) (h := 2000 / 98259) (r :=
      1586851 / 5000) (e := 78619 / 500000) (p := 3962191 / 1000) (s := 44951 / 1000) (z :=
      8711 / 250) (F := 265353 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge48_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3726780 / 37 : ℝ) * (37 / 20) = 186339 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge48_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3726780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3726780 / 37 : ℝ)) ≤
      7937 / 25 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3173701 / 10000) (T := 1586851 / 5000) (Z :=
      57601 / 5000) (by norm_num only) (by norm_num only) gammaAnalyticBridge48_roots.1
      gammaAnalyticBridge48_roots.2.1 gammaAnalyticBridge48_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge48_power : (3726780 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 77 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 48 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge48_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (186339 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 186339) (x := 3726780 / 37) (H := 19828 / 25) (R :=
      3173701 / 10000) (W := 77 / 50000) (F := 265353 / 1000) (U := 7937 / 25) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge48_power (gammaAnalyticBridge48_main hGRH.riemann)
      (gammaAnalyticBridge48_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 49. -/
theorem gammaAnalyticBridge49_roots :
    ((798459 / 2500 : ℝ) ≤ Real.sqrt (3774220 / 37 : ℝ) ∧
      Real.sqrt (3774220 / 37 : ℝ) ≤ 3193837 / 10000 ∧ Real.sqrt (188711 : ℝ) ≤ 543011 / 1250) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 49. -/
theorem gammaAnalyticBridge49_logs :
    Real.log (3774220 / 37 : ℝ) ≤ 7208 / 625 ∧ Real.log (188711 : ℝ) ≤ 3037 / 250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3774220 / 37) 17 20 0 (7208 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 188711 18 20 0 (3037 / 250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge49_main (hRH : RiemannHypothesis) :
    (66761 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 188711,
        Real.exp (-(n : ℝ) / (3774220 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3774220 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 197141) * ((3774220 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3774220 / 37) * (37 / 20)) + 1) / (4000 / 197141) +
        1839 / 1000 ≤
      499989 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge49_roots.2.2]
  have hs :
    Real.sqrt ((3774220 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3774220 / 37) * (37 / 20)) +
        21 / 20 ≤
      45111 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge49_roots.2.2, gammaAnalyticBridge49_logs.2]
  have hz :
    Real.sqrt (3774220 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3774220 / 37) + 2469 / 800 ≤
      34963 / 1000 := by
    linarith only [gammaAnalyticBridge49_roots.2.1, gammaAnalyticBridge49_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3774220 / 37) (y := 37 / 20) (h := 4000 / 197141) (r :=
      3193837 / 10000) (e := 78619 / 500000) (p := 499989 / 125) (s := 45111 / 1000) (z :=
      34963 / 1000) (F := 66761 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge49_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3774220 / 37 : ℝ) * (37 / 20) = 188711 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge49_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3774220 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3774220 / 37 : ℝ)) ≤
      159747 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 798459 / 2500) (T := 3193837 / 10000) (Z := 7208 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge49_roots.1
      gammaAnalyticBridge49_roots.2.1 gammaAnalyticBridge49_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge49_power : (3774220 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 153 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 49 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge49_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (19953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (188711 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 188711) (x := 3774220 / 37) (H := 19953 / 25) (R :=
      798459 / 2500) (W := 153 / 100000) (F := 66761 / 250) (U := 159747 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge49_power (gammaAnalyticBridge49_main hGRH.riemann)
      (gammaAnalyticBridge49_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 50. -/
theorem gammaAnalyticBridge50_roots :
    ((803493 / 2500 : ℝ) ≤ Real.sqrt (3821960 / 37 : ℝ) ∧
      Real.sqrt (3821960 / 37 : ℝ) ≤ 3213973 / 10000 ∧
      Real.sqrt (191098 : ℝ) ≤ 1092869 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 50. -/
theorem gammaAnalyticBridge50_logs :
    Real.log (3821960 / 37 : ℝ) ≤ 57727 / 5000 ∧ Real.log (191098 : ℝ) ≤ 60803 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3821960 / 37) 17 20 0 (57727 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 191098 18 20 0 (60803 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge50_main (hRH : RiemannHypothesis) :
    (53747 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 191098,
        Real.exp (-(n : ℝ) / (3821960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3821960 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 49441) * ((3821960 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3821960 / 37) * (37 / 20)) + 1) / (1000 / 49441) +
        1839 / 1000 ≤
      504719 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge50_roots.2.2]
  have hs :
    Real.sqrt ((3821960 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3821960 / 37) * (37 / 20)) +
        21 / 20 ≤
      45271 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge50_roots.2.2, gammaAnalyticBridge50_logs.2]
  have hz :
    Real.sqrt (3821960 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3821960 / 37) + 2469 / 800 ≤
      35081 / 1000 := by
    linarith only [gammaAnalyticBridge50_roots.2.1, gammaAnalyticBridge50_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3821960 / 37) (y := 37 / 20) (h := 1000 / 49441) (r :=
      3213973 / 10000) (e := 78619 / 500000) (p := 504719 / 125) (s := 45271 / 1000) (z :=
      35081 / 1000) (F := 53747 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge50_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3821960 / 37 : ℝ) * (37 / 20) = 191098 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge50_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3821960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3821960 / 37 : ℝ)) ≤
      321507 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 803493 / 2500) (T := 3213973 / 10000) (Z := 57727 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge50_roots.1
      gammaAnalyticBridge50_roots.2.1 gammaAnalyticBridge50_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge50_power : (3821960 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 19 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 50 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge50_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (19953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (191098 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 19953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 191098) (x := 3821960 / 37) (H := 20078 / 25) (R :=
      803493 / 2500) (W := 19 / 12500) (F := 53747 / 200) (U := 321507 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge50_power (gammaAnalyticBridge50_main hGRH.riemann)
      (gammaAnalyticBridge50_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 51. -/
theorem gammaAnalyticBridge51_roots :
    ((808527 / 2500 : ℝ) ≤ Real.sqrt (3870000 / 37 : ℝ) ∧
      Real.sqrt (3870000 / 37 : ℝ) ≤ 3234109 / 10000 ∧ Real.sqrt (193500 : ℝ) ≤ 274929 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 51. -/
theorem gammaAnalyticBridge51_logs :
    Real.log (3870000 / 37 : ℝ) ≤ 115579 / 10000 ∧ Real.log (193500 : ℝ) ≤ 121731 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3870000 / 37) 17 20 0 (115579 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 193500 18 20 0 (121731 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge51_main (hRH : RiemannHypothesis) :
    (270427 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 193500,
        Real.exp (-(n : ℝ) / (3870000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3870000 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (200 / 9919) * ((3870000 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3870000 / 37) * (37 / 20)) + 1) / (200 / 9919) +
        1839 / 1000 ≤
      4075711 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge51_roots.2.2]
  have hs :
    Real.sqrt ((3870000 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3870000 / 37) * (37 / 20)) +
        21 / 20 ≤
      45431 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge51_roots.2.2, gammaAnalyticBridge51_logs.2]
  have hz :
    Real.sqrt (3870000 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3870000 / 37) + 2469 / 800 ≤
      35199 / 1000 := by
    linarith only [gammaAnalyticBridge51_roots.2.1, gammaAnalyticBridge51_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3870000 / 37) (y := 37 / 20) (h := 200 / 9919) (r :=
      3234109 / 10000) (e := 78619 / 500000) (p := 4075711 / 1000) (s := 45431 / 1000) (z :=
      35199 / 1000) (F := 270427 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge51_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3870000 / 37 : ℝ) * (37 / 20) = 193500 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge51_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3870000 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3870000 / 37 : ℝ)) ≤
      8088 / 25 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 808527 / 2500) (T := 3234109 / 10000) (Z :=
      115579 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge51_roots.1
      gammaAnalyticBridge51_roots.2.1 gammaAnalyticBridge51_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge51_power : (3870000 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 151 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 51 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge51_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (193500 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 193500) (x := 3870000 / 37) (H := 20203 / 25) (R :=
      808527 / 2500) (W := 151 / 100000) (F := 270427 / 1000) (U := 8088 / 25) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge51_power (gammaAnalyticBridge51_main hGRH.riemann)
      (gammaAnalyticBridge51_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 52. -/
theorem gammaAnalyticBridge52_roots :
    ((813561 / 2500 : ℝ) ≤ Real.sqrt (3918340 / 37 : ℝ) ∧
      Real.sqrt (3918340 / 37 : ℝ) ≤ 650849 / 2000 ∧ Real.sqrt (195917 : ℝ) ≤ 1106563 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 52. -/
theorem gammaAnalyticBridge52_logs :
    Real.log (3918340 / 37 : ℝ) ≤ 115703 / 10000 ∧ Real.log (195917 : ℝ) ≤ 24371 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3918340 / 37) 17 20 0 (115703 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 195917 18 20 0 (24371 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge52_main (hRH : RiemannHypothesis) :
    (136059 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 195917,
        Real.exp (-(n : ℝ) / (3918340 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3918340 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 49749) * ((3918340 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3918340 / 37) * (37 / 20)) + 1) / (1000 / 49749) +
        1839 / 1000 ≤
      1028447 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge52_roots.2.2]
  have hs :
    Real.sqrt ((3918340 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3918340 / 37) * (37 / 20)) +
        21 / 20 ≤
      45591 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge52_roots.2.2, gammaAnalyticBridge52_logs.2]
  have hz :
    Real.sqrt (3918340 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3918340 / 37) + 2469 / 800 ≤
      8829 / 250 := by
    linarith only [gammaAnalyticBridge52_roots.2.1, gammaAnalyticBridge52_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3918340 / 37) (y := 37 / 20) (h := 1000 / 49749) (r :=
      650849 / 2000) (e := 78619 / 500000) (p := 1028447 / 250) (s := 45591 / 1000) (z :=
      8829 / 250) (F := 136059 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge52_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3918340 / 37 : ℝ) * (37 / 20) = 195917 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge52_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3918340 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3918340 / 37 : ℝ)) ≤
      162767 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 813561 / 2500) (T := 650849 / 2000) (Z := 115703 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge52_roots.1
      gammaAnalyticBridge52_roots.2.1 gammaAnalyticBridge52_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge52_power : (3918340 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 3 / 2000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 52 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge52_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (195917 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 195917) (x := 3918340 / 37) (H := 20328 / 25) (R :=
      813561 / 2500) (W := 3 / 2000) (F := 136059 / 500) (U := 162767 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge52_power (gammaAnalyticBridge52_main hGRH.riemann)
      (gammaAnalyticBridge52_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 53. -/
theorem gammaAnalyticBridge53_roots :
    ((163719 / 500 : ℝ) ≤ Real.sqrt (3966980 / 37 : ℝ) ∧
      Real.sqrt (3966980 / 37 : ℝ) ≤ 3274381 / 10000 ∧
      Real.sqrt (198349 : ℝ) ≤ 4453639 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 53. -/
theorem gammaAnalyticBridge53_logs :
    Real.log (3966980 / 37 : ℝ) ≤ 57913 / 5000 ∧ Real.log (198349 : ℝ) ≤ 60989 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (3966980 / 37) 17 20 0 (57913 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 198349 18 20 0 (60989 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge53_main (hRH : RiemannHypothesis) :
    (273809 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 198349,
        Real.exp (-(n : ℝ) / (3966980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3966980 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 49903) * ((3966980 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((3966980 / 37) * (37 / 20)) + 1) / (1000 / 49903) +
        1839 / 1000 ≤
      4151983 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge53_roots.2.2]
  have hs :
    Real.sqrt ((3966980 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((3966980 / 37) * (37 / 20)) +
        21 / 20 ≤
      183 / 4 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge53_roots.2.2, gammaAnalyticBridge53_logs.2]
  have hz :
    Real.sqrt (3966980 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (3966980 / 37) + 2469 / 800 ≤
      17717 / 500 := by
    linarith only [gammaAnalyticBridge53_roots.2.1, gammaAnalyticBridge53_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 3966980 / 37) (y := 37 / 20) (h := 1000 / 49903) (r :=
      3274381 / 10000) (e := 78619 / 500000) (p := 4151983 / 1000) (s := 183 / 4) (z := 17717 / 500)
      (F := 273809 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge53_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (3966980 / 37 : ℝ) * (37 / 20) = 198349 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge53_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (3966980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (3966980 / 37 : ℝ)) ≤
      327547 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 163719 / 500) (T := 3274381 / 10000) (Z := 57913 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge53_roots.1
      gammaAnalyticBridge53_roots.2.1 gammaAnalyticBridge53_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge53_power : (3966980 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 149 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 53 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge53_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (198349 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 198349) (x := 3966980 / 37) (H := 20453 / 25) (R :=
      163719 / 500) (W := 149 / 100000) (F := 273809 / 1000) (U := 327547 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge53_power (gammaAnalyticBridge53_main hGRH.riemann)
      (gammaAnalyticBridge53_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 54. -/
theorem gammaAnalyticBridge54_roots :
    ((823629 / 2500 : ℝ) ≤ Real.sqrt (4015920 / 37 : ℝ) ∧
      Real.sqrt (4015920 / 37 : ℝ) ≤ 3294517 / 10000 ∧
      Real.sqrt (200796 : ℝ) ≤ 4481027 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 54. -/
theorem gammaAnalyticBridge54_logs :
    Real.log (4015920 / 37 : ℝ) ≤ 115949 / 10000 ∧ Real.log (200796 : ℝ) ≤ 122101 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4015920 / 37) 17 20 0 (115949 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 200796 18 20 0 (122101 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge54_main (hRH : RiemannHypothesis) :
    (551 / 2 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 200796,
        Real.exp (-(n : ℝ) / (4015920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4015920 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 200221) * ((4015920 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4015920 / 37) * (37 / 20)) + 1) / (4000 / 200221) +
        1839 / 1000 ≤
      523787 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge54_roots.2.2]
  have hs :
    Real.sqrt ((4015920 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4015920 / 37) * (37 / 20)) +
        21 / 20 ≤
      4591 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge54_roots.2.2, gammaAnalyticBridge54_logs.2]
  have hz :
    Real.sqrt (4015920 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4015920 / 37) + 2469 / 800 ≤
      4444 / 125 := by
    linarith only [gammaAnalyticBridge54_roots.2.1, gammaAnalyticBridge54_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4015920 / 37) (y := 37 / 20) (h := 4000 / 200221) (r :=
      3294517 / 10000) (e := 78619 / 500000) (p := 523787 / 125) (s := 4591 / 100) (z := 4444 / 125)
      (F := 551 / 2) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge54_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4015920 / 37 : ℝ) * (37 / 20) = 200796 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge54_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4015920 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4015920 / 37 : ℝ)) ≤
      8239 / 25 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 823629 / 2500) (T := 3294517 / 10000) (Z :=
      115949 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge54_roots.1
      gammaAnalyticBridge54_roots.2.1 gammaAnalyticBridge54_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge54_power : (4015920 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 37 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 54 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge54_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (200796 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 200796) (x := 4015920 / 37) (H := 20578 / 25) (R :=
      823629 / 2500) (W := 37 / 25000) (F := 551 / 2) (U := 8239 / 25) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge54_power (gammaAnalyticBridge54_main hGRH.riemann)
      (gammaAnalyticBridge54_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 55. -/
theorem gammaAnalyticBridge55_roots :
    ((828661 / 2500 : ℝ) ≤ Real.sqrt (4065140 / 37 : ℝ) ∧
      Real.sqrt (4065140 / 37 : ℝ) ≤ 662929 / 2000 ∧ Real.sqrt (203257 : ℝ) ≤ 1127101 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 55. -/
theorem gammaAnalyticBridge55_logs :
    Real.log (4065140 / 37 : ℝ) ≤ 116071 / 10000 ∧ Real.log (203257 : ℝ) ≤ 122223 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4065140 / 37) 17 20 0 (116071 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 203257 18 20 0 (122223 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge55_main (hRH : RiemannHypothesis) :
    (277191 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 203257,
        Real.exp (-(n : ℝ) / (4065140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4065140 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 200837) * ((4065140 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4065140 / 37) * (37 / 20)) + 1) / (4000 / 200837) +
        1839 / 1000 ≤
      4228709 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge55_roots.2.2]
  have hs :
    Real.sqrt ((4065140 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4065140 / 37) * (37 / 20)) +
        21 / 20 ≤
      46069 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge55_roots.2.2, gammaAnalyticBridge55_logs.2]
  have hz :
    Real.sqrt (4065140 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4065140 / 37) + 2469 / 800 ≤
      35669 / 1000 := by
    linarith only [gammaAnalyticBridge55_roots.2.1, gammaAnalyticBridge55_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4065140 / 37) (y := 37 / 20) (h := 4000 / 200837) (r :=
      662929 / 2000) (e := 78619 / 500000) (p := 4228709 / 1000) (s := 46069 / 1000) (z :=
      35669 / 1000) (F := 277191 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge55_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4065140 / 37 : ℝ) * (37 / 20) = 203257 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge55_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4065140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4065140 / 37 : ℝ)) ≤
      331573 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 828661 / 2500) (T := 662929 / 2000) (Z := 116071 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge55_roots.1
      gammaAnalyticBridge55_roots.2.1 gammaAnalyticBridge55_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge55_power : (4065140 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 147 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 55 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge55_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (203257 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 203257) (x := 4065140 / 37) (H := 20703 / 25) (R :=
      828661 / 2500) (W := 147 / 100000) (F := 277191 / 1000) (U := 331573 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge55_power (gammaAnalyticBridge55_main hGRH.riemann)
      (gammaAnalyticBridge55_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 56. -/
theorem gammaAnalyticBridge56_roots :
    ((3334779 / 10000 : ℝ) ≤ Real.sqrt (4114680 / 37 : ℝ) ∧
      Real.sqrt (4114680 / 37 : ℝ) ≤ 166739 / 500 ∧ Real.sqrt (205734 : ℝ) ≤ 283487 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 56. -/
theorem gammaAnalyticBridge56_logs :
    Real.log (4114680 / 37 : ℝ) ≤ 7262 / 625 ∧ Real.log (205734 : ℝ) ≤ 15293 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4114680 / 37) 17 20 0 (7262 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 205734 18 20 0 (15293 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge56_main (hRH : RiemannHypothesis) :
    (139441 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 205734,
        Real.exp (-(n : ℝ) / (4114680 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4114680 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 100723) * ((4114680 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4114680 / 37) * (37 / 20)) + 1) / (2000 / 100723) +
        1839 / 1000 ≤
      533407 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge56_roots.2.2]
  have hs :
    Real.sqrt ((4114680 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4114680 / 37) * (37 / 20)) +
        21 / 20 ≤
      46229 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge56_roots.2.2, gammaAnalyticBridge56_logs.2]
  have hz :
    Real.sqrt (4114680 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4114680 / 37) + 2469 / 800 ≤
      17893 / 500 := by
    linarith only [gammaAnalyticBridge56_roots.2.1, gammaAnalyticBridge56_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4114680 / 37) (y := 37 / 20) (h := 2000 / 100723) (r :=
      166739 / 500) (e := 78619 / 500000) (p := 533407 / 125) (s := 46229 / 1000) (z := 17893 / 500)
      (F := 139441 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge56_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4114680 / 37 : ℝ) * (37 / 20) = 205734 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge56_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4114680 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4114680 / 37 : ℝ)) ≤
      166793 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3334779 / 10000) (T := 166739 / 500) (Z := 7262 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge56_roots.1
      gammaAnalyticBridge56_roots.2.1 gammaAnalyticBridge56_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge56_power : (4114680 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 73 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 56 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge56_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (205734 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 205734) (x := 4114680 / 37) (H := 20828 / 25) (R :=
      3334779 / 10000) (W := 73 / 50000) (F := 139441 / 500) (U := 166793 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge56_power (gammaAnalyticBridge56_main hGRH.riemann)
      (gammaAnalyticBridge56_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 57. -/
theorem gammaAnalyticBridge57_roots :
    ((670983 / 2000 : ℝ) ≤ Real.sqrt (4164520 / 37 : ℝ) ∧
      Real.sqrt (4164520 / 37 : ℝ) ≤ 838729 / 2500 ∧ Real.sqrt (208226 : ℝ) ≤ 4563179 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 57. -/
theorem gammaAnalyticBridge57_logs :
    Real.log (4164520 / 37 : ℝ) ≤ 14539 / 1250 ∧ Real.log (208226 : ℝ) ≤ 7654 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4164520 / 37) 17 20 0 (14539 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 208226 18 20 0 (7654 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge57_main (hRH : RiemannHypothesis) :
    (140287 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 208226,
        Real.exp (-(n : ℝ) / (4164520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4164520 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (125 / 6314) * ((4164520 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4164520 / 37) * (37 / 20)) + 1) / (125 / 6314) +
        1839 / 1000 ≤
      4305919 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge57_roots.2.2]
  have hs :
    Real.sqrt ((4164520 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4164520 / 37) * (37 / 20)) +
        21 / 20 ≤
      11597 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge57_roots.2.2, gammaAnalyticBridge57_logs.2]
  have hz :
    Real.sqrt (4164520 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4164520 / 37) + 2469 / 800 ≤
      4488 / 125 := by
    linarith only [gammaAnalyticBridge57_roots.2.1, gammaAnalyticBridge57_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4164520 / 37) (y := 37 / 20) (h := 125 / 6314) (r :=
      838729 / 2500) (e := 78619 / 500000) (p := 4305919 / 1000) (s := 11597 / 250) (z :=
      4488 / 125) (F := 140287 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge57_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4164520 / 37 : ℝ) * (37 / 20) = 208226 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge57_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4164520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4164520 / 37 : ℝ)) ≤
      335599 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 670983 / 2000) (T := 838729 / 2500) (Z := 14539 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge57_roots.1
      gammaAnalyticBridge57_roots.2.1 gammaAnalyticBridge57_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge57_power : (4164520 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 29 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 57 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge57_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (20953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (208226 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 208226) (x := 4164520 / 37) (H := 20953 / 25) (R :=
      670983 / 2000) (W := 29 / 20000) (F := 140287 / 500) (U := 335599 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge57_power (gammaAnalyticBridge57_main hGRH.riemann)
      (gammaAnalyticBridge57_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 58. -/
theorem gammaAnalyticBridge58_roots :
    ((3375051 / 10000 : ℝ) ≤ Real.sqrt (4214660 / 37 : ℝ) ∧
      Real.sqrt (4214660 / 37 : ℝ) ≤ 843763 / 2500 ∧ Real.sqrt (210733 : ℝ) ≤ 4590567 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 58. -/
theorem gammaAnalyticBridge58_logs :
    Real.log (4214660 / 37 : ℝ) ≤ 7277 / 625 ∧ Real.log (210733 : ℝ) ≤ 15323 / 1250 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4214660 / 37) 17 20 0 (7277 / 625) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 210733 18 20 0 (15323 / 1250) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge58_main (hRH : RiemannHypothesis) :
    (56453 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 210733,
        Real.exp (-(n : ℝ) / (4214660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4214660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 202657) * ((4214660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4214660 / 37) * (37 / 20)) + 1) / (4000 / 202657) +
        1839 / 1000 ≤
      4344697 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge58_roots.2.2]
  have hs :
    Real.sqrt ((4214660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4214660 / 37) * (37 / 20)) +
        21 / 20 ≤
      46547 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge58_roots.2.2, gammaAnalyticBridge58_logs.2]
  have hz :
    Real.sqrt (4214660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4214660 / 37) + 2469 / 800 ≤
      36021 / 1000 := by
    linarith only [gammaAnalyticBridge58_roots.2.1, gammaAnalyticBridge58_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4214660 / 37) (y := 37 / 20) (h := 4000 / 202657) (r :=
      843763 / 2500) (e := 78619 / 500000) (p := 4344697 / 1000) (s := 46547 / 1000) (z :=
      36021 / 1000) (F := 56453 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge58_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4214660 / 37 : ℝ) * (37 / 20) = 210733 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge58_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4214660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4214660 / 37 : ℝ)) ≤
      84403 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3375051 / 10000) (T := 843763 / 2500) (Z := 7277 / 625)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge58_roots.1
      gammaAnalyticBridge58_roots.2.1 gammaAnalyticBridge58_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge58_power : (4214660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 9 / 6250 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 58 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge58_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (20953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (210733 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 20953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 210733) (x := 4214660 / 37) (H := 21078 / 25) (R :=
      3375051 / 10000) (W := 9 / 6250) (F := 56453 / 200) (U := 84403 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge58_power (gammaAnalyticBridge58_main hGRH.riemann)
      (gammaAnalyticBridge58_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 59. -/
theorem gammaAnalyticBridge59_roots :
    ((3395187 / 10000 : ℝ) ≤ Real.sqrt (4265100 / 37 : ℝ) ∧
      Real.sqrt (4265100 / 37 : ℝ) ≤ 848797 / 2500 ∧ Real.sqrt (213255 : ℝ) ≤ 923591 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 59. -/
theorem gammaAnalyticBridge59_logs :
    Real.log (4265100 / 37 : ℝ) ≤ 116551 / 10000 ∧ Real.log (213255 : ℝ) ≤ 122703 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4265100 / 37) 17 20 0 (116551 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 213255 18 20 0 (122703 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge59_main (hRH : RiemannHypothesis) :
    (70989 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 213255,
        Real.exp (-(n : ℝ) / (4265100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4265100 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 203259) * ((4265100 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4265100 / 37) * (37 / 20)) + 1) / (4000 / 203259) +
        1839 / 1000 ≤
      547949 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge59_roots.2.2]
  have hs :
    Real.sqrt ((4265100 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4265100 / 37) * (37 / 20)) +
        21 / 20 ≤
      9341 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge59_roots.2.2, gammaAnalyticBridge59_logs.2]
  have hz :
    Real.sqrt (4265100 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4265100 / 37) + 2469 / 800 ≤
      18069 / 500 := by
    linarith only [gammaAnalyticBridge59_roots.2.1, gammaAnalyticBridge59_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4265100 / 37) (y := 37 / 20) (h := 4000 / 203259) (r :=
      848797 / 2500) (e := 78619 / 500000) (p := 547949 / 125) (s := 9341 / 200) (z := 18069 / 500)
      (F := 70989 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge59_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4265100 / 37 : ℝ) * (37 / 20) = 213255 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge59_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4265100 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4265100 / 37 : ℝ)) ≤
      169813 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3395187 / 10000) (T := 848797 / 2500) (Z :=
      116551 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge59_roots.1
      gammaAnalyticBridge59_roots.2.1 gammaAnalyticBridge59_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge59_power : (4265100 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 143 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 59 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge59_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (213255 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 213255) (x := 4265100 / 37) (H := 21203 / 25) (R :=
      3395187 / 10000) (W := 143 / 100000) (F := 70989 / 250) (U := 169813 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge59_power (gammaAnalyticBridge59_main hGRH.riemann)
      (gammaAnalyticBridge59_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 60. -/
theorem gammaAnalyticBridge60_roots :
    ((3415323 / 10000 : ℝ) ≤ Real.sqrt (4315840 / 37 : ℝ) ∧
      Real.sqrt (4315840 / 37 : ℝ) ≤ 853831 / 2500 ∧ Real.sqrt (215792 : ℝ) ≤ 2322671 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 60. -/
theorem gammaAnalyticBridge60_logs :
    Real.log (4315840 / 37 : ℝ) ≤ 116669 / 10000 ∧ Real.log (215792 : ℝ) ≤ 122821 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4315840 / 37) 17 20 0 (116669 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 215792 18 20 0 (122821 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge60_main (hRH : RiemannHypothesis) :
    (35706 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 215792,
        Real.exp (-(n : ℝ) / (4315840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4315840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 203861) * ((4315840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4315840 / 37) * (37 / 20)) + 1) / (4000 / 203861) +
        1839 / 1000 ≤
      2211301 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge60_roots.2.2]
  have hs :
    Real.sqrt ((4315840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4315840 / 37) * (37 / 20)) +
        21 / 20 ≤
      5858 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge60_roots.2.2, gammaAnalyticBridge60_logs.2]
  have hz :
    Real.sqrt (4315840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4315840 / 37) + 2469 / 800 ≤
      7251 / 200 := by
    linarith only [gammaAnalyticBridge60_roots.2.1, gammaAnalyticBridge60_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4315840 / 37) (y := 37 / 20) (h := 4000 / 203861) (r :=
      853831 / 2500) (e := 78619 / 500000) (p := 2211301 / 500) (s := 5858 / 125) (z := 7251 / 200)
      (F := 35706 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge60_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4315840 / 37 : ℝ) * (37 / 20) = 215792 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge60_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4315840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4315840 / 37 : ℝ)) ≤
      341639 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3415323 / 10000) (T := 853831 / 2500) (Z :=
      116669 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge60_roots.1
      gammaAnalyticBridge60_roots.2.1 gammaAnalyticBridge60_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge60_power : (4315840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 71 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 60 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge60_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (215792 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 215792) (x := 4315840 / 37) (H := 21328 / 25) (R :=
      3415323 / 10000) (W := 71 / 50000) (F := 35706 / 125) (U := 341639 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge60_power (gammaAnalyticBridge60_main hGRH.riemann)
      (gammaAnalyticBridge60_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 61. -/
theorem gammaAnalyticBridge61_roots :
    ((1717729 / 5000 : ℝ) ≤ Real.sqrt (4366880 / 37 : ℝ) ∧
      Real.sqrt (4366880 / 37 : ℝ) ≤ 3435459 / 10000 ∧ Real.sqrt (218344 : ℝ) ≤ 467273 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 61. -/
theorem gammaAnalyticBridge61_logs :
    Real.log (4366880 / 37 : ℝ) ≤ 116787 / 10000 ∧ Real.log (218344 : ℝ) ≤ 122939 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4366880 / 37) 17 20 0 (116787 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 218344 18 20 0 (122939 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge61_main (hRH : RiemannHypothesis) :
    (287339 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 218344,
        Real.exp (-(n : ℝ) / (4366880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4366880 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 204463) * ((4366880 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4366880 / 37) * (37 / 20)) + 1) / (4000 / 204463) +
        1839 / 1000 ≤
      4461727 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge61_roots.2.2]
  have hs :
    Real.sqrt ((4366880 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4366880 / 37) * (37 / 20)) +
        21 / 20 ≤
      47023 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge61_roots.2.2, gammaAnalyticBridge61_logs.2]
  have hz :
    Real.sqrt (4366880 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4366880 / 37) + 2469 / 800 ≤
      9093 / 250 := by
    linarith only [gammaAnalyticBridge61_roots.2.1, gammaAnalyticBridge61_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4366880 / 37) (y := 37 / 20) (h := 4000 / 204463) (r :=
      3435459 / 10000) (e := 78619 / 500000) (p := 4461727 / 1000) (s := 47023 / 1000) (z :=
      9093 / 250) (F := 287339 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge61_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4366880 / 37 : ℝ) * (37 / 20) = 218344 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge61_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4366880 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4366880 / 37 : ℝ)) ≤
      85913 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1717729 / 5000) (T := 3435459 / 10000) (Z :=
      116787 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge61_roots.1
      gammaAnalyticBridge61_roots.2.1 gammaAnalyticBridge61_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge61_power : (4366880 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 141 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 61 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge61_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (218344 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 218344) (x := 4366880 / 37) (H := 21453 / 25) (R :=
      1717729 / 5000) (W := 141 / 100000) (F := 287339 / 1000) (U := 85913 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge61_power (gammaAnalyticBridge61_main hGRH.riemann)
      (gammaAnalyticBridge61_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 62. -/
theorem gammaAnalyticBridge62_roots :
    ((1727793 / 5000 : ℝ) ≤ Real.sqrt (4418200 / 37 : ℝ) ∧
      Real.sqrt (4418200 / 37 : ℝ) ≤ 3455587 / 10000 ∧
      Real.sqrt (220910 : ℝ) ≤ 4700107 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 62. -/
theorem gammaAnalyticBridge62_logs :
    Real.log (4418200 / 37 : ℝ) ≤ 14613 / 1250 ∧ Real.log (220910 : ℝ) ≤ 7691 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4418200 / 37) 17 20 0 (14613 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 220910 18 20 0 (7691 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge62_main (hRH : RiemannHypothesis) :
    (28903 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 220910,
        Real.exp (-(n : ℝ) / (4418200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4418200 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 102529) * ((4418200 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4418200 / 37) * (37 / 20)) + 1) / (2000 / 102529) +
        1839 / 1000 ≤
      562619 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge62_roots.2.2]
  have hs :
    Real.sqrt ((4418200 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4418200 / 37) * (37 / 20)) +
        21 / 20 ≤
      47181 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge62_roots.2.2, gammaAnalyticBridge62_logs.2]
  have hz :
    Real.sqrt (4418200 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4418200 / 37) + 2469 / 800 ≤
      36489 / 1000 := by
    linarith only [gammaAnalyticBridge62_roots.2.1, gammaAnalyticBridge62_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4418200 / 37) (y := 37 / 20) (h := 2000 / 102529) (r :=
      3455587 / 10000) (e := 78619 / 500000) (p := 562619 / 125) (s := 47181 / 1000) (z :=
      36489 / 1000) (F := 28903 / 100) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge62_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4418200 / 37 : ℝ) * (37 / 20) = 220910 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge62_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4418200 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4418200 / 37 : ℝ)) ≤
      69133 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1727793 / 5000) (T := 3455587 / 10000) (Z :=
      14613 / 1250) (by norm_num only) (by norm_num only) gammaAnalyticBridge62_roots.1
      gammaAnalyticBridge62_roots.2.1 gammaAnalyticBridge62_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge62_power : (4418200 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 7 / 5000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 62 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge62_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (220910 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 220910) (x := 4418200 / 37) (H := 21578 / 25) (R :=
      1727793 / 5000) (W := 7 / 5000) (F := 28903 / 100) (U := 69133 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge62_power (gammaAnalyticBridge62_main hGRH.riemann)
      (gammaAnalyticBridge62_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 63. -/
theorem gammaAnalyticBridge63_roots :
    ((1737861 / 5000 : ℝ) ≤ Real.sqrt (4469840 / 37 : ℝ) ∧
      Real.sqrt (4469840 / 37 : ℝ) ≤ 3475723 / 10000 ∧ Real.sqrt (223492 : ℝ) ≤ 945499 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 63. -/
theorem gammaAnalyticBridge63_logs :
    Real.log (4469840 / 37 : ℝ) ≤ 5851 / 500 ∧ Real.log (223492 : ℝ) ≤ 30793 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4469840 / 37) 17 20 0 (5851 / 500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 223492 18 20 0 (30793 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge63_main (hRH : RiemannHypothesis) :
    (290721 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 223492,
        Real.exp (-(n : ℝ) / (4469840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4469840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 205653) * ((4469840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4469840 / 37) * (37 / 20)) + 1) / (4000 / 205653) +
        1839 / 1000 ≤
      4540307 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge63_roots.2.2]
  have hs :
    Real.sqrt ((4469840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4469840 / 37) * (37 / 20)) +
        21 / 20 ≤
      47339 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge63_roots.2.2, gammaAnalyticBridge63_logs.2]
  have hz :
    Real.sqrt (4469840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4469840 / 37) + 2469 / 800 ≤
      7321 / 200 := by
    linarith only [gammaAnalyticBridge63_roots.2.1, gammaAnalyticBridge63_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4469840 / 37) (y := 37 / 20) (h := 4000 / 205653) (r :=
      3475723 / 10000) (e := 78619 / 500000) (p := 4540307 / 1000) (s := 47339 / 1000) (z :=
      7321 / 200) (F := 290721 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge63_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4469840 / 37 : ℝ) * (37 / 20) = 223492 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge63_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4469840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4469840 / 37 : ℝ)) ≤
      173839 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1737861 / 5000) (T := 3475723 / 10000) (Z := 5851 / 500)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge63_roots.1
      gammaAnalyticBridge63_roots.2.1 gammaAnalyticBridge63_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge63_power : (4469840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 139 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 63 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge63_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (223492 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 223492) (x := 4469840 / 37) (H := 21703 / 25) (R :=
      1737861 / 5000) (W := 139 / 100000) (F := 290721 / 1000) (U := 173839 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge63_power (gammaAnalyticBridge63_main hGRH.riemann)
      (gammaAnalyticBridge63_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 64. -/
theorem gammaAnalyticBridge64_roots :
    ((1747929 / 5000 : ℝ) ≤ Real.sqrt (4521780 / 37 : ℝ) ∧
      Real.sqrt (4521780 / 37 : ℝ) ≤ 3495859 / 10000 ∧
      Real.sqrt (226089 : ℝ) ≤ 2377441 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 64. -/
theorem gammaAnalyticBridge64_logs :
    Real.log (4521780 / 37 : ℝ) ≤ 23427 / 2000 ∧ Real.log (226089 : ℝ) ≤ 123287 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4521780 / 37) 17 20 0 (23427 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 226089 18 20 0 (123287 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge64_main (hRH : RiemannHypothesis) :
    (292413 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 226089,
        Real.exp (-(n : ℝ) / (4521780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4521780 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 25781) * ((4521780 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4521780 / 37) * (37 / 20)) + 1) / (500 / 25781) +
        1839 / 1000 ≤
      183191 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge64_roots.2.2]
  have hs :
    Real.sqrt ((4521780 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4521780 / 37) * (37 / 20)) +
        21 / 20 ≤
      47497 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge64_roots.2.2, gammaAnalyticBridge64_logs.2]
  have hz :
    Real.sqrt (4521780 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4521780 / 37) + 2469 / 800 ≤
      18361 / 500 := by
    linarith only [gammaAnalyticBridge64_roots.2.1, gammaAnalyticBridge64_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4521780 / 37) (y := 37 / 20) (h := 500 / 25781) (r :=
      3495859 / 10000) (e := 78619 / 500000) (p := 183191 / 40) (s := 47497 / 1000) (z :=
      18361 / 500) (F := 292413 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge64_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4521780 / 37 : ℝ) * (37 / 20) = 226089 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge64_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4521780 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4521780 / 37 : ℝ)) ≤
      349691 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1747929 / 5000) (T := 3495859 / 10000) (Z :=
      23427 / 2000) (by norm_num only) (by norm_num only) gammaAnalyticBridge64_roots.1
      gammaAnalyticBridge64_roots.2.1 gammaAnalyticBridge64_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge64_power : (4521780 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 69 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 64 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge64_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (226089 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 226089) (x := 4521780 / 37) (H := 21828 / 25) (R :=
      1747929 / 5000) (W := 69 / 50000) (F := 292413 / 1000) (U := 349691 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge64_power (gammaAnalyticBridge64_main hGRH.riemann)
      (gammaAnalyticBridge64_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 65. -/
theorem gammaAnalyticBridge65_roots :
    ((1757997 / 5000 : ℝ) ≤ Real.sqrt (4574020 / 37 : ℝ) ∧
      Real.sqrt (4574020 / 37 : ℝ) ≤ 703199 / 2000 ∧ Real.sqrt (228701 : ℝ) ≤ 478227 / 1000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 65. -/
theorem gammaAnalyticBridge65_logs :
    Real.log (4574020 / 37 : ℝ) ≤ 469 / 40 ∧ Real.log (228701 : ℝ) ≤ 61701 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4574020 / 37) 17 20 0 (469 / 40) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 228701 18 20 0 (61701 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge65_main (hRH : RiemannHypothesis) :
    (36763 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 228701,
        Real.exp (-(n : ℝ) / (4574020 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4574020 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 206843) * ((4574020 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4574020 / 37) * (37 / 20)) + 1) / (4000 / 206843) +
        1839 / 1000 ≤
      4619357 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge65_roots.2.2]
  have hs :
    Real.sqrt ((4574020 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4574020 / 37) * (37 / 20)) +
        21 / 20 ≤
      9531 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge65_roots.2.2, gammaAnalyticBridge65_logs.2]
  have hz :
    Real.sqrt (4574020 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4574020 / 37) + 2469 / 800 ≤
      18419 / 500 := by
    linarith only [gammaAnalyticBridge65_roots.2.1, gammaAnalyticBridge65_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4574020 / 37) (y := 37 / 20) (h := 4000 / 206843) (r :=
      703199 / 2000) (e := 78619 / 500000) (p := 4619357 / 1000) (s := 9531 / 200) (z :=
      18419 / 500) (F := 36763 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge65_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4574020 / 37 : ℝ) * (37 / 20) = 228701 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge65_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4574020 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4574020 / 37 : ℝ)) ≤
      70341 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1757997 / 5000) (T := 703199 / 2000) (Z := 469 / 40)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge65_roots.1
      gammaAnalyticBridge65_roots.2.1 gammaAnalyticBridge65_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge65_power : (4574020 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 137 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 65 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge65_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (21953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (228701 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 228701) (x := 4574020 / 37) (H := 21953 / 25) (R :=
      1757997 / 5000) (W := 137 / 100000) (F := 36763 / 125) (U := 70341 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge65_power (gammaAnalyticBridge65_main hGRH.riemann)
      (gammaAnalyticBridge65_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 66. -/
theorem gammaAnalyticBridge66_roots :
    ((353613 / 1000 : ℝ) ≤ Real.sqrt (4626560 / 37 : ℝ) ∧
      Real.sqrt (4626560 / 37 : ℝ) ≤ 3536131 / 10000 ∧
      Real.sqrt (231328 : ℝ) ≤ 4809657 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 66. -/
theorem gammaAnalyticBridge66_logs :
    Real.log (4626560 / 37 : ℝ) ≤ 23473 / 2000 ∧ Real.log (231328 : ℝ) ≤ 30879 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4626560 / 37) 17 20 0 (23473 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 231328 18 20 0 (30879 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge66_main (hRH : RiemannHypothesis) :
    (59159 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 231328,
        Real.exp (-(n : ℝ) / (4626560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4626560 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 103719) * ((4626560 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4626560 / 37) * (37 / 20)) + 1) / (2000 / 103719) +
        1839 / 1000 ≤
      4659051 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge66_roots.2.2]
  have hs :
    Real.sqrt ((4626560 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4626560 / 37) * (37 / 20)) +
        21 / 20 ≤
      47813 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge66_roots.2.2, gammaAnalyticBridge66_logs.2]
  have hz :
    Real.sqrt (4626560 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4626560 / 37) + 2469 / 800 ≤
      7391 / 200 := by
    linarith only [gammaAnalyticBridge66_roots.2.1, gammaAnalyticBridge66_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4626560 / 37) (y := 37 / 20) (h := 2000 / 103719) (r :=
      3536131 / 10000) (e := 78619 / 500000) (p := 4659051 / 1000) (s := 47813 / 1000) (z :=
      7391 / 200) (F := 59159 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge66_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4626560 / 37 : ℝ) * (37 / 20) = 231328 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge66_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4626560 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4626560 / 37 : ℝ)) ≤
      176859 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 353613 / 1000) (T := 3536131 / 10000) (Z := 23473 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge66_roots.1
      gammaAnalyticBridge66_roots.2.1 gammaAnalyticBridge66_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge66_power : (4626560 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 17 / 12500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 66 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge66_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (21953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (231328 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 21953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 231328) (x := 4626560 / 37) (H := 22078 / 25) (R :=
      353613 / 1000) (W := 17 / 12500) (F := 59159 / 200) (U := 176859 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge66_power (gammaAnalyticBridge66_main hGRH.riemann)
      (gammaAnalyticBridge66_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 67. -/
theorem gammaAnalyticBridge67_roots :
    ((711253 / 2000 : ℝ) ≤ Real.sqrt (4679400 / 37 : ℝ) ∧
      Real.sqrt (4679400 / 37 : ℝ) ≤ 1778133 / 5000 ∧ Real.sqrt (233970 : ℝ) ≤ 967409 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 67. -/
theorem gammaAnalyticBridge67_logs :
    Real.log (4679400 / 37 : ℝ) ≤ 58739 / 5000 ∧ Real.log (233970 : ℝ) ≤ 12363 / 1000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4679400 / 37) 17 20 0 (58739 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 233970 18 20 0 (12363 / 1000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge67_main (hRH : RiemannHypothesis) :
    (297487 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 233970,
        Real.exp (-(n : ℝ) / (4679400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4679400 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 104013) * ((4679400 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4679400 / 37) * (37 / 20)) + 1) / (2000 / 104013) +
        1839 / 1000 ≤
      234943 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge67_roots.2.2]
  have hs :
    Real.sqrt ((4679400 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4679400 / 37) * (37 / 20)) +
        21 / 20 ≤
      47971 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge67_roots.2.2, gammaAnalyticBridge67_logs.2]
  have hz :
    Real.sqrt (4679400 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4679400 / 37) + 2469 / 800 ≤
      37071 / 1000 := by
    linarith only [gammaAnalyticBridge67_roots.2.1, gammaAnalyticBridge67_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4679400 / 37) (y := 37 / 20) (h := 2000 / 104013) (r :=
      1778133 / 5000) (e := 78619 / 500000) (p := 234943 / 50) (s := 47971 / 1000) (z :=
      37071 / 1000) (F := 297487 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge67_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4679400 / 37 : ℝ) * (37 / 20) = 233970 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge67_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4679400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4679400 / 37 : ℝ)) ≤
      355731 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 711253 / 2000) (T := 1778133 / 5000) (Z := 58739 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge67_roots.1
      gammaAnalyticBridge67_roots.2.1 gammaAnalyticBridge67_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge67_power : (4679400 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 27 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 67 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge67_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (233970 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 233970) (x := 4679400 / 37) (H := 22203 / 25) (R :=
      711253 / 2000) (W := 27 / 20000) (F := 297487 / 1000) (U := 355731 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge67_power (gammaAnalyticBridge67_main hGRH.riemann)
      (gammaAnalyticBridge67_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 68. -/
theorem gammaAnalyticBridge68_roots :
    ((3576401 / 10000 : ℝ) ≤ Real.sqrt (4732540 / 37 : ℝ) ∧
      Real.sqrt (4732540 / 37 : ℝ) ≤ 1788201 / 5000 ∧
      Real.sqrt (236627 : ℝ) ≤ 4864433 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 68. -/
theorem gammaAnalyticBridge68_logs :
    Real.log (4732540 / 37 : ℝ) ≤ 117591 / 10000 ∧ Real.log (236627 : ℝ) ≤ 123743 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4732540 / 37) 17 20 0 (117591 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 236627 18 20 0 (123743 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge68_main (hRH : RiemannHypothesis) :
    (149589 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 236627,
        Real.exp (-(n : ℝ) / (4732540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4732540 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 104307) * ((4732540 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4732540 / 37) * (37 / 20)) + 1) / (2000 / 104307) +
        1839 / 1000 ≤
      2369391 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge68_roots.2.2]
  have hs :
    Real.sqrt ((4732540 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4732540 / 37) * (37 / 20)) +
        21 / 20 ≤
      48129 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge68_roots.2.2, gammaAnalyticBridge68_logs.2]
  have hz :
    Real.sqrt (4732540 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4732540 / 37) + 2469 / 800 ≤
      37187 / 1000 := by
    linarith only [gammaAnalyticBridge68_roots.2.1, gammaAnalyticBridge68_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4732540 / 37) (y := 37 / 20) (h := 2000 / 104307) (r :=
      1788201 / 5000) (e := 78619 / 500000) (p := 2369391 / 500) (s := 48129 / 1000) (z :=
      37187 / 1000) (F := 149589 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge68_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4732540 / 37 : ℝ) * (37 / 20) = 236627 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge68_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4732540 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4732540 / 37 : ℝ)) ≤
      71549 / 200 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3576401 / 10000) (T := 1788201 / 5000) (Z :=
      117591 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge68_roots.1
      gammaAnalyticBridge68_roots.2.1 gammaAnalyticBridge68_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge68_power : (4732540 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 27 / 20000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 68 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge68_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (236627 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 236627) (x := 4732540 / 37) (H := 22328 / 25) (R :=
      3576401 / 10000) (W := 27 / 20000) (F := 149589 / 500) (U := 71549 / 200) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge68_power (gammaAnalyticBridge68_main hGRH.riemann)
      (gammaAnalyticBridge68_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 69. -/
theorem gammaAnalyticBridge69_roots :
    ((3596537 / 10000 : ℝ) ≤ Real.sqrt (4785980 / 37 : ℝ) ∧
      Real.sqrt (4785980 / 37 : ℝ) ≤ 1798269 / 5000 ∧ Real.sqrt (239299 : ℝ) ≤ 244591 / 500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 69. -/
theorem gammaAnalyticBridge69_logs :
    Real.log (4785980 / 37 : ℝ) ≤ 117703 / 10000 ∧ Real.log (239299 : ℝ) ≤ 24771 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4785980 / 37) 17 20 0 (117703 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 239299 18 20 0 (24771 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge69_main (hRH : RiemannHypothesis) :
    (30087 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 239299,
        Real.exp (-(n : ℝ) / (4785980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4785980 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 104601) * ((4785980 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4785980 / 37) * (37 / 20)) + 1) / (2000 / 104601) +
        1839 / 1000 ≤
      955763 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge69_roots.2.2]
  have hs :
    Real.sqrt ((4785980 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4785980 / 37) * (37 / 20)) +
        21 / 20 ≤
      48287 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge69_roots.2.2, gammaAnalyticBridge69_logs.2]
  have hz :
    Real.sqrt (4785980 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4785980 / 37) + 2469 / 800 ≤
      4663 / 125 := by
    linarith only [gammaAnalyticBridge69_roots.2.1, gammaAnalyticBridge69_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4785980 / 37) (y := 37 / 20) (h := 2000 / 104601) (r :=
      1798269 / 5000) (e := 78619 / 500000) (p := 955763 / 200) (s := 48287 / 1000) (z :=
      4663 / 125) (F := 30087 / 100) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge69_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4785980 / 37 : ℝ) * (37 / 20) = 239299 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge69_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4785980 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4785980 / 37 : ℝ)) ≤
      179879 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3596537 / 10000) (T := 1798269 / 5000) (Z :=
      117703 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge69_roots.1
      gammaAnalyticBridge69_roots.2.1 gammaAnalyticBridge69_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge69_power : (4785980 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 67 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 69 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge69_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (239299 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 239299) (x := 4785980 / 37) (H := 22453 / 25) (R :=
      3596537 / 10000) (W := 67 / 50000) (F := 30087 / 100) (U := 179879 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge69_power (gammaAnalyticBridge69_main hGRH.riemann)
      (gammaAnalyticBridge69_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 70. -/
theorem gammaAnalyticBridge70_roots :
    ((723333 / 2000 : ℝ) ≤ Real.sqrt (4839700 / 37 : ℝ) ∧
      Real.sqrt (4839700 / 37 : ℝ) ≤ 1808333 / 5000 ∧ Real.sqrt (241985 : ℝ) ≤ 2459599 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 70. -/
theorem gammaAnalyticBridge70_logs :
    Real.log (4839700 / 37 : ℝ) ≤ 23563 / 2000 ∧ Real.log (241985 : ℝ) ≤ 123967 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4839700 / 37) 17 20 0 (23563 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 241985 18 20 0 (123967 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge70_main (hRH : RiemannHypothesis) :
    (302561 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 241985,
        Real.exp (-(n : ℝ) / (4839700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4839700 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 209783) * ((4839700 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4839700 / 37) * (37 / 20)) + 1) / (4000 / 209783) +
        1839 / 1000 ≤
      4818947 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge70_roots.2.2]
  have hs :
    Real.sqrt ((4839700 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4839700 / 37) * (37 / 20)) +
        21 / 20 ≤
      12111 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge70_roots.2.2, gammaAnalyticBridge70_logs.2]
  have hz :
    Real.sqrt (4839700 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4839700 / 37) + 2469 / 800 ≤
      1871 / 50 := by
    linarith only [gammaAnalyticBridge70_roots.2.1, gammaAnalyticBridge70_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4839700 / 37) (y := 37 / 20) (h := 4000 / 209783) (r :=
      1808333 / 5000) (e := 78619 / 500000) (p := 4818947 / 1000) (s := 12111 / 250) (z :=
      1871 / 50) (F := 302561 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge70_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4839700 / 37 : ℝ) * (37 / 20) = 241985 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge70_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4839700 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4839700 / 37 : ℝ)) ≤
      361771 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 723333 / 2000) (T := 1808333 / 5000) (Z := 23563 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge70_roots.1
      gammaAnalyticBridge70_roots.2.1 gammaAnalyticBridge70_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge70_power : (4839700 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 133 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 70 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge70_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (241985 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 241985) (x := 4839700 / 37) (H := 22578 / 25) (R :=
      723333 / 2000) (W := 133 / 100000) (F := 302561 / 1000) (U := 361771 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge70_power (gammaAnalyticBridge70_main hGRH.riemann)
      (gammaAnalyticBridge70_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 71. -/
theorem gammaAnalyticBridge71_roots :
    ((3636801 / 10000 : ℝ) ≤ Real.sqrt (4893740 / 37 : ℝ) ∧
      Real.sqrt (4893740 / 37 : ℝ) ≤ 1818401 / 5000 ∧ Real.sqrt (244687 : ℝ) ≤ 989317 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 71. -/
theorem gammaAnalyticBridge71_logs :
    Real.log (4893740 / 37 : ℝ) ≤ 58963 / 5000 ∧ Real.log (244687 : ℝ) ≤ 62039 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4893740 / 37) 18 20 0 (58963 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 244687 18 20 0 (62039 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge71_main (hRH : RiemannHypothesis) :
    (76063 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 244687,
        Real.exp (-(n : ℝ) / (4893740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4893740 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 52591) * ((4893740 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4893740 / 37) * (37 / 20)) + 1) / (1000 / 52591) +
        1839 / 1000 ≤
      971841 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge71_roots.2.2]
  have hs :
    Real.sqrt ((4893740 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4893740 / 37) * (37 / 20)) +
        21 / 20 ≤
      48601 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge71_roots.2.2, gammaAnalyticBridge71_logs.2]
  have hz :
    Real.sqrt (4893740 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4893740 / 37) + 2469 / 800 ≤
      4692 / 125 := by
    linarith only [gammaAnalyticBridge71_roots.2.1, gammaAnalyticBridge71_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4893740 / 37) (y := 37 / 20) (h := 1000 / 52591) (r :=
      1818401 / 5000) (e := 78619 / 500000) (p := 971841 / 200) (s := 48601 / 1000) (z :=
      4692 / 125) (F := 76063 / 250) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge71_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4893740 / 37 : ℝ) * (37 / 20) = 244687 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge71_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4893740 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4893740 / 37 : ℝ)) ≤
      45473 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3636801 / 10000) (T := 1818401 / 5000) (Z :=
      58963 / 5000) (by norm_num only) (by norm_num only) gammaAnalyticBridge71_roots.1
      gammaAnalyticBridge71_roots.2.1 gammaAnalyticBridge71_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge71_power : (4893740 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 33 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 71 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge71_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (244687 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 244687) (x := 4893740 / 37) (H := 22703 / 25) (R :=
      3636801 / 10000) (W := 33 / 25000) (F := 76063 / 250) (U := 45473 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge71_power (gammaAnalyticBridge71_main hGRH.riemann)
      (gammaAnalyticBridge71_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 72. -/
theorem gammaAnalyticBridge72_roots :
    ((3656937 / 10000 : ℝ) ≤ Real.sqrt (4948080 / 37 : ℝ) ∧
      Real.sqrt (4948080 / 37 : ℝ) ≤ 1828469 / 5000 ∧
      Real.sqrt (247404 : ℝ) ≤ 4973973 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 72. -/
theorem gammaAnalyticBridge72_logs :
    Real.log (4948080 / 37 : ℝ) ≤ 29509 / 2500 ∧ Real.log (247404 : ℝ) ≤ 31047 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (4948080 / 37) 18 20 0 (29509 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 247404 18 20 0 (31047 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge72_main (hRH : RiemannHypothesis) :
    (38243 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 247404,
        Real.exp (-(n : ℝ) / (4948080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4948080 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 26369) * ((4948080 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((4948080 / 37) * (37 / 20)) + 1) / (500 / 26369) +
        1839 / 1000 ≤
      4899573 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge72_roots.2.2]
  have hs :
    Real.sqrt ((4948080 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((4948080 / 37) * (37 / 20)) +
        21 / 20 ≤
      48759 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge72_roots.2.2, gammaAnalyticBridge72_logs.2]
  have hz :
    Real.sqrt (4948080 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (4948080 / 37) + 2469 / 800 ≤
      9413 / 250 := by
    linarith only [gammaAnalyticBridge72_roots.2.1, gammaAnalyticBridge72_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 4948080 / 37) (y := 37 / 20) (h := 500 / 26369) (r :=
      1828469 / 5000) (e := 78619 / 500000) (p := 4899573 / 1000) (s := 48759 / 1000) (z :=
      9413 / 250) (F := 38243 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge72_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (4948080 / 37 : ℝ) * (37 / 20) = 247404 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge72_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (4948080 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (4948080 / 37 : ℝ)) ≤
      365797 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3656937 / 10000) (T := 1828469 / 5000) (Z :=
      29509 / 2500) (by norm_num only) (by norm_num only) gammaAnalyticBridge72_roots.1
      gammaAnalyticBridge72_roots.2.1 gammaAnalyticBridge72_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge72_power : (4948080 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 131 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 72 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge72_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (247404 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 247404) (x := 4948080 / 37) (H := 22828 / 25) (R :=
      3656937 / 10000) (W := 131 / 100000) (F := 38243 / 125) (U := 365797 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge72_power (gammaAnalyticBridge72_main hGRH.riemann)
      (gammaAnalyticBridge72_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 73. -/
theorem gammaAnalyticBridge73_roots :
    ((229817 / 625 : ℝ) ≤ Real.sqrt (5002720 / 37 : ℝ) ∧
      Real.sqrt (5002720 / 37 : ℝ) ≤ 3677073 / 10000 ∧ Real.sqrt (250136 : ℝ) ≤ 62517 / 125) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 73. -/
theorem gammaAnalyticBridge73_logs :
    Real.log (5002720 / 37 : ℝ) ≤ 59073 / 5000 ∧ Real.log (250136 : ℝ) ≤ 62149 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5002720 / 37) 18 20 0 (59073 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 250136 18 20 0 (62149 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge73_main (hRH : RiemannHypothesis) :
    (61527 / 200 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 250136,
        Real.exp (-(n : ℝ) / (5002720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5002720 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 105763) * ((5002720 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5002720 / 37) * (37 / 20)) + 1) / (2000 / 105763) +
        1839 / 1000 ≤
      2470027 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge73_roots.2.2]
  have hs :
    Real.sqrt ((5002720 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5002720 / 37) * (37 / 20)) +
        21 / 20 ≤
      12229 / 250 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge73_roots.2.2, gammaAnalyticBridge73_logs.2]
  have hz :
    Real.sqrt (5002720 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5002720 / 37) + 2469 / 800 ≤
      37767 / 1000 := by
    linarith only [gammaAnalyticBridge73_roots.2.1, gammaAnalyticBridge73_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5002720 / 37) (y := 37 / 20) (h := 2000 / 105763) (r :=
      3677073 / 10000) (e := 78619 / 500000) (p := 2470027 / 500) (s := 12229 / 250) (z :=
      37767 / 1000) (F := 61527 / 200) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge73_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5002720 / 37 : ℝ) * (37 / 20) = 250136 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge73_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5002720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5002720 / 37 : ℝ)) ≤
      367811 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 229817 / 625) (T := 3677073 / 10000) (Z := 59073 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge73_roots.1
      gammaAnalyticBridge73_roots.2.1 gammaAnalyticBridge73_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge73_power : (5002720 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 13 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 73 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge73_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (22953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (250136 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 250136) (x := 5002720 / 37) (H := 22953 / 25) (R :=
      229817 / 625) (W := 13 / 10000) (F := 61527 / 200) (U := 367811 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge73_power (gammaAnalyticBridge73_main hGRH.riemann)
      (gammaAnalyticBridge73_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 74. -/
theorem gammaAnalyticBridge74_roots :
    ((462151 / 1250 : ℝ) ≤ Real.sqrt (5057660 / 37 : ℝ) ∧
      Real.sqrt (5057660 / 37 : ℝ) ≤ 3697209 / 10000 ∧
      Real.sqrt (252883 : ℝ) ≤ 1257187 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 74. -/
theorem gammaAnalyticBridge74_logs :
    Real.log (5057660 / 37 : ℝ) ≤ 23651 / 2000 ∧ Real.log (252883 : ℝ) ≤ 124407 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5057660 / 37) 18 20 0 (23651 / 2000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 252883 18 20 0 (124407 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge74_main (hRH : RiemannHypothesis) :
    (309327 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 252883,
        Real.exp (-(n : ℝ) / (5057660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5057660 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 212107) * ((5057660 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5057660 / 37) * (37 / 20)) + 1) / (4000 / 212107) +
        1839 / 1000 ≤
      996129 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge74_roots.2.2]
  have hs :
    Real.sqrt ((5057660 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5057660 / 37) * (37 / 20)) +
        21 / 20 ≤
      49073 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge74_roots.2.2, gammaAnalyticBridge74_logs.2]
  have hz :
    Real.sqrt (5057660 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5057660 / 37) + 2469 / 800 ≤
      37883 / 1000 := by
    linarith only [gammaAnalyticBridge74_roots.2.1, gammaAnalyticBridge74_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5057660 / 37) (y := 37 / 20) (h := 4000 / 212107) (r :=
      3697209 / 10000) (e := 78619 / 500000) (p := 996129 / 200) (s := 49073 / 1000) (z :=
      37883 / 1000) (F := 309327 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge74_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5057660 / 37 : ℝ) * (37 / 20) = 252883 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge74_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5057660 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5057660 / 37 : ℝ)) ≤
      46228 / 125 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 462151 / 1250) (T := 3697209 / 10000) (Z := 23651 / 2000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge74_roots.1
      gammaAnalyticBridge74_roots.2.1 gammaAnalyticBridge74_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge74_power : (5057660 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 13 / 10000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 74 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge74_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (22953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (252883 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 22953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 252883) (x := 5057660 / 37) (H := 23078 / 25) (R :=
      462151 / 1250) (W := 13 / 10000) (F := 309327 / 1000) (U := 46228 / 125) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge74_power (gammaAnalyticBridge74_main hGRH.riemann)
      (gammaAnalyticBridge74_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 75. -/
theorem gammaAnalyticBridge75_roots :
    ((232334 / 625 : ℝ) ≤ Real.sqrt (5112900 / 37 : ℝ) ∧
      Real.sqrt (5112900 / 37 : ℝ) ≤ 743469 / 2000 ∧ Real.sqrt (255645 : ℝ) ≤ 1011227 / 2000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 75. -/
theorem gammaAnalyticBridge75_logs :
    Real.log (5112900 / 37 : ℝ) ≤ 29591 / 2500 ∧ Real.log (255645 : ℝ) ≤ 31129 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5112900 / 37) 18 20 0 (29591 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 255645 18 20 0 (31129 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge75_main (hRH : RiemannHypothesis) :
    (155509 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 255645,
        Real.exp (-(n : ℝ) / (5112900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5112900 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 212681) * ((5112900 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5112900 / 37) * (37 / 20)) + 1) / (4000 / 212681) +
        1839 / 1000 ≤
      5021347 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge75_roots.2.2]
  have hs :
    Real.sqrt ((5112900 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5112900 / 37) * (37 / 20)) +
        21 / 20 ≤
      4923 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge75_roots.2.2, gammaAnalyticBridge75_logs.2]
  have hz :
    Real.sqrt (5112900 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5112900 / 37) + 2469 / 800 ≤
      37999 / 1000 := by
    linarith only [gammaAnalyticBridge75_roots.2.1, gammaAnalyticBridge75_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5112900 / 37) (y := 37 / 20) (h := 4000 / 212681) (r :=
      743469 / 2000) (e := 78619 / 500000) (p := 5021347 / 1000) (s := 4923 / 100) (z :=
      37999 / 1000) (F := 155509 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge75_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5112900 / 37 : ℝ) * (37 / 20) = 255645 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge75_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5112900 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5112900 / 37 : ℝ)) ≤
      371837 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 232334 / 625) (T := 743469 / 2000) (Z := 29591 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge75_roots.1
      gammaAnalyticBridge75_roots.2.1 gammaAnalyticBridge75_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge75_power : (5112900 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 129 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 75 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge75_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (255645 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 255645) (x := 5112900 / 37) (H := 23203 / 25) (R :=
      232334 / 625) (W := 129 / 100000) (F := 155509 / 500) (U := 371837 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge75_power (gammaAnalyticBridge75_main hGRH.riemann)
      (gammaAnalyticBridge75_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 76. -/
theorem gammaAnalyticBridge76_roots :
    ((93437 / 250 : ℝ) ≤ Real.sqrt (5168440 / 37 : ℝ) ∧
      Real.sqrt (5168440 / 37 : ℝ) ≤ 3737481 / 10000 ∧
      Real.sqrt (258422 : ℝ) ≤ 5083523 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 76. -/
theorem gammaAnalyticBridge76_logs :
    Real.log (5168440 / 37 : ℝ) ≤ 14809 / 1250 ∧ Real.log (258422 : ℝ) ≤ 7789 / 625 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5168440 / 37) 18 20 0 (14809 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 258422 18 20 0 (7789 / 625) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge76_main (hRH : RiemannHypothesis) :
    (31271 / 100 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 258422,
        Real.exp (-(n : ℝ) / (5168440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5168440 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 106631) * ((5168440 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5168440 / 37) * (37 / 20)) + 1) / (2000 / 106631) +
        1839 / 1000 ≤
      2531079 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge76_roots.2.2]
  have hs :
    Real.sqrt ((5168440 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5168440 / 37) * (37 / 20)) +
        21 / 20 ≤
      24693 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge76_roots.2.2, gammaAnalyticBridge76_logs.2]
  have hz :
    Real.sqrt (5168440 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5168440 / 37) + 2469 / 800 ≤
      19057 / 500 := by
    linarith only [gammaAnalyticBridge76_roots.2.1, gammaAnalyticBridge76_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5168440 / 37) (y := 37 / 20) (h := 2000 / 106631) (r :=
      3737481 / 10000) (e := 78619 / 500000) (p := 2531079 / 500) (s := 24693 / 500) (z :=
      19057 / 500) (F := 31271 / 100) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge76_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5168440 / 37 : ℝ) * (37 / 20) = 258422 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge76_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5168440 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5168440 / 37 : ℝ)) ≤
      373851 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 93437 / 250) (T := 3737481 / 10000) (Z := 14809 / 1250)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge76_roots.1
      gammaAnalyticBridge76_roots.2.1 gammaAnalyticBridge76_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge76_power : (5168440 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 4 / 3125 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 76 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge76_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (258422 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 258422) (x := 5168440 / 37) (H := 23328 / 25) (R :=
      93437 / 250) (W := 4 / 3125) (F := 31271 / 100) (U := 373851 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge76_power (gammaAnalyticBridge76_main hGRH.riemann)
      (gammaAnalyticBridge76_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 77. -/
theorem gammaAnalyticBridge77_roots :
    ((469701 / 1250 : ℝ) ≤ Real.sqrt (5224260 / 37 : ℝ) ∧
      Real.sqrt (5224260 / 37 : ℝ) ≤ 3757609 / 10000 ∧
      Real.sqrt (261213 : ℝ) ≤ 5110901 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 77. -/
theorem gammaAnalyticBridge77_logs :
    Real.log (5224260 / 37 : ℝ) ≤ 5929 / 500 ∧ Real.log (261213 : ℝ) ≤ 124731 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5224260 / 37) 18 20 0 (5929 / 500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 261213 18 20 0 (124731 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge77_main (hRH : RiemannHypothesis) :
    (314401 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 261213,
        Real.exp (-(n : ℝ) / (5224260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5224260 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (1000 / 53459) * ((5224260 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5224260 / 37) * (37 / 20)) + 1) / (1000 / 53459) +
        1839 / 1000 ≤
      2551533 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge77_roots.2.2]
  have hs :
    Real.sqrt ((5224260 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5224260 / 37) * (37 / 20)) +
        21 / 20 ≤
      49543 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge77_roots.2.2, gammaAnalyticBridge77_logs.2]
  have hz :
    Real.sqrt (5224260 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5224260 / 37) + 2469 / 800 ≤
      3823 / 100 := by
    linarith only [gammaAnalyticBridge77_roots.2.1, gammaAnalyticBridge77_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5224260 / 37) (y := 37 / 20) (h := 1000 / 53459) (r :=
      3757609 / 10000) (e := 78619 / 500000) (p := 2551533 / 500) (s := 49543 / 1000) (z :=
      3823 / 100) (F := 314401 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge77_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5224260 / 37 : ℝ) * (37 / 20) = 261213 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge77_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5224260 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5224260 / 37 : ℝ)) ≤
      375863 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 469701 / 1250) (T := 3757609 / 10000) (Z := 5929 / 500)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge77_roots.1
      gammaAnalyticBridge77_roots.2.1 gammaAnalyticBridge77_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge77_power : (5224260 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 127 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 77 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge77_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (261213 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 261213) (x := 5224260 / 37) (H := 23453 / 25) (R :=
      469701 / 1250) (W := 127 / 100000) (F := 314401 / 1000) (U := 375863 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge77_power (gammaAnalyticBridge77_main hGRH.riemann)
      (gammaAnalyticBridge77_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 78. -/
theorem gammaAnalyticBridge78_roots :
    ((236109 / 625 : ℝ) ≤ Real.sqrt (5280400 / 37 : ℝ) ∧
      Real.sqrt (5280400 / 37 : ℝ) ≤ 755549 / 2000 ∧ Real.sqrt (264020 : ℝ) ≤ 321143 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 78. -/
theorem gammaAnalyticBridge78_logs :
    Real.log (5280400 / 37 : ℝ) ≤ 59343 / 5000 ∧ Real.log (264020 : ℝ) ≤ 62419 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5280400 / 37) 18 20 0 (59343 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 264020 19 20 0 (62419 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge78_main (hRH : RiemannHypothesis) :
    (316093 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 264020,
        Real.exp (-(n : ℝ) / (5280400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5280400 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 214403) * ((5280400 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5280400 / 37) * (37 / 20)) + 1) / (4000 / 214403) +
        1839 / 1000 ≤
      5144099 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge78_roots.2.2]
  have hs :
    Real.sqrt ((5280400 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5280400 / 37) * (37 / 20)) +
        21 / 20 ≤
      497 / 10 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge78_roots.2.2, gammaAnalyticBridge78_logs.2]
  have hz :
    Real.sqrt (5280400 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5280400 / 37) + 2469 / 800 ≤
      7669 / 200 := by
    linarith only [gammaAnalyticBridge78_roots.2.1, gammaAnalyticBridge78_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5280400 / 37) (y := 37 / 20) (h := 4000 / 214403) (r :=
      755549 / 2000) (e := 78619 / 500000) (p := 5144099 / 1000) (s := 497 / 10) (z := 7669 / 200)
      (F := 316093 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge78_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5280400 / 37 : ℝ) * (37 / 20) = 264020 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge78_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5280400 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5280400 / 37 : ℝ)) ≤
      377877 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 236109 / 625) (T := 755549 / 2000) (Z := 59343 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge78_roots.1
      gammaAnalyticBridge78_roots.2.1 gammaAnalyticBridge78_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge78_power : (5280400 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 127 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 78 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge78_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (264020 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 264020) (x := 5280400 / 37) (H := 23578 / 25) (R :=
      236109 / 625) (W := 127 / 100000) (F := 316093 / 1000) (U := 377877 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge78_power (gammaAnalyticBridge78_main hGRH.riemann)
      (gammaAnalyticBridge78_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 79. -/
theorem gammaAnalyticBridge79_roots :
    ((3797879 / 10000 : ℝ) ≤ Real.sqrt (5336840 / 37 : ℝ) ∧
      Real.sqrt (5336840 / 37 : ℝ) ≤ 94947 / 250 ∧ Real.sqrt (266842 : ℝ) ≤ 1291419 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 79. -/
theorem gammaAnalyticBridge79_logs :
    Real.log (5336840 / 37 : ℝ) ≤ 118793 / 10000 ∧ Real.log (266842 : ℝ) ≤ 24989 / 2000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5336840 / 37) 18 20 0 (118793 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 266842 19 20 0 (24989 / 2000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge79_main (hRH : RiemannHypothesis) :
    (39723 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 266842,
        Real.exp (-(n : ℝ) / (5336840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5336840 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 214977) * ((5336840 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5336840 / 37) * (37 / 20)) + 1) / (4000 / 214977) +
        1839 / 1000 ≤
      129631 / 25 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge79_roots.2.2]
  have hs :
    Real.sqrt ((5336840 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5336840 / 37) * (37 / 20)) +
        21 / 20 ≤
      6232 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge79_roots.2.2, gammaAnalyticBridge79_logs.2]
  have hz :
    Real.sqrt (5336840 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5336840 / 37) + 2469 / 800 ≤
      38461 / 1000 := by
    linarith only [gammaAnalyticBridge79_roots.2.1, gammaAnalyticBridge79_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5336840 / 37) (y := 37 / 20) (h := 4000 / 214977) (r :=
      94947 / 250) (e := 78619 / 500000) (p := 129631 / 25) (s := 6232 / 125) (z := 38461 / 1000)
      (F := 39723 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge79_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5336840 / 37 : ℝ) * (37 / 20) = 266842 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge79_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5336840 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5336840 / 37 : ℝ)) ≤
      37989 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3797879 / 10000) (T := 94947 / 250) (Z := 118793 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge79_roots.1
      gammaAnalyticBridge79_roots.2.1 gammaAnalyticBridge79_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge79_power : (5336840 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 63 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 79 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge79_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (266842 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 266842) (x := 5336840 / 37) (H := 23703 / 25) (R :=
      3797879 / 10000) (W := 63 / 50000) (F := 39723 / 125) (U := 37989 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge79_power (gammaAnalyticBridge79_main hGRH.riemann)
      (gammaAnalyticBridge79_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 80. -/
theorem gammaAnalyticBridge80_roots :
    ((763603 / 2000 : ℝ) ≤ Real.sqrt (5393580 / 37 : ℝ) ∧
      Real.sqrt (5393580 / 37 : ℝ) ≤ 238626 / 625 ∧ Real.sqrt (269679 : ℝ) ≤ 5193063 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 80. -/
theorem gammaAnalyticBridge80_logs :
    Real.log (5393580 / 37 : ℝ) ≤ 118899 / 10000 ∧ Real.log (269679 : ℝ) ≤ 2501 / 200 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5393580 / 37) 18 20 0 (118899 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 269679 19 20 0 (2501 / 200) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge80_main (hRH : RiemannHypothesis) :
    (79869 / 250 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 269679,
        Real.exp (-(n : ℝ) / (5393580 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5393580 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (500 / 26943) * ((5393580 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5393580 / 37) * (37 / 20)) + 1) / (500 / 26943) +
        1839 / 1000 ≤
      522649 / 100 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge80_roots.2.2]
  have hs :
    Real.sqrt ((5393580 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5393580 / 37) * (37 / 20)) +
        21 / 20 ≤
      50013 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge80_roots.2.2, gammaAnalyticBridge80_logs.2]
  have hz :
    Real.sqrt (5393580 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5393580 / 37) + 2469 / 800 ≤
      4822 / 125 := by
    linarith only [gammaAnalyticBridge80_roots.2.1, gammaAnalyticBridge80_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5393580 / 37) (y := 37 / 20) (h := 500 / 26943) (r :=
      238626 / 625) (e := 78619 / 500000) (p := 522649 / 100) (s := 50013 / 1000) (z := 4822 / 125)
      (F := 79869 / 250) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge80_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5393580 / 37 : ℝ) * (37 / 20) = 269679 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge80_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5393580 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5393580 / 37 : ℝ)) ≤
      381903 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 763603 / 2000) (T := 238626 / 625) (Z := 118899 / 10000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge80_roots.1
      gammaAnalyticBridge80_roots.2.1 gammaAnalyticBridge80_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge80_power : (5393580 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 1 / 800 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 80 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge80_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (269679 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 269679) (x := 5393580 / 37) (H := 23828 / 25) (R :=
      763603 / 2000) (W := 1 / 800) (F := 79869 / 250) (U := 381903 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge80_power (gammaAnalyticBridge80_main hGRH.riemann)
      (gammaAnalyticBridge80_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 81. -/
theorem gammaAnalyticBridge81_roots :
    ((3838151 / 10000 : ℝ) ≤ Real.sqrt (5450620 / 37 : ℝ) ∧
      Real.sqrt (5450620 / 37 : ℝ) ≤ 479769 / 1250 ∧ Real.sqrt (272531 : ℝ) ≤ 5220451 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 81. -/
theorem gammaAnalyticBridge81_logs :
    Real.log (5450620 / 37 : ℝ) ≤ 29751 / 2500 ∧ Real.log (272531 : ℝ) ≤ 31289 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5450620 / 37) 18 20 0 (29751 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 272531 19 20 0 (31289 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge81_main (hRH : RiemannHypothesis) :
    (321167 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 272531,
        Real.exp (-(n : ℝ) / (5450620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5450620 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (4000 / 216111) * ((5450620 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5450620 / 37) * (37 / 20)) + 1) / (4000 / 216111) +
        1839 / 1000 ≤
      105357 / 20 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge81_roots.2.2]
  have hs :
    Real.sqrt ((5450620 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5450620 / 37) * (37 / 20)) +
        21 / 20 ≤
      50169 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge81_roots.2.2, gammaAnalyticBridge81_logs.2]
  have hz :
    Real.sqrt (5450620 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5450620 / 37) + 2469 / 800 ≤
      38691 / 1000 := by
    linarith only [gammaAnalyticBridge81_roots.2.1, gammaAnalyticBridge81_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5450620 / 37) (y := 37 / 20) (h := 4000 / 216111) (r :=
      479769 / 1250) (e := 78619 / 500000) (p := 105357 / 20) (s := 50169 / 1000) (z :=
      38691 / 1000) (F := 321167 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge81_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5450620 / 37 : ℝ) * (37 / 20) = 272531 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge81_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5450620 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5450620 / 37 : ℝ)) ≤
      383917 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3838151 / 10000) (T := 479769 / 1250) (Z := 29751 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge81_roots.1
      gammaAnalyticBridge81_roots.2.1 gammaAnalyticBridge81_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge81_power : (5450620 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 31 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 81 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge81_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (23953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (272531 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 272531) (x := 5450620 / 37) (H := 23953 / 25) (R :=
      3838151 / 10000) (W := 31 / 25000) (F := 321167 / 1000) (U := 383917 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge81_power (gammaAnalyticBridge81_main hGRH.riemann)
      (gammaAnalyticBridge81_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 82. -/
theorem gammaAnalyticBridge82_roots :
    ((1929143 / 5000 : ℝ) ≤ Real.sqrt (5507960 / 37 : ℝ) ∧
      Real.sqrt (5507960 / 37 : ℝ) ≤ 3858287 / 10000 ∧
      Real.sqrt (275398 : ℝ) ≤ 2623919 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 82. -/
theorem gammaAnalyticBridge82_logs :
    Real.log (5507960 / 37 : ℝ) ≤ 29777 / 2500 ∧ Real.log (275398 : ℝ) ≤ 6263 / 500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5507960 / 37) 18 20 0 (29777 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 275398 19 20 0 (6263 / 500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge82_main (hRH : RiemannHypothesis) :
    (322859 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 275398,
        Real.exp (-(n : ℝ) / (5507960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5507960 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 108339) * ((5507960 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5507960 / 37) * (37 / 20)) + 1) / (2000 / 108339) +
        1839 / 1000 ≤
      5309317 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge82_roots.2.2]
  have hs :
    Real.sqrt ((5507960 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5507960 / 37) * (37 / 20)) +
        21 / 20 ≤
      2013 / 40 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge82_roots.2.2, gammaAnalyticBridge82_logs.2]
  have hz :
    Real.sqrt (5507960 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5507960 / 37) + 2469 / 800 ≤
      19403 / 500 := by
    linarith only [gammaAnalyticBridge82_roots.2.1, gammaAnalyticBridge82_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5507960 / 37) (y := 37 / 20) (h := 2000 / 108339) (r :=
      3858287 / 10000) (e := 78619 / 500000) (p := 5309317 / 1000) (s := 2013 / 40) (z :=
      19403 / 500) (F := 322859 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge82_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5507960 / 37 : ℝ) * (37 / 20) = 275398 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge82_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5507960 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5507960 / 37 : ℝ)) ≤
      38593 / 100 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1929143 / 5000) (T := 3858287 / 10000) (Z :=
      29777 / 2500) (by norm_num only) (by norm_num only) gammaAnalyticBridge82_roots.1
      gammaAnalyticBridge82_roots.2.1 gammaAnalyticBridge82_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge82_power : (5507960 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 31 / 25000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 82 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge82_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (23953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24078 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (275398 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 23953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 275398) (x := 5507960 / 37) (H := 24078 / 25) (R :=
      1929143 / 5000) (W := 31 / 25000) (F := 322859 / 1000) (U := 38593 / 100) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge82_power (gammaAnalyticBridge82_main hGRH.riemann)
      (gammaAnalyticBridge82_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 83. -/
theorem gammaAnalyticBridge83_roots :
    ((1939211 / 5000 : ℝ) ≤ Real.sqrt (5565600 / 37 : ℝ) ∧
      Real.sqrt (5565600 / 37 : ℝ) ≤ 3878423 / 10000 ∧
      Real.sqrt (278280 : ℝ) ≤ 2637613 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 83. -/
theorem gammaAnalyticBridge83_logs :
    Real.log (5565600 / 37 : ℝ) ≤ 29803 / 2500 ∧ Real.log (278280 : ℝ) ≤ 31341 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5565600 / 37) 18 20 0 (29803 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 278280 19 20 0 (31341 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge83_main (hRH : RiemannHypothesis) :
    (324551 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 278280,
        Real.exp (-(n : ℝ) / (5565600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5565600 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 43449) * ((5565600 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5565600 / 37) * (37 / 20)) + 1) / (800 / 43449) +
        1839 / 1000 ≤
      5350893 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge83_roots.2.2]
  have hs :
    Real.sqrt ((5565600 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5565600 / 37) * (37 / 20)) +
        21 / 20 ≤
      50481 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge83_roots.2.2, gammaAnalyticBridge83_logs.2]
  have hz :
    Real.sqrt (5565600 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5565600 / 37) + 2469 / 800 ≤
      38921 / 1000 := by
    linarith only [gammaAnalyticBridge83_roots.2.1, gammaAnalyticBridge83_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5565600 / 37) (y := 37 / 20) (h := 800 / 43449) (r :=
      3878423 / 10000) (e := 78619 / 500000) (p := 5350893 / 1000) (s := 50481 / 1000) (z :=
      38921 / 1000) (F := 324551 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge83_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5565600 / 37 : ℝ) * (37 / 20) = 278280 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge83_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5565600 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5565600 / 37 : ℝ)) ≤
      387943 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1939211 / 5000) (T := 3878423 / 10000) (Z :=
      29803 / 2500) (by norm_num only) (by norm_num only) gammaAnalyticBridge83_roots.1
      gammaAnalyticBridge83_roots.2.1 gammaAnalyticBridge83_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge83_power : (5565600 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 123 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 83 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge83_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24078 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24203 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (278280 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24078 / 25)]
  apply
    reject_03_of_analytic_caps (B := 278280) (x := 5565600 / 37) (H := 24203 / 25) (R :=
      1939211 / 5000) (W := 123 / 100000) (F := 324551 / 1000) (U := 387943 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge83_power (gammaAnalyticBridge83_main hGRH.riemann)
      (gammaAnalyticBridge83_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 84. -/
theorem gammaAnalyticBridge84_roots :
    ((3898551 / 10000 : ℝ) ≤ Real.sqrt (5623520 / 37 : ℝ) ∧
      Real.sqrt (5623520 / 37 : ℝ) ≤ 487319 / 1250 ∧ Real.sqrt (281176 : ℝ) ≤ 1325651 / 2500) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 84. -/
theorem gammaAnalyticBridge84_logs :
    Real.log (5623520 / 37 : ℝ) ≤ 29829 / 2500 ∧ Real.log (281176 : ℝ) ≤ 31367 / 2500 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5623520 / 37) 18 20 0 (29829 / 2500) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 281176 19 20 0 (31367 / 2500) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge84_main (hRH : RiemannHypothesis) :
    (163121 / 500 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 281176,
        Real.exp (-(n : ℝ) / (5623520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5623520 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 43561) * ((5623520 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5623520 / 37) * (37 / 20)) + 1) / (800 / 43561) +
        1839 / 1000 ≤
      5392563 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge84_roots.2.2]
  have hs :
    Real.sqrt ((5623520 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5623520 / 37) * (37 / 20)) +
        21 / 20 ≤
      50637 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge84_roots.2.2, gammaAnalyticBridge84_logs.2]
  have hz :
    Real.sqrt (5623520 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5623520 / 37) + 2469 / 800 ≤
      9759 / 250 := by
    linarith only [gammaAnalyticBridge84_roots.2.1, gammaAnalyticBridge84_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5623520 / 37) (y := 37 / 20) (h := 800 / 43561) (r :=
      487319 / 1250) (e := 78619 / 500000) (p := 5392563 / 1000) (s := 50637 / 1000) (z :=
      9759 / 250) (F := 163121 / 500) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge84_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5623520 / 37 : ℝ) * (37 / 20) = 281176 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge84_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5623520 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5623520 / 37 : ℝ)) ≤
      97489 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3898551 / 10000) (T := 487319 / 1250) (Z := 29829 / 2500)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge84_roots.1
      gammaAnalyticBridge84_roots.2.1 gammaAnalyticBridge84_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge84_power : (5623520 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 61 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 84 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge84_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24203 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24328 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (281176 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24203 / 25)]
  apply
    reject_03_of_analytic_caps (B := 281176) (x := 5623520 / 37) (H := 24328 / 25) (R :=
      3898551 / 10000) (W := 61 / 50000) (F := 163121 / 500) (U := 97489 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge84_power (gammaAnalyticBridge84_main hGRH.riemann)
      (gammaAnalyticBridge84_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 85. -/
theorem gammaAnalyticBridge85_roots :
    ((3918687 / 10000 : ℝ) ≤ Real.sqrt (5681760 / 37 : ℝ) ∧
      Real.sqrt (5681760 / 37 : ℝ) ≤ 244918 / 625 ∧ Real.sqrt (284088 : ℝ) ≤ 5329991 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 85. -/
theorem gammaAnalyticBridge85_logs :
    Real.log (5681760 / 37 : ℝ) ≤ 119419 / 10000 ∧ Real.log (284088 : ℝ) ≤ 125571 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5681760 / 37) 18 20 0 (119419 / 10000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 284088 19 20 0 (125571 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge85_main (hRH : RiemannHypothesis) :
    (327933 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 284088,
        Real.exp (-(n : ℝ) / (5681760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5681760 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 43673) * ((5681760 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5681760 / 37) * (37 / 20)) + 1) / (800 / 43673) +
        1839 / 1000 ≤
      1086871 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge85_roots.2.2]
  have hs :
    Real.sqrt ((5681760 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5681760 / 37) * (37 / 20)) +
        21 / 20 ≤
      50793 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge85_roots.2.2, gammaAnalyticBridge85_logs.2]
  have hz :
    Real.sqrt (5681760 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5681760 / 37) + 2469 / 800 ≤
      39151 / 1000 := by
    linarith only [gammaAnalyticBridge85_roots.2.1, gammaAnalyticBridge85_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5681760 / 37) (y := 37 / 20) (h := 800 / 43673) (r :=
      244918 / 625) (e := 78619 / 500000) (p := 1086871 / 200) (s := 50793 / 1000) (z :=
      39151 / 1000) (F := 327933 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge85_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5681760 / 37 : ℝ) * (37 / 20) = 284088 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge85_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5681760 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5681760 / 37 : ℝ)) ≤
      391969 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3918687 / 10000) (T := 244918 / 625) (Z :=
      119419 / 10000) (by norm_num only) (by norm_num only) gammaAnalyticBridge85_roots.1
      gammaAnalyticBridge85_roots.2.1 gammaAnalyticBridge85_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge85_power : (5681760 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 121 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 85 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge85_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24328 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24453 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (284088 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24328 / 25)]
  apply
    reject_03_of_analytic_caps (B := 284088) (x := 5681760 / 37) (H := 24453 / 25) (R :=
      3918687 / 10000) (W := 121 / 100000) (F := 327933 / 1000) (U := 391969 / 1000) hn ho hc hGRH
      hL (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only)
      (by norm_num only) hhi gammaAnalyticBridge85_power (gammaAnalyticBridge85_main hGRH.riemann)
      (gammaAnalyticBridge85_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 86. -/
theorem gammaAnalyticBridge86_roots :
    ((1969411 / 5000 : ℝ) ≤ Real.sqrt (5740300 / 37 : ℝ) ∧
      Real.sqrt (5740300 / 37 : ℝ) ≤ 3938823 / 10000 ∧
      Real.sqrt (287015 : ℝ) ≤ 5357379 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 86. -/
theorem gammaAnalyticBridge86_logs :
    Real.log (5740300 / 37 : ℝ) ≤ 59761 / 5000 ∧ Real.log (287015 : ℝ) ≤ 125673 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5740300 / 37) 18 20 0 (59761 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 287015 19 20 0 (125673 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge86_main (hRH : RiemannHypothesis) :
    (2637 / 8 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 287015,
        Real.exp (-(n : ℝ) / (5740300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5740300 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (160 / 8757) * ((5740300 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5740300 / 37) * (37 / 20)) + 1) / (160 / 8757) +
        1839 / 1000 ≤
      1095251 / 200 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge86_roots.2.2]
  have hs :
    Real.sqrt ((5740300 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5740300 / 37) * (37 / 20)) +
        21 / 20 ≤
      50949 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge86_roots.2.2, gammaAnalyticBridge86_logs.2]
  have hz :
    Real.sqrt (5740300 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5740300 / 37) + 2469 / 800 ≤
      19633 / 500 := by
    linarith only [gammaAnalyticBridge86_roots.2.1, gammaAnalyticBridge86_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5740300 / 37) (y := 37 / 20) (h := 160 / 8757) (r :=
      3938823 / 10000) (e := 78619 / 500000) (p := 1095251 / 200) (s := 50949 / 1000) (z :=
      19633 / 500) (F := 2637 / 8) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge86_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5740300 / 37 : ℝ) * (37 / 20) = 287015 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge86_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5740300 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5740300 / 37 : ℝ)) ≤
      196991 / 500 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1969411 / 5000) (T := 3938823 / 10000) (Z :=
      59761 / 5000) (by norm_num only) (by norm_num only) gammaAnalyticBridge86_roots.1
      gammaAnalyticBridge86_roots.2.1 gammaAnalyticBridge86_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge86_power : (5740300 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 121 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 86 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge86_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24453 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24578 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (287015 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24453 / 25)]
  apply
    reject_03_of_analytic_caps (B := 287015) (x := 5740300 / 37) (H := 24578 / 25) (R :=
      1969411 / 5000) (W := 121 / 100000) (F := 2637 / 8) (U := 196991 / 500) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge86_power (gammaAnalyticBridge86_main hGRH.riemann)
      (gammaAnalyticBridge86_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 87. -/
theorem gammaAnalyticBridge87_roots :
    ((1979479 / 5000 : ℝ) ≤ Real.sqrt (5799140 / 37 : ℝ) ∧
      Real.sqrt (5799140 / 37 : ℝ) ≤ 3958959 / 10000 ∧
      Real.sqrt (289957 : ℝ) ≤ 2692383 / 5000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 87. -/
theorem gammaAnalyticBridge87_logs :
    Real.log (5799140 / 37 : ℝ) ≤ 14953 / 1250 ∧ Real.log (289957 : ℝ) ≤ 5031 / 400 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5799140 / 37) 18 20 0 (14953 / 1250) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 289957 19 20 0 (5031 / 400) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge87_main (hRH : RiemannHypothesis) :
    (331317 / 1000 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 289957,
        Real.exp (-(n : ℝ) / (5799140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5799140 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 43897) * ((5799140 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5799140 / 37) * (37 / 20)) + 1) / (800 / 43897) +
        1839 / 1000 ≤
      275913 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge87_roots.2.2]
  have hs :
    Real.sqrt ((5799140 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5799140 / 37) * (37 / 20)) +
        21 / 20 ≤
      6388 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge87_roots.2.2, gammaAnalyticBridge87_logs.2]
  have hz :
    Real.sqrt (5799140 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5799140 / 37) + 2469 / 800 ≤
      39381 / 1000 := by
    linarith only [gammaAnalyticBridge87_roots.2.1, gammaAnalyticBridge87_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5799140 / 37) (y := 37 / 20) (h := 800 / 43897) (r :=
      3958959 / 10000) (e := 78619 / 500000) (p := 275913 / 50) (s := 6388 / 125) (z :=
      39381 / 1000) (F := 331317 / 1000) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge87_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5799140 / 37 : ℝ) * (37 / 20) = 289957 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge87_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5799140 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5799140 / 37 : ℝ)) ≤
      98999 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1979479 / 5000) (T := 3958959 / 10000) (Z :=
      14953 / 1250) (by norm_num only) (by norm_num only) gammaAnalyticBridge87_roots.1
      gammaAnalyticBridge87_roots.2.1 gammaAnalyticBridge87_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge87_power : (5799140 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 3 / 2500 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 87 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge87_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24578 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24703 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (289957 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24578 / 25)]
  apply
    reject_03_of_analytic_caps (B := 289957) (x := 5799140 / 37) (H := 24703 / 25) (R :=
      1979479 / 5000) (W := 3 / 2500) (F := 331317 / 1000) (U := 98999 / 250) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge87_power (gammaAnalyticBridge87_main hGRH.riemann)
      (gammaAnalyticBridge87_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 88. -/
theorem gammaAnalyticBridge88_roots :
    ((1989547 / 5000 : ℝ) ≤ Real.sqrt (5858280 / 37 : ℝ) ∧
      Real.sqrt (5858280 / 37 : ℝ) ≤ 795819 / 2000 ∧ Real.sqrt (292914 : ℝ) ≤ 5412153 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 88. -/
theorem gammaAnalyticBridge88_logs :
    Real.log (5858280 / 37 : ℝ) ≤ 4789 / 400 ∧ Real.log (292914 : ℝ) ≤ 125877 / 10000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5858280 / 37) 18 20 0 (4789 / 400) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 292914 19 20 0 (125877 / 10000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge88_main (hRH : RiemannHypothesis) :
    (41626 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 292914,
        Real.exp (-(n : ℝ) / (5858280 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5858280 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (800 / 44009) * ((5858280 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5858280 / 37) * (37 / 20)) + 1) / (800 / 44009) +
        1839 / 1000 ≤
      5560373 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge88_roots.2.2]
  have hs :
    Real.sqrt ((5858280 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5858280 / 37) * (37 / 20)) +
        21 / 20 ≤
      2563 / 50 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge88_roots.2.2, gammaAnalyticBridge88_logs.2]
  have hz :
    Real.sqrt (5858280 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5858280 / 37) + 2469 / 800 ≤
      7899 / 200 := by
    linarith only [gammaAnalyticBridge88_roots.2.1, gammaAnalyticBridge88_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5858280 / 37) (y := 37 / 20) (h := 800 / 44009) (r :=
      795819 / 2000) (e := 78619 / 500000) (p := 5560373 / 1000) (s := 2563 / 50) (z := 7899 / 200)
      (F := 41626 / 125) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge88_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5858280 / 37 : ℝ) * (37 / 20) = 292914 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge88_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5858280 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5858280 / 37 : ℝ)) ≤
      398009 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 1989547 / 5000) (T := 795819 / 2000) (Z := 4789 / 400)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge88_roots.1
      gammaAnalyticBridge88_roots.2.1 gammaAnalyticBridge88_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge88_power : (5858280 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 119 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 88 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge88_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24703 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24828 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (292914 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24703 / 25)]
  apply
    reject_03_of_analytic_caps (B := 292914) (x := 5858280 / 37) (H := 24828 / 25) (R :=
      1989547 / 5000) (W := 119 / 100000) (F := 41626 / 125) (U := 398009 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge88_power (gammaAnalyticBridge88_main hGRH.riemann)
      (gammaAnalyticBridge88_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 89. -/
theorem gammaAnalyticBridge89_roots :
    ((3999229 / 10000 : ℝ) ≤ Real.sqrt (5917720 / 37 : ℝ) ∧
      Real.sqrt (5917720 / 37 : ℝ) ≤ 399923 / 1000 ∧ Real.sqrt (295886 : ℝ) ≤ 5439541 / 10000) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 89. -/
theorem gammaAnalyticBridge89_logs :
    Real.log (5917720 / 37 : ℝ) ≤ 59913 / 5000 ∧ Real.log (295886 : ℝ) ≤ 62989 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5917720 / 37) 18 20 0 (59913 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 295886 19 20 0 (62989 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge89_main (hRH : RiemannHypothesis) :
    (3347 / 10 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 295886,
        Real.exp (-(n : ℝ) / (5917720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5917720 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 110299) * ((5917720 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5917720 / 37) * (37 / 20)) + 1) / (2000 / 110299) +
        1839 / 1000 ≤
      2801297 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge89_roots.2.2]
  have hs :
    Real.sqrt ((5917720 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5917720 / 37) * (37 / 20)) +
        21 / 20 ≤
      6427 / 125 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge89_roots.2.2, gammaAnalyticBridge89_logs.2]
  have hz :
    Real.sqrt (5917720 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5917720 / 37) + 2469 / 800 ≤
      3961 / 100 := by
    linarith only [gammaAnalyticBridge89_roots.2.1, gammaAnalyticBridge89_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5917720 / 37) (y := 37 / 20) (h := 2000 / 110299) (r :=
      399923 / 1000) (e := 78619 / 500000) (p := 2801297 / 500) (s := 6427 / 125) (z := 3961 / 100)
      (F := 3347 / 10) (by norm_num only) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) gammaAnalyticBridge89_roots.2.1 gamma_analytic100_exp hp hs hz
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5917720 / 37 : ℝ) * (37 / 20) = 295886 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge89_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5917720 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5917720 / 37 : ℝ)) ≤
      400023 / 1000 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 3999229 / 10000) (T := 399923 / 1000) (Z := 59913 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge89_roots.1
      gammaAnalyticBridge89_roots.2.1 gammaAnalyticBridge89_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge89_power : (5917720 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 119 / 100000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 89 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge89_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24828 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (24953 / 25 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (295886 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24828 / 25)]
  apply
    reject_03_of_analytic_caps (B := 295886) (x := 5917720 / 37) (H := 24953 / 25) (R :=
      3999229 / 10000) (W := 119 / 100000) (F := 3347 / 10) (U := 400023 / 1000) hn ho hc hGRH hL
      (by norm_num only) (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only)
      hhi gammaAnalyticBridge89_power (gammaAnalyticBridge89_main hGRH.riemann)
      (gammaAnalyticBridge89_principal hGRH.riemann)
  norm_num only

/-- Exact root caps for analytic cell 90. -/
theorem gammaAnalyticBridge90_roots :
    ((803873 / 2000 : ℝ) ≤ Real.sqrt (5977460 / 37 : ℝ) ∧
      Real.sqrt (5977460 / 37 : ℝ) ≤ 2009683 / 5000 ∧ Real.sqrt (298873 : ℝ) ≤ 341683 / 625) := by
  constructor
  · apply Real.le_sqrt_of_sq_le
    norm_num only
  · constructor <;> apply (Real.sqrt_le_iff).2 <;> constructor <;> norm_num only

/-- Exact Taylor checks bound the two logarithms for analytic cell 90. -/
theorem gammaAnalyticBridge90_logs :
    Real.log (5977460 / 37 : ℝ) ≤ 59963 / 5000 ∧ Real.log (298873 : ℝ) ≤ 63039 / 5000 := by
  have hc1 : Analysis.rationalLogIntervalCheck (5977460 / 37) 18 20 0 (59963 / 5000) = true := by
    decide +kernel
  have hc2 : Analysis.rationalLogIntervalCheck 298873 19 20 0 (63039 / 5000) = true := by
    decide +kernel
  have h1 := (Analysis.rationalLogIntervalCheck_sound hc1).2
  have h2 := (Analysis.rationalLogIntervalCheck_sound hc2).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h1 h2
  exact ⟨h1, h2⟩

/-- Under RH the finite Gamma main sum exceeds its rational cell cap. -/
theorem gammaAnalyticBridge90_main (hRH : RiemannHypothesis) :
    (42049 / 125 : ℝ) ≤
      ∑ n ∈ Finset.Ioc (0 : ℕ) 298873,
        Real.exp (-(n : ℝ) / (5977460 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5977460 / 37 : ℝ) := by
  have hp :
    (10 / 19 : ℝ) * (2000 / 110579) * ((5977460 / 37) * (37 / 20)) +
        (231 / 2500 : ℝ) * (Real.sqrt ((5977460 / 37) * (37 / 20)) + 1) / (2000 / 110579) +
        1839 / 1000 ≤
      2822459 / 500 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge90_roots.2.2]
  have hs :
    Real.sqrt ((5977460 / 37 : ℝ) * (37 / 20)) / 20 +
        (1839 / 1000 : ℝ) * Real.log ((5977460 / 37) * (37 / 20)) +
        21 / 20 ≤
      51571 / 1000 := by
    norm_num only at ⊢
    linarith only [gammaAnalyticBridge90_roots.2.2, gammaAnalyticBridge90_logs.2]
  have hz :
    Real.sqrt (5977460 / 37 : ℝ) / 20 + (5517 / 4000 : ℝ) * Real.log (5977460 / 37) + 2469 / 800 ≤
      9931 / 250 := by
    linarith only [gammaAnalyticBridge90_roots.2.1, gammaAnalyticBridge90_logs.1]
  have h :=
    finite_gamma_lower_of_caps hRH (x := 5977460 / 37) (y := 37 / 20) (h := 2000 / 110579) (r :=
      2009683 / 5000) (e := 78619 / 500000) (p := 2822459 / 500) (s := 51571 / 1000) (z :=
      9931 / 250) (F := 42049 / 125) (by norm_num only) (by norm_num only) (by norm_num only)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge90_roots.2.1 gamma_analytic100_exp hp
      hs hz (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [show (5977460 / 37 : ℝ) * (37 / 20) = 298873 by norm_num only,
    Nat.floor_ofNat] at h
  exact h

/-- Under RH the principal Gamma series is below its rational cap. -/
theorem gammaAnalyticBridge90_principal (hRH : RiemannHypothesis) :
    (∑' n : ℕ,
        Real.exp (-(n : ℝ) / (5977460 / 37)) * ArithmeticFunction.vonMangoldt n /
          Real.sqrt (5977460 / 37 : ℝ)) ≤
      100509 / 250 := by
  apply
    gamma_principal_upper_rh_cap hRH (R := 803873 / 2000) (T := 2009683 / 5000) (Z := 59963 / 5000)
      (by norm_num only) (by norm_num only) gammaAnalyticBridge90_roots.1
      gammaAnalyticBridge90_roots.2.1 gammaAnalyticBridge90_logs.1 (by norm_num only)
  norm_num only

/-- An exact integer-power comparison bounds the negative power. -/
theorem gammaAnalyticBridge90_power : (5977460 / 37 : ℝ) ^ (-9 / 16 : ℝ) ≤ 59 / 50000 := by
  apply
    Analysis.rpow_neg_nat_div_le_of_power_bound (by norm_num only) (by norm_num only) 9 16
      (by decide)
  norm_num only

/-- Under GRH, analytic cell 90 supplies a `3/10` rejecting prime. -/
theorem gammaAnalyticBridge90_witness {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hlo : (24953 / 25 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ (1000 : ℝ)) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (298873 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 := by
    nlinarith only [hlo, sq_nonneg (Real.log n - 24953 / 25)]
  apply
    reject_03_of_analytic_caps (B := 298873) (x := 5977460 / 37) (H := 1000) (R := 803873 / 2000)
      (W := 59 / 50000) (F := 42049 / 125) (U := 100509 / 250) hn ho hc hGRH hL (by norm_num only)
      (by decide) hcut (by norm_num only) (by norm_num only) (by norm_num only) hhi
      gammaAnalyticBridge90_power (gammaAnalyticBridge90_main hGRH.riemann)
      (gammaAnalyticBridge90_principal hGRH.riemann)
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
