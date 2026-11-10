/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalUpper109
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLower109
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegralCaps

/-! # A uniform triple cell at cutoff 109 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational endpoint estimates certify the uniform-cell budget through logarithm 23.79. -/
theorem quarter_uniform_budget109 :
    quarterUniformBudget 109 (2379 / 100) (5119 / 2500) (35102 / 10000) (7 / 10) ≤
      4 * (26617 / 10000 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 109 7 32 0 (9383 / 2000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 109 0 (157587 / 25000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 109 ≤ (9383 / 2000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (109 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (157587 / 25000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hlog0 : 0 ≤ Real.log 109 := Real.log_nonneg (by norm_num only)
  have hz0 : 0 ≤ (21 / 8 : ℝ) + Real.log 109 := by linarith only [hlog0]
  have hz : (21 / 8 : ℝ) + Real.log 109 ≤ (21 / 8 : ℝ) + 9383 / 2000 := by linarith only [hlog]
  have he : Real.exp (-((27 / 25 : ℝ) * (21 / 8))) ≤ (588 / 10000 : ℝ) := by
    convert refined_exp_neg_unit_le using 1
    norm_num only
  have hq0 : 0 ≤ (109 : ℝ) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hep := mul_le_mul he hpow hq0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hp0 : 0 ≤ (588 / 10000 : ℝ) * (157587 / 25000000) := by norm_num only
  have hpower := pow_le_pow_left₀ hz0 hz 5
  have hmain := mul_le_mul hep hpower (pow_nonneg hz0 5) hp0
  have hmain' :=
    mul_le_mul_of_nonneg_left hmain
      (show (0 : ℝ) ≤ (2 * (2379 / 100 : ℝ)) * ((27 / 25 : ℝ) ^ 5 / 120) by norm_num only)
  dsimp only [quarterUniformBudget]
  nlinarith only [hmain']

/-- Under GRH and the stated reflected Euler bound, every uniform Korselt triple
in the interval has a quarter-square rejecting prime. The cutoff and all numerical estimates are
certified by the independent finite-support row computations. -/
theorem quarter_uniform_2262_2379_of_reflected {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 109 ≤ (7 / 10 : ℝ))
    (hlo : (1131 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2379 / 100) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (109 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hlo]
  exact
    quarter_uniform_of_bounds hn ho hu hGRH (X := 109) (U := 2379 / 100) (S := 26617 / 10000) (P :=
      5119 / 2500) (F := 35102 / 10000) (H := 7 / 10) (by norm_num only) hH hhi hcut
      quarter_principal_lower109_explicit quarter_euler_lower109_explicit
      quarter_principal_upper109_explicit quarter_uniform_budget109

/-- The six paper moment caps imply the reflected Euler bound needed by the
cutoff-109 cell. Rational logarithm and power certificates bound the scale factor. -/
theorem quarter_reflected109_of_moments (hm : QuarterMomentBounds) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 109 ≤ (7 / 10 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 109 7 32 0 (9383 / 2000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 109 0 (157587 / 25000000) 27
              25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 109 ≤ (9383 / 2000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (109 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (157587 / 25000000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hz0 : 0 ≤ (21 / 8 : ℝ) + Real.log 109 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 109 by norm_num only)
    linarith only [h]
  have hz : (21 / 8 : ℝ) + Real.log 109 ≤ (21 / 8 : ℝ) + 9383 / 2000 := by linarith only [hlog]
  have he : Real.exp (-((27 / 25 : ℝ) * (21 / 8))) ≤ (588 / 10000 : ℝ) := by
    convert refined_exp_neg_unit_le using 1
    norm_num only
  have hq0 : 0 ≤ (109 : ℝ) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hep := mul_le_mul he hpow hq0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hp0 : 0 ≤ (588 / 10000 : ℝ) * (157587 / 25000000) := by norm_num only
  have hpoly := quarter_moment_polynomial_le hz0 hz
  have hpoly0 : 0 ≤ quarterMomentPolynomial ((21 / 8 : ℝ) + Real.log 109) := by
    dsimp only [quarterMomentPolynomial]
    positivity
  have hproduct := mul_le_mul hep hpoly hpoly0 hp0
  have hbound :=
    mul_le_mul_of_nonneg_left hproduct (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 / 120 by norm_num only)
  have hnum :
    (27 / 25 : ℝ) ^ 5 / 120 *
        ((588 / 10000 : ℝ) * (157587 / 25000000) *
          quarterMomentPolynomial ((21 / 8 : ℝ) + 9383 / 2000)) ≤
      7 / 10 := by
    norm_num only [quarterMomentPolynomial]
  have h := quarter_reflected_of_moments (x := 109) (by norm_num only) hm
  nlinarith only [h, hbound, hnum]

/-- The paper's six moment bounds and GRH yield the quarter-square witness
for every uniform Korselt triple in the cutoff-109 interval. -/
theorem quarter_uniform_2262_2379_of_moments {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hm : QuarterMomentBounds) (hlo : (1131 / 50 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 2379 / 100) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  exact
    quarter_uniform_2262_2379_of_reflected hn ho hu hGRH (quarter_reflected109_of_moments hm) hlo
      hhi

/-- Under GRH, the six explicit power-logarithm tail integrals are sufficient
for the cutoff-109 uniform triple cell. All finite numerical inputs are proved. -/
theorem quarter_uniform_2262_2379_of_integrals {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hi : QuarterMomentIntegralBounds) (hlo : (1131 / 50 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 2379 / 100) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  exact
    quarter_uniform_2262_2379_of_moments hn ho hu hGRH
      (quarter_moment_bounds_of_integrals hGRH.riemann hi) hlo hhi

/-- Under GRH, every uniform Korselt triple with logarithm between 22.62
and 23.79 has a rejecting prime below the quarter-square bound. The six
moment caps, finite principal sum, Euler prefix and full principal bound
are all supplied by kernel-checked certificates. -/
theorem quarter_uniform_2262_2379 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (1131 / 50 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 2379 / 100) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  exact quarter_uniform_2262_2379_of_integrals hn ho hu hGRH quarter_moment_integral_bounds hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
