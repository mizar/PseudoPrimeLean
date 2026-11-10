/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalUpper59
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLower59
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMomentIntegralCaps

/-! # A uniform triple cell at cutoff 59 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Rational endpoint estimates certify the uniform-cell budget through logarithm 15.9963. -/
theorem quarter_uniform_budget59 :
    quarterUniformBudget 59 (159963 / 10000) (8967 / 5000) (24891 / 10000) (259 / 250) ≤
      4 * (18359 / 10000 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 59 6 32 0 (40777 / 10000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 59 0 (76447 / 6250000) 27 25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 59 ≤ (40777 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (59 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (76447 / 6250000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hlog0 : 0 ≤ Real.log 59 := Real.log_nonneg (by norm_num only)
  have hz0 : 0 ≤ (21 / 8 : ℝ) + Real.log 59 := by linarith only [hlog0]
  have hz : (21 / 8 : ℝ) + Real.log 59 ≤ (21 / 8 : ℝ) + 40777 / 10000 := by linarith only [hlog]
  have he : Real.exp (-((27 / 25 : ℝ) * (21 / 8))) ≤ (588 / 10000 : ℝ) := by
    convert refined_exp_neg_unit_le using 1
    norm_num only
  have hq0 : 0 ≤ (59 : ℝ) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hep := mul_le_mul he hpow hq0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hp0 : 0 ≤ (588 / 10000 : ℝ) * (76447 / 6250000) := by norm_num only
  have hpower := pow_le_pow_left₀ hz0 hz 5
  have hmain := mul_le_mul hep hpower (pow_nonneg hz0 5) hp0
  have hmain' :=
    mul_le_mul_of_nonneg_left hmain
      (show (0 : ℝ) ≤ (2 * (159963 / 10000 : ℝ)) * ((27 / 25 : ℝ) ^ 5 / 120) by norm_num only)
  dsimp only [quarterUniformBudget]
  nlinarith only [hmain']

/-- Under GRH and the stated reflected Euler bound, every uniform Korselt triple
in the interval has a quarter-square rejecting prime. The cutoff and all numerical estimates are
certified by the independent finite-support row computations. -/
theorem quarter_uniform_154413_159963_of_reflected {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hH : refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 59 ≤ (259 / 250 : ℝ))
    (hlo : (154413 / 10000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 159963 / 10000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  have hcut : (59 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 := by nlinarith only [hlo]
  exact
    quarter_uniform_of_bounds hn ho hu hGRH (X := 59) (U := 159963 / 10000) (S := 18359 / 10000)
      (P := 8967 / 5000) (F := 24891 / 10000) (H := 259 / 250) (by norm_num only) hH hhi hcut
      quarter_principal_lower59_explicit quarter_euler_lower59_explicit
      quarter_principal_upper59_explicit quarter_uniform_budget59

/-- The six paper moment caps imply the reflected Euler bound needed by the
cutoff-59 cell. Rational logarithm and power certificates bound the scale factor. -/
theorem quarter_reflected59_of_moments (hm : QuarterMomentBounds) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) 59 ≤ (259 / 250 : ℝ) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 59 6 32 0 (40777 / 10000) = true from by
          decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound
        (show
          AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck 59 0 (76447 / 6250000) 27 25 =
            true
          from by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hl hp
  have hlog : Real.log 59 ≤ (40777 / 10000 : ℝ) := by
    norm_num only at hl ⊢
    exact hl
  have hpow : (59 : ℝ) ^ (-(27 / 25 : ℝ)) ≤ (76447 / 6250000 : ℝ) := by
    norm_num only at hp ⊢
    exact hp
  have hz0 : 0 ≤ (21 / 8 : ℝ) + Real.log 59 := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ 59 by norm_num only)
    linarith only [h]
  have hz : (21 / 8 : ℝ) + Real.log 59 ≤ (21 / 8 : ℝ) + 40777 / 10000 := by linarith only [hlog]
  have he : Real.exp (-((27 / 25 : ℝ) * (21 / 8))) ≤ (588 / 10000 : ℝ) := by
    convert refined_exp_neg_unit_le using 1
    norm_num only
  have hq0 : 0 ≤ (59 : ℝ) ^ (-(27 / 25 : ℝ)) := Real.rpow_nonneg (by norm_num only) _
  have hep := mul_le_mul he hpow hq0 (by norm_num only : (0 : ℝ) ≤ 588 / 10000)
  have hp0 : 0 ≤ (588 / 10000 : ℝ) * (76447 / 6250000) := by norm_num only
  have hpoly := quarter_moment_polynomial_le hz0 hz
  have hpoly0 : 0 ≤ quarterMomentPolynomial ((21 / 8 : ℝ) + Real.log 59) := by
    dsimp only [quarterMomentPolynomial]
    positivity
  have hproduct := mul_le_mul hep hpoly hpoly0 hp0
  have hbound :=
    mul_le_mul_of_nonneg_left hproduct (show (0 : ℝ) ≤ (27 / 25 : ℝ) ^ 5 / 120 by norm_num only)
  have hnum :
    (27 / 25 : ℝ) ^ 5 / 120 *
        ((588 / 10000 : ℝ) * (76447 / 6250000) *
          quarterMomentPolynomial ((21 / 8 : ℝ) + 40777 / 10000)) ≤
      259 / 250 := by
    norm_num only [quarterMomentPolynomial]
  have h := quarter_reflected_of_moments (x := 59) (by norm_num only) hm
  nlinarith only [h, hbound, hnum]

/-- The paper's six moment bounds and GRH yield the quarter-square witness
for every uniform Korselt triple in the cutoff-59 interval. -/
theorem quarter_uniform_154413_159963_of_moments {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hm : QuarterMomentBounds) (hlo : (154413 / 10000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 159963 / 10000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  exact
    quarter_uniform_154413_159963_of_reflected hn ho hu hGRH (quarter_reflected59_of_moments hm) hlo
      hhi

/-- Under GRH, the six explicit power-logarithm tail integrals are sufficient
for the cutoff-59 uniform triple cell. All finite numerical inputs are proved. -/
theorem quarter_uniform_154413_159963_of_integrals {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hi : QuarterMomentIntegralBounds) (hlo : (154413 / 10000 : ℝ) ≤ Real.log n)
    (hhi : Real.log n ≤ 159963 / 10000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  exact
    quarter_uniform_154413_159963_of_moments hn ho hu hGRH
      (quarter_moment_bounds_of_integrals hGRH.riemann hi) hlo hhi

/-- Under GRH, every uniform Korselt triple with logarithm between 15.4413
and 15.9963 has a rejecting prime below the quarter-square bound. The six
moment caps, finite principal sum, Euler prefix and full principal bound
are all supplied by kernel-checked certificates. -/
theorem quarter_uniform_154413_159963 {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hu : UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hlo : (154413 / 10000 : ℝ) ≤ Real.log n) (hhi : Real.log n ≤ 159963 / 10000) :
    ∃ l : ℕ,
      l.Prime ∧
        (l : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (l : ZMod n) := by
  exact
    quarter_uniform_154413_159963_of_integrals hn ho hu hGRH quarter_moment_integral_bounds hlo hhi

end PseudoPrime.PrimeTestBounds.MillerRabin
