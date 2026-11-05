/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.DualScaleCore
public import PseudoPrime.PrimeTestBounds.MillerRabin.ReducedGaussianBounds

/-! # Rational dual-scale and Gaussian witnesses for five fixed profiles -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A rational logarithm certificate supplies the core's entrance bound. -/
theorem dual_log_040 : (2993 / 100 : ℝ) ≤ Real.log ((2 / 5 : ℝ) * (5000000 : ℝ) ^ 2) := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 10000000000000 44 32 (2993 / 100) 31 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  norm_num only
  exact hc

/-- This rational dual-scale core certifies the gap above its entrance. -/
noncomputable def dualCore040 : DualScaleCore where
  C := 2 / 5
  T := 5000000
  a := 126491 / 200000
  v := 2236
  ell := 2993 / 100
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  logLower := dual_log_040
  margin := by norm_num only [max_eq_right, max_eq_left]

/-- This Gaussian profile certifies the exceptional triple case at the same cutoff. -/
noncomputable def dualGaussian040 : ReducedGaussianProfile where
  C := 2 / 5
  T := 5000000
  gamma := 87287 / 200000
  v := 2236
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- Under GRH, every odd composite above this entrance has a rejecting prime below
this quadratic cutoff. The dual core and Gaussian profile cover all factor structures. -/
theorem prime_witness_dual040 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (5000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (2 / 5 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_dualCore dualCore040 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness dualGaussian040 ho hsf ht hK hU hGRH hL

/-- A rational logarithm certificate supplies the core's entrance bound. -/
theorem dual_log_036 : (1601 / 50 : ℝ) ≤ Real.log ((9 / 25 : ℝ) * (15000000 : ℝ) ^ 2) := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 81000000000000 47 32 (1601 / 50) 34 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  norm_num only
  exact hc

/-- This rational dual-scale core certifies the gap above its entrance. -/
noncomputable def dualCore036 : DualScaleCore where
  C := 9 / 25
  T := 15000000
  a := 3 / 5
  v := 3872
  ell := 1601 / 50
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  logLower := dual_log_036
  margin := by norm_num only [max_eq_right, max_eq_left]

/-- This Gaussian profile certifies the exceptional triple case at the same cutoff. -/
noncomputable def dualGaussian036 : ReducedGaussianProfile where
  C := 9 / 25
  T := 15000000
  gamma := 414039 / 1000000
  v := 3872
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- Under GRH, every odd composite above this entrance has a rejecting prime below
this quadratic cutoff. The dual core and Gaussian profile cover all factor structures. -/
theorem prime_witness_dual036 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (15000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (9 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_dualCore dualCore036 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness dualGaussian036 ho hsf ht hK hU hGRH hL

/-- A rational logarithm certificate supplies the core's entrance bound. -/
theorem dual_log_033 : (833 / 25 : ℝ) ≤ Real.log ((33 / 100 : ℝ) * (30000000 : ℝ) ^ 2) := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 297000000000000 49 32 (833 / 25) 35 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  norm_num only
  exact hc

/-- This rational dual-scale core certifies the gap above its entrance. -/
noncomputable def dualCore033 : DualScaleCore where
  C := 33 / 100
  T := 30000000
  a := 71807 / 125000
  v := 5477
  ell := 833 / 25
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  logLower := dual_log_033
  margin := by norm_num only [max_eq_right, max_eq_left]

/-- This Gaussian profile certifies the exceptional triple case at the same cutoff. -/
noncomputable def dualGaussian033 : ReducedGaussianProfile where
  C := 33 / 100
  T := 30000000
  gamma := 99103 / 250000
  v := 5477
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- Under GRH, every odd composite above this entrance has a rejecting prime below
this quadratic cutoff. The dual core and Gaussian profile cover all factor structures. -/
theorem prime_witness_dual033 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (30000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (33 / 100 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_dualCore dualCore033 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness dualGaussian033 ho hsf ht hK hU hGRH hL

/-- A rational logarithm certificate supplies the core's entrance bound. -/
theorem dual_log_031 : (866 / 25 : ℝ) ≤ Real.log ((31 / 100 : ℝ) * (60000000 : ℝ) ^ 2) := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 1116000000000000 50 32 (866 / 25) 36 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  norm_num only
  exact hc

/-- This rational dual-scale core certifies the gap above its entrance. -/
noncomputable def dualCore031 : DualScaleCore where
  C := 31 / 100
  T := 60000000
  a := 69597 / 125000
  v := 7745
  ell := 866 / 25
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  logLower := dual_log_031
  margin := by norm_num only [max_eq_right, max_eq_left]

/-- This Gaussian profile certifies the exceptional triple case at the same cutoff. -/
noncomputable def dualGaussian031 : ReducedGaussianProfile where
  C := 31 / 100
  T := 60000000
  gamma := 96053 / 250000
  v := 7745
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- Under GRH, every odd composite above this entrance has a rejecting prime below
this quadratic cutoff. The dual core and Gaussian profile cover all factor structures. -/
theorem prime_witness_dual031 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (60000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (31 / 100 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_dualCore dualCore031 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness dualGaussian031 ho hsf ht hK hU hGRH hL

/-- A rational logarithm certificate supplies the core's entrance bound. -/
theorem dual_log_029 : (178 / 5 : ℝ) ≤ Real.log ((29 / 100 : ℝ) * (100000000 : ℝ) ^ 2) := by
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 2900000000000000 52 32 (178 / 5) 37 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  norm_num only
  exact hc

/-- This rational dual-scale core certifies the gap above its entrance. -/
noncomputable def dualCore029 : DualScaleCore where
  C := 29 / 100
  T := 100000000
  a := 134629 / 250000
  v := 10000
  ell := 178 / 5
  entry := by norm_num only
  root := by norm_num only
  localBudget := by norm_num only
  square := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  logLower := dual_log_029
  margin := by norm_num only [max_eq_right, max_eq_left]

/-- This Gaussian profile certifies the exceptional triple case at the same cutoff. -/
noncomputable def dualGaussian029 : ReducedGaussianProfile where
  C := 29 / 100
  T := 100000000
  gamma := 371611 / 1000000
  v := 10000
  entry := by norm_num only
  gammaLower := by norm_num only
  lower := by norm_num only
  upper := by norm_num only
  fourth := by norm_num only [and_self]
  margin := by norm_num only

/-- Under GRH, every odd composite above this entrance has a rejecting prime below
this quadratic cutoff. The dual core and Gaussian profile cover all factor structures. -/
theorem prime_witness_dual029 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (100000000 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (29 / 100 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply exists_prime_dualCore dualCore029 hn ho hc hGRH hL
  intro hsf ht hK hU
  exact reducedGaussian_cardWitness dualGaussian029 ho hsf ht hK hU hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
