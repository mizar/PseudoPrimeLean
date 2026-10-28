/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMRPrefixComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMR240WitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMRRefinedWitnessBounds

/-! # Pointwise Gaussian MR envelopes with certified starting ranges -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The minimum of the two Gamma prefix candidates and B6.
All three witness bounds apply from scale 240, where this minimum equals B6
by `gaussianMRPrefixEnvelope_eq`. The definition retains the candidate interfaces. -/
noncomputable def gaussianMRPrefixEnvelope (L : ℝ) : ℝ :=
  min (analysis13GammaPrefixEnvelope L) (Analysis.gaussianMR6Bound L)

/-- For L>=240, the three-candidate prefix minimum equals B6.
Both Gamma bounds are strictly larger on this half-line. The equality simplifies
the public envelope without changing the existing minimum definition. -/
theorem gaussianMRPrefixEnvelope_eq {L : ℝ} (hL : 240 ≤ L) :
    gaussianMRPrefixEnvelope L = Analysis.gaussianMR6Bound L := by
  exact
    min_eq_right (le_min (gaussianMR6_lt_gammaClipped hL).le (gaussianMR6_lt_gammaIndex100 hL).le)

/-- Add the separate refined Gaussian bound to the log240 envelope.
The new candidate is valid only from scale 300. Below that range this definition
has no witness claim. -/
noncomputable def gaussianMRRefinedEnvelope (L : ℝ) : ℝ :=
  min (gaussianMRPrefixEnvelope L) (Analysis.gaussianMRRefinedBound L)

/-- Add the existing 0.282924 L^2 candidate to the refined envelope.
Its witness theorem retains the original decimal input threshold. -/
noncomputable def gaussianMRLargeEnvelope (L : ℝ) : ℝ :=
  min (gaussianMRRefinedEnvelope L) ((282924 / 1000000 : ℝ) * L ^ 2)

/-- From logarithmic scale 240, the least rejecting prime obeys the prefix minimum.
Combine the two-Gamma witness bound with the B6 witness bound. The resulting
minimum equals B6 throughout this range by `gaussianMRPrefixEnvelope_eq`. -/
theorem exists_least_witness_gaussianMRPrefix {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ gaussianMRPrefixEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    least_prime_witness_bound_min
      (exists_least_prime_witness_le_analysis13GammaPrefixEnvelope hnOdd hcomp hGRH hL)
      (exists_least_witness_gaussianMR6_log240 hnOdd hcomp hGRH hL)

/-- From logarithmic scale 300, the least rejecting prime also obeys the refined minimum.
The certified index-four, small-index and large-index branches all use the same new cutoff.
This is the least-witness interface before simplifying comparisons. -/
theorem exists_least_witness_gaussianMRRefinedEnvelope {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ gaussianMRRefinedEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  exact
    least_prime_witness_bound_min
      (exists_least_witness_gaussianMRPrefix hnOdd hcomp hGRH (by linarith only [hL]))
      (exists_least_witness_gaussianMRRefined hnOdd hcomp hGRH hL)

/-- For L>=300 the refined formula is below the complete log240 prefix envelope.
Combine its strict improvement over B6 with the previously proved Gamma comparisons.
This justifies simplifying the refined minimum on its whole applicable half-line. -/
theorem gaussianMRRefined_lt_prefixEnvelope {L : ℝ} (hL : 300 ≤ L) :
    Analysis.gaussianMRRefinedBound L < gaussianMRPrefixEnvelope L := by
  have hnew := Analysis.gaussianMRRefined_lt_gaussianMR6 hL
  have hold := gaussianMR6Bound_lt_min_prefixUpper_gaussianMR18Bound hL
  have hGamma :=
    (lt_of_lt_of_le hold (min_le_right _ _)).trans (gaussianMR18Bound_lt_gammaClippedUpper hL)
  have hPrefix := lt_of_lt_of_le hold (min_le_left _ _)
  exact lt_min (lt_min (hnew.trans hGamma) (hnew.trans hPrefix)) hnew

/-- For L>=300 the refined envelope is exactly the new refined Gaussian formula.
Use the strict half-line comparison with every retained candidate. -/
theorem gaussianMRRefinedEnvelope_eq {L : ℝ} (hL : 300 ≤ L) :
    gaussianMRRefinedEnvelope L = Analysis.gaussianMRRefinedBound L := by
  exact min_eq_right (gaussianMRRefined_lt_prefixEnvelope hL).le

/-- For L>=300 the large-scale candidate minimum equals its coefficient branch.
The refined bound is above 0.3 L^2, while 0.282924 is smaller.
This algebraic comparison does not extend the coefficient witness theorem's input range. -/
theorem gaussianMRLargeEnvelope_eq {L : ℝ} (hL : 300 ≤ L) :
    gaussianMRLargeEnvelope L = (282924 / 1000000 : ℝ) * L ^ 2 := by
  have hc :=
    mul_lt_mul_of_pos_right (by norm_num only : (282924 / 1000000 : ℝ) < 3 / 10)
      (sq_pos_of_pos (by linarith only [hL] : 0 < L))
  rw [gaussianMRLargeEnvelope, gaussianMRRefinedEnvelope_eq hL]
  exact min_eq_right (hc.trans (Analysis.gaussianMRRefined_local hL)).le

/-- Above the unchanged decimal threshold, the least rejecting prime obeys the full minimum.
Use the old coefficient witness theorem and the proved envelope equality. -/
theorem exists_least_witness_gaussianMRLarge {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 9565217391305 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ gaussianMRLargeEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  rw [gaussianMRLargeEnvelope_eq
      (by
        have h := log_ge_triangular_large_index_of_decimal hN
        linarith only [h])]
  exact exists_least_prime_witness_le_0282924 hnOdd hcomp hGRH hN

/-- The public pointwise envelope selects the large-scale coefficient branch at its original
input threshold, the refined formula from log n>=300, and the three-candidate minimum below 300.
Its least-witness theorem assumes only GRH, odd compositeness and log n>=240. -/
noncomputable def gaussianMRWitnessEnvelope (n : ℕ) : ℝ :=
  if 10 ^ 9565217391305 ≤ n then gaussianMRLargeEnvelope (Real.log n)
  else
    if 300 ≤ Real.log n then gaussianMRRefinedEnvelope (Real.log n)
    else gaussianMRPrefixEnvelope (Real.log n)

/-- For 240<=log n<300, the public pointwise envelope equals B6.
The logarithmic upper bound excludes the huge-input branch, and the half-line
prefix equality simplifies the remaining minimum. No primality or GRH is needed. -/
theorem gaussianMRWitnessEnvelope_eq240 {n : ℕ} (hL : 240 ≤ Real.log n) (hU : Real.log n < 300) :
    gaussianMRWitnessEnvelope n = Analysis.gaussianMR6Bound (Real.log n) := by
  have hN : ¬10 ^ 9565217391305 ≤ n := by
    intro h
    have hlog := log_ge_triangular_large_index_of_decimal h
    linarith only [hlog, hU]
  simp only [gaussianMRWitnessEnvelope, ite_eq_right hN, ite_eq_right (not_le.mpr hU),
    gaussianMRPrefixEnvelope_eq hL]

/-- For every odd composite with log n>=240, GRH gives a least prime rejecting strong MR
below the public pointwise envelope. Split only at the certified input thresholds.
This combines both new Gaussian ranges while preserving the existing huge-scale coefficient. -/
theorem exists_least_witness_gaussianMR_envelope {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ gaussianMRWitnessEnvelope n ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  by_cases hN : 10 ^ 9565217391305 ≤ n
  · rw [gaussianMRWitnessEnvelope, ite_eq_left hN]
    exact exists_least_witness_gaussianMRLarge hnOdd hcomp hGRH hN
  · rw [gaussianMRWitnessEnvelope, ite_eq_right hN]
    by_cases hs : 300 ≤ Real.log n
    · rw [ite_eq_left hs]
      exact exists_least_witness_gaussianMRRefinedEnvelope hnOdd hcomp hGRH hs
    · rw [ite_eq_right hs]
      exact exists_least_witness_gaussianMRPrefix hnOdd hcomp hGRH hL

end PseudoPrime.PrimeTestBounds.MillerRabin
