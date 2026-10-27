/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LeastWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaLinearCutoffCompletion
public import PseudoPrime.PrimeTestBounds.MillerRabin.TriangularWitnessBounds

/-! # Analysis13 upper-envelope candidates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A natural number with logarithm at least 240 is greater than one. -/
theorem nat_gt_one_of_log_ge_240 {n : ℕ} (hL : 240 ≤ Real.log n) : 1 < n := by
  have hn0 : 0 < n := by
    by_contra hnot
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hnz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hnlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hn0)
  have hn1R : (1 : ℝ) < (n : ℝ) := by linarith only [hL, hnlog]
  exact Nat.cast_lt.mp (by simpa only [Nat.cast_one] using hn1R)

/-- Pointwise minimum of the existing clipped Gamma and the retained-prefix
index-100 Gamma bounds, both applicable from scale 240. -/
noncomputable def analysis13GammaPrefixEnvelope (L : ℝ) : ℝ :=
  min (gammaClippedUpper L) (gammaIndex100PrefixUpper L)

/-- From logarithmic scale 300, the retained-prefix index-100 envelope is
strictly above the constant-6 Gaussian coefficient bound. -/
theorem gaussianMR6_coefficient_lt_gammaIndex100PrefixUpper {L : ℝ} (hL : 300 ≤ L) :
    (15123 / 25000 : ℝ) * L ^ 2 < gammaIndex100PrefixUpper L := by
  let c : ℝ := (11783423 / 25000000) / (91 / 100)
  have hLpos : 0 < L := by linarith only [hL]
  have hcpos : 0 < c := by
    dsimp only [c]
    positivity
  have hcoef : 15123 / 25000 < (99 / 40 : ℝ) * c ^ 2 := by
    dsimp only [c]
    norm_num only
  have hrad0 := gammaPrefix100Radius_lower_mu_six (by linarith only [hL] : 240 ≤ L)
  have hrad1 := gammaPrefix100Radius_lower_mu_fourteen_fifths (by linarith only [hL] : 270 ≤ L)
  have hrad0sq : c ^ 2 * L ^ 2 ≤ gammaPrefix100Radius L (203 / 50) ^ 2 := by
    have hbase : c * L ≤ gammaPrefix100Radius L (203 / 50) := by linarith only [hrad0]
    have hcl : 0 ≤ c * L := le_of_lt (mul_pos hcpos hLpos)
    calc
      c ^ 2 * L ^ 2 = (c * L) ^ 2 := by ring
      _ ≤ gammaPrefix100Radius L (203 / 50) ^ 2 := (sq_le_sq₀ hcl (le_trans hcl hbase)).2 hbase
  have hrad1sq : c ^ 2 * L ^ 2 ≤ gammaPrefix100Radius L (28493 / 5000) ^ 2 := by
    have hbase : c * L ≤ gammaPrefix100Radius L (28493 / 5000) := by linarith only [hrad1]
    have hcl : 0 ≤ c * L := le_of_lt (mul_pos hcpos hLpos)
    calc
      c ^ 2 * L ^ 2 = (c * L) ^ 2 := by ring
      _ ≤ gammaPrefix100Radius L (28493 / 5000) ^ 2 := (sq_le_sq₀ hcl (le_trans hcl hbase)).2 hbase
  have hbound0 :
    (15123 / 25000 : ℝ) * L ^ 2 <
      max 1000 ((99 / 40 : ℝ) * gammaPrefix100Radius L (203 / 50) ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hrad0sq (by norm_num only : (0 : ℝ) ≤ 99 / 40)
    have hcoefL := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hLpos)
    have hsmall :
      (15123 / 25000 : ℝ) * L ^ 2 < (99 / 40 : ℝ) * gammaPrefix100Radius L (203 / 50) ^ 2 := by
      nlinarith only [hcoefL, hscaled]
    exact lt_of_lt_of_le hsmall (le_max_right _ _)
  have hbound1 :
    (15123 / 25000 : ℝ) * L ^ 2 <
      max 50000 ((99 / 40 : ℝ) * gammaPrefix100Radius L (28493 / 5000) ^ 2) := by
    have hscaled := mul_le_mul_of_nonneg_left hrad1sq (by norm_num only : (0 : ℝ) ≤ 99 / 40)
    have hcoefL := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hLpos)
    have hsmall :
      (15123 / 25000 : ℝ) * L ^ 2 < (99 / 40 : ℝ) * gammaPrefix100Radius L (28493 / 5000) ^ 2 := by
      nlinarith only [hcoefL, hscaled]
    exact lt_of_lt_of_le hsmall (le_max_right _ _)
  exact lt_min hbound0 hbound1

/-- From scale 300, the constant-6 Gaussian cutoff is strictly below both
retained-prefix index-100 Gamma and constant-18 Gaussian candidates. -/
theorem gaussianMR6Bound_lt_min_prefixUpper_gaussianMR18Bound {L : ℝ} (hL : 300 ≤ L) :
    Analysis.gaussianMR6Bound L <
      min (gammaIndex100PrefixUpper L) (Analysis.gaussianMR18Bound L) := by
  have h6U : Analysis.gaussianMR6Bound L < gammaIndex100PrefixUpper L :=
    lt_trans (Analysis.gaussianMR6Bound_lt_060492_sq hL)
      (gaussianMR6_coefficient_lt_gammaIndex100PrefixUpper hL)
  exact lt_min h6U (Analysis.gaussianMR6Bound_lt_gaussianMR18Bound hL)

/-- From scale 240, combine the existing clipped Gamma and the extended
two-prefix index-100 candidates. -/
theorem exists_least_prime_witness_le_analysis13GammaPrefixEnvelope {n : ℕ} (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ analysis13GammaPrefixEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  have hn := nat_gt_one_of_log_ge_240 hL
  obtain ⟨pOld, hpOld, hboundOld, hfailOld, hminOld⟩ :=
    exists_least_prime_witness_le_gammaClippedUpper hn hnOdd hcomp hGRH (by linarith only [hL])
  obtain ⟨pNew, hpNew, hboundNew, hfailNew, hminNew⟩ :=
    exists_least_prime_witness_le_gammaIndex100PrefixUpper hnOdd hcomp hGRH hL
  exact
    least_prime_witness_bound_min ⟨pOld, hpOld, hfailOld, hboundOld, hminOld⟩
      ⟨pNew, hpNew, hfailNew, hboundNew, hminNew⟩

/-- From logarithmic scale 300, the constant-18 Gaussian candidate is strictly
below the existing clipped Gamma bound. -/
theorem gaussianMR18Bound_lt_gammaClippedUpper {L : ℝ} (hL : 300 ≤ L) :
    Analysis.gaussianMR18Bound L < gammaClippedUpper L := by
  exact
    lt_of_lt_of_le (Analysis.gaussianMR18Bound_lt_sevenTenths_sq hL)
      (gammaClippedUpper_ge_sevenTenths_sq hL)

/-- Pointwise minimum of the retained-prefix index-100 Gamma and constant-18
Gaussian bounds, both of which apply from logarithmic scale 300. -/
noncomputable def analysis13GammaGaussianEnvelope (L : ℝ) : ℝ :=
  min (gammaIndex100PrefixUpper L) (Analysis.gaussianMR18Bound L)

/-- From logarithmic scale 300, the least rejecting prime is bounded by the
minimum of the two analysis13 candidates. Take the least witness from the
candidate whose bound is smaller. -/
theorem exists_least_prime_witness_le_analysis13GammaGaussianEnvelope {n : ℕ} (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ analysis13GammaGaussianEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨p₁, hp₁, hf₁, hb₁, hm₁⟩ :=
    exists_least_prime_witness_le_gammaIndex100PrefixUpper hnOdd hcomp hGRH (by linarith only [hL])
  obtain ⟨p₂, hp₂, hb₂, hf₂, hm₂⟩ := exists_least_prime_witness_le_gaussianMR18 hnOdd hcomp hGRH hL
  by_cases hmin : gammaIndex100PrefixUpper (Real.log n) ≤ Analysis.gaussianMR18Bound (Real.log n)
  · refine ⟨p₁, hp₁, hb₁, ?_, hm₁⟩
    rw [analysis13GammaGaussianEnvelope, min_eq_left hmin]
    exact hf₁
  · have hmin' : Analysis.gaussianMR18Bound (Real.log n) ≤ gammaIndex100PrefixUpper (Real.log n) :=
      le_of_not_ge hmin
    refine ⟨p₂, hp₂, hb₂, ?_, hm₂⟩
    rw [analysis13GammaGaussianEnvelope, min_eq_right hmin']
    exact hf₂

/-- From scale 300 onward, take the minimum of the existing clipped Gamma
bound and the two-candidate analysis13 envelope. -/
noncomputable def analysis13ClippedGammaEnvelope (L : ℝ) : ℝ :=
  min (gammaClippedUpper L) (analysis13GammaGaussianEnvelope L)

/-- From scale 300 onward, the constant-18 Gaussian candidate is below the
clipped Gamma bound, so the combined envelope reduces to the two new branches. -/
theorem analysis13ClippedGammaEnvelope_eq_gammaGaussianEnvelope {L : ℝ} (hL : 300 ≤ L) :
    analysis13ClippedGammaEnvelope L = analysis13GammaGaussianEnvelope L := by
  have h18Clip := gaussianMR18Bound_lt_gammaClippedUpper hL
  have hnewClip : analysis13GammaGaussianEnvelope L ≤ gammaClippedUpper L := by
    change min (gammaIndex100PrefixUpper L) (Analysis.gaussianMR18Bound L) ≤ _
    exact (min_le_right _ _).trans h18Clip.le
  change min (gammaClippedUpper L) (analysis13GammaGaussianEnvelope L) = _
  exact min_eq_right hnewClip

/-- The clipped Gamma candidate remains available from scale 300, so combine
it with the minimum of the new prefix-Gamma and constant-18 Gaussian bounds. -/
theorem exists_least_prime_witness_le_analysis13ClippedGammaEnvelope {n : ℕ} (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ analysis13ClippedGammaEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  have hn := nat_gt_one_of_log_ge_240 (by linarith only [hL])
  obtain ⟨pOld, hpOld, hboundOld, hfailOld, hminOld⟩ :=
    exists_least_prime_witness_le_gammaClippedUpper hn hnOdd hcomp hGRH (by linarith only [hL])
  obtain ⟨pNew, hpNew, hfailNew, hboundNew, hminNew⟩ :=
    exists_least_prime_witness_le_analysis13GammaGaussianEnvelope hnOdd hcomp hGRH hL
  exact
    least_prime_witness_bound_min ⟨pOld, hpOld, hfailOld, hboundOld, hminOld⟩
      ⟨pNew, hpNew, hfailNew, hboundNew, hminNew⟩

/-- Add the established index-100 Gamma branch where it becomes applicable. -/
noncomputable def analysis13Index100Envelope (L : ℝ) : ℝ :=
  min (analysis13GammaGaussianEnvelope L) (gammaIndex100Bound L)

/-- From scale 330 onward, the constant-18 branch is below the old index-100
Gamma bound, so this candidate minimum reduces to the two analysis13 bounds. -/
theorem analysis13Index100Envelope_eq_gammaGaussianEnvelope {L : ℝ} (hL : 330 ≤ L) :
    analysis13Index100Envelope L = analysis13GammaGaussianEnvelope L := by
  have h18Index := gaussianMR18Bound_lt_gammaIndex100Bound hL
  have hnewIndex : analysis13GammaGaussianEnvelope L ≤ gammaIndex100Bound L := by
    change min (gammaIndex100PrefixUpper L) (Analysis.gaussianMR18Bound L) ≤ _
    exact (min_le_right _ _).trans h18Index.le
  change min (analysis13GammaGaussianEnvelope L) (gammaIndex100Bound L) = _
  exact min_eq_left hnewIndex

/-- From logarithmic scale 330, include the existing index-100 bound in the
pointwise minimum with the clipped Gamma and analysis13 candidates. -/
theorem exists_least_prime_witness_le_analysis13Index100Envelope {n : ℕ} (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 330 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ analysis13Index100Envelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨pOld, hpOld, hfailOld, hboundOld, hminOld⟩ :=
    exists_least_prime_witness_le_analysis13GammaGaussianEnvelope hnOdd hcomp hGRH
      (by linarith only [hL])
  obtain ⟨pNew, hpNew, hboundNew, hfailNew, hminNew⟩ :=
    exists_least_prime_witness_le_gammaIndex100 hnOdd hcomp hGRH hL
  exact
    least_prime_witness_bound_min ⟨pOld, hpOld, hfailOld, hboundOld, hminOld⟩
      ⟨pNew, hpNew, hfailNew, hboundNew, hminNew⟩

/-- Add the established 6/5 Gaussian branch from its logarithmic starting
scale to the all-input candidate minimum. -/
noncomputable def analysis13SixFifthsEnvelope (L : ℝ) : ℝ :=
  min (analysis13Index100Envelope L) (Analysis.gaussianMR6FifthsBound L)

/-- From scale 500 onward, all later legacy candidates are dominated by the
constant-18 Gaussian, so the nested envelope reduces to the two new branches. -/
theorem analysis13SixFifthsEnvelope_eq_gammaGaussianEnvelope {L : ℝ} (hL : 500 ≤ L) :
    analysis13SixFifthsEnvelope L = analysis13GammaGaussianEnvelope L := by
  have h18Index := gaussianMR18Bound_lt_gammaIndex100Bound (by linarith only [hL])
  have h18Six := Analysis.gaussianMR18Bound_lt_gaussianMR6FifthsBound hL
  have hOldIndex : analysis13GammaGaussianEnvelope L ≤ gammaIndex100Bound L := by
    change min (gammaIndex100PrefixUpper L) (Analysis.gaussianMR18Bound L) ≤ _
    exact (min_le_right _ _).trans h18Index.le
  have hOldSix : analysis13GammaGaussianEnvelope L ≤ Analysis.gaussianMR6FifthsBound L := by
    change min (gammaIndex100PrefixUpper L) (Analysis.gaussianMR18Bound L) ≤ _
    exact (min_le_right _ _).trans h18Six.le
  dsimp only [analysis13SixFifthsEnvelope, analysis13Index100Envelope]
  rw [min_eq_left hOldIndex, min_eq_left hOldSix]

/-- From logarithmic scale 500, the pointwise minimum also includes the
established 6/5 Gaussian bound. -/
theorem exists_least_prime_witness_le_analysis13SixFifthsEnvelope {n : ℕ} (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ analysis13SixFifthsEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  obtain ⟨pOld, hpOld, hfailOld, hboundOld, hminOld⟩ :=
    exists_least_prime_witness_le_analysis13Index100Envelope hnOdd hcomp hGRH
      (by linarith only [hL])
  obtain ⟨pNew, hpNew, hfailNew, hboundNew, hminNew⟩ :=
    exists_least_prime_witness_le_gaussian6fifths hnOdd hcomp hGRH hL
  exact
    least_prime_witness_bound_min ⟨pOld, hpOld, hfailOld, hboundOld, hminOld⟩
      ⟨pNew, hpNew, hfailNew, hboundNew, hminNew⟩

/-- At the decimal threshold for the coefficient bound, take the pointwise
minimum of that bound and every previously established applicable candidate. -/
noncomputable def analysis13LargeScaleEnvelope (L : ℝ) : ℝ :=
  min (analysis13SixFifthsEnvelope L) ((282924 / 1000000 : ℝ) * L ^ 2)

/-- The two-candidate Gamma-Gaussian envelope retains the local three-tenths
quadratic lower bound from scale 300 onward. -/
theorem analysis13GammaGaussianEnvelope_lower_three_tenths {L : ℝ} (hL : 300 ≤ L) :
    (3 / 10 : ℝ) * L ^ 2 ≤ analysis13GammaGaussianEnvelope L := by
  have hPrefix := local_three_tenths_le_gammaIndex100PrefixUpper (by linarith only [hL])
  have hGaussian := Analysis.gaussianMR18Bound_gt_local_three_tenths hL
  change (3 / 10 : ℝ) * L ^ 2 ≤ min (gammaIndex100PrefixUpper L) (Analysis.gaussianMR18Bound L)
  exact le_min hPrefix hGaussian.le

/-- Beyond scale 500, the large-scale candidate minimum is exactly its
coefficient branch because every retained envelope exceeds `3/10 L²`. -/
theorem analysis13LargeScaleEnvelope_eq_coefficient {L : ℝ} (hL : 500 ≤ L) :
    analysis13LargeScaleEnvelope L = (282924 / 1000000 : ℝ) * L ^ 2 := by
  have hcoef : (282924 / 1000000 : ℝ) < 3 / 10 := by norm_num only
  have hLpos : 0 < L := by linarith only [hL]
  have hscale := mul_lt_mul_of_pos_right hcoef (sq_pos_of_pos hLpos)
  have hlower := analysis13GammaGaussianEnvelope_lower_three_tenths (by linarith only [hL])
  have hsmall := lt_of_lt_of_le hscale hlower
  rw [analysis13LargeScaleEnvelope, analysis13SixFifthsEnvelope_eq_gammaGaussianEnvelope hL]
  exact min_eq_right hsmall.le

/-- For odd composites above the coefficient theorem's decimal threshold, the
least rejecting prime obeys the minimum of the Gamma, Gaussian, and quadratic
coefficient candidates. -/
theorem exists_least_prime_witness_le_analysis13LargeScaleEnvelope {n : ℕ} (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hN : 10 ^ 9565217391305 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ analysis13LargeScaleEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  have hL := log_ge_triangular_large_index_of_decimal hN
  have hL500 : 500 ≤ Real.log n := by linarith only [hL]
  obtain ⟨p, hp, hfail, hbound, hmin⟩ := exists_least_prime_witness_le_0282924 hnOdd hcomp hGRH hN
  refine ⟨p, hp, hfail, ?_, hmin⟩
  rw [analysis13LargeScaleEnvelope_eq_coefficient hL500]
  exact hbound

end PseudoPrime.PrimeTestBounds.MillerRabin
