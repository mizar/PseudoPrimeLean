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
theorem gaussianMR6_coefficient_lt_gamma100PrefixUpper {L : ℝ} (hL : 300 ≤ L) :
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
theorem gaussian6_lt_prefix_gaussian18 {L : ℝ} (hL : 300 ≤ L) :
    gaussian6Bound L < min (gammaIndex100PrefixUpper L) (gaussian18Bound L) := by
  have h6U : gaussian6Bound L < gammaIndex100PrefixUpper L :=
    lt_trans (gaussian6Bound_lt_060492_sq hL) (gaussianMR6_coefficient_lt_gamma100PrefixUpper hL)
  exact lt_min h6U (gaussian6Bound_lt_gaussian18Bound hL)

/-- From scale 240, combine the existing clipped Gamma and the extended
two-prefix index-100 candidates. -/
theorem exists_least_prime_analysis13Prefix_GRH {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ analysis13GammaPrefixEnvelope (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  have hn := nat_gt_one_of_log_ge_240 hL
  obtain ⟨pOld, hpOld, hboundOld, hfailOld, hminOld⟩ :=
    exists_least_prime_witness_le_gammaClippedUpper hn hnOdd hcomp hGRH (by linarith only [hL])
  obtain ⟨pNew, hpNew, hboundNew, hfailNew, hminNew⟩ :=
    exists_leastWitness_le_gammaIndex100PrefixUpper hnOdd hcomp hGRH hL
  exact
    least_prime_witness_bound_min ⟨pOld, hpOld, hfailOld, hboundOld, hminOld⟩
      ⟨pNew, hpNew, hfailNew, hboundNew, hminNew⟩

/-- From logarithmic scale 300, the constant-18 Gaussian candidate is strictly
below the existing clipped Gamma bound. -/
theorem gaussianMR18Bound_lt_gammaClippedUpper {L : ℝ} (hL : 300 ≤ L) :
    gaussian18Bound L < gammaClippedUpper L := by
  exact
    lt_of_lt_of_le (gaussian18Bound_lt_sevenTenths_sq hL) (gammaClippedUpper_ge_sevenTenths_sq hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
