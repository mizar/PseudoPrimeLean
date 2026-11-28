/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianRemainderEntry
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredSeries
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalHeadCert
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianCenteredTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelData
import Mathlib.Tactic.Linarith

/-! # Rational bounds for the H27 boundary charge -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the H27 boundary derivative from the cached rational profile coefficients. -/
private def h27BoundaryValue (K : HighGaussianKernel) : ℚ :=
  let n := 2 * K.degree + 3
  let c := headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)
  let b := headCoeffCache (n + 2) (highProfileFrom K c)
  (List.ofFn fun j : Fin (n + 1) ↦
      centeredCoeff (K.pole - 1 / 2) (headCached b) j * (5 : ℚ) ^ j.val).sum

/-- The boundary evaluator is exact, including the degree padding. -/
private theorem h27_boundary_value_eq (K : HighGaussianKernel) :
    h27BoundaryValue K = highPrincipalBoundaryRat K := by
  have hc :
    highProfileFrom K (headCoeffCache (2 * K.degree + 1) (headCompactCoeff K)) =
      highProfileCoeff K :=
    rfl
  simp only [h27BoundaryValue, highPrincipalBoundaryRat, List.sum_ofFn, head_coeff_cache_eq, hc,
    ← centered_coeff_eq, Polynomial.eval_eq_sum_range]
  rw [Fin.sum_univ_eq_sum_range (fun j ↦ (highCenteredRatPoly K).coeff j * 5 ^ j)]
  symm
  apply Finset.sum_subset (Finset.range_mono (Nat.add_le_add_right (high_centered_rat_degree K) 1))
  intro j _ hj
  have hj' := Nat.lt_of_not_ge fun h ↦ hj (Finset.mem_range.mpr (Nat.lt_succ_of_le h))
  rw [Polynomial.coeff_eq_zero_of_natDegree_lt hj', zero_mul]

/-- The K186 boundary derivative has rational magnitude at most one million. -/
private theorem h27_k186_boundary_rat_le : |highPrincipalBoundaryRat .k186| ≤ 1000000 := by
  rw [← h27_boundary_value_eq]
  decide +kernel

/-- The logarithmic decay makes the boundary budget negligible for both high kernels. -/
public theorem h27_boundary_decay (K : HighGaussianKernel) {l M : ℝ} (hl : 11 ≤ l)
    (hM : |M| ≤ 1000000) :
    Real.exp (-(5 * (K.pole : ℝ))) * (5 / 3 * |M| * Real.exp (-(5 / 2 : ℝ) * l)) ≤ 1 / 100000 := by
  have hk : 0 ≤ (K.pole : ℝ) :=
    (by norm_num only : (0 : ℝ) ≤ 1 / 2).trans (high_gaussian_pole_gt K).le
  have hnorm : Real.exp (-(5 * (K.pole : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (by norm_num only) hk))
  have hq : headExpUpper (55 / 2) 64 ≤ (2 / 10 ^ 12 : ℚ) := by decide +kernel
  have hc :=
    (head_exp_upper_sound (by norm_num only : (0 : ℚ) ≤ 55 / 2) 64).trans
      ((Rat.cast_le (K := ℝ)).mpr hq)
  have hb : Real.exp (-(55 / 2 : ℝ)) ≤ 2 / 10 ^ 12 := by
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hc
  have he : Real.exp (-(5 / 2 : ℝ) * l) ≤ 2 / 10 ^ 12 :=
    (Real.exp_le_exp.mpr (by linarith only [hl])).trans hb
  calc
    _ ≤ 1 * (5 / 3 * |M| * Real.exp (-(5 / 2 : ℝ) * l)) :=
      mul_le_mul_of_nonneg_right hnorm
        (mul_nonneg (mul_nonneg (by norm_num only) (abs_nonneg _)) (Real.exp_nonneg _))
    _ ≤ 5 / 3 * 1000000 * (2 / 10 ^ 12) := by
      rw [one_mul]
      exact
        mul_le_mul (mul_le_mul_of_nonneg_left hM (by norm_num only)) he (Real.exp_nonneg _)
          (by norm_num only)
    _ ≤ _ := by norm_num only

/-- The K186 boundary charge is bounded by one hundred-thousandth above log cutoff eleven. -/
public theorem h27_k186_boundary_le {l : ℝ} (hl : 11 ≤ l) :
    Real.exp (-(5 * (HighGaussianKernel.k186.pole : ℝ))) *
        (5 / 3 * |(highPrincipalBoundaryRat .k186 : ℝ)| * Real.exp (-(5 / 2 : ℝ) * l)) ≤
      1 / 100000 := by
  apply h27_boundary_decay .k186 hl
  have h := (Rat.cast_le (K := ℝ)).mpr h27_k186_boundary_rat_le
  simpa only [Rat.cast_abs, Rat.cast_ofNat] using h

end PseudoPrime.PrimeTestBounds.MillerRabin
