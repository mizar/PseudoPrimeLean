/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Polynomial.Eval.Degree
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
public import PseudoPrime.Analysis.IntegerIntervals

/-! # Signed power-row lower bounds for finite K186 curvature -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A lower coefficient contributes at worst its negative part times
the largest nonnegative power of the cell coordinate. -/
private theorem signed_power_lower {c d y w : ℝ} {n : ℕ} (hcd : c ≤ d) (hy : 0 ≤ y) (hyw : y ≤ w) :
    min 0 c * w ^ n ≤ d * y ^ n := by
  have hc := min_le_left (0 : ℝ) c
  have he := (min_le_right (0 : ℝ) c).trans hcd
  exact
    (mul_le_mul_of_nonpos_left (pow_le_pow_left₀ hy hyw n) hc).trans
      (mul_le_mul_of_nonneg_right he (pow_nonneg hy n))

/-- Lower polynomial evaluation on a nonnegative local coordinate using
the constant term and a single weighted sum of negative coefficient bounds. -/
public theorem k186_signed_taylor_lower {P : Polynomial ℝ} {N : ℕ} (hd : P.natDegree ≤ N)
    (c : ℕ → ℝ) (hc : ∀ i ≤ N, c i ≤ P.coeff i) {y w : ℝ} (hy : 0 ≤ y) (hw : y ≤ w) :
    c 0 + ∑ i ∈ Finset.range N, min 0 (c (i + 1)) * w ^ (i + 1) ≤ P.eval y := by
  have he : P.eval y = ∑ i ∈ Finset.range (N + 1), P.coeff i * y ^ i := by
    rw [Polynomial.eval_eq_sum_range]
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hd))
    intro i _ hi
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt
        (Nat.lt_of_succ_le (Nat.le_of_not_gt (fun h ↦ hi (Finset.mem_range.mpr h)))),
      zero_mul]
  rw [he, Finset.sum_range_succ', pow_zero, mul_one, add_comm _ (P.coeff 0)]
  exact
    add_le_add (hc 0 (Nat.zero_le N))
      (Finset.sum_le_sum fun i hi ↦
        signed_power_lower (hc (i + 1) (Nat.succ_le_of_lt (Finset.mem_range.mp hi))) hy hw)

/-- Sum lower ticks over the unit interval. Only the constant term contributes
its full lower value, while higher coefficients contribute their negative part. -/
@[expose]
public def k186TaylorTicks (N : ℕ) (lower : ℕ → ℤ) : ℤ :=
  lower 0 + ∑ i ∈ Finset.range N, min 0 (lower (i + 1))

/-- Integer coefficient enclosures at one scale imply a uniform lower bound
over the normalized Taylor interval. -/
public theorem k186_taylor_ticks_le {G : ℤ} (hG : 0 < G) {P : Polynomial ℝ} {N : ℕ}
    (hd : P.natDegree ≤ N) (I : ℕ → Analysis.IntegerInterval)
    (hc : ∀ i ≤ N, (I i).Contains G (P.coeff i)) {y : ℝ} (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    (k186TaylorTicks N (fun i ↦ (I i).lower) : ℝ) / (G : ℝ) ≤ P.eval y := by
  have hp : (0 : ℝ) < G := Int.cast_pos.mpr hG
  have h :=
    k186_signed_taylor_lower hd (fun i ↦ ((I i).lower : ℝ) / (G : ℝ)) (fun i hi ↦ (hc i hi).1) hy.1
      hy.2
  simp only [one_pow, mul_one] at h
  simp only [k186TaylorTicks, Int.cast_add, Int.cast_sum, Int.cast_min, Int.cast_zero, add_div,
    Finset.sum_div]
  simp only [← min_div_div_right hp.le, zero_div]
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
