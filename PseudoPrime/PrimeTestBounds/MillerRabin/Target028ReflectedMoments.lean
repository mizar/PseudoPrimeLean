/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028LogMomentBounds

/-! # Binomial moment bound for the reflected Euler term -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The inverse-scale first logarithmic term factors into the scale power and
the first fixed moment. This is the pointwise version of the series identity. -/
theorem target028_scaled_moment_one {x : ℝ} (hx : 0 < x) (n : ℕ) :
    Real.log n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ) =
      x ^ (-(27 / 25 : ℝ)) * target028LogMoment 1 n := by
  by_cases hn : n = 0
  · subst n
    simp only [Nat.cast_zero, Real.log_zero, Real.sqrt_zero, div_zero, zero_mul, mul_zero,
      target028LogMoment, zero_pow (by decide : 1 ≠ 0)]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow :
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(27 / 25 : ℝ)) = (n : ℝ) ^ (-(79 / 50 : ℝ)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      norm_num only
    rw [Real.sqrt_eq_rpow, Real.inv_rpow (mul_nonneg hnpos.le hx.le), Real.mul_rpow hnpos.le hx.le]
    simp only [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg hnpos.le, ← Real.rpow_neg hx.le]
    simp only [div_eq_mul_inv] at hpow
    dsimp only [target028LogMoment]
    simp only [pow_one, div_eq_mul_inv]
    rw [← hpow]
    ring

/-- Expanding the fifth power keeps all six nonnegative logarithmic moments
separate. This avoids the factor sixteen introduced by the coarse two-term
convexity bound and prepares the paper's finite-scale Euler estimate. -/
theorem target028_reflected_binomial {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
          x ^ (-(27 / 25 : ℝ))) *
        ∑ j ∈ Finset.range 6,
          ((Nat.choose 5 j : ℕ) : ℝ) * ((21 / 8 : ℝ) + Real.log x) ^ (5 - j) *
            ∑' n : ℕ, target028LogMoment (j + 1) n := by
  let z : ℝ := 21 / 8 + Real.log x
  let C : ℝ :=
    ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * x ^ (-(27 / 25 : ℝ))
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs (j : ℕ) :
    Summable
      (fun n : ℕ ↦ ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * target028LogMoment (j + 1) n) := by
    exact (refined_log_power_summable (j + 1)).mul_left _
  have hsum :
    Summable
      (fun n : ℕ ↦
        ∑ j ∈ Finset.range 6,
          ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * target028LogMoment (j + 1) n) :=
    summable_sum (fun j _ ↦ hs j)
  have hpoint (n : ℕ) :
    refinedDualWeight x n ≤
      C *
        ∑ j ∈ Finset.range 6,
          ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * target028LogMoment (j + 1) n := by
    have h := refined_dual_weight_log_bound hx n
    rw [target028_scaled_moment_one hx0 n] at h
    have he :
      C *
          (∑ j ∈ Finset.range 6,
            ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * target028LogMoment (j + 1) n) =
        (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
          ((21 / 8 : ℝ) + Real.log x + Real.log n) ^ 5 *
          (x ^ (-(27 / 25 : ℝ)) * target028LogMoment 1 n) := by
      dsimp only [C, z, target028LogMoment]
      norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
        Nat.reduceAdd, Nat.cast_ofNat, pow_zero, pow_one, mul_one, add_zero, zero_add]
      ring
    rw [he]
    simpa only [mul_assoc] using h
  have h := refined_reflected_principal_le hx0 _ (hsum.mul_left C) hpoint
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun j _ ↦ hs j)] at h
  simp only [tsum_mul_left] at h
  exact h

/-- Rational upper polynomial for the six logarithmic moments. The integral
part and the two turning-point values are bounded separately for each degree. -/
noncomputable def target028MomentPolynomial (z : ℝ) : ℝ :=
  z ^ 5 * ((1 : ℝ) / (29 / 50 : ℝ) ^ 2 + 2 * (232 / 1000 : ℝ)) +
    5 * z ^ 4 * ((2 : ℝ) / (29 / 50 : ℝ) ^ 3 + 2 * (216 / 1000 : ℝ)) +
    10 * z ^ 3 * ((6 : ℝ) / (29 / 50 : ℝ) ^ 4 + 2 * (341 / 1000 : ℝ)) +
    10 * z ^ 2 * ((24 : ℝ) / (29 / 50 : ℝ) ^ 5 + 2 * (753 / 1000 : ℝ)) +
    5 * z * ((120 : ℝ) / (29 / 50 : ℝ) ^ 6 + 2 * (2140 / 1000 : ℝ)) +
    ((720 : ℝ) / (29 / 50 : ℝ) ^ 7 + 2 * (7443 / 1000 : ℝ))

/-- The explicit moment polynomial is nondecreasing on nonnegative arguments.
Each of its coefficients is nonnegative and each power preserves the order. -/
theorem target028_moment_polynomial_le {z Z : ℝ} (hz : 0 ≤ z) (hZ : z ≤ Z) :
    target028MomentPolynomial z ≤ target028MomentPolynomial Z := by
  have h2 := pow_le_pow_left₀ hz hZ 2
  have h3 := pow_le_pow_left₀ hz hZ 3
  have h4 := pow_le_pow_left₀ hz hZ 4
  have h5 := pow_le_pow_left₀ hz hZ 5
  dsimp only [target028MomentPolynomial]
  linarith only [hZ, h2, h3, h4, h5]

/-- At every scale at least one, the reflected Euler term is bounded by the
explicit six-moment polynomial. Each moment uses its integral and certified
turning-point bounds, and all binomial coefficients are nonnegative. -/
theorem target028_reflected_moment_bound {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
          x ^ (-(27 / 25 : ℝ))) *
        target028MomentPolynomial ((21 / 8 : ℝ) + Real.log x) := by
  let z : ℝ := (21 / 8 : ℝ) + Real.log x
  have hz : 0 ≤ z := by
    dsimp only [z]
    have hl := Real.log_nonneg hx
    linarith only [hl]
  have h1 := mul_le_mul_of_nonneg_left target028_log_moment_1_bound (pow_nonneg hz 5)
  have h2 :=
    mul_le_mul_of_nonneg_left target028_log_moment_2_bound (show (0 : ℝ) ≤ 5 * z ^ 4 by positivity)
  have h3 :=
    mul_le_mul_of_nonneg_left target028_log_moment_3_bound (show (0 : ℝ) ≤ 10 * z ^ 3 by positivity)
  have h4 :=
    mul_le_mul_of_nonneg_left target028_log_moment_4_bound (show (0 : ℝ) ≤ 10 * z ^ 2 by positivity)
  have h5 :=
    mul_le_mul_of_nonneg_left target028_log_moment_5_bound (show (0 : ℝ) ≤ 5 * z by positivity)
  have h6 := target028_log_moment_6_bound
  have hsum :
    (∑ j ∈ Finset.range 6,
        ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * ∑' n : ℕ, target028LogMoment (j + 1) n) ≤
      target028MomentPolynomial z := by
    dsimp only [target028MomentPolynomial]
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
      Nat.reduceAdd, Nat.cast_ofNat, pow_zero, pow_one, mul_one, add_zero, zero_add]
    linarith only [h1, h2, h3, h4, h5, h6]
  have hp :
    0 ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
        x ^ (-(27 / 25 : ℝ)) := by
    positivity
  exact (target028_reflected_binomial hx).trans (mul_le_mul_of_nonneg_left hsum hp)

/-- The explicit six-moment reflected Euler upper bound at scale `x`. It is
the scalar quantity used by the finite-cell witness criterion. -/
noncomputable def target028ReflectedMomentUpper (x : ℝ) : ℝ :=
  ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) * x ^ (-(27 / 25 : ℝ))) *
    target028MomentPolynomial ((21 / 8 : ℝ) + Real.log x)

end PseudoPrime.PrimeTestBounds.MillerRabin
