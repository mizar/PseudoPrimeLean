/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ReflectedMoments

/-! # Mangoldt moments for the reflected Euler term -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The degree `k` Mangoldt moment summand at exponent `79/50`. Its series
retains the prime-power structure needed for the refined reflected bound. -/
noncomputable def quarterMangoldtMoment (k n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log n ^ k * (n : ℝ) ^ (-(79 / 50 : ℝ))

/-- Every Mangoldt moment summand is nonnegative. -/
theorem quarter_mangoldt_moment_nonneg (k n : ℕ) : 0 ≤ quarterMangoldtMoment k n := by
  unfold quarterMangoldtMoment
  exact
    mul_nonneg
      (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- The logarithmic majorant proves absolute convergence of each Mangoldt moment. -/
theorem quarter_mangoldt_moment_summable (k : ℕ) : Summable (quarterMangoldtMoment k) := by
  apply
    Summable.of_nonneg_of_le (quarter_mangoldt_moment_nonneg k) _
      (refined_log_power_summable (k + 1))
  intro n
  dsimp only [quarterMangoldtMoment, target028LogMoment]
  have h :=
    mul_le_mul_of_nonneg_right (ArithmeticFunction.vonMangoldt_le_log (n := n))
      (mul_nonneg (pow_nonneg (Real.log_natCast_nonneg n) k)
        (Real.rpow_nonneg (Nat.cast_nonneg n) (-(79 / 50 : ℝ))))
  rw [pow_succ]
  nlinarith only [h]

/-- At positive scale the inverse-weight factor separates into a scale power
and the degree-zero Mangoldt moment, including the zero index. -/
theorem quarter_scaled_mangoldt {x : ℝ} (hx : 0 < x) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n / Real.sqrt n * (((n : ℝ) * x)⁻¹) ^ (27 / 25 : ℝ) =
      x ^ (-(27 / 25 : ℝ)) * quarterMangoldtMoment 0 n := by
  by_cases hn : n = 0
  · subst n
    simp only [ArithmeticFunction.map_zero, zero_div, zero_mul, quarterMangoldtMoment, pow_zero,
      mul_one, mul_zero]
  · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hpow :
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (n : ℝ) ^ (-(27 / 25 : ℝ)) = (n : ℝ) ^ (-(79 / 50 : ℝ)) := by
      rw [← Real.rpow_add hnpos]
      congr 1
      norm_num only
    rw [Real.sqrt_eq_rpow, Real.inv_rpow (mul_nonneg hnpos.le hx.le), Real.mul_rpow hnpos.le hx.le]
    simp only [div_eq_mul_inv, mul_inv_rev, ← Real.rpow_neg hnpos.le, ← Real.rpow_neg hx.le]
    dsimp only [quarterMangoldtMoment]
    simp only [pow_zero, mul_one]
    rw [← hpow]
    ring_nf

/-- For scales at least one the reflected principal Euler term is bounded by
six Mangoldt moments with the exact binomial coefficients. Unlike the coarse
logarithmic majorant, these moments retain the sparse von Mangoldt support. -/
theorem quarter_reflected_mangoldt {x : ℝ} (hx : 1 ≤ x) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
          x ^ (-(27 / 25 : ℝ))) *
        ∑ j ∈ Finset.range 6,
          ((Nat.choose 5 j : ℕ) : ℝ) * ((21 / 8 : ℝ) + Real.log x) ^ (5 - j) *
            ∑' n : ℕ, quarterMangoldtMoment j n := by
  let z : ℝ := 21 / 8 + Real.log x
  let C : ℝ :=
    ((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8))) * x ^ (-(27 / 25 : ℝ))
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hs (j : ℕ) :
    Summable (fun n : ℕ ↦ ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * quarterMangoldtMoment j n) :=
    (quarter_mangoldt_moment_summable j).mul_left _
  have hsum :
    Summable
      (fun n : ℕ ↦
        ∑ j ∈ Finset.range 6,
          ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * quarterMangoldtMoment j n) :=
    summable_sum (fun j _ ↦ hs j)
  have hpoint (n : ℕ) :
    refinedDualWeight x n ≤
      C *
        ∑ j ∈ Finset.range 6,
          ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * quarterMangoldtMoment j n := by
    by_cases hn : n = 0
    · subst n
      simp only [refinedDualWeight, ArithmeticFunction.map_zero, zero_div, zero_mul,
        quarterMangoldtMoment, Finset.sum_const_zero, mul_zero, le_refl]
    · have hn1 : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      have he :
        C *
            (∑ j ∈ Finset.range 6,
              ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * quarterMangoldtMoment j n) =
          (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
            ((21 / 8 : ℝ) + Real.log x + Real.log n) ^ 5 *
            (x ^ (-(27 / 25 : ℝ)) * quarterMangoldtMoment 0 n) := by
        dsimp only [C, z, quarterMangoldtMoment]
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
          Nat.reduceAdd, Nat.cast_ofNat, pow_zero, pow_one, mul_one, add_zero, zero_add]
        ring
      rw [he, refined_dual_weight_explicit hx hn1, ← quarter_scaled_mangoldt hx0 n]
      apply le_of_eq
      ring
  have h := refined_reflected_principal_le hx0 _ (hsum.mul_left C) hpoint
  rw [tsum_mul_left, Summable.tsum_finsetSum (fun j _ ↦ hs j)] at h
  simp only [tsum_mul_left] at h
  exact h

/-- The rational caps for the six Mangoldt moments used in the refined bound.
The index is a moment degree from zero through five; other indices map to zero. -/
noncomputable def quarterMomentCap : ℕ → ℝ
  | 0 => 1244 / 1000
  | 1 => 2856 / 1000
  | 2 => 10382 / 1000
  | 3 => 54699 / 1000
  | 4 => 381081 / 1000
  | 5 => 3295239 / 1000
  | _ => 0

/-- The six numerical moment bounds needed for the refined reflected Euler
estimate. They are independent of the input integer and its characters. -/
def QuarterMomentBounds : Prop :=
  ∀ j < 6, (∑' n : ℕ, quarterMangoldtMoment j n) ≤ quarterMomentCap j

/-- The polynomial formed by the six rational Mangoldt moment caps and the
fifth-power binomial coefficients. -/
noncomputable def quarterMomentPolynomial (z : ℝ) : ℝ :=
  (1244 / 1000 : ℝ) * z ^ 5 + 5 * (2856 / 1000 : ℝ) * z ^ 4 + 10 * (10382 / 1000 : ℝ) * z ^ 3 +
    10 * (54699 / 1000 : ℝ) * z ^ 2 +
    5 * (381081 / 1000 : ℝ) * z +
    (3295239 / 1000 : ℝ)

/-- The cap polynomial is nondecreasing for nonnegative arguments. -/
theorem quarter_moment_polynomial_le {z Z : ℝ} (hz : 0 ≤ z) (hZ : z ≤ Z) :
    quarterMomentPolynomial z ≤ quarterMomentPolynomial Z := by
  have h2 := pow_le_pow_left₀ hz hZ 2
  have h3 := pow_le_pow_left₀ hz hZ 3
  have h4 := pow_le_pow_left₀ hz hZ 4
  have h5 := pow_le_pow_left₀ hz hZ 5
  dsimp only [quarterMomentPolynomial]
  linarith only [hZ, h2, h3, h4, h5]

/-- The six moment caps give the paper's refined reflected Euler bound at
every scale at least one. This isolates the arithmetic moment estimates. -/
theorem quarter_reflected_of_moments {x : ℝ} (hx : 1 ≤ x) (hm : QuarterMomentBounds) :
    refinedReflectedEuler (1 : DirichletCharacter ℂ 1) x ≤
      ((((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
          x ^ (-(27 / 25 : ℝ))) *
        quarterMomentPolynomial ((21 / 8 : ℝ) + Real.log x) := by
  let z : ℝ := (21 / 8 : ℝ) + Real.log x
  have hz : 0 ≤ z := by
    dsimp only [z]
    have h := Real.log_nonneg hx
    linarith only [h]
  have h0 := hm 0 (by decide)
  have h1 := hm 1 (by decide)
  have h2 := hm 2 (by decide)
  have h3 := hm 3 (by decide)
  have h4 := hm 4 (by decide)
  have h5 := hm 5 (by decide)
  norm_num only [quarterMomentCap] at h0 h1 h2 h3 h4 h5
  have hp0 := mul_le_mul_of_nonneg_left h0 (pow_nonneg hz 5)
  have hp1 := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 5 * z ^ 4 by positivity)
  have hp2 := mul_le_mul_of_nonneg_left h2 (show 0 ≤ 10 * z ^ 3 by positivity)
  have hp3 := mul_le_mul_of_nonneg_left h3 (show 0 ≤ 10 * z ^ 2 by positivity)
  have hp4 := mul_le_mul_of_nonneg_left h4 (show 0 ≤ 5 * z by positivity)
  have hsum :
    (∑ j ∈ Finset.range 6,
        ((Nat.choose 5 j : ℕ) : ℝ) * z ^ (5 - j) * ∑' n : ℕ, quarterMangoldtMoment j n) ≤
      quarterMomentPolynomial z := by
    dsimp only [quarterMomentPolynomial]
    norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose, Nat.reduceSub,
      Nat.reduceAdd, Nat.cast_ofNat, pow_zero, pow_one, mul_one, add_zero, zero_add]
    linarith only [hp0, hp1, hp2, hp3, hp4, h5]
  have hC :
    0 ≤
      (((27 / 25 : ℝ) ^ 5 / 120) * Real.exp (-((27 / 25 : ℝ) * (21 / 8)))) *
        x ^ (-(27 / 25 : ℝ)) := by
    positivity
  exact (quarter_reflected_mangoldt hx).trans (mul_le_mul_of_nonneg_left hsum hC)

end PseudoPrime.PrimeTestBounds.MillerRabin
