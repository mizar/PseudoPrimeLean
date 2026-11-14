/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalPhaseTaylor
public import PseudoPrime.Analysis.ComplexCpowDerivatives
import all PseudoPrime.Analysis.ComplexCpowDerivatives

/-! # Exact rational arithmetic for Mellin Taylor weights -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The falling product for the critical exponent `-3/4 + i*t/2`, computed
as rational component pairs. The successor multiplies by the next factor;
no list or numerical table is accessed. -/
def rationalMellinFalling (t : ℚ) : ℕ → ℚ × ℚ
  | 0 => (1, 0)
  | n + 1 => rationalComplexMul (rationalMellinFalling t n) (-(3 / 4) - n, t / 2)

/-- The componentwise one-norm of a rational complex pair. It gives a
rational upper bound suitable for finite calculations without square roots. -/
def rationalComplexOneNorm (z : ℚ × ℚ) : ℚ :=
  |z.1| + |z.2|

/-- The one-norm of a rational complex product is at most the product of
the one-norms. The proof uses only the triangle inequality and rational
arithmetic on the two components. -/
theorem rational_complex_one_norm_mul (z w : ℚ × ℚ) :
    rationalComplexOneNorm (rationalComplexMul z w) ≤
      rationalComplexOneNorm z * rationalComplexOneNorm w := by
  have h₁ := abs_sub (z.1 * w.1) (z.2 * w.2)
  have h₂ := abs_add_le (z.1 * w.2) (z.2 * w.1)
  simp only [abs_mul] at h₁ h₂
  dsimp only [rationalComplexOneNorm, rationalComplexMul]
  nlinarith only [h₁, h₂]

/-- The componentwise one-norm is subadditive for rational complex pairs. -/
theorem rational_complex_one_norm_add (z w : ℚ × ℚ) :
    rationalComplexOneNorm (z + w) ≤ rationalComplexOneNorm z + rationalComplexOneNorm w := by
  have h₁ := abs_add_le z.1 w.1
  have h₂ := abs_add_le z.2 w.2
  dsimp only [rationalComplexOneNorm, Prod.fst_add, Prod.snd_add]
  linarith only [h₁, h₂]

/-- The one-norm of a finite rational-pair sum is at most the sum of the
individual one-norms. -/
theorem rational_complex_one_norm_sum {ι : Type*} (S : Finset ι) (f : ι → ℚ × ℚ) :
    rationalComplexOneNorm (∑ i ∈ S, f i) ≤ ∑ i ∈ S, rationalComplexOneNorm (f i) := by
  classical
    induction S using Finset.induction_on with
  | empty =>
    norm_num only [Finset.sum_empty, rationalComplexOneNorm, Prod.fst_zero, Prod.snd_zero, abs_zero,
      add_zero, le_refl]
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    calc
      rationalComplexOneNorm (f i + ∑ j ∈ S, f j) ≤
          rationalComplexOneNorm (f i) + rationalComplexOneNorm (∑ j ∈ S, f j) :=
        rational_complex_one_norm_add _ _
      _ ≤ rationalComplexOneNorm (f i) + ∑ j ∈ S, rationalComplexOneNorm (f j) :=
        add_le_add le_rfl ih

/-- A uniform rational majorant for the critical-exponent falling product
when `|t| ≤ 100`. It multiplies by `j + 51` at each successive order. -/
def rationalMellinFallingBound : ℕ → ℚ
  | 0 => 1
  | n + 1 => rationalMellinFallingBound n * (n + 51)

/-- The falling-product majorant is nonnegative at every order. -/
theorem rational_mellin_falling_bound_nonneg (n : ℕ) : 0 ≤ rationalMellinFallingBound n := by
  induction n with
  | zero => norm_num only [rationalMellinFallingBound]
  | succ n ih =>
    rw [rationalMellinFallingBound]
    exact mul_nonneg ih (add_nonneg (Nat.cast_nonneg n) (by norm_num only))

/-- For every rational height with `|t| ≤ 100`, the componentwise norm of
the rational falling product is bounded by the same recursively computed
majorant. The recurrence is independent of the grid node and final block. -/
theorem rational_mellin_falling_le (t : ℚ) (ht : |t| ≤ 100) (n : ℕ) :
    rationalComplexOneNorm (rationalMellinFalling t n) ≤ rationalMellinFallingBound n := by
  induction n with
  | zero =>
    norm_num only [rationalMellinFalling, rationalComplexOneNorm, rationalMellinFallingBound,
      abs_one, abs_zero, add_zero]
  | succ n ih =>
    rw [rationalMellinFalling, rationalMellinFallingBound]
    have hfactor : rationalComplexOneNorm (-(3 / 4) - n, t / 2) ≤ n + 51 := by
      dsimp only [rationalComplexOneNorm]
      rw [abs_div, abs_of_nonneg (by norm_num only : (0 : ℚ) ≤ 2)]
      have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
      rw [abs_of_nonpos (by linarith only [hn])]
      linarith only [ht]
    have hn : (0 : ℚ) ≤ n + 51 := add_nonneg (Nat.cast_nonneg n) (by norm_num only)
    exact
      (rational_complex_one_norm_mul _ _).trans
        (mul_le_mul ih hfactor (by exact add_nonneg (abs_nonneg _) (abs_nonneg _))
          (rational_mellin_falling_bound_nonneg n))

/-- Casting the rational falling product gives the complex falling product
of the critical exponent. Induction follows the finite-product recurrence. -/
theorem rational_mellin_falling_cast (t : ℚ) (n : ℕ) :
    rationalComplexCast (rationalMellinFalling t n) =
      complexFalling ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 - 1) n := by
  induction n with
  | zero =>
    simp only [rationalMellinFalling, rationalComplexCast, Rat.cast_one, Rat.cast_zero,
      complexFalling, Finset.range_zero, Finset.prod_empty]
    rfl
  | succ n ih =>
    rw [rationalMellinFalling, rationalComplexCast_mul, ih]
    simp only [complexFalling, Finset.prod_range_succ]
    congr 1
    have hpair :
      rationalComplexCast (-(3 / 4) - n, t / 2) =
        ((-(3 / 4 : ℚ) - n : ℚ) : ℂ) + ((t / 2 : ℚ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp only [rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
          Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      · simp only [rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
          Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [hpair]
    push_cast
    ring

/-- The Gaussian derivative polynomial for rational height, node and π
parameter. Each finite term scales the recursively computed falling product
by an exact rational coefficient. -/
def rationalGaussianPoly (t x p : ℚ) (n k : ℕ) : ℚ × ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    rationalComplexScale ((n.choose j : ℚ) * (x ^ j)⁻¹ * (-p * ((k : ℚ) + 1) ^ 2) ^ (n - j))
      (rationalMellinFalling t j)

/-- The exact rational Gaussian weight of a Taylor cell. It sums the
derivative polynomials with their rational integration coefficients and
applies the factor two from the theta integrand. -/
def rationalGaussianWeight (t a b p : ℚ) (n k : ℕ) : ℚ × ℚ :=
  rationalComplexScale 2
    (∑ l ∈ Finset.range (n + 1),
      rationalComplexScale ((l.factorial : ℚ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1)))
        (rationalGaussianPoly t a p l k))

/-- The rational pair multiplying an integer power in a Gaussian
derivative polynomial. It combines a binomial coefficient, node inverse
power and the critical-exponent falling product. -/
def rationalGaussianCoeff (t x : ℚ) (n j : ℕ) : ℚ × ℚ :=
  rationalComplexScale ((n.choose j : ℚ) * (x ^ j)⁻¹) (rationalMellinFalling t j)

/-- Scaling a rational complex pair scales its componentwise one-norm by
the absolute value of the scalar. This makes the coefficient bound exact. -/
theorem rational_complex_one_norm_scale (c : ℚ) (z : ℚ × ℚ) :
    rationalComplexOneNorm (rationalComplexScale c z) = |c| * rationalComplexOneNorm z := by
  simp only [rationalComplexOneNorm, rationalComplexScale, abs_mul, mul_add]

/-- For `|t| ≤ 100` and `x ≥ 1`, each rational derivative coefficient has a
node-independent one-norm bound. The bound combines the binomial coefficient
with the uniform falling-product majorant. -/
theorem rational_gaussian_coeff_le (t x : ℚ) (ht : |t| ≤ 100) (hx : 1 ≤ x) (n j : ℕ) :
    rationalComplexOneNorm (rationalGaussianCoeff t x n j) ≤
      (n.choose j : ℚ) * rationalMellinFallingBound j := by
  rw [rationalGaussianCoeff, rational_complex_one_norm_scale]
  have hp : 1 ≤ x ^ j := one_le_pow₀ hx
  have hi : (x ^ j)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hp
  have hi0 : 0 ≤ (x ^ j)⁻¹ := inv_nonneg.mpr (pow_nonneg (le_trans (by norm_num only) hx) _)
  have hc0 : (0 : ℚ) ≤ n.choose j := Nat.cast_nonneg _
  have hc : (n.choose j : ℚ) * (x ^ j)⁻¹ ≤ n.choose j := by
    have h := mul_le_mul_of_nonneg_left hi hc0
    simpa only [mul_one] using h
  rw [abs_of_nonneg (mul_nonneg hc0 hi0)]
  exact
    mul_le_mul hc (rational_mellin_falling_le t ht j)
      (by
        dsimp only [rationalComplexOneNorm]; exact add_nonneg (abs_nonneg _) (abs_nonneg _))
      hc0

/-- A common node- and height-independent one-norm bound for a rational
Gaussian derivative polynomial when the π parameter has magnitude at most
four. It uses the shared falling-product majorant. -/
def rationalGaussianPolyBound (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    ((n.choose j : ℚ) * rationalMellinFallingBound j) * (4 * ((k : ℚ) + 1) ^ 2) ^ (n - j)

/-- The polynomial one-norm majorant is monotone in the Gaussian index. -/
theorem rational_gaussian_poly_norm_bound_mono (n : ℕ) {k K : ℕ} (hk : k ≤ K) :
    rationalGaussianPolyBound n k ≤ rationalGaussianPolyBound n K := by
  have hkk : (k : ℚ) + 1 ≤ (K : ℚ) + 1 := add_le_add (Nat.cast_le.mpr hk) le_rfl
  have hsq := pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg k) (by norm_num only)) hkk 2
  have hB := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℚ) ≤ 4)
  have hB0 : (0 : ℚ) ≤ 4 * ((k : ℚ) + 1) ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg _)
  dsimp only [rationalGaussianPolyBound]
  apply Finset.sum_le_sum
  intro j hj
  exact
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hB0 hB (n - j))
      (mul_nonneg (Nat.cast_nonneg _) (rational_mellin_falling_bound_nonneg j))

/-- The rational Gaussian polynomial is bounded by the common positive
majorant for `|t| ≤ 100`, node at least one and `|p| ≤ 4`. -/
theorem rational_gaussian_poly_norm_le (t x p : ℚ) (ht : |t| ≤ 100) (hx : 1 ≤ x) (hp : |p| ≤ 4)
    (n k : ℕ) :
    rationalComplexOneNorm (rationalGaussianPoly t x p n k) ≤ rationalGaussianPolyBound n k := by
  have hs : (0 : ℚ) ≤ ((k : ℚ) + 1) ^ 2 := sq_nonneg _
  have hbase : |-p * ((k : ℚ) + 1) ^ 2| ≤ 4 * ((k : ℚ) + 1) ^ 2 := by
    rw [neg_mul, abs_neg, abs_mul, abs_of_nonneg hs]
    exact mul_le_mul_of_nonneg_right hp hs
  have hB : (0 : ℚ) ≤ 4 * ((k : ℚ) + 1) ^ 2 := mul_nonneg (by norm_num only) hs
  rw [rationalGaussianPoly, rationalGaussianPolyBound]
  refine (rational_complex_one_norm_sum _ _).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  have he :
    rationalComplexScale ((n.choose j : ℚ) * (x ^ j)⁻¹ * (-p * ((k : ℚ) + 1) ^ 2) ^ (n - j))
        (rationalMellinFalling t j) =
      rationalComplexScale ((-p * ((k : ℚ) + 1) ^ 2) ^ (n - j))
        (rationalGaussianCoeff t x n j) := by
    apply Prod.ext <;> simp only [rationalComplexScale, rationalGaussianCoeff] <;> ring
  rw [he, rational_complex_one_norm_scale, abs_pow]
  have hpw := pow_le_pow_left₀ (abs_nonneg (-p * ((k : ℚ) + 1) ^ 2)) hbase (n - j)
  have hc := rational_gaussian_coeff_le t x ht hx n j
  have hm :=
    mul_le_mul hpw hc
      (by
        dsimp only [rationalComplexOneNorm]; exact add_nonneg (abs_nonneg _) (abs_nonneg _))
      (pow_nonneg hB _)
  nlinarith only [hm]

/-- A common one-norm bound for rational Gaussian weights on cells of
width `1/16`. The expression depends only on the Taylor order and Gaussian
index, so one certified comparison applies to all matching cells. -/
def rationalGaussianWeightBound (n k : ℕ) : ℚ :=
  2 *
    ∑ l ∈ Finset.range (n + 1),
      (l.factorial : ℚ)⁻¹ * ((1 / 16 : ℚ) ^ (l + 1) / (l + 1)) * rationalGaussianPolyBound l k

/-- The common weight one-norm majorant is monotone in the Gaussian index. -/
theorem rational_gaussian_weight_norm_bound_mono (n : ℕ) {k K : ℕ} (hk : k ≤ K) :
    rationalGaussianWeightBound n k ≤ rationalGaussianWeightBound n K := by
  dsimp only [rationalGaussianWeightBound]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  apply Finset.sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left (rational_gaussian_poly_norm_bound_mono l hk)
  exact
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (div_nonneg (pow_nonneg (by norm_num only) _)
        (add_nonneg (Nat.cast_nonneg l) (by norm_num only)))

/-- All rational Gaussian cell weights satisfy the common one-norm bound
when `|t| ≤ 100`, the left node is at least one, the width is `1/16`, and
the rational π parameter has magnitude at most four. -/
theorem rational_gaussian_weight_norm_le (t a b p : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) (hp : |p| ≤ 4) (n k : ℕ) :
    rationalComplexOneNorm (rationalGaussianWeight t a b p n k) ≤
      rationalGaussianWeightBound n k := by
  rw [rationalGaussianWeight, rational_complex_one_norm_scale, abs_of_nonneg (by norm_num only)]
  dsimp only [rationalGaussianWeightBound]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  refine (rational_complex_one_norm_sum _ _).trans ?_
  apply Finset.sum_le_sum
  intro l hl
  rw [rational_complex_one_norm_scale, hab]
  have hc : 0 ≤ (l.factorial : ℚ)⁻¹ * ((1 / 16 : ℚ) ^ (l + 1) / (l + 1)) := by
    exact
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (div_nonneg (pow_nonneg (by norm_num only) _)
          (add_nonneg (Nat.cast_nonneg l) (by norm_num only)))
  rw [abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (rational_gaussian_poly_norm_le t a p ht ha hp l k) hc

/-- A rational error budget for replacing π in one derivative polynomial.
It uses the componentwise absolute-value bound and a finite geometric sum;
all inputs and operations are exact rational arithmetic. -/
def rationalGaussianPolyError (t x : ℚ) (n k : ℕ) : ℚ :=
  let B : ℚ := 4 * ((k : ℚ) + 1) ^ 2
  let D : ℚ := ((k : ℚ) + 1) ^ 2 / 10 ^ 50
  ∑ j ∈ Finset.range (n + 1),
    let c := rationalGaussianCoeff t x n j
    (|c.1| + |c.2|) * (D * ∑ h ∈ Finset.range (n - j), B ^ h * B ^ (n - j - 1 - h))

/-- The same rational derivative error budget with its geometric sum
collapsed to `(n-j) * B^(n-j-1)`. It avoids the nested sum in finite
endpoint computations while preserving the exact value. -/
def rationalGaussianPolyErrorFast (t x : ℚ) (n k : ℕ) : ℚ :=
  let B : ℚ := 4 * ((k : ℚ) + 1) ^ 2
  let D : ℚ := ((k : ℚ) + 1) ^ 2 / 10 ^ 50
  ∑ j ∈ Finset.range (n + 1),
    let c := rationalGaussianCoeff t x n j
    (|c.1| + |c.2|) * (D * ((n - j : ℕ) : ℚ) * B ^ (n - j - 1))

/-- A node- and height-independent rational majorant for the derivative
error budget when the node is at least one and `|t| ≤ 100`. It replaces each
coefficient one-norm by the common falling-product bound. -/
def rationalGaussianPolyErrorBound (n k : ℕ) : ℚ :=
  let B : ℚ := 4 * ((k : ℚ) + 1) ^ 2
  let D : ℚ := ((k : ℚ) + 1) ^ 2 / 10 ^ 50
  ∑ j ∈ Finset.range (n + 1),
    ((n.choose j : ℚ) * rationalMellinFallingBound j) * (D * ((n - j : ℕ) : ℚ) * B ^ (n - j - 1))

/-- The fast derivative error budget is bounded by the common majorant at
every node at least one and every rational height of magnitude at most 100. -/
theorem rational_gaussian_poly_error_le (t x : ℚ) (ht : |t| ≤ 100) (hx : 1 ≤ x) (n k : ℕ) :
    rationalGaussianPolyErrorFast t x n k ≤ rationalGaussianPolyErrorBound n k := by
  dsimp only [rationalGaussianPolyErrorFast, rationalGaussianPolyErrorBound]
  apply Finset.sum_le_sum
  intro j hj
  apply mul_le_mul_of_nonneg_right (rational_gaussian_coeff_le t x ht hx n j)
  apply mul_nonneg
  · exact mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num only)) (Nat.cast_nonneg _)
  · exact pow_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _)) _

/-- The common derivative-error majorant is monotone in the Gaussian
index. This permits one certificate for the largest of the eight indices. -/
theorem rational_gaussian_poly_bound_mono (n : ℕ) {k K : ℕ} (hk : k ≤ K) :
    rationalGaussianPolyErrorBound n k ≤ rationalGaussianPolyErrorBound n K := by
  have hkk : (k : ℚ) + 1 ≤ (K : ℚ) + 1 := add_le_add (Nat.cast_le.mpr hk) le_rfl
  have hsq := pow_le_pow_left₀ (add_nonneg (Nat.cast_nonneg k) (by norm_num only)) hkk 2
  have hB := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℚ) ≤ 4)
  have hD := div_le_div_of_nonneg_right hsq (by norm_num only : (0 : ℚ) ≤ 10 ^ 50)
  dsimp only [rationalGaussianPolyErrorBound]
  apply Finset.sum_le_sum
  intro j hj
  apply
    mul_le_mul_of_nonneg_left _
      (mul_nonneg (Nat.cast_nonneg _) (rational_mellin_falling_bound_nonneg j))
  have hD' := mul_le_mul_of_nonneg_right hD (Nat.cast_nonneg (n - j) : (0 : ℚ) ≤ ((n - j : ℕ) : ℚ))
  have hB0 : (0 : ℚ) ≤ 4 * ((k : ℚ) + 1) ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg _)
  have hpow := pow_le_pow_left₀ hB0 hB (n - j - 1)
  exact
    mul_le_mul hD' hpow (pow_nonneg hB0 _)
      (mul_nonneg (div_nonneg (sq_nonneg _) (by norm_num only)) (Nat.cast_nonneg _))

/-- The collapsed error budget is exactly the original geometric-sum
budget for every rational input and derivative order. -/
theorem rational_gaussian_poly_error_fast (t x : ℚ) (n k : ℕ) :
    rationalGaussianPolyErrorFast t x n k = rationalGaussianPolyError t x n k := by
  simp only [rationalGaussianPolyErrorFast, rationalGaussianPolyError, geom_sum₂_self]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- The exact rational π-perturbation error budget for an entire Taylor
cell's Gaussian weight. It sums the derivative budgets with absolute values
of the rational integration coefficients. -/
def rationalGaussianWeightError (t a b : ℚ) (n k : ℕ) : ℚ :=
  2 *
    ∑ l ∈ Finset.range (n + 1),
      |(l.factorial : ℚ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))| * rationalGaussianPolyError t a l k

/-- A Taylor-cell error budget using the collapsed derivative error formula.
The exact rational value agrees with the original finite-sum budget. -/
def rationalGaussianWeightErrorFast (t a b : ℚ) (n k : ℕ) : ℚ :=
  2 *
    ∑ l ∈ Finset.range (n + 1),
      |(l.factorial : ℚ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))| * rationalGaussianPolyErrorFast t a l k

/-- A common rational error budget for any cell of width `1/16`, every
node at least one, and every rational height of magnitude at most 100. It
depends only on the derivative order and Gaussian index. -/
def rationalGaussianWeightErrorBound (n k : ℕ) : ℚ :=
  2 *
    ∑ l ∈ Finset.range (n + 1),
      (l.factorial : ℚ)⁻¹ * ((1 / 16 : ℚ) ^ (l + 1) / (l + 1)) * rationalGaussianPolyErrorBound l k

/-- A cell of width `1/16` satisfies the common rational π-substitution
budget whenever its node is at least one and `|t| ≤ 100`. -/
theorem rational_gaussian_weight_error_le (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) (n k : ℕ) :
    rationalGaussianWeightErrorFast t a b n k ≤ rationalGaussianWeightErrorBound n k := by
  dsimp only [rationalGaussianWeightErrorFast, rationalGaussianWeightErrorBound]
  rw [hab]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  apply Finset.sum_le_sum
  intro l hl
  have hw : 0 ≤ (l.factorial : ℚ)⁻¹ * ((1 / 16 : ℚ) ^ (l + 1) / (l + 1)) := by
    apply mul_nonneg
    · exact inv_nonneg.mpr (Nat.cast_nonneg _)
    · exact
        div_nonneg (pow_nonneg (by norm_num only) _)
          (add_nonneg (Nat.cast_nonneg l) (by norm_num only))
  rw [abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_left (rational_gaussian_poly_error_le t a ht ha l k) hw

/-- The common cell-error majorant is monotone in the Gaussian index. One
finite comparison at the largest index therefore covers all earlier terms. -/
theorem rational_gaussian_weight_bound_mono (n : ℕ) {k K : ℕ} (hk : k ≤ K) :
    rationalGaussianWeightErrorBound n k ≤ rationalGaussianWeightErrorBound n K := by
  dsimp only [rationalGaussianWeightErrorBound]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  apply Finset.sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left (rational_gaussian_poly_bound_mono l hk)
  apply mul_nonneg
  · exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · exact
      div_nonneg (pow_nonneg (by norm_num only) _)
        (add_nonneg (Nat.cast_nonneg l) (by norm_num only))

/-- The fast cell budget preserves the original rational error bound at
every cell, including the final block. -/
theorem rational_gaussian_weight_error_fast (t a b : ℚ) (n k : ℕ) :
    rationalGaussianWeightErrorFast t a b n k = rationalGaussianWeightError t a b n k := by
  simp only [rationalGaussianWeightErrorFast, rationalGaussianWeightError,
    rational_gaussian_poly_error_fast]

/-- The zeroth-order first-cell weight equals one eighth. This exact kernel
check exercises the executable finite-sum and rational-pair definitions. -/
theorem rational_gaussian_weight_first :
    rationalGaussianWeight (1413 / 100) 1 (17 / 16)
        (314159265358979323846264338327950288419716939937510 / 10 ^ 50) 0 0 =
      (1 / 8, 0) := by
  decide +kernel

/-- The zeroth-order first-cell π-substitution error budget is zero. The
finite sum has no power-difference terms at order zero, which is verified
directly by the kernel. -/
theorem rational_gaussian_error_first :
    rationalGaussianWeightError (1413 / 100) 1 (17 / 16) 0 0 = 0 := by decide +kernel

/-- At first order, the first-cell π-substitution error budget is the exact
rational `1 / (256 * 10^50)`. This check exercises a nonzero finite error
term without importing any numerical table. -/
theorem rational_gaussian_error_first_order :
    rationalGaussianWeightError (1413 / 100) 1 (17 / 16) 1 0 = 1 / (256 * 10 ^ 50) := by
  decide +kernel

end PseudoPrime.Analysis
