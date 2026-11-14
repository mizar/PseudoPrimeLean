/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.RationalMellinWeight

/-! # Tail bounds for rational Mellin weights -/

public section

namespace PseudoPrime.Analysis

/-- The difference between two rational weights is bounded by the difference
of their common nonnegative majorants. The Taylor orders satisfy `m ≤ n`,
the cell has width `1/16`, and the height and π replacement are bounded. -/
theorem rational_gaussian_weight_tail_le (t a b p : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) (hp : |p| ≤ 4) {m n k : ℕ} (hmn : m ≤ n) :
    rationalComplexOneNorm
        (rationalGaussianWeight t a b p n k - rationalGaussianWeight t a b p m k) ≤
      rationalGaussianWeightBound n k - rationalGaussianWeightBound m k := by
  let f : ℕ → ℚ × ℚ := fun l ↦
    rationalComplexScale ((l.factorial : ℚ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1)))
      (rationalGaussianPoly t a p l k)
  let g : ℕ → ℚ := fun l ↦
    (l.factorial : ℚ)⁻¹ * ((1 / 16 : ℚ) ^ (l + 1) / (l + 1)) * rationalGaussianPolyBound l k
  let S := (Finset.range (n + 1)).filter (fun l ↦ m + 1 ≤ l)
  have hmn' : m + 1 ≤ n + 1 := Nat.add_le_add_right hmn 1
  have hf :
    rationalGaussianWeight t a b p n k - rationalGaussianWeight t a b p m k =
      rationalComplexScale 2 (∑ l ∈ S, f l) := by
    dsimp only [rationalGaussianWeight, S]
    rw [← Finset.sum_range_sub_sum_range hmn']
    apply Prod.ext <;>
      simp only [rationalComplexScale, Prod.fst_sub, Prod.snd_sub, Prod.fst_sum, Prod.snd_sum,
        f] <;>
      ring
  have hg :
    rationalGaussianWeightBound n k - rationalGaussianWeightBound m k = 2 * ∑ l ∈ S, g l := by
    dsimp only [rationalGaussianWeightBound, S]
    rw [← Finset.sum_range_sub_sum_range hmn']
    dsimp only [g]
    ring
  rw [hf, hg, rational_complex_one_norm_scale, abs_of_nonneg (by norm_num only : (0 : ℚ) ≤ 2)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  refine (rational_complex_one_norm_sum _ _).trans ?_
  apply Finset.sum_le_sum
  intro l hl
  dsimp only [f, g]
  rw [rational_complex_one_norm_scale, hab]
  have hc : 0 ≤ (l.factorial : ℚ)⁻¹ * ((1 / 16 : ℚ) ^ (l + 1) / (l + 1)) := by
    exact
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
        (div_nonneg (pow_nonneg (by norm_num only) _)
          (add_nonneg (Nat.cast_nonneg l) (by norm_num only)))
  rw [abs_of_nonneg hc]
  exact mul_le_mul_of_nonneg_left (rational_gaussian_poly_norm_le t a p ht ha hp l k) hc

/-- The difference of the weight majorants is monotone in the Gaussian
index when the lower Taylor order does not exceed the upper order. -/
theorem rational_gaussian_weight_tail_mono {m n k K : ℕ} (hmn : m ≤ n) (hk : k ≤ K) :
    rationalGaussianWeightBound n k - rationalGaussianWeightBound m k ≤
      rationalGaussianWeightBound n K - rationalGaussianWeightBound m K := by
  have hmn' : m + 1 ≤ n + 1 := Nat.add_le_add_right hmn 1
  dsimp only [rationalGaussianWeightBound]
  have he :
    ∀ (f : ℕ → ℚ),
      2 * (∑ l ∈ Finset.range (n + 1), f l) - 2 * (∑ l ∈ Finset.range (m + 1), f l) =
        2 * ∑ l ∈ (Finset.range (n + 1)).filter (fun l ↦ m + 1 ≤ l), f l := by
    intro f
    rw [← Finset.sum_range_sub_sum_range hmn']
    ring
  rw [he, he]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  apply Finset.sum_le_sum
  intro l hl
  apply mul_le_mul_of_nonneg_left (rational_gaussian_poly_norm_bound_mono l hk)
  exact
    mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
      (div_nonneg (pow_nonneg (by norm_num only) _)
        (add_nonneg (Nat.cast_nonneg l) (by norm_num only)))

set_option maxRecDepth 16384 in
set_option maxHeartbeats 8000000 in
-- Exact reduction compares the two 200th- and 127th-order majorants.
/-- The common weight majorant of terms 128 through 200 is below `10⁻⁴⁹`
for the largest Gaussian index. The comparison uses exact rational arithmetic. -/
theorem rational_gaussian_tail_bound :
    rationalGaussianWeightBound 200 7 - rationalGaussianWeightBound 127 7 < 1 / 10 ^ 49 := by
  decide +kernel

/-- For every admissible cell and each of the eight Gaussian indices,
truncating the rational Gaussian weight at order 127 changes its one-norm
by less than `10⁻⁴⁹`. The common tail comparison is reused for every cell. -/
theorem rational_gaussian_weight_tail_small (t a b p : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) (hp : |p| ≤ 4) {k : ℕ} (hk : k < 8) :
    rationalComplexOneNorm
        (rationalGaussianWeight t a b p 200 k - rationalGaussianWeight t a b p 127 k) <
      1 / 10 ^ 49 := by
  have hk' : k ≤ 7 := Nat.lt_succ_iff.mp hk
  exact
    ((rational_gaussian_weight_tail_le t a b p ht ha hab hp (by norm_num only)).trans
          (rational_gaussian_weight_tail_mono (by norm_num only) hk')).trans_lt
      rational_gaussian_tail_bound

end PseudoPrime.Analysis
