/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Weighted finite Schur bounds

Symmetry and nonnegativity turn row budgets into quadratic-form bounds.
Weights retain zero multiplicities without replacing them by distinct-zero counts.
-/

@[expose] public section

namespace PseudoPrime.Analysis.FiniteSymmetricKernel

/-- For nonnegative weights and kernel entry, twice a mixed quadratic term is at most
the two diagonal terms. Multiply the square of the coefficient difference by the weight.
This is the pointwise input to the weighted Schur estimate. -/
theorem mixed_le_diagonal {u v k : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (hk : 0 ≤ k) (a b : ℝ) :
    2 * (u * v * a * b * k) ≤ u * a ^ 2 * (v * k) + v * b ^ 2 * (u * k) := by
  have h := mul_nonneg (mul_nonneg (mul_nonneg hu hv) hk) (sq_nonneg (a - b))
  nlinarith only [h]

/-- A symmetric nonnegative finite kernel obeys a weighted quadratic-form bound by
its actual row sums. Sum the mixed-term inequality and transpose the second diagonal sum.
The weights may vanish and need not be normalized. -/
theorem quadratic_le_rows {ι : Type*} (s : Finset ι) (K : ι → ι → ℝ) (m b : ι → ℝ)
    (hm : ∀ i ∈ s, 0 ≤ m i) (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hKs : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i) :
    ∑ i ∈ s, ∑ j ∈ s, m i * m j * b i * b j * K i j ≤
      ∑ i ∈ s, m i * (b i) ^ 2 * (∑ j ∈ s, m j * K i j) := by
  have hterm :=
    Finset.sum_le_sum (s := s)
      (fun i hi ↦
        Finset.sum_le_sum (s := s)
          (fun j hj ↦ mixed_le_diagonal (hm i hi) (hm j hj) (hK i hi j hj) (b i) (b j)))
  have hswap :
    (∑ i ∈ s, ∑ j ∈ s, m j * (b j) ^ 2 * (m i * K i j)) =
      ∑ i ∈ s, ∑ j ∈ s, m i * (b i) ^ 2 * (m j * K i j) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hKs j hj i hi]
  simp only [← Finset.mul_sum, Finset.sum_add_distrib] at hterm
  rw [hswap] at hterm
  simp only [← Finset.mul_sum] at hterm
  linarith only [hterm]

/-- Uniform row budget R gives the weighted l2 Schur bound for arbitrary real coefficients.
Combine the row identity with nonnegative diagonal coefficient weights. -/
theorem quadratic_le_of_rows {ι : Type*} (s : Finset ι) (K : ι → ι → ℝ) (m b : ι → ℝ) {R : ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hK : ∀ i ∈ s, ∀ j ∈ s, 0 ≤ K i j)
    (hKs : ∀ i ∈ s, ∀ j ∈ s, K i j = K j i) (hR : ∀ i ∈ s, ∑ j ∈ s, m j * K i j ≤ R) :
    ∑ i ∈ s, ∑ j ∈ s, m i * m j * b i * b j * K i j ≤ R * ∑ i ∈ s, m i * (b i) ^ 2 := by
  have h := quadratic_le_rows s K m b hm hK hKs
  have hr :=
    Finset.sum_le_sum (s := s)
      (fun i hi ↦ mul_le_mul_of_nonneg_left (hR i hi) (mul_nonneg (hm i hi) (sq_nonneg (b i))))
  rw [← Finset.sum_mul] at hr
  nlinarith only [h, hr]

end PseudoPrime.Analysis.FiniteSymmetricKernel
