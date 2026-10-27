/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquareRowPointBounds

/-!
# A limitation of coefficient-independent point budgets

A point bound C times weighted coefficient l2 mass, valid for every coefficient family,
must have C at least the total multiplicity. Weighted Cauchy-Schwarz then shows that its
upper bound is never smaller than the squared triangle-inequality upper bound.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- Nonnegative finite weights give weighted Cauchy-Schwarz for arbitrary real coefficients.
Apply the square-versus-product form with pointwise equality of the two products.
This compares the squared triangle bound with total mass times coefficient l2 mass. -/
theorem weighted_sum_sq_le_mass {ι : Type*} (s : Finset ι) (m x : ι → ℝ) (hm : ∀ i ∈ s, 0 ≤ m i) :
    (∑ i ∈ s, m i * x i) ^ 2 ≤ (∑ i ∈ s, m i) * ∑ i ∈ s, m i * (x i) ^ 2 := by
  exact
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s hm (fun i hi ↦ mul_nonneg (hm i hi) (sq_nonneg _))
      (fun i hi ↦ by exact le_of_eq (by ring))

/-- A nonnegative coefficient-independent complex point budget must be at least the
total nonnegative weight. Test the point bound on coefficients identically one, treating
zero total weight separately before cancelling a positive mass. -/
theorem mass_le_uniform_point_budget {ι : Type*} (s : Finset ι) (m : ι → ℝ) {C : ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hC : 0 ≤ C)
    (hp : ∀ a : ι → ℂ, ‖∑ i ∈ s, (m i : ℂ) * a i‖ ^ 2 ≤ C * ∑ i ∈ s, m i * ‖a i‖ ^ 2) :
    ∑ i ∈ s, m i ≤ C := by
  have hm0 := Finset.sum_nonneg hm
  by_cases hz : ∑ i ∈ s, m i = 0
  · rw [hz]
    exact hC
  · have hpos := lt_of_le_of_ne hm0 (Ne.symm hz)
    have h := hp (fun _ ↦ 1)
    simp only [mul_one, norm_one, one_pow] at h
    rw [← Complex.ofReal_sum, Complex.norm_of_nonneg hm0] at h
    nlinarith only [h, hpos]

/-- Every coefficient-independent weighted l2 point budget dominates the squared triangle
bound for every coefficient family. Combine the constant-coefficient mass test with
weighted Cauchy-Schwarz; no zero-distribution or kernel hypothesis is required. -/
theorem triangle_sq_le_uniform_point_budget {ι : Type*} (s : Finset ι) (m : ι → ℝ) {C : ℝ}
    (hm : ∀ i ∈ s, 0 ≤ m i) (hC : 0 ≤ C)
    (hp : ∀ a : ι → ℂ, ‖∑ i ∈ s, (m i : ℂ) * a i‖ ^ 2 ≤ C * ∑ i ∈ s, m i * ‖a i‖ ^ 2) (a : ι → ℂ) :
    (∑ i ∈ s, m i * ‖a i‖) ^ 2 ≤ C * ∑ i ∈ s, m i * ‖a i‖ ^ 2 := by
  have hmass := mass_le_uniform_point_budget s m hm hC hp
  exact
    (weighted_sum_sq_le_mass s m (fun i ↦ ‖a i‖) hm).trans
      (mul_le_mul_of_nonneg_right hmass
        (Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hm i hi) (sq_nonneg _))))

/-- The previously proved direct Schur-Sobolev point upper bound cannot improve the
squared triangle upper bound for any coefficient family on the same finite height window.
Apply the general obstruction to its coefficient-independent point budget. -/
theorem triangle_sq_le_row_point_budget {ι : Type*} (s : Finset ι) (γ m : ι → ℝ) (a : ι → ℂ)
    {R H : ℝ} (hR0 : 0 ≤ R) (hH : 0 ≤ H) (hm : ∀ i ∈ s, 0 ≤ m i) (hheight : ∀ i ∈ s, |γ i| ≤ H)
    (hR : ∀ i ∈ s, ∑ j ∈ s, m j * gramKernel (γ i - γ j) ≤ R) :
    (∑ i ∈ s, m i * ‖a i‖) ^ 2 ≤ (1 + H) * (R * ∑ i ∈ s, m i * ‖a i‖ ^ 2) := by
  have hC : 0 ≤ (1 + H) * R := mul_nonneg (by linarith only [hH]) hR0
  have hp :
    ∀ b : ι → ℂ, ‖∑ i ∈ s, (m i : ℂ) * b i‖ ^ 2 ≤ ((1 + H) * R) * ∑ i ∈ s, m i * ‖b i‖ ^ 2 := by
    intro b
    have h := point_le_weighted_rows_height s γ m b hR0 hH hm hheight hR
    simpa only [exponentialSum, Complex.ofReal_zero, mul_zero, Complex.exp_zero, mul_one,
      mul_assoc] using h
  simpa only [mul_assoc] using triangle_sq_le_uniform_point_budget s m hm hC hp a

end PseudoPrime.Analysis.ExponentialMeanSquare
