/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialMeanSquareSchur

/-!
# Direct point bounds from actual weighted rows

Apply Schur directly to the differentiated coefficients. This avoids the prefix-difference
and Abel losses when a finite absolute height bound is already known.
-/

@[expose] public section

namespace PseudoPrime.Analysis.ExponentialMeanSquare

/-- A weighted row budget controls the actual derivative energy by the weighted second
height moment of the coefficients. Regroup the differentiated multiplicity coefficient
and apply Schur to the differentiated coefficient family. -/
theorem derivative_energy_le_weighted_rows {ι : Type*} (s : Finset ι) (γ m : ι → ℝ) (a : ι → ℂ)
    {R : ℝ} (hm : ∀ i ∈ s, 0 ≤ m i) (hR : ∀ i ∈ s, ∑ j ∈ s, m j * gramKernel (γ i - γ j) ≤ R) :
    energy (exponentialSum s γ (fun i ↦ Complex.I * γ i * ((m i : ℂ) * a i))) ≤
      R * ∑ i ∈ s, m i * ((γ i) ^ 2 * ‖a i‖ ^ 2) := by
  have he :
    (fun i ↦ Complex.I * γ i * ((m i : ℂ) * a i)) = fun i ↦
      (m i : ℂ) * (Complex.I * γ i * a i) := by
    funext i
    ring
  rw [he]
  have h := energy_le_weighted_rows s γ m (fun i ↦ Complex.I * γ i * a i) hm hR
  have hn : ∀ i, ‖Complex.I * γ i * a i‖ ^ 2 = (γ i) ^ 2 * ‖a i‖ ^ 2 := by
    intro i
    rw [norm_mul, norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow,
      sq_abs]
  simpa only [hn] using h

/-- On an absolute height window H, the actual derivative energy has budget H squared
times the original weighted row allowance. Use the second coefficient moment, with
all multiplicities retained. -/
theorem derivative_energy_le_weighted_rows_height {ι : Type*} (s : Finset ι) (γ m : ι → ℝ)
    (a : ι → ℂ) {R H : ℝ} (hR0 : 0 ≤ R) (hH : 0 ≤ H) (hm : ∀ i ∈ s, 0 ≤ m i)
    (hheight : ∀ i ∈ s, |γ i| ≤ H) (hR : ∀ i ∈ s, ∑ j ∈ s, m j * gramKernel (γ i - γ j) ≤ R) :
    energy (exponentialSum s γ (fun i ↦ Complex.I * γ i * ((m i : ℂ) * a i))) ≤
      H ^ 2 * (R * ∑ i ∈ s, m i * ‖a i‖ ^ 2) := by
  have he := derivative_energy_le_weighted_rows s γ m a hm hR
  have hs : (∑ i ∈ s, m i * ((γ i) ^ 2 * ‖a i‖ ^ 2)) ≤ H ^ 2 * ∑ i ∈ s, m i * ‖a i‖ ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    have hg := (sq_le_sq₀ (abs_nonneg (γ i)) hH).mpr (hheight i hi)
    rw [sq_abs] at hg
    have h := mul_le_mul_of_nonneg_right hg (mul_nonneg (hm i hi) (sq_nonneg ‖a i‖))
    nlinarith only [h]
  have h := he.trans (mul_le_mul_of_nonneg_left hs hR0)
  nlinarith only [h]

/-- An absolute height window and a nonnegative weighted row budget give the direct
point bound (1+H)R times coefficient l2 mass. Supply both actual energies to Sobolev;
there is no Abel prefix-difference factor four. -/
theorem point_le_weighted_rows_height {ι : Type*} (s : Finset ι) (γ m : ι → ℝ) (a : ι → ℂ) {R H : ℝ}
    (hR0 : 0 ≤ R) (hH : 0 ≤ H) (hm : ∀ i ∈ s, 0 ≤ m i) (hheight : ∀ i ∈ s, |γ i| ≤ H)
    (hR : ∀ i ∈ s, ∑ j ∈ s, m j * gramKernel (γ i - γ j) ≤ R) :
    ‖exponentialSum s γ (fun i ↦ (m i : ℂ) * a i) 0‖ ^ 2 ≤
      (1 + H) * (R * ∑ i ∈ s, m i * ‖a i‖ ^ 2) := by
  have hA : 0 ≤ R * ∑ i ∈ s, m i * ‖a i‖ ^ 2 :=
    mul_nonneg hR0 (Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hm i hi) (sq_nonneg _)))
  have he := energy_le_weighted_rows s γ m a hm hR
  have hd := derivative_energy_le_weighted_rows_height s γ m a hR0 hH hm hheight hR
  have hp :=
    exponentialSum_point_le_of_energy_derivative_bound s γ (fun i ↦ (m i : ℂ) * a i) (A :=
      (R * ∑ i ∈ s, m i * ‖a i‖ ^ 2) / 4) (div_nonneg hA (by norm_num only)) hH
      (by nlinarith only [he]) (by nlinarith only [hd])
  nlinarith only [hp]

end PseudoPrime.Analysis.ExponentialMeanSquare
