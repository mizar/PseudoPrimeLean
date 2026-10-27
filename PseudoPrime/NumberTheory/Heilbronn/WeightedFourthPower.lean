/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Fourier.ZMod

/-! # A finite weighted fourth-power inequality -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For a nonnegative weight M, two Cauchy-Schwarz inequalities bound the fourth
power of the weighted sum by the squared mass, square mass and fourth moment.
The values T may have either sign; the result is used for Fourier norms. -/
theorem weighted_fourth_power_le {ι : Type*} (S : Finset ι) (M T : ι → ℝ) (hM : ∀ i ∈ S, 0 ≤ M i) :
    (∑ i ∈ S, M i * T i) ^ 4 ≤ (∑ i ∈ S, M i) ^ 2 * (∑ i ∈ S, M i ^ 2) * (∑ i ∈ S, T i ^ 4) := by
  have h₁ :=
    Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul S (r := fun i ↦ M i * T i) (f := M) (g := fun i ↦
      M i * T i ^ 2) hM (fun i hi ↦ mul_nonneg (hM i hi) (sq_nonneg (T i)))
      (fun i hi ↦ le_of_eq (by ring))
  have h₂ := Finset.sum_mul_sq_le_sq_mul_sq S M (fun i ↦ T i ^ 2)
  have hpos : 0 ≤ (∑ i ∈ S, M i) * (∑ i ∈ S, M i * T i ^ 2) :=
    mul_nonneg (Finset.sum_nonneg hM)
      (Finset.sum_nonneg (fun i hi ↦ mul_nonneg (hM i hi) (sq_nonneg (T i))))
  have hsq := (sq_le_sq₀ (sq_nonneg (∑ i ∈ S, M i * T i)) hpos).2 h₁
  have hmul := mul_le_mul_of_nonneg_left h₂ (sq_nonneg (∑ i ∈ S, M i))
  calc
    _ ≤ ((∑ i ∈ S, M i) * (∑ i ∈ S, M i * T i ^ 2)) ^ 2 := by nlinarith only [hsq]
    _ = (∑ i ∈ S, M i) ^ 2 * (∑ i ∈ S, M i * T i ^ 2) ^ 2 := by ring
    _ ≤ _ := by simpa only [← pow_mul, mul_assoc] using hmul

end PseudoPrime.NumberTheory.Heilbronn
