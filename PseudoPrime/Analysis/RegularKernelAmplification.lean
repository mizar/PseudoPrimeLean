/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteEnergyAmplification

/-! # Energy amplification for a regular symmetric finite kernel -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A symmetric natural-valued kernel with constant row mass μ also has
column mass μ. Consequently its action on an incidence matrix has column
sums μ times the original column sums. This verifies the column hypothesis
of finite energy amplification directly from regularity. -/
theorem regular_kernel_column_sum {ι α : Type*} [Fintype ι] (k : ι → ι → ℕ) (v : ι → α → ℕ) (μ : ℕ)
    (hs : ∀ x y, k x y = k y x) (hr : ∀ y, ∑ x, k y x = μ) (a : α) :
    (∑ x, ∑ y, k x y * v y a) = μ * ∑ y, v y a := by
  rw [Finset.sum_comm]
  simp only [← Finset.sum_mul, hs, hr, Finset.mul_sum]

/-- The squared-entry mass of a kernel acting on an incidence matrix equals
its triple weighted overlap sum. Expand the squares and interchange finite
sums. This identifies the amplification output with concrete correlations. -/
theorem kernel_square_mass_eq_triple {ι α : Type*} [Fintype ι] [Fintype α] (k : ι → ι → ℕ)
    (v : ι → α → ℕ) :
    (∑ a, ∑ x, (∑ y, k x y * v y a) ^ 2) = ∑ x, ∑ y, ∑ z, k x y * k x z * (∑ a, v y a * v z a) := by
  simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  congr 1
  funext x
  rw [Finset.sum_comm]
  congr 1
  funext y
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- A regular symmetric kernel amplifies the energy of any natural-valued
incidence matrix into its triple overlap sum. The weighted mass is the
actual sum of kernel entries, rather than an independent input. Verify
column sums, apply finite Cauchy–Schwarz, and expand the entry squares. -/
theorem regular_kernel_energy_amplification {ι α : Type*} [Fintype ι] [Fintype α] (k : ι → ι → ℕ)
    (v : ι → α → ℕ) (μ : ℕ) (hs : ∀ x y, k x y = k y x) (hr : ∀ y, ∑ x, k y x = μ) :
    (∑ x, ∑ y, k x y) ^ 2 * (∑ a, (∑ y, v y a) ^ 2) ≤
      (Fintype.card ι) ^ 3 * ∑ x, ∑ y, ∑ z, k x y * k x z * (∑ a, v y a * v z a) := by
  have h :=
    weighted_energy_amplification (fun x a ↦ ∑ y, k x y * v y a) (fun a ↦ ∑ y, v y a) μ
      (∑ x, ∑ y, k x y) (regular_kernel_column_sum k v μ hs hr)
      (by simp only [hr, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id])
  rw [kernel_square_mass_eq_triple] at h
  exact h

end PseudoPrime.Analysis
