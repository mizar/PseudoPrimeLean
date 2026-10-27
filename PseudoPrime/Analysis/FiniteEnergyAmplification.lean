/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring

/-! # Finite matrix estimates for energy amplification -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A finite natural-valued matrix with column sums μr has squared column
mass at most the row count times its squared-entry mass. Apply finite
Cauchy–Schwarz columnwise and sum. This avoids spectral theory in the
weighted-correlation amplification step. -/
theorem matrix_energy_le_of_column_sums {ι α : Type*} [Fintype ι] [Fintype α] (u : ι → α → ℕ)
    (r : α → ℕ) (μ : ℕ) (h : ∀ a, (∑ x, u x a) = μ * r a) :
    μ ^ 2 * (∑ a, r a ^ 2) ≤ Fintype.card ι * ∑ a, ∑ x, u x a ^ 2 := by
  have hs :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun a (_ : a ∈ (Finset.univ : Finset α)) ↦
        Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset ι) (fun _ ↦ (1 : ℕ)) (fun x ↦ u x a))
  simp only [one_mul, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
    Nat.cast_id, h, mul_pow, ← Finset.mul_sum] at hs
  exact hs

/-- If the weighted row mass B equals tμ and a matrix has column sums μr,
then B² times the correlation energy is at most t³ times its entry energy.
Multiply the columnwise estimate by t² and use the exact mass identity.
No positivity or division by t is needed, including the empty case. -/
theorem weighted_energy_amplification {ι α : Type*} [Fintype ι] [Fintype α] (u : ι → α → ℕ)
    (r : α → ℕ) (μ B : ℕ) (h : ∀ a, (∑ x, u x a) = μ * r a) (hB : B = Fintype.card ι * μ) :
    B ^ 2 * (∑ a, r a ^ 2) ≤ (Fintype.card ι) ^ 3 * ∑ a, ∑ x, u x a ^ 2 := by
  have hm := Nat.mul_le_mul_left ((Fintype.card ι) ^ 2) (matrix_energy_le_of_column_sums u r μ h)
  calc
    _ = (Fintype.card ι) ^ 2 * (μ ^ 2 * (∑ a, r a ^ 2)) := by
      rw [hB]; ring
    _ ≤ (Fintype.card ι) ^ 2 * (Fintype.card ι * ∑ a, ∑ x, u x a ^ 2) := hm
    _ = _ := by ring

/-- If the weighted mass B is at most the correlation energy, the stronger
B²E amplification also implies B³≤t³Q. Multiply B≤E by B² and compose.
This supplies the weaker form used in the published energy argument. -/
theorem weighted_mass_cube_le {ι α : Type*} [Fintype ι] [Fintype α] (u : ι → α → ℕ) (r : α → ℕ)
    (μ B : ℕ) (h : ∀ a, (∑ x, u x a) = μ * r a) (hB : B = Fintype.card ι * μ)
    (hE : B ≤ ∑ a, r a ^ 2) : B ^ 3 ≤ (Fintype.card ι) ^ 3 * ∑ a, ∑ x, u x a ^ 2 := by
  calc
    _ = B ^ 2 * B := by ring
    _ ≤ B ^ 2 * (∑ a, r a ^ 2) := Nat.mul_le_mul_left _ hE
    _ ≤ _ := weighted_energy_amplification u r μ B h hB

end PseudoPrime.Analysis
