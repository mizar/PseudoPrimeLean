/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.DirichletCharacter.Bounds
public import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
public import Mathlib.Analysis.Complex.Polynomial.Basic
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-! # Finite weighted progression sums from character orthogonality -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a unit residue, positive modulus, finite support, and complex weights,
summing weighted character sums gives the totient times the restricted sum.
Exchange the finite sums and apply character orthogonality pointwise. This
retains the principal term and all nonprincipal errors without a family factor. -/
theorem sum_character_weighted_eq_progression {q : ℕ} [NeZero q] (u : (ZMod q)ˣ) (S : Finset ℕ)
    (w : ℕ → ℂ) :
    (∑ χ : DirichletCharacter ℂ q, χ (↑(u⁻¹) : ZMod q) * ∑ n ∈ S, w n * χ n) =
      (q.totient : ℂ) * ∑ n ∈ S.filter (fun n : ℕ ↦ (u : ZMod q) = (n : ZMod q)), w n := by
  classical
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  trans ∑ n ∈ S, w n * (if (u : ZMod q) = n then (q.totient : ℂ) else 0)
  · apply Finset.sum_congr rfl
    intro n _
    trans ∑ χ : DirichletCharacter ℂ q, w n * (χ (↑(u⁻¹) : ZMod q) * χ n)
    · exact Finset.sum_congr rfl (fun _ _ ↦ by ring)
    rw [← Finset.mul_sum, ← ZMod.inv_coe_unit,
      DirichletCharacter.sum_char_inv_mul_char_eq ℂ (Units.isUnit u)]
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n _
    split_ifs <;> ring

open Classical in
/-- For any finite character family at a positive modulus and unit residue,
the weighted real sum is at least the principal real value minus the sum of
nonprincipal norms. Split off the principal character and use character norm
at most one. This is the error interface for progression lower bounds. -/
theorem principal_re_sub_nonprincipal_norm_sum_le_weighted_re {q : ℕ} [NeZero q] (u : (ZMod q)ˣ)
    (F : DirichletCharacter ℂ q → ℂ) :
    (F 1).re - ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖F χ‖ ≤
      (∑ χ : DirichletCharacter ℂ q, χ (↑(u⁻¹) : ZMod q) * F χ).re := by
  classical
  have he :=
    Finset.add_sum_erase (Finset.univ : Finset (DirichletCharacter ℂ q))
      (fun χ ↦ χ (↑(u⁻¹) : ZMod q) * F χ) (Finset.mem_univ 1)
  rw [MulChar.one_apply (Units.isUnit (u⁻¹)), one_mul] at he
  have hb :
    (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, -‖F χ‖) ≤
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1,
        (χ (↑(u⁻¹) : ZMod q) * F χ).re := by
    apply Finset.sum_le_sum
    intro χ _
    have hm : ‖χ (↑(u⁻¹) : ZMod q) * F χ‖ ≤ ‖F χ‖ := by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (DirichletCharacter.norm_le_one χ _)
    exact (neg_le_neg hm).trans (abs_le.mp (Complex.abs_re_le_norm _)).1
  have hre := congrArg Complex.re he
  rw [Complex.add_re, Complex.re_sum] at hre
  rw [Finset.sum_neg_distrib] at hb
  linarith only [hre, hb]

open Classical in
/-- For finite real weights and a unit residue, the totient times the restricted
weighted sum is bounded below by its principal character sum minus all
nonprincipal norms. Combine orthogonality with the weighted real-part bound.
This applies to logarithmic differences without any positivity assumption on weights. -/
theorem weighted_progression_lower_of_character_sums {q : ℕ} [NeZero q] (u : (ZMod q)ˣ)
    (S : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ S, (w n : ℂ) * (1 : DirichletCharacter ℂ q) n).re -
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).erase 1, ‖∑ n ∈ S, (w n : ℂ) * χ n‖ ≤
      (q.totient : ℝ) * ∑ n ∈ S.filter (fun n : ℕ ↦ (u : ZMod q) = (n : ZMod q)), w n := by
  have hb :=
    principal_re_sub_nonprincipal_norm_sum_le_weighted_re u (fun χ ↦ ∑ n ∈ S, (w n : ℂ) * χ n)
  rw [sum_character_weighted_eq_progression u S] at hb
  simpa only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, Complex.re_sum,
    Complex.ofReal_re, zero_mul, sub_zero] using hb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
