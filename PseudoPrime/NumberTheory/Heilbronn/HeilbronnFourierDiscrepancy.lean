/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ShortHeilbronnFourierBounds

/-! # Fourier inversion and discrepancy for Heilbronn test sums -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Sum any complex test function over the Heilbronn subgroup using its finite Fourier
transform. Invert the transform pointwise and interchange the two finite sums. -/
theorem sum_over_heilbronn_eq_fourier {p : ℕ} [Fact p.Prime] (f : ZMod (p ^ 2) → ℂ) :
    (by classical exact ∑ x ∈ (shiftedTeichCoset p 0).toFinset, f x) =
      ((p ^ 2 : ℕ) : ℂ)⁻¹ * ∑ w : ZMod (p ^ 2), heilbronnCharacterSum p w * ZMod.dft f w := by
  classical
  have hx (x : ZMod (p ^ 2)) :
    f x = ((p ^ 2 : ℕ) : ℂ)⁻¹ * ∑ w : ZMod (p ^ 2), ZMod.stdAddChar (w * x) * ZMod.dft f w := by
    have h := congrFun (ZMod.dft.symm_apply_apply f) x
    rw [ZMod.invDFT_apply, smul_eq_mul] at h
    simpa only [smul_eq_mul] using h.symm
  simp only [hx, ← Finset.mul_sum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w hw
  rw [heilbronnCharacterSum, Finset.sum_mul]

/-- The zero-frequency character sum is the subgroup order p-1. -/
theorem heilbronnCharacterSum_zero {p : ℕ} [Fact p.Prime] :
    heilbronnCharacterSum p 0 = ((p - 1 : ℕ) : ℂ) := by
  classical
  rw [heilbronnCharacterSum_eq_subgroup_sum]
  simp only [zero_mul, AddChar.map_zero_eq_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, ← Nat.card_eq_fintype_card, card_heilbronnSubgroup]

/-- Removing the zero Fourier coefficient separates the subgroup average from the error.
This exact identity applies to arbitrary test functions, before choosing an interval kernel. -/
theorem heilbronn_fourier_discrepancy {p : ℕ} [Fact p.Prime] (f : ZMod (p ^ 2) → ℂ) :
    (by classical exact ∑ x ∈ (shiftedTeichCoset p 0).toFinset, f x) -
        ((p ^ 2 : ℕ) : ℂ)⁻¹ * ((p - 1 : ℕ) : ℂ) * (∑ x, f x) =
      ((p ^ 2 : ℕ) : ℂ)⁻¹ *
        ∑ w ∈ (Finset.univ : Finset (ZMod (p ^ 2))).erase 0,
          heilbronnCharacterSum p w * ZMod.dft f w := by
  classical
  rw [sum_over_heilbronn_eq_fourier]
  have hzero : ZMod.dft f 0 = ∑ x, f x := by
    simp only [ZMod.dft_apply, mul_zero, neg_zero, AddChar.map_zero_eq_one, one_smul]
  have he :=
    Finset.sum_erase_add (Finset.univ : Finset (ZMod (p ^ 2)))
      (fun w ↦ heilbronnCharacterSum p w * ZMod.dft f w) (Finset.mem_univ 0)
  rw [heilbronnCharacterSum_zero, hzero] at he
  rw [← he]
  ring

/-- The discrepancy is bounded by the nonzero Fourier norm sum, scaled by p^-2.
This is the triangle-inequality interface for a future interval or smoothed test function. -/
theorem norm_heilbronn_fourier_discrepancy_le {p : ℕ} [Fact p.Prime] (f : ZMod (p ^ 2) → ℂ) :
    ‖(by classical exact ∑ x ∈ (shiftedTeichCoset p 0).toFinset, f x) -
          ((p ^ 2 : ℕ) : ℂ)⁻¹ * ((p - 1 : ℕ) : ℂ) * (∑ x, f x)‖ ≤
      ‖((p ^ 2 : ℕ) : ℂ)⁻¹‖ *
        ∑ w ∈ (Finset.univ : Finset (ZMod (p ^ 2))).erase 0,
          ‖heilbronnCharacterSum p w‖ * ‖ZMod.dft f w‖ := by
  classical
  rw [heilbronn_fourier_discrepancy, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  simpa only [norm_mul] using
    norm_sum_le ((Finset.univ : Finset (ZMod (p ^ 2))).erase 0)
      (fun w ↦ heilbronnCharacterSum p w * ZMod.dft f w)

end PseudoPrime.NumberTheory.Heilbronn
