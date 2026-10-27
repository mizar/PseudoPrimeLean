/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Analysis.Fourier.ZMod

/-! # Second and fourth moments of finite residue character sums -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For nonzero modulus N, sum the standard additive character over a multiple of every residue.
The result is N for the zero multiple and zero otherwise, by character primitivity. -/
theorem sum_stdAddChar_mul {N : ℕ} [NeZero N] (t : ZMod N) :
    (∑ i : ZMod N, ZMod.stdAddChar (t * i)) = if t = 0 then (N : ℂ) else 0 := by
  classical
  by_cases h : t = 0
  · simp only [h, zero_mul, AddChar.map_zero_eq_one, ite_true, Finset.sum_const, Finset.card_univ,
      ZMod.card, nsmul_eq_mul, mul_one]
  · rw [ite_eq_right h]
    exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar N h)

/-- Complex conjugation of the standard additive character equals evaluation at the negative.
Use its unit-circle norm and the additive character inverse identity. -/
theorem conj_stdAddChar {N : ℕ} [NeZero N] (t : ZMod N) :
    (starRingEnd ℂ) (ZMod.stdAddChar t) = ZMod.stdAddChar (-t) := by
  rw [AddChar.map_neg_eq_inv, ZMod.stdAddChar_apply]
  exact (Complex.inv_eq_conj (Circle.norm_coe _)).symm

/-- For any finite indexed residue family, express the squared modulus of its character sum
as the character sum over ordered differences of two indices. Expand the conjugate product. -/
theorem char_sum_normSq_pairs {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (f : ι → ZMod N)
    (l : ZMod N) :
    (Complex.normSq (∑ x ∈ S, ZMod.stdAddChar (l * f x)) : ℂ) =
      ∑ x ∈ S, ∑ y ∈ S, ZMod.stdAddChar (l * (f x - f y)) := by
  rw [← Complex.mul_conj]
  simp only [map_sum, Finset.sum_mul, Finset.mul_sum, conj_stdAddChar, ← AddChar.map_add_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  congr 1
  ring

/-- For any finite indexed residue family, its second Fourier moment equals N times the
number of ordered index pairs with equal residues, as a complex equality.
Exchange the finite sums and apply additive character orthogonality. -/
theorem char_sum_second_moment_complex {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι)
    (f : ι → ZMod N) :
    (∑ l : ZMod N, (Complex.normSq (∑ x ∈ S, ZMod.stdAddChar (l * f x)) : ℂ)) =
      (N : ℂ) * ((S ×ˢ S).filter (fun z ↦ f z.1 = f z.2)).card := by
  classical
  simp only [char_sum_normSq_pairs]
  rw [Finset.sum_comm]
  calc
    _ = ∑ x ∈ S, ∑ y ∈ S, ∑ l : ZMod N, ZMod.stdAddChar (l * (f x - f y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [Finset.sum_comm]
    _ = ∑ z ∈ S ×ˢ S, ∑ l : ZMod N, ZMod.stdAddChar ((f z.1 - f z.2) * l) := by
      simp only [Finset.sum_product, mul_comm]
    _ = ∑ z ∈ S ×ˢ S, if f z.1 = f z.2 then (N : ℂ) else 0 := by
      simp only [sum_stdAddChar_mul, sub_eq_zero]
    _ = (N : ℂ) * (∑ z ∈ S ×ˢ S, if f z.1 = f z.2 then (1 : ℂ) else 0) := by
      simp only [Finset.mul_sum, mul_ite, mul_one, mul_zero]
    _ = _ := by rw [Finset.sum_boole]

/-- The real second Fourier moment of a finite indexed residue family is N times its collision
count. Transfer the complex identity through the injective real embedding. -/
theorem char_sum_second_moment {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (f : ι → ZMod N) :
    (∑ l : ZMod N, Complex.normSq (∑ x ∈ S, ZMod.stdAddChar (l * f x))) =
      (N : ℝ) * ((S ×ˢ S).filter (fun z ↦ f z.1 = f z.2)).card := by
  apply Complex.ofReal_injective
  simpa only [Complex.ofReal_sum, Complex.ofReal_mul, Complex.ofReal_natCast] using
    char_sum_second_moment_complex S f

/-- For a finite indexed residue family, its fourth Fourier moment is N times the number of
ordered quadruples with equal differences. Apply the second moment to the pair-difference
family and use the exact squared-modulus expansion, allowing repeated residue values. -/
theorem char_sum_fourth_moment {N : ℕ} [NeZero N] {ι : Type*} (S : Finset ι) (f : ι → ZMod N) :
    (∑ l : ZMod N, ‖∑ x ∈ S, ZMod.stdAddChar (l * f x)‖ ^ 4) =
      (N : ℝ) *
        (((S ×ˢ S) ×ˢ (S ×ˢ S)).filter (fun z ↦ f z.1.1 - f z.1.2 = f z.2.1 - f z.2.2)).card := by
  classical
  have h := char_sum_second_moment (S ×ˢ S) (fun z ↦ f z.1 - f z.2)
  have he (l : ZMod N) :
    (∑ z ∈ S ×ˢ S, ZMod.stdAddChar (l * (f z.1 - f z.2))) =
      (Complex.normSq (∑ x ∈ S, ZMod.stdAddChar (l * f x)) : ℂ) := by
    simpa only [Finset.sum_product] using (char_sum_normSq_pairs S f l).symm
  simp only [he, Complex.normSq_ofReal] at h
  calc
    _ =
        ∑ l : ZMod N,
          Complex.normSq (∑ x ∈ S, ZMod.stdAddChar (l * f x)) *
            Complex.normSq (∑ x ∈ S, ZMod.stdAddChar (l * f x)) :=
      by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Complex.normSq_eq_norm_sq]
      ring
    _ = _ := h

end PseudoPrime.NumberTheory.Heilbronn
