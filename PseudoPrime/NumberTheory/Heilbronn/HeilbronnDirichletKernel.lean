/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.HeilbronnFourierDiscrepancy

/-! # Short Dirichlet kernels and their subgroup averages -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A short additive-character sum on integer frequencies 0 through H. -/
noncomputable def shortDirichletSum {N : ℕ} [NeZero N] (H : ℕ) (x : ZMod N) : ℂ :=
  ∑ j ∈ Finset.Icc (0 : ℤ) H, ZMod.stdAddChar (x * (j : ZMod N))

/-- For each j in [0,H], translate differences j-l into [-H,H].
The zero term is p-1 and every remaining term belongs to the signed short sum. -/
theorem sum_norm_heilbronn_differences_le {p H : ℕ} [Fact p.Prime] (j : ℤ)
    (hj : j ∈ Finset.Icc (0 : ℤ) H) :
    (∑ l ∈ Finset.Icc (0 : ℤ) H, ‖heilbronnCharacterSum p ((j - l : ℤ) : ZMod (p ^ 2))‖) ≤
      ((p - 1 : ℕ) : ℝ) +
        ∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖ := by
  have hsum :=
    Finset.sum_le_sum_of_injOn (fun l : ℤ ↦ j - l) (s := Finset.Icc (0 : ℤ) H) (t :=
      Finset.Icc (-(H : ℤ)) H) (f := fun l ↦ ‖heilbronnCharacterSum p ((j - l : ℤ) : ZMod (p ^ 2))‖)
      (g := fun z : ℤ ↦ ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖)
      (fun a ha b hb h ↦ sub_right_injective h)
      (by
        intro z hz
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hz
        have ha := Finset.mem_Icc.mp hj
        have hb := Finset.mem_Icc.mp hl
        exact Finset.mem_Icc.mpr ⟨by linarith only [ha.1, hb.2], by linarith only [ha.2, hb.1]⟩)
      (fun l hl ↦ le_rfl) (fun z hz hn ↦ norm_nonneg _)
  have hm : (0 : ℤ) ∈ Finset.Icc (-(H : ℤ)) H :=
    Finset.mem_Icc.mpr ⟨neg_nonpos.mpr (Nat.cast_nonneg H), Nat.cast_nonneg H⟩
  have he :=
    Finset.sum_erase_add (Finset.Icc (-(H : ℤ)) H)
      (fun z ↦ ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖) hm
  rw [Int.cast_zero, heilbronnCharacterSum_zero, Complex.norm_natCast] at he
  rw [← he] at hsum
  simpa only [signedShortIntegers, add_comm] using hsum

/-- Expand the squared Dirichlet norm and sum over the subgroup.
The exact formula is the sum of real parts of its short character sums. -/
theorem sum_heilbronn_dirichlet_normSq {p H : ℕ} [Fact p.Prime] :
    (by
        classical
          exact ∑ x ∈ (shiftedTeichCoset p 0).toFinset, Complex.normSq (shortDirichletSum H x)) =
      ∑ j ∈ Finset.Icc (0 : ℤ) H,
        ∑ l ∈ Finset.Icc (0 : ℤ) H, (heilbronnCharacterSum p ((j - l : ℤ) : ZMod (p ^ 2))).re := by
  classical
  have he (x : ZMod (p ^ 2)) :
    (Complex.normSq (shortDirichletSum H x) : ℂ) =
      ∑ j ∈ Finset.Icc (0 : ℤ) H,
        ∑ l ∈ Finset.Icc (0 : ℤ) H, ZMod.stdAddChar (x * ((j - l : ℤ) : ZMod (p ^ 2))) := by
    simpa only [shortDirichletSum, Int.cast_sub] using
      char_sum_normSq_pairs (Finset.Icc (0 : ℤ) H) (fun j ↦ (j : ZMod (p ^ 2))) x
  have hs :
    (∑ x ∈ (shiftedTeichCoset p 0).toFinset, (Complex.normSq (shortDirichletSum H x) : ℂ)) =
      ∑ j ∈ Finset.Icc (0 : ℤ) H,
        ∑ l ∈ Finset.Icc (0 : ℤ) H, heilbronnCharacterSum p ((j - l : ℤ) : ZMod (p ^ 2)) := by
    simp only [he]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j hj
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro l hl
    simp only [heilbronnCharacterSum, mul_comm]
  have h := congrArg Complex.re hs
  simpa only [Complex.re_sum, Complex.ofReal_re] using h

/-- The subgroup average of the nonnegative kernel is bounded by
(H+1) times the subgroup order plus the signed short Fourier norm sum. -/
theorem sum_heilbronn_dirichlet_normSq_le {p H : ℕ} [Fact p.Prime] :
    (by
        classical
          exact ∑ x ∈ (shiftedTeichCoset p 0).toFinset, Complex.normSq (shortDirichletSum H x)) ≤
      (H + 1 : ℝ) *
        (((p - 1 : ℕ) : ℝ) +
          ∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖) := by
  rw [sum_heilbronn_dirichlet_normSq]
  calc
    _ ≤
        ∑ j ∈ Finset.Icc (0 : ℤ) H,
          ∑ l ∈ Finset.Icc (0 : ℤ) H, ‖heilbronnCharacterSum p ((j - l : ℤ) : ZMod (p ^ 2))‖ :=
      by
      apply Finset.sum_le_sum
      intro j hj
      exact Finset.sum_le_sum (fun l hl ↦ Complex.re_le_norm _)
    _ ≤
        ∑ j ∈ Finset.Icc (0 : ℤ) H,
          (((p - 1 : ℕ) : ℝ) +
            ∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖) :=
      Finset.sum_le_sum (fun j hj ↦ sum_norm_heilbronn_differences_le j hj)
    _ = _ := by
      rw [Finset.sum_const, Int.card_Icc]
      rw [sub_zero, ← Int.natCast_one, ← Nat.cast_add, Int.toNat_natCast, nsmul_eq_mul,
        Nat.cast_add, Nat.cast_one]

end PseudoPrime.NumberTheory.Heilbronn
