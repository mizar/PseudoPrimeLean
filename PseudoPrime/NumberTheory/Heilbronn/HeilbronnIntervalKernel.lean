/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.ShortDirichletLowerBound

/-! # Counting initial Heilbronn residues by a nonnegative short-frequency kernel -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Number of natural integers 1<=a<=k whose residue lies in the Heilbronn subgroup.
This counts integers, retaining any multiplicity beyond the modulus. -/
noncomputable def heilbronnInitialCount (p k : ℕ) [Fact p.Prime] : ℕ := by
  classical
    exact ((Finset.Icc 1 k).filter (fun a : ℕ ↦ (a : ZMod (p ^ 2)) ∈ shiftedTeichCoset p 0)).card

/-- For k<p^2 and 32Hk<=p^2, the interval count times H+1 is at most
four times the subgroup order plus the signed short Fourier norm sum.
The residue map is injective on the interval, so its kernel sum is bounded by the full average. -/
theorem heilbronnInitialCount_mul_height_le {p H k : ℕ} [Fact p.Prime] (hk : k < p ^ 2)
    (hHk : 32 * H * k ≤ p ^ 2) :
    (heilbronnInitialCount p k : ℝ) * (H + 1 : ℝ) ≤
      4 *
        (((p - 1 : ℕ) : ℝ) +
          ∑ z ∈ signedShortIntegers H, ‖heilbronnCharacterSum p (z : ZMod (p ^ 2))‖) := by
  classical
  let I := (Finset.Icc 1 k).filter (fun a : ℕ ↦ (a : ZMod (p ^ 2)) ∈ shiftedTeichCoset p 0)
  have hinj : Set.InjOn (fun a : ℕ ↦ (a : ZMod (p ^ 2))) (I : Set ℕ) := by
    intro a ha b hb he
    have ha' := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
    have hb' := (Finset.mem_Icc.mp (Finset.mem_filter.mp hb).1).2
    have hh := congrArg ZMod.val he
    rw [ZMod.val_natCast_of_lt (lt_of_le_of_lt ha' hk),
      ZMod.val_natCast_of_lt (lt_of_le_of_lt hb' hk)] at hh
    exact hh
  have hsum :=
    Finset.sum_le_sum_of_injOn (fun a : ℕ ↦ (a : ZMod (p ^ 2))) (s := I) (t :=
      (shiftedTeichCoset p 0).toFinset) (f := fun _ ↦ (H + 1 : ℝ) ^ 2) (g := fun x ↦
      4 * Complex.normSq (shortDirichletSum H x)) hinj
      (by
        intro x hx
        obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hx
        exact Set.mem_toFinset.mpr (Finset.mem_filter.mp ha).2)
      (by
        intro a ha
        have hb := (Finset.mem_Icc.mp (Finset.mem_filter.mp ha).1).2
        exact shortDirichletSum_normSq_lower ((Nat.mul_le_mul_left (32 * H) hb).trans hHk))
      (fun x hx hn ↦ mul_nonneg (by norm_num only) (Complex.normSq_nonneg _))
  rw [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum] at hsum
  have hupper := sum_heilbronn_dirichlet_normSq_le (p := p) (H := H)
  have hpos : 0 < (H + 1 : ℝ) := by linarith only [Nat.cast_nonneg (α := ℝ) H]
  apply (mul_le_mul_iff_right₀ hpos).mp
  change (H + 1 : ℝ) * ((I.card : ℝ) * (H + 1 : ℝ)) ≤ _
  nlinarith only [hsum, hupper]

end PseudoPrime.NumberTheory.Heilbronn
