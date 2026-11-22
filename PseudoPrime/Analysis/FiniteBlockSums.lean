/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.BigOperators.Fin

/-! # Finite sums split into equally sized blocks and a final partial block -/

public section

namespace PseudoPrime.Analysis

/-- A finite sum over b*k indices is the sum of b blocks of k terms.
The identity allows independent arithmetic certificates for each block. -/
theorem sum_fin_blocks {α : Type*} [AddCommMonoid α] (b k : ℕ) (f : ℕ → α) :
    (∑ i : Fin (b * k), f i.val) = ∑ j : Fin b, ∑ i : Fin k, f (j.val * k + i.val) := by
  induction b with
  | zero =>
    rw [Nat.zero_mul]
    simp only [Fin.sum_univ_zero]
  | succ b ih =>
    calc
      _ = (∑ i : Fin (b * k), f i.val) + ∑ i : Fin k, f (b * k + i.val) := by
        rw [Nat.succ_mul]
        simpa only [Fin.val_castAdd, Fin.val_natAdd] using
          (Fin.sum_univ_add (a := b * k) (b := k) (fun i ↦ f i.val))
      _ = (∑ j : Fin b, ∑ i : Fin k, f (j.val * k + i.val)) + ∑ i : Fin k, f (b * k + i.val) := by
        rw [ih]
      _ = _ := by
        symm
        simpa only [Fin.val_castSucc, Fin.val_last] using
          (Fin.sum_univ_castSucc (fun j : Fin (b + 1) ↦ ∑ i : Fin k, f (j.val * k + i.val)))

/-- A sum with b full blocks and r remaining terms separates into independently
checkable block sums and the final short block. No list indexing is involved. -/
theorem sum_fin_blocks_tail {α : Type*} [AddCommMonoid α] (b k r : ℕ) (f : ℕ → α) :
    (∑ i : Fin (b * k + r), f i.val) =
      (∑ j : Fin b, ∑ i : Fin k, f (j.val * k + i.val)) + ∑ i : Fin r, f (b * k + i.val) := by
  have h := Fin.sum_univ_add (a := b * k) (b := r) (fun i ↦ f i.val)
  simpa only [Fin.val_castAdd, Fin.val_natAdd, sum_fin_blocks] using h

/-- Certified full-block sums and a final partial-block sum determine the total.
Only the cached block values appear in the final finite sum, so nonlinear
endpoint computations can be verified once and reused during assembly. -/
theorem sum_fin_blocks_of_sums {α : Type*} [AddCommMonoid α] (b k r : ℕ) (f B : ℕ → α)
    (hfull : ∀ j : Fin b, (∑ i : Fin k, f (j.val * k + i.val)) = B j.val)
    (htail : (∑ i : Fin r, f (b * k + i.val)) = B b) :
    (∑ i : Fin (b * k + r), f i.val) = ∑ j : Fin (b + 1), B j.val := by
  calc
    _ = (∑ j : Fin b, ∑ i : Fin k, f (j.val * k + i.val)) + ∑ i : Fin r, f (b * k + i.val) :=
      sum_fin_blocks_tail b k r f
    _ = (∑ j : Fin b, B j.val) + B b :=
      congrArg₂ (fun x y : α ↦ x + y) (Finset.sum_congr rfl (fun j _ ↦ hfull j)) htail
    _ = _ := by
      symm
      simpa only [Fin.val_castSucc, Fin.val_last] using
        (Fin.sum_univ_castSucc (fun j : Fin (b + 1) ↦ B j.val))

end PseudoPrime.Analysis
