/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianEulerPolyRH

/-! # Transfer of a weighted Euler tail bound to a larger cutoff -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A tail bound uniform in the deficit weights holds from every larger
cutoff. Zeroing the extra weights makes the two sums equal. -/
public theorem euler_weighted_tail_from (W : ℕ → ℝ) {A X C : ℝ} (hAX : A ≤ X)
    (h :
      ∀ α : ℕ → ℝ, (∀ n, α n ∈ Set.Icc 0 4) → (∑' n : { n : ℕ // ⌊A⌋₊ < n }, α n.val * W n.val) ≤ C)
    (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    (∑' n : { n : ℕ // ⌊X⌋₊ < n }, α n.val * W n.val) ≤ C := by
  let β : ℕ → ℝ := fun n ↦ if ⌊X⌋₊ < n then α n else 0
  have hβ (n : ℕ) : β n ∈ Set.Icc 0 4 := by
    by_cases hn : ⌊X⌋₊ < n
    · simpa only [β, ite_eq_left hn] using hα n
    · simpa only [β, ite_eq_right hn] using
        (show (0 : ℝ) ∈ Set.Icc 0 4 from ⟨le_rfl, by norm_num only⟩)
  have he :
    (∑' n : { n : ℕ // ⌊A⌋₊ < n }, β n.val * W n.val) =
      ∑' n : { n : ℕ // ⌊X⌋₊ < n }, α n.val * W n.val := by
    refine (tsum_subtype {n : ℕ | ⌊A⌋₊ < n} (fun n ↦ β n * W n)).trans ?_
    refine Eq.trans ?_ (tsum_subtype {n : ℕ | ⌊X⌋₊ < n} (fun n ↦ α n * W n)).symm
    refine tsum_congr fun n ↦ ?_
    by_cases hn : ⌊X⌋₊ < n
    · have hm : ⌊A⌋₊ < n := (Nat.floor_mono hAX).trans_lt hn
      simp only [Set.indicator_apply, Set.mem_ofPred_eq, hm, hn, β, ite_true]
    · simp only [Set.indicator_apply, Set.mem_ofPred_eq, hn, β, ite_false, zero_mul, ite_self]
  rw [← he]
  exact h β hβ

end PseudoPrime.PrimeTestBounds.MillerRabin
