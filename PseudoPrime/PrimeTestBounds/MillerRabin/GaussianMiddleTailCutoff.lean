/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK141MassNumeric
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK156MassNumeric

/-! # Fixed lower cutoffs for the middle Euler tails -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A bound uniform in the deficit weights remains valid when the cutoff increases.
Mask the extra summands to transfer the bound without evaluating another Abel envelope. -/
private theorem tail_cutoff_le (W : ℕ → ℝ) {A X C : ℝ} (hAX : A ≤ X)
    (h :
      ∀ α : ℕ → ℝ,
        (∀ n, α n ∈ Set.Icc 0 4) → 2 * (∑' n : { n : ℕ // ⌊A⌋₊ < n }, α n.val * W n.val) ≤ C)
    (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    2 * (∑' n : { n : ℕ // ⌊X⌋₊ < n }, α n.val * W n.val) ≤ C := by
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

/-- For K141 an admissible lower cutoff controls every larger cutoff by one RH moment. -/
public theorem middle_k141_tail_from (hRH : RiemannHypothesis) {A X : ℝ} (hA : 101 ≤ A)
    (ha : 20 ≤ Real.log A) (hAX : A ≤ X) (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    2 *
        (∑' n : { n : ℕ // ⌊X⌋₊ < n },
          α n.val *
            (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
              middleMassProfile middleK141Kernel 2 14 n.val)) ≤
      4 * middleMassTailCost middleK141Kernel 2 14 A := by
  exact
    tail_cutoff_le
      (fun n ↦
        ArithmeticFunction.vonMangoldt n / Real.sqrt n * middleMassProfile middleK141Kernel 2 14 n)
      hAX (middle_k141_mass_tail_le hRH hA ha) α hα

/-- For K156 an admissible lower cutoff controls every larger cutoff by one RH moment. -/
public theorem middle_k156_tail_from (hRH : RiemannHypothesis) {A X : ℝ} (hA : 101 ≤ A)
    (ha : 24 ≤ Real.log A) (hAX : A ≤ X) (α : ℕ → ℝ) (hα : ∀ n, α n ∈ Set.Icc 0 4) :
    2 *
        (∑' n : { n : ℕ // ⌊X⌋₊ < n },
          α n.val *
            (ArithmeticFunction.vonMangoldt n.val / Real.sqrt n.val *
              middleMassProfile middleK156Kernel (49 / 20) 24 n.val)) ≤
      4 * middleMassTailCost middleK156Kernel (49 / 20) 24 A := by
  exact
    tail_cutoff_le
      (fun n ↦
        ArithmeticFunction.vonMangoldt n / Real.sqrt n *
          middleMassProfile middleK156Kernel (49 / 20) 24 n)
      hAX (middle_k156_mass_tail_le hRH hA ha) α hα

end PseudoPrime.PrimeTestBounds.MillerRabin
