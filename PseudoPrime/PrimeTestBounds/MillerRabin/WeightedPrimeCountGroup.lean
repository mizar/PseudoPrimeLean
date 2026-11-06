/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCountExtend

/-! # Grouped lower bounds for weighted prime-product counts -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Adding `m` labels of positive weight `p` and increasing the budget by
`k * p` multiplies the prior weighted count by at least the multichoose
coefficient `choose (m + k) k`. Induction on the labels and the number of
additional factors follows the counting recurrence and Pascal's identity. -/
theorem weightedPrimeCount_group_lower (p A m k : ℕ) (ps : List ℕ) (hp : 0 < p) :
    (Nat.choose (m + k) k) * weightedPrimeCount id ps A ≤
      weightedPrimeCount id (List.replicate m p ++ ps) (A + k * p) := by
  induction m generalizing k with
  | zero =>
    simp only [List.replicate_zero, List.nil_append, Nat.zero_add, Nat.choose_self, Nat.one_mul]
    exact weightedPrimeCount_mono id ps (Nat.le_add_right _ _)
  | succ m im =>
    induction k with
    | zero =>
      simp only [Nat.add_zero, Nat.choose_zero_right, Nat.zero_mul, Nat.one_mul]
      change weightedPrimeCount id ps A ≤ weightedPrimeCount id (p :: (List.replicate m p ++ ps)) A
      have hi := im 0
      simp only [Nat.add_zero, Nat.choose_zero_right, Nat.zero_mul, Nat.one_mul] at hi
      conv_rhs => rw [weightedPrimeCount.eq_def]
      dsimp only [id_eq]
      rw [dite_eq_left hp]
      by_cases hf : p ≤ A
      · simp only [hf, dite_true]
        exact hi.trans (Nat.le_add_right _ _)
      · simp only [hf, dite_false]
        exact hi
    | succ k
      ik =>
      change
        Nat.choose (m + 1 + (k + 1)) (k + 1) * weightedPrimeCount id ps A ≤
          weightedPrimeCount id (p :: (List.replicate m p ++ ps)) (A + (k + 1) * p)
      have hf : p ≤ A + (k + 1) * p := by nlinarith only [hp]
      have heq : A + (k + 1) * p - p = A + k * p := by
        rw [Nat.add_mul, Nat.one_mul, ← Nat.add_assoc, Nat.add_sub_cancel]
      have hchoose :
        Nat.choose (m + 1 + (k + 1)) (k + 1) =
          Nat.choose (m + (k + 1)) (k + 1) + Nat.choose ((m + 1) + k) k := by
        rw [show m + 1 + (k + 1) = (m + (k + 1)) + 1 by omega, Nat.choose_succ_succ, Nat.add_comm]
        congr 1
        congr 1
        omega
      conv_rhs => rw [weightedPrimeCount.eq_def]
      dsimp only [id_eq]
      rw [dite_eq_left hp, dite_eq_left hf, heq, hchoose, Nat.add_mul]
      exact Nat.add_le_add (im (k + 1)) ik

end PseudoPrime.PrimeTestBounds.MillerRabin
