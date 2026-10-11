/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiWitness.Basic
public import PseudoPrime.NumberTheory.Jacobi.Prime
public import PseudoPrime.NumberTheory.JacobiWitness.Smaller

/-!
# Existence of odd-prime Jacobi witnesses for odd nonsquares

Odd nonsquare inputs greater than `3` have smaller odd-prime Jacobi `-1` witnesses.
The remaining input `3` has witness `5`; together these cases establish nonemptiness of the
odd-prime witness set without any analytic assumptions.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Every odd nonsquare has an odd-prime denominator where its Jacobi symbol is `-1`.
For `n > 3`, use the smaller-prime witness construction; for `n = 3`, use the explicit denominator
five. This discharges the nonemptiness premise of the least-witness definitions without GRH. -/
theorem primeNegOneWitnessSet_nonempty_of_odd_nonsquare {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) :
    (primeNegOneWitnessSet n).Nonempty := by
  have hn1 : n ≠ 1 := by
    intro hnone
    subst n
    exact hns ⟨1, by norm_num only⟩
  have hn3 : n = 3 ∨ 3 < n := by
    obtain ⟨k, hk⟩ := hn
    by_cases hk0 : k = 0
    · subst k
      norm_num only [mul_zero, add_zero] at hk
      exact False.elim (hn1 hk)
    have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
    rcases Nat.eq_or_lt_of_le hkpos with hkeq | hkgt
    · subst k
      left
      norm_num only at hk ⊢
      exact hk
    · right
      nlinarith only [hk, hkgt]
  rcases hn3 with rfl | hn3
  · exact ⟨5, Nat.prime_five, by decide, jacobiSym_three_five_eq_neg_one⟩
  · obtain ⟨q, hqprime, hqodd, _, hqvalue⟩ :=
      exists_smaller_prime_jacobiSym_eq_neg_one_of_odd_nonsquare hn hn3 hns
    exact ⟨q, hqprime, hqodd, hqvalue⟩

end PseudoPrime.NumberTheory
