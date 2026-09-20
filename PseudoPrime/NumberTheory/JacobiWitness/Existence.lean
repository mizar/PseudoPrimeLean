/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.JacobiWitness.Basic
import PseudoPrime.NumberTheory.JacobiWitness.Smaller

/-!
# Existence of odd-prime Jacobi witnesses for odd nonsquares

Odd nonsquare inputs greater than `3` have smaller odd-prime Jacobi `-1` witnesses.
The remaining input `3` has witness `5`; together these cases establish nonemptiness of the
odd-prime witness set without any analytic assumptions.
-/

namespace PseudoPrime.NumberTheory

namespace Internal

/-- The fixed Jacobi value used for the exceptional odd nonsquare modulus `3`. -/
theorem jacobiSym_three_five_eq_neg_one : jacobiSym 3 5 = -1 := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rw [← jacobiSym.legendreSym.to_jacobiSym 5 3]
  have hthree : ((3 : ℤ) : ZMod 5) ≠ 0 := by
    intro hzero
    have hval := congrArg ZMod.val hzero
    change 3 = 0 at hval
    norm_num only at hval
  rcases legendreSym.eq_one_or_neg_one 5 hthree with hone | hneg
  · have hpow := legendreSym.eq_pow 5 3
    rw [hone] at hpow
    have hne : (1 : ZMod 5) ≠ 3 ^ ((5 - 1) / 2) := by
      intro hmod
      have hval := congrArg ZMod.val hmod
      change 1 = 4 at hval
      norm_num only at hval
    exact (hne hpow).elim
  · exact hneg

end Internal

/-- Every odd nonsquare has an odd-prime denominator where its Jacobi symbol is `-1`. -/
theorem primeNegOneWitnessSet_nonempty_of_odd_nonsquare {n : ℕ} (hn : Odd n) (hns : ¬IsSquare n) :
    (PrimeNegOneWitnessSet n).Nonempty := by
  have hn1 : n ≠ 1 := by
    intro hnone
    subst n
    exact hns ⟨1, by norm_num only⟩
  have hn3 : n = 3 ∨ 3 < n := by
    obtain ⟨k, hk⟩ := hn
    omega
  rcases hn3 with rfl | hn3
  · exact ⟨5, Nat.prime_five, by decide, Internal.jacobiSym_three_five_eq_neg_one⟩
  · obtain ⟨q, hqprime, hqodd, _, hqvalue⟩ := oddNonsquareHasSmallerNegOneWitness hn hn3 hns
    exact ⟨q, hqprime, hqodd, hqvalue⟩

end PseudoPrime.NumberTheory
