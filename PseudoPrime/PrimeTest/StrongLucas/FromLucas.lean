/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Lucas.FiniteField
import PseudoPrime.PrimeTest.StrongLucas.Defs

/-! # Strong Lucas consequences of finite-field Lucas identities -/

namespace PseudoPrime.PrimeTest

/-- A zero of `U_(d 2^s)` yields the finite Strong Lucas disjunction. -/
theorem lucasU_twoAdic_zero_implies_strong {K : Type*} [Field K] (P Q : ℤ) :
    ∀ d s : ℕ,
      (lucasU P Q (d * 2 ^ s) : K) = 0 →
        (lucasU P Q d : K) = 0 ∨ ∃ r ∈ List.range s, (lucasV P Q (d * 2 ^ r) : K) = 0 := by
  intro d s
  induction s with
  | zero =>
    intro hzero
    left
    simpa only [pow_zero, mul_one] using hzero
  | succ s ih =>
    intro hzero
    have hindex : d * 2 ^ (s + 1) = 2 * (d * 2 ^ s) := by
      rw [pow_succ]
      ring
    have hfactor : (lucasU P Q (d * 2 ^ s) : K) * (lucasV P Q (d * 2 ^ s) : K) = 0 := by
      rw [← Int.cast_mul]
      rw [← lucasU_two_mul P Q (d * 2 ^ s), ← hindex]
      exact hzero
    rcases mul_eq_zero.mp hfactor with hU | hV
    · rcases ih hU with hU | ⟨r, hr, hV⟩
      · exact Or.inl hU
      · right
        exact ⟨r, List.mem_range.mpr ((List.mem_range.mp hr).trans (Nat.lt_succ_self s)), hV⟩
    · right
      exact ⟨s, List.mem_range.mpr (Nat.lt_succ_self s), hV⟩

/-- A zero at the full Lucas index implies the finite Strong Lucas condition. -/
theorem isStrongLucasProbablePrime_of_lucasUZMod_index_zero {n : ℕ} [Fact n.Prime]
    (param : LucasParams)
    (hzero : lucasUZMod n param.P param.Q (lucasProbablePrimeIndex n param.D) = 0) :
    IsStrongLucasProbablePrime n param := by
  let m := lucasProbablePrimeIndex n param.D
  let d := oddPart m
  let s := twoAdicExponent m
  have hdecomp : d * 2 ^ s = m := by
    dsimp [d, s]
    rw [mul_comm]
    exact twoAdicPart_mul_oddPart m
  have hzero' : (lucasU param.P param.Q (d * 2 ^ s) : ZMod n) = 0 := by
    rw [hdecomp]
    exact hzero
  have hstrong := lucasU_twoAdic_zero_implies_strong param.P param.Q d s hzero'
  dsimp [IsStrongLucasProbablePrime, strongLucasOddPart, strongLucasTwoAdicExponent]
  simpa only [lucasUZMod, lucasVZMod] using hstrong

end PseudoPrime.PrimeTest
