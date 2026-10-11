/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Sign

/-! # Symbol-only batched Jacobi recursion

A tail-recursive sign accumulator reuses each round's maximal two-power decomposition.
The procedure computes no gcd component and requires no externally selected fuel.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory.Jacobi

/-- Batched symbol recursion on a natural numerator and denominator with a sign accumulator.
Each positive round decomposes the numerator once, applies parity and reciprocity signs,
and recurses on the remainder. At numerator zero, return the sign only at denominator one.
The numerator strictly decreases, so no Fibonacci budget is computed.
Semantic Jacobi correctness uses an odd denominator; reference equivalence holds for every one. -/
def symbolNat (a n : ℕ) (sign : ℤ := 1) : ℤ :=
  if _ha : a = 0 then if n = 1 then sign else 0
  else
    match ht : Nat.maxPowDvdDiv 2 a with
    | (e, d) =>
      symbolNat (n % d) d (sign * twoPowerSign n e * (if d % 4 = 3 ∧ n % 4 = 3 then -1 else 1))
termination_by a
decreasing_by
  simpa only [Nat.divMaxPow, ht] using
    (Nat.mod_lt n (TwoAdic.oddPart_pos a _ha)).trans_le (TwoAdic.oddPart_le a _ha)

/-- The symbol-only recursion returns the accumulated sign times the reference Jacobi recursion.
No parity assumption is needed for this algorithmic equality. Strong induction follows
the decreasing numerator; the parity factor equals the reference two-power sign.
Together with odd-denominator reference correctness, this certifies normalized symbol execution. -/
theorem symbolNat_eq_reference (a n : ℕ) (sign : ℤ) :
    symbolNat a n sign = sign * jacobiNat a n := by
  induction a using Nat.strong_induction_on generalizing n sign with
  | h a ih =>
    rw [symbolNat]
    split
    · next ha =>
        conv_rhs => rw [jacobiNat, dite_eq_left ha]
        simp only [mul_ite, mul_one, mul_zero]
    · next ha =>
        conv_rhs => rw [jacobiNat, dite_eq_right ha]
        rcases ht : Nat.maxPowDvdDiv 2 a with ⟨e, d⟩
        dsimp only
        rw [ih _
            (by
              simpa only [Nat.divMaxPow, ht] using
                (Nat.mod_lt n (TwoAdic.oddPart_pos a ha)).trans_le (TwoAdic.oddPart_le a ha))]
        simp only [twoPowerSign_eq, jacobiRoundSign, padicValNat, Nat.divMaxPow, ht, mul_assoc]

end PseudoPrime.NumberTheory.Jacobi
