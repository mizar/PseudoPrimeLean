/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Kronecker.Basic

/-! # Parity evaluation of Kronecker two-power factors -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Evaluate the denominator's two-power factor without integer exponentiation.
Exponent zero gives one, an even numerator with positive exponent gives zero, and an
odd numerator contributes the mod-eight sign only for an odd exponent. -/
def kroneckerTwoPowerFactor (a : ℤ) (e : ℕ) : ℤ :=
  if e = 0 then 1
  else if a % 2 = 0 then 0 else if (a % 8 = 3 ∨ a % 8 = 5) ∧ e % 2 = 1 then -1 else 1

/-- The parity computation equals the power of the independent factor-at-two specification.
Zero exponent and even numerator are separate branches; minus-one powers reduce modulo two.
This permits the full integer computation to avoid sign exponentiation. -/
theorem kroneckerTwoPowerFactor_eq (a : ℤ) (e : ℕ) :
    kroneckerTwoPowerFactor a e = kroneckerAtTwo a ^ e := by
  exact
    if he : e = 0 then (show _ by simp only [kroneckerTwoPowerFactor, he, ite_true, pow_zero])
    else
      if ha : a % 2 = 0 then
        (show _ by
          simp only [kroneckerTwoPowerFactor, kroneckerAtTwo, he, ha, ite_false, ite_true,
            zero_pow he])
      else
        if h8 : a % 8 = 3 ∨ a % 8 = 5 then
          (show _
            by
            simp only [kroneckerTwoPowerFactor, kroneckerAtTwo, he, ha, h8, ite_false, ite_true,
              true_and]
            rw [neg_one_pow_eq_pow_mod_two]
            rcases Nat.mod_two_eq_zero_or_one e with hp | hp <;>
              simp only [hp, Nat.reduceEqDiff, ite_false, ite_true, pow_zero, pow_one])
        else
          (show _ by
            simp only [kroneckerTwoPowerFactor, kroneckerAtTwo, he, ha, h8, false_and, ite_false,
              one_pow])

end PseudoPrime.NumberTheory
