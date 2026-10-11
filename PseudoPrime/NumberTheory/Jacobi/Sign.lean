/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Computation

/-! # Parity evaluation of the two-adic Jacobi sign -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Jacobi

/-- The two-power Jacobi factor, evaluated using only exponent parity.
Residues three and five modulo eight reverse the sign exactly for odd exponents.
This avoids constructing an exponent-sized power in the shared execution kernel. -/
def twoPowerSign (N e : ℕ) : ℤ :=
  if (N % 8 = 3 ∨ N % 8 = 5) ∧ e % 2 = 1 then -1 else 1

/-- The parity implementation equals the usual power of the mod-eight sign.
Reduction of minus-one powers modulo two and the two possible remainders prove the identity.
This preserves the certified batched Jacobi sign when the execution kernel is optimized. -/
theorem twoPowerSign_eq (N e : ℕ) :
    twoPowerSign N e = (if N % 8 = 3 ∨ N % 8 = 5 then (-1 : ℤ) else 1) ^ e := by
  exact
    if hN : N % 8 = 3 ∨ N % 8 = 5 then
      (show _ by
        rw [twoPowerSign, ite_eq_left hN, neg_one_pow_eq_pow_mod_two]
        rcases Nat.mod_two_eq_zero_or_one e with he | he <;>
          simp only [hN, he, true_and, Nat.reduceEqDiff, ite_false, ite_true, pow_zero, pow_one])
    else (show _ by simp only [twoPowerSign, hN, false_and, ite_false, one_pow])

end PseudoPrime.NumberTheory.Jacobi
