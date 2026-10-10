/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Basic

/-!
# Prime-denominator Jacobi interfaces

These lemmas are neutral arithmetic interfaces for finite residue checkers.  They do not depend on
the `SmallN` certificate or on any Q-side bound.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- A non-one Jacobi value at a prime not dividing the numerator is `-1`. -/
lemma jacobi_eq_neg_one_of_prime_of_not_dvd_of_ne_one {n p : ℕ} (hp : p.Prime) (hndvd : ¬p ∣ n)
    (hne : jacobiSym n p ≠ 1) : jacobiSym n p = -1 := by
  have hcop : Nat.Coprime p n := hp.coprime_iff_not_dvd.mpr hndvd
  have hgcd : (n : ℤ).gcd p = 1 := by exact_mod_cast hcop.symm.gcd_eq_one
  rcases jacobiSym.eq_one_or_neg_one hgcd with hone | hneg
  · exact False.elim (hne hone)
  · exact hneg

end PseudoPrime.NumberTheory
