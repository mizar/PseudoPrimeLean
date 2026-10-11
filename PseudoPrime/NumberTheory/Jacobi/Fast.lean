/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Kronecker.Computation
public import PseudoPrime.NumberTheory.Kronecker.Compatibility

/-! # All-input Jacobi execution through the shared symbol-and-gcd kernel -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- Natural-denominator Jacobi symbol and exact gcd from the shared integer trajectory.
At denominator zero only the symbol convention changes to one; zero numerators are direct.
For a positive even denominator `n = 2 ^ e * m` with odd `m`, the symbol is zero when
the numerator is even and equals `jacobiSym a m` when the numerator is odd.
Thus the factor at two is zero or one, unlike the signed factor in the Kronecker symbol.
The gcd component remains `Nat.gcd a.natAbs n` in every case.
Nonzero inputs reuse the normalization and factor-at-two correction without decomposing twice. -/
def jacobiGcdFast (a : ℤ) (n : ℕ) : ℤ × ℕ :=
  if n = 0 then (1, a.natAbs)
  else if a = 0 then (if n = 1 then 1 else 0, n) else kroneckerGcdNonzero a (n : ℤ) true

/-- Both projections of the natural-denominator adapter match the mathematical specifications.
Boundary conventions are explicit; other inputs use the corrected Kronecker computation.
The equality permits callers to share the symbol and gcd rather than recomputing either. -/
theorem jacobiGcdFast_spec (a : ℤ) (n : ℕ) :
    jacobiGcdFast a n = (jacobiSym a n, Nat.gcd a.natAbs n) := by
  exact
    if hn : n = 0 then
      (show _ by
        subst n
        simp only [jacobiGcdFast, ite_true, jacobiSym.zero_right, Nat.gcd_zero_right])
    else
      if ha : a = 0 then
        (show _ by
          subst a
          simp only [jacobiGcdFast, hn, ite_false, ite_true, Int.natAbs_zero, Nat.gcd_zero_left]
          exact
            congrArg (fun z ↦ (z, n))
              (if h1 : n = 1 then (show _ by simp only [h1, ite_true, jacobiSym.one_right])
              else
                (show _ by
                  rw [ite_eq_right h1]
                  exact
                    (jacobiSym.zero_left
                        (Nat.lt_of_le_of_ne (Nat.pos_of_ne_zero hn) (Ne.symm h1))).symm)))
      else
        (show _ by
          rw [jacobiGcdFast, ite_eq_right hn, ite_eq_right ha,
            kroneckerGcdNonzero_corrected_spec a (n : ℤ) ha (Int.natCast_ne_zero.mpr hn),
            Int.natAbs_natCast, ← jacobiSym_eq_kronecker a n (Nat.pos_of_ne_zero hn)])

/-- Natural-denominator Jacobi execution sharing the Kronecker-and-gcd trajectory.
Denominator zero gives one for every numerator. A zero numerator is handled directly;
other inputs enable the shared kernel's correction without repeating two-adic extraction. -/
def jacobiSymFast (a : ℤ) (n : ℕ) : ℤ :=
  (jacobiGcdFast a n).1

/-- The fast entry equals mathlib's Jacobi specification on every natural denominator.
Project the proved symbol-and-gcd adapter identity onto its symbol component.
This keeps the symbol-only execution API consistent with the shared pair entry. -/
theorem jacobiSymFast_eq (a : ℤ) (n : ℕ) : jacobiSymFast a n = jacobiSym a n := by
  exact congrArg Prod.fst (jacobiGcdFast_spec a n)

end PseudoPrime.NumberTheory
