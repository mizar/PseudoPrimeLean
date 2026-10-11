/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Kronecker.Computation
public import PseudoPrime.NumberTheory.Kronecker.Fast
public import PseudoPrime.NumberTheory.Kronecker.GcdFast
public import PseudoPrime.NumberTheory.Kronecker.Compatibility

/-! # All-input Jacobi execution with symbol-only and shared-gcd entry points -/

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

/-- Fuel-free Jacobi symbol and exact gcd for every natural denominator.
The decreasing-numerator kernel performs no Fibonacci budget calculation.
At denominator zero only the symbol convention changes to one; zero numerators are direct.
For a positive even denominator `n = 2 ^ e * m` with odd `m`, the symbol is zero when
the numerator is even and equals `jacobiSym a m` when the numerator is odd.
Thus the factor at two is zero or one, unlike the signed factor in the Kronecker symbol.
The gcd component remains `Nat.gcd a.natAbs n` in every case.
Nonzero inputs reuse the normalization and factor-at-two correction without decomposing twice. -/
def jacobiGcdFuelFreeFast (a : ℤ) (n : ℕ) : ℤ × ℕ :=
  if n = 0 then (1, a.natAbs)
  else if a = 0 then (if n = 1 then 1 else 0, n) else kroneckerGcdNonzeroFast a (n : ℤ) true

/-- Both projections of the natural-denominator adapter match the mathematical specifications.
Boundary conventions are explicit; other inputs use the corrected Kronecker computation.
The equality permits callers to share the symbol and gcd rather than recomputing either. -/
theorem jacobiGcdFuelFreeFast_spec (a : ℤ) (n : ℕ) :
    jacobiGcdFuelFreeFast a n = (jacobiSym a n, Nat.gcd a.natAbs n) := by
  exact
    if hn : n = 0 then
      (show _ by
        subst n
        simp only [jacobiGcdFuelFreeFast, ite_true, jacobiSym.zero_right, Nat.gcd_zero_right])
    else
      if ha : a = 0 then
        (show _ by
          subst a
          simp only [jacobiGcdFuelFreeFast, hn, ite_false, ite_true, Int.natAbs_zero,
            Nat.gcd_zero_left]
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
          rw [jacobiGcdFuelFreeFast, ite_eq_right hn, ite_eq_right ha,
            kroneckerGcdNonzeroFast_corrected_spec a (n : ℤ) ha (Int.natCast_ne_zero.mpr hn),
            Int.natAbs_natCast, ← jacobiSym_eq_kronecker a n (Nat.pos_of_ne_zero hn)])

/-- Fuel-free and fuel-based Jacobi pairs agree on every natural denominator.
Their all-input specifications identify both components, including denominator zero.
Callers may choose the fuel-free entry without changing the existing Jacobi convention. -/
theorem jacobiGcdFuelFreeFast_eq (a : ℤ) (n : ℕ) :
    jacobiGcdFuelFreeFast a n = jacobiGcdFast a n := by
  exact (jacobiGcdFuelFreeFast_spec a n).trans (jacobiGcdFast_spec a n).symm

/-- Executable Jacobi symbol for all natural denominators without computing a gcd.
Denominator zero gives one for every numerator. Other inputs use symbol-only Kronecker
normalization with the factor-at-two correction, including even and zero numerators.
No shared gcd state, gcd restoration, or Fibonacci fuel selection is evaluated. -/
def jacobiSymFast (a : ℤ) (n : ℕ) : ℤ :=
  if n = 0 then 1 else kroneckerSymNonzeroFast a (n : ℤ) true

/-- The fast entry equals mathlib's Jacobi specification on every natural denominator.
The zero-denominator convention and the corrected symbol-only normalization identify it.
This permits symbol-only consumers to omit the shared gcd computation. -/
theorem jacobiSymFast_eq (a : ℤ) (n : ℕ) : jacobiSymFast a n = jacobiSym a n := by
  by_cases hn : n = 0
  · subst n
    simp only [jacobiSymFast, ite_true, jacobiSym.zero_right]
  · rw [jacobiSymFast, ite_eq_right hn,
      kroneckerSymNonzeroFast_spec a (n : ℤ) true (Int.natCast_ne_zero.mpr hn)]
    simp only [ite_true, Int.natAbs_natCast]
    exact (jacobiSym_eq_kronecker a n (Nat.pos_of_ne_zero hn)).symm

/-- The shared Jacobi result is zero exactly at a nonzero denominator with nonunit gcd.
The denominator-zero convention gives one even when the gcd differs from one.
Project the all-input specification and apply mathlib's Jacobi zero criterion.
This exposes the symbol/gcd relation for callers retaining both components. -/
theorem jacobiGcdFast_zero_iff (a : ℤ) (n : ℕ) :
    (jacobiGcdFast a n).1 = 0 ↔ n ≠ 0 ∧ (jacobiGcdFast a n).2 ≠ 1 := by
  rw [jacobiGcdFast_spec]
  exact jacobiSym.eq_zero_iff

end PseudoPrime.NumberTheory
