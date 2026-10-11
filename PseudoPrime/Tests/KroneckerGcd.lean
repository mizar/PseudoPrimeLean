/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Jacobi.Fast
meta import PseudoPrime.NumberTheory.Jacobi.Fast

/-! # Deterministic executable Kronecker and gcd regression checks

Runtime checks compare the shared trajectory with the independent mathematical specification.
They supplement the all-input correctness proofs and do not introduce proof assumptions.
-/

@[expose] public section

namespace PseudoPrime.Tests

/-- Check signed inputs from minus 32 through 32 against both specification projections.
Also check all natural-denominator Jacobi conventions over the same numerator range.
This exercises zero branches, even denominators, signs and shared factors deterministically.
Both symbol-only entries are also compared with the independently specified values. -/
def kroneckerGcdRegression : Bool :=
  (List.range 65).all fun i ↦
    let a : ℤ := (i : ℤ) - 32
    ((List.range 65).all fun j ↦
        let n : ℤ := (j : ℤ) - 32
        let out := NumberTheory.kroneckerGcd a n
        out.1 == NumberTheory.kroneckerSym a n && out.2 == Nat.gcd a.natAbs n.natAbs &&
          NumberTheory.kroneckerSymFast a n == out.1) &&
      ((List.range 33).all fun n ↦
        let out := NumberTheory.jacobiGcdFast a n
        out.1 == jacobiSym a n && out.2 == Nat.gcd a.natAbs n &&
          NumberTheory.jacobiSymFast a n == out.1)

/-- Check fixed boundary pairs independently of the specification evaluation.
The examples distinguish Kronecker's zero-denominator convention and retain complete gcds. -/
def kroneckerGcdBoundaryRegression : Bool :=
  ([((0, 0), (0, 0)), ((1, 0), (1, 1)), ((-1, 0), (1, 1)), ((2, 0), (0, 2)), ((0, -1), (1, 1)),
          ((0, 12), (0, 12)), ((-1, -1), (-1, 1)), ((3, 2), (-1, 1)), ((-3, -2), (1, 1)),
          ((6, 10), (0, 2)), ((-12, 18), (0, 6)), ((45, 75), (0, 15)), ((57, 31), (-1, 1))] :
        List ((ℤ × ℤ) × (ℤ × ℕ))).all
    fun p ↦ NumberTheory.kroneckerGcd p.1.1 p.1.2 == p.2

/-- Replay signed powers of two, their neighbors and Fibonacci numerators.
Exponents reach 1024; small odd denominator parts keep specification evaluation inexpensive.
The independent symbol specification and gcd supply both expected projections.
Symbol-only Kronecker execution is checked on the same multiword signed inputs. -/
def kroneckerGcdStructuredRegression : Bool :=
  ([0, 1, 2, 7, 31, 127, 1024] : List ℕ).all fun e ↦
    ([3, 5, 15] : List ℕ).all fun d ↦
      ([-1, 1] : List ℤ).all fun sa ↦
        ([-1, 1] : List ℤ).all fun sn ↦
          ([2 ^ e * d * 31, 2 ^ e * d * 31 + 1, Nat.fastFib (e + 3)] : List ℕ).all fun A ↦
            let a := sa * (A : ℤ)
            let n := sn * ((2 ^ (e / 2) * d * 57 : ℕ) : ℤ)
            let out := NumberTheory.kroneckerGcd a n
            out.1 == NumberTheory.kroneckerSym a n && out.2 == Nat.gcd a.natAbs n.natAbs &&
              NumberTheory.kroneckerGcdFast a n == out &&
              NumberTheory.kroneckerSymFast a n == out.1 &&
              NumberTheory.jacobiSymFast a n.natAbs == jacobiSym a n.natAbs

/-- Compare success and exhaustion with the old symbol procedure for arbitrary small states.
Both odd and even denominators are included, with accumulated coefficients minus one, zero and one.
The four budgets include zero, one, the sufficient Fibonacci bound and an excess round.
The fixed (31, 26) example separates ordinary and batched stopping counts.
The symbol-only accumulator is also compared with the reference on every small state. -/
def jacobiGcdFuelRegression : Bool :=
  (NumberTheory.Euclid.run 3 31 26).2 == 0 &&
    (NumberTheory.Jacobi.Gcd.runFuel 3 ⟨31, 26, 1⟩ == none) &&
    (NumberTheory.Jacobi.Gcd.runFuel 4 ⟨31, 26, 1⟩ == some (-1, 1)) &&
    (List.range 33).all fun c ↦
      (List.range 33).all fun m ↦
        ([-1, 0, 1] : List ℤ).all fun s ↦
          (NumberTheory.Jacobi.symbolNat m c s == s * NumberTheory.Jacobi.jacobiNat m c) &&
            let bound := NumberTheory.Euclid.stepBound m
            ([0, 1, bound, bound + 1] : List ℕ).all fun fuel ↦
              (NumberTheory.Jacobi.Gcd.runFuel fuel ⟨c, m, s⟩).map Prod.fst ==
                (NumberTheory.Jacobi.jacobiNatBatchedFuel fuel m c).map (fun j ↦ s * j)

/-- Compare the separate fuel-free pair APIs with the retained fuel-based entries.
Signed denominators, zero inputs and even natural denominators occur in this small grid.
These executable checks supplement the all-input specification theorems. -/
def gcdFuelFreeRegression : Bool :=
  (List.range 65).all fun i ↦
    (List.range 65).all fun j ↦
      let a := (i : ℤ) - 32
      let n := (j : ℤ) - 32
      NumberTheory.kroneckerGcdFast a n == NumberTheory.kroneckerGcd a n &&
        NumberTheory.jacobiGcdFuelFreeFast a j == NumberTheory.jacobiGcdFast a j

set_option linter.hashCommand false in
#eval
  show IO Unit from do
    unless
      kroneckerGcdRegression && kroneckerGcdBoundaryRegression &&
        kroneckerGcdStructuredRegression &&
        jacobiGcdFuelRegression &&
        gcdFuelFreeRegression do
      throw (IO.userError "Kronecker/gcd or Jacobi compatibility regression")

end PseudoPrime.Tests
