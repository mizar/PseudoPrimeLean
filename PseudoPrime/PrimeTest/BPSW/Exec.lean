/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.MillerRabin.Loop
import PseudoPrime.PrimeTest.BPSW.Top
import PseudoPrime.PrimeTest.StrongLucas.Loop

/-!
# Miller–Rabin-first BPSW execution

These entries preserve the current Boolean specifications while moving the
successive-square MR test ahead of square testing and parameter search.
The factor-detecting wheel and shared Lucas evaluator are later stages.
-/

namespace PseudoPrime.PrimeTest

/-- Run the small-input and parity checks, then Miller–Rabin, then the square
check and classical Selfridge search. The supplied Lucas test consumes the
selected parameters. Search failure remains false, and no GRH is assumed. -/
def bpswMRFirst (n : ℕ) (lucasTest : LucasParams → Bool) : Bool :=
  if n < 2 then false
  else if n = 2 then true
  else if Even n then false
  else if strongMillerRabinWithBaseLoop n 2 then
    if natIsSquare n then false
    else match selfridgeClassicalMethodAStarParamsWithinTwoMul n with
      | none => false
      | some param => lucasTest param
  else false
/-- Moving Miller–Rabin ahead of the square check and search preserves the
original composition for every input and Lucas consumer. The proof separates
the precheck branches from the modular-test and search branches. -/
theorem bpswMRFirst_eq (n : ℕ) (lucasTest : LucasParams → Bool) :
    bpswMRFirst n lucasTest =
      (match primalityPrecheck n with
      | some result => result
      | none => match selfridgeClassicalMethodAStarParamsWithinTwoMul n with
        | none => false
        | some param => strongMillerRabinBase2WithPrecheck n && lucasTest param) := by
  by_cases hlt : n < 2
  · simp only [bpswMRFirst, primalityPrecheck, hlt, ↓reduceIte]
  · by_cases htwo : n = 2
    · simp only [bpswMRFirst, primalityPrecheck, ite_eq_right hlt, ite_eq_left htwo]
    · by_cases heven : Even n
      · simp only [bpswMRFirst, primalityPrecheck, hlt, htwo, heven, ↓reduceIte]
      · by_cases hsquare : natIsSquare n = true
        · simp only [bpswMRFirst, primalityPrecheck, hlt, htwo, heven,
            hsquare, ↓reduceIte, ite_self]
        · cases hmr : strongMillerRabinWithBase n 2 <;>
            cases hparams : selfridgeClassicalMethodAStarParamsWithinTwoMul n <;>
            simp only [bpswMRFirst, primalityPrecheck, hlt, htwo, heven, hsquare,
              strongMillerRabinWithBaseLoop_eq, strongMillerRabinBase2,
              hmr, hparams, strongMillerRabinBase2WithPrecheck, ↓reduceIte,
              Bool.false_and, Bool.true_and, Bool.false_eq_true]

/-- Ordinary BPSW using successive-square MR before square testing and search.
The classical pure-minus-one search and the existing Strong Lucas test are
retained so that the all-input equality theorem applies. -/
def bailliePSWMRFirst (n : ℕ) : Bool :=
  bpswMRFirst n (fun param ↦ strongLucasWithParamsLoop n param.D param.P param.Q)
/-- Strengthened BPSW with MR evaluated before square testing and search.
The existing Lucas-V and unmultiplied Euler–Jacobi conditions are retained;
this stage does not yet adopt the reference programs' multiplied Q condition. -/
def strengthenedBPSWMRFirst (n : ℕ) : Bool :=
  bpswMRFirst n (fun param ↦ strongLucasWithParamsLoop n param.D param.P param.Q &&
    (lucasVWithParams n param.D param.P param.Q && eulerJacobiWithIntBase n param.Q))
/-- The reordered ordinary entry equals the current public BPSW on every input.
This connects the new execution order to the existing unconditional specification. -/
theorem bailliePSWMRFirst_eq (n : ℕ) : bailliePSWMRFirst n = bailliePSW n := by
  rw [bailliePSWMRFirst]
  simp only [strongLucasWithParamsLoop_eq]
  rw [bpswMRFirst_eq]
  rfl
/-- The reordered strengthened entry equals the current public strengthened
BPSW on every input. Associativity aligns the unchanged component tests. -/
theorem strengthenedBPSWMRFirst_eq (n : ℕ) :
    strengthenedBPSWMRFirst n = strengthenedBPSW n := by
  rw [strengthenedBPSWMRFirst]
  simp only [strongLucasWithParamsLoop_eq]
  rw [bpswMRFirst_eq]
  simp only [strengthenedBPSW, strengthenedBPSWWithParams, bailliePSWWithParams,
    Bool.and_assoc]
  rfl
/-- The reordered ordinary entry inherits the unconditional primality-test
specification by function equality. Acceptance is a probable-prime result. -/
theorem bailliePSWMRFirst_spec : PrimalityTestSpec bailliePSWMRFirst := by
  have hfun : bailliePSWMRFirst = bailliePSW := funext bailliePSWMRFirst_eq
  rw [hfun]
  exact bailliePSW_spec_unconditional
/-- The reordered strengthened entry inherits the unconditional specification
by function equality, without an analytic or GRH assumption. -/
theorem strengthenedBPSWMRFirst_spec : PrimalityTestSpec strengthenedBPSWMRFirst := by
  have hfun : strengthenedBPSWMRFirst = strengthenedBPSW := funext strengthenedBPSWMRFirst_eq
  rw [hfun]
  exact strengthenedBPSW_spec_unconditional
end PseudoPrime.PrimeTest
