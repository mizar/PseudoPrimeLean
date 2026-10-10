/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Loop
public import PseudoPrime.PrimeTest.BPSW.Top
public import PseudoPrime.PrimeTest.StrongLucas.Loop
public import PseudoPrime.PrimeTest.StrongLucas.NoGcd

/-!
# Miller–Rabin-first BPSW execution

These entries preserve the current Boolean specifications while moving the
successive-square MR test ahead of square testing and parameter search.
The factor-detecting wheel and shared Lucas evaluator are later stages.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
MR-first ordinary composition with a caller-supplied Lucas consumer of selected parameters.
For natural `n`, handle values below two, two, and other even inputs first; then run base-two
successive-square MR, reject squares, and perform the bounded classical Method A* search.
A failed MR test or search returns false; successful search evaluates `lucasTest param`.
This is the pure-minus-one search path used for boundary fallback, not the factor-detecting wheel.
-/
def bpswMRFirst (n : ℕ) (lucasTest : LucasParams → Bool) : Bool :=
  if n < 2 then false
  else
    if n = 2 then true
    else
      if Even n then false
      else
        if strongMillerRabinWithBaseLoop n 2 then
          if natIsSquare n then false
          else
            match selfridgeClassicalMethodAStarParamsWithinTwoMul n with
            | none => false
            | some param => lucasTest param
        else false

/--
Moving MR before square checking and classical search preserves the composition for any consumer.
For arbitrary natural `n` and `lucasTest`, the right side prechecks, searches, and conjoins MR
with the consumer. The proof splits small inputs, parity, squares, MR results, and search results,
using equality of the successive-square and defining MR tests. This all-input equality permits
reusing ordinary BPSW correctness without changing the search or Lucas predicate.
-/
theorem bpswMRFirst_eq (n : ℕ) (lucasTest : LucasParams → Bool) :
    bpswMRFirst n lucasTest =
      (match primalityPrecheck n with
      | some result => result
      | none =>
        match selfridgeClassicalMethodAStarParamsWithinTwoMul n with
        | none => false
        | some param => strongMillerRabinBase2WithPrecheck n && lucasTest param) := by
  by_cases hlt : n < 2
  · simp only [bpswMRFirst, primalityPrecheck, hlt, ↓reduceIte]
  · by_cases htwo : n = 2
    · simp only [bpswMRFirst, primalityPrecheck, ite_eq_right hlt, ite_eq_left htwo]
    · by_cases heven : Even n
      · simp only [bpswMRFirst, primalityPrecheck, hlt, htwo, heven, ↓reduceIte]
      · by_cases hsquare : natIsSquare n = true
        · simp only [bpswMRFirst, primalityPrecheck, hlt, htwo, heven, hsquare, ↓reduceIte,
            ite_self]
        · cases hmr : strongMillerRabinWithBase n 2 <;>
            cases hparams : selfridgeClassicalMethodAStarParamsWithinTwoMul n <;>
            simp only [bpswMRFirst, primalityPrecheck, hlt, htwo, heven, hsquare,
              strongMillerRabinWithBaseLoop_eq, strongMillerRabinBase2, hmr, hparams,
              strongMillerRabinBase2WithPrecheck, ↓reduceIte, Bool.false_and, Bool.true_and,
              Bool.false_eq_true]

/--
Ordinary BPSW with base-two MR before square checking and pure-minus-one Selfridge search.
Use `bpswMRFirst` with the shared `U`, `V`, and `Q` Strong Lucas initializer at the selected
Method A* parameters. The search retains the classical bounded order; this is not the
factor-detecting Wheel30 entry. Scan boundary handling uses its one-sided correctness contract.
-/
def bailliePSWMRFirst (n : ℕ) : Bool :=
  bpswMRFirst n (fun param ↦ strongLucasWithParamsUVQ n param.D param.P param.Q)

/--
For every natural input, MR-first ordinary BPSW equals precheck-first `bailliePSW`.
No arithmetic hypothesis is needed. Rewrite the shared Strong Lucas Boolean to its defining
comparison and use `bpswMRFirst_eq`; the remaining composition is definitional.
This transfers the existing all-input contract to the reordered entry.
-/
theorem bailliePSWMRFirst_eq (n : ℕ) : bailliePSWMRFirst n = bailliePSW n := by
  rw [bailliePSWMRFirst]
  simp only [strongLucasWithParamsUVQ_eq]
  rw [bpswMRFirst_eq]
  rfl

/--
Unconditional one-sided primality-filter contract for MR-first ordinary BPSW.
Function extensionality lifts `bailliePSWMRFirst_eq`, then rewriting gives the precheck-first
entry's unconditional contract. Consequently rejection certifies non-primality, while acceptance
still provides only a probable-prime result. Selfridge scan boundary fallbacks use this contract.
-/
theorem bailliePSWMRFirst_spec : PrimalityTestSpec bailliePSWMRFirst := by
  have hfun : bailliePSWMRFirst = bailliePSW := funext bailliePSWMRFirst_eq
  rw [hfun]
  exact bailliePSW_spec_unconditional

end PseudoPrime.PrimeTest
