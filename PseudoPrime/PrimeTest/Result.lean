/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Prime.Basic

/-!
# Certified primality decisions
This foundational interface is shared by trial division, certificate methods and test adapters.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Proof-carrying result for the natural input `n`.
`unknown` supplies no conclusion; `prime` carries a proof of `Nat.Prime n`; `notPrime` carries
its negation, including the cases `0` and `1`. The result type makes contradictory conclusive
answers impossible. Certificate methods, trial division, and one-sided filters share this
interface; probable-prime acceptance and exhausted searches remain `unknown`.
-/
inductive Decision (n : ℕ) where
  | unknown
  | prime (proof : Nat.Prime n)
  | notPrime (proof : ¬Nat.Prime n)

/--
Display a certified decision without retaining its proof term.
For the same input `n`, map `unknown` to `none`, `prime` to `some true`, and `notPrime` to
`some false`. This projection is used for result comparison and executable regressions;
`none` denotes absence of a conclusion rather than a claim of compositeness.
-/
def Decision.toOption {n : ℕ} : Decision n → Option Bool
  | .unknown => none
  | .prime _ => some true
  | .notPrime _ => some false

/--
Conclusive decisions `a` and `b` about the same natural input cannot disagree.
The assumptions `ha` and `hb` identify their projections with `some x` and `some y`, excluding
`unknown`; the conclusion is `x = y`. The proof splits the constructors: matching conclusions
identify the Booleans, and opposite conclusions contradict their carried primality proofs.
This validates comparisons between independent certified decision procedures.
-/
theorem Decision.agrees {n : ℕ} (a b : Decision n) {x y : Bool} (ha : a.toOption = some x)
    (hb : b.toOption = some y) : x = y := by
  cases a <;> cases b <;> simp only [toOption, Option.some.injEq] at ha hb
  all_goals
    first
    | contradiction
    | exact ha.symm.trans hb

end PseudoPrime.PrimeTest
