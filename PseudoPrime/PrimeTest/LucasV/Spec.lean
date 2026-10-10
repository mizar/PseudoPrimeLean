/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.LucasV.Defs

/-! # Lucas-V executable specification -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Identify explicit-parameter executable acceptance with `IsLucasVProbablePrime`.
The premise `D = P * P - 4 * Q` packages the parameters into `LucasParams`; no primality
assumption is made. The proof unfolds the Boolean decision and replaces fast `V` evaluation
by its mathematical sequence. Prime completeness and guarded decision adapters use this bridge.
-/
theorem lucasVWithParams_eq_true_iff (n : ℕ) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) :
    lucasVWithParams n D P Q = true ↔
      IsLucasVProbablePrime n (LucasParams.ofDiscriminant D P Q hdisc) := by
  simp only [lucasVWithParams, IsLucasVProbablePrime, LucasParams.ofDiscriminant, decide_eq_true_eq,
    lucasVZModFast_eq_lucasVZMod]

/--
The modular right-hand side `2 * (param.Q : ZMod n)` equals the cast of the integer `2Q`.
This holds for every natural modulus and signed parameter `Q`, without a primality hypothesis.
The proof uses preservation of multiplication and numerals by the integer cast.
It aligns integer parameter arithmetic with the Lucas-V congruence notation.
-/
theorem lucasVProbablePrime_rhs (n : ℕ) (param : LucasParams) :
    2 * (param.Q : ZMod n) = (2 * param.Q : ℤ) := by simp only [Int.cast_mul, Int.cast_ofNat]

end PseudoPrime.PrimeTest
