/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.LucasV.Defs

/-! # Lucas-V executable specification -/

namespace PseudoPrime.PrimeTest

/-- The executable Lucas-V test is equivalent to its mathematical specification. -/
theorem lucasVWithParams_eq_true_iff (n : ℕ) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) :
    lucasVWithParams n D P Q = true ↔
      IsLucasVProbablePrime n (LucasParams.ofDiscriminant D P Q hdisc) := by
  simp only [lucasVWithParams, IsLucasVProbablePrime, LucasParams.ofDiscriminant, decide_eq_true_eq,
    lucasVZModFast_eq_lucasVZMod]

/-- The Lucas-V right-hand side in the Selfridge branch is the doubled parameter `Q`. -/
theorem lucasVProbablePrime_rhs (n : ℕ) (param : LucasParams) :
    2 * (param.Q : ZMod n) = (2 * param.Q : ℤ) := by simp only [Int.cast_mul, Int.cast_ofNat]

end PseudoPrime.PrimeTest
