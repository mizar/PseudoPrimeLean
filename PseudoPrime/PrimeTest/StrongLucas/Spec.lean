/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.StrongLucas.Defs

/-! # Strong Lucas executable specification -/

namespace PseudoPrime.PrimeTest

/-- The executable Strong Lucas test is equivalent to its finite specification. -/
theorem strongLucasWithParams_eq_true_iff (n : ℕ) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) :
    strongLucasWithParams n D P Q = true ↔
      IsStrongLucasProbablePrime n (LucasParams.ofDiscriminant D P Q hdisc) := by
  simp only [strongLucasWithParams, IsStrongLucasProbablePrime, LucasParams.ofDiscriminant,
    Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range, lucasUZModFast_eq_lucasUZMod,
    lucasVZModFast_eq_lucasVZMod]

/-- The Strong Lucas odd part is odd when its selected index is nonzero. -/
theorem strongLucasOddPart_odd {n : ℕ} {D : ℤ} (hindex : lucasProbablePrimeIndex n D ≠ 0) :
    Odd (strongLucasOddPart n D) := by exact oddPart_odd hindex

end PseudoPrime.PrimeTest
