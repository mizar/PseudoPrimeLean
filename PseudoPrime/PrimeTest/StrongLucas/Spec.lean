/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.StrongLucas.Defs

/-! # Strong Lucas executable specification -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
The explicit Strong Lucas Boolean accepts exactly its finite propositional specification.
The discriminant identity packages `D`, `P`, `Q` into `LucasParams`; no primality assumption
is required. The proof unfolds disjunction and list search, then replaces fast modular `U` and
`V` values by their mathematical sequences. This is the bridge for Strong Lucas correctness.
-/
theorem strongLucasWithParams_eq_true_iff (n : ℕ) (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) :
    strongLucasWithParams n D P Q = true ↔
      IsStrongLucasProbablePrime n (LucasParams.ofDiscriminant D P Q hdisc) := by
  simp only [strongLucasWithParams, IsStrongLucasProbablePrime, LucasParams.ofDiscriminant,
    Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range, lucasUZModFast_eq_lucasUZMod,
    lucasVZModFast_eq_lucasVZMod]

/--
The selected Strong Lucas odd part is odd whenever the full selected index is nonzero.
The premise is `lucasProbablePrimeIndex n D ≠ 0`; no modulus-primality assumption is made.
Apply the general odd-part lemma to the selected index. Subsequent doubling arguments use
this to distinguish the initial odd exponent from the power-of-two scan.
-/
theorem strongLucasOddPart_odd {n : ℕ} {D : ℤ} (hindex : lucasProbablePrimeIndex n D ≠ 0) :
    Odd (strongLucasOddPart n D) := by exact oddPart_odd hindex

end PseudoPrime.PrimeTest
