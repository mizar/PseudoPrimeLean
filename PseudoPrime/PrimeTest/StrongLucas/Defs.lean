/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.ProbablePrime
public import PseudoPrime.PrimeTest.MillerRabin.Defs

/-!
# Strong Lucas probable-prime test

The initial implementation follows the Selfridge branch with the Lucas index
selected by the discriminant Jacobi value.  The index is split into its odd
part and its power-of-two part, and the finite strong condition checks the
corresponding `U` and `V` values in `ZMod n`.
The explicit-parameter executable is a raw probable-prime comparison; its
totalized Jacobi branches are not a substitute for the common precheck.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Odd part of the Jacobi-selected Lucas index at natural `n` and integer discriminant `D`.
Compute `Nat.divMaxPow (lucasProbablePrimeIndex n D) 2`. This returns the exponent `d` used
for the initial `U_d` value and the later doubled `V` values. Oddness is guaranteed only when
the selected index is nonzero, as stated by `strongLucasOddPart_odd`.
-/
def strongLucasOddPart (n : ℕ) (D : ℤ) : ℕ :=
  Nat.divMaxPow (lucasProbablePrimeIndex n D) 2

/--
Exponent of `2` in the selected Lucas index for `n` and `D`.
Compute `padicValNat 2 (lucasProbablePrimeIndex n D)`, with the valuation's totalized behavior
at zero. Strong Lucas execution uses this value `s` to bound the finite range of doubled
`V` indices; the associated odd part is defined separately.
-/
def strongLucasTwoAdicExponent (n : ℕ) (D : ℤ) : ℕ :=
  padicValNat 2 (lucasProbablePrimeIndex n D)

/--
Finite Strong Lucas condition for natural input `n` and proof-carrying parameters `param`.
Let `d` and `s` be the odd part and two-adic exponent of the Jacobi-selected index.
Require `U_d = 0` or a zero `V_(d * 2^r)` for some `r` in `List.range s`, all in `ZMod n`.
The discriminant invariant is stored in `param`; no prime or Jacobi-minus-one premise is
included here. Executable specifications and prime-completeness proofs use this proposition.
-/
def IsStrongLucasProbablePrime (n : ℕ) (param : LucasParams) : Prop :=
  let d := strongLucasOddPart n param.D
  let s := strongLucasTwoAdicExponent n param.D
  lucasUZMod n param.P param.Q d = 0 ∨
    ∃ r ∈ List.range s, lucasVZMod n param.P param.Q (d * 2 ^ r) = 0

/--
Boolean Strong Lucas comparison for natural `n` and integer parameters `D`, `P`, `Q`.
Evaluate the fast modular `U_d` comparison, or search `r < s` for a zero fast `V_(d * 2^r)`,
where `d` and `s` decompose the Jacobi-selected index. The finite disjunction is totalized
without a primality precheck or a discriminant-identity guard. Guarded decision adapters and
Selfridge-based top-level tests provide the hypotheses needed for certified rejection.
-/
def strongLucasWithParams (n : ℕ) (D P Q : ℤ) : Bool :=
  let d := strongLucasOddPart n D
  let s := strongLucasTwoAdicExponent n D
  (lucasUZModFast n P Q d == 0) ||
    (List.range s).any (fun r ↦ lucasVZModFast n P Q (d * 2 ^ r) == 0)

end PseudoPrime.PrimeTest
