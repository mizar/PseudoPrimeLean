/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.ReferenceProcedure
public import PseudoPrime.PrimeTest.StrongLucas.Prime

/-! # Explicit Strong Lucas execution

The PQ core follows isprime_lucas_strong_pq: split n + 1, initialize the Lucas triple
once, then check successive V values before doubling. Definition-side APIs remain
separate, and callers explicitly choose the executable API. No compiler rewrite is used.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- Share one scalar companion power between the initial U and V for any modulus.
Index-zero U is zero; other indices use the state's c component. The subsequent
scan shares V and Q powers. This total fallback handles unsupported PQ-core inputs. -/
def strongLucasScalarShared (n : ℕ) (D P Q : ℤ) : Bool :=
  let d := strongLucasOddPart n D
  let x := lucasScalarPowFast n P Q d
  let u := if d = 0 then 0 else x.c
  (u == 0) || lucasVScan n (x.a + x.d) (npowBinRec d (Q : ZMod n)) (strongLucasTwoAdicExponent n D)

/-- Sharing the initial companion power preserves the total doubling-loop result.
Splitting the initial index identifies U and V with their original evaluators. -/
theorem strongLucasScalarShared_eq (n : ℕ) (D P Q : ℤ) :
    strongLucasScalarShared n D P Q = strongLucasWithParamsLoop n D P Q := by
  simp only [strongLucasScalarShared, strongLucasWithParamsLoop, lucasVZModFast]
  cases strongLucasOddPart n D <;> rfl

/-- Execute the reference Strong Lucas PQ procedure with the fixed index n + 1.
The intended input is odd n at least three with Jacobi(P^2 - 4Q, n) = -1; this raw
core does not check that hypothesis or select parameters. It initializes U, V, and
Q^d once, accepts initial U = 0, and scans V at d * 2^r for r < v_2(n + 1).
The scan returns on acceptance and omits the final unused doubling. -/
def strongLucasWithPQ (n : ℕ) (P Q : ℤ) : Bool :=
  let delta := n + 1
  let s := padicValNat 2 delta
  let d := Nat.divMaxPow delta 2
  let x := lucasUVQLeading n P Q d
  (x.u == 0) || lucasVScan n x.v x.qk s

/-- For odd n and Jacobi-minus-one D, the PQ procedure equals the defining test.
The reference initializer and doubling invariant identify every tested congruence.
The Boolean equality itself needs no discriminant identity. -/
theorem strongLucasWithPQ_eq (n : ℕ) (hn : Odd n) (D P Q : ℤ) (hD : jacobiSym D n = -1) :
    strongLucasWithPQ n P Q = strongLucasWithParams n D P Q := by
  rw [← strongLucasWithParamsUVQ_eq]
  simp only [strongLucasWithPQ, strongLucasWithParamsUVQ, ite_eq_left hn, strongLucasOddPart,
    strongLucasTwoAdicExponent, lucasProbablePrimeIndex_of_jacobi_eq_neg_one hD, leading_eq n hn]

/-- Fast explicit-parameter Strong Lucas, separate from the finite-index definition.
Odd Jacobi-minus-one inputs run the reference PQ core; all other inputs use shared
scalar initialization and a doubling scan. No common primality precheck is performed. -/
def strongLucasWithParamsFast (n : ℕ) (D P Q : ℤ) : Bool :=
  if Odd n ∧ jacobiSym D n = -1 then strongLucasWithPQ n P Q else strongLucasScalarShared n D P Q

/-- The explicit executable agrees with the finite-index definition on every input.
The PQ-core identity and total fallback identity cover the two execution branches. -/
theorem strongLucasWithParamsFast_eq (n : ℕ) (D P Q : ℤ) :
    strongLucasWithParamsFast n D P Q = strongLucasWithParams n D P Q := by
  unfold strongLucasWithParamsFast
  split
  · next h => exact strongLucasWithPQ_eq n h.1 D P Q h.2
  · exact (strongLucasScalarShared_eq n D P Q).trans (strongLucasWithParamsLoop_eq n D P Q)

/-- Every prime passes fast execution for valid Jacobi-minus-one parameters.
The all-input equality transfers the defining test's prime completeness theorem. -/
theorem strongLucasWithParamsFast_of_prime {n : ℕ} (hn : n.Prime) (D P Q : ℤ)
    (hdisc : D = P * P - 4 * Q) (hjacobi : jacobiSym D n = -1) :
    strongLucasWithParamsFast n D P Q = true :=
  (strongLucasWithParamsFast_eq n D P Q).trans
    (strongLucasWithParams_of_prime hn D P Q hdisc hjacobi)

end PseudoPrime.PrimeTest
