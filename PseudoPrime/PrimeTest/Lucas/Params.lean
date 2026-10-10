/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Defs

/-!
# Lucas parameters

This structure keeps the discriminant equation available to proofs while the
executable Lucas APIs continue to accept explicit integer parameters.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Signed Lucas recurrence parameters equipped with the discriminant invariant.
`P` and `Q` define the `U` and `V` recurrences, `D` names their discriminant, and `discr` proves
`D = P * P - 4 * Q`. No Jacobi, coprimality, or modulus-primality property is stored.
The record keeps the discriminant equation available when passing parameters from Selfridge
selection to propositional Lucas criteria and sequence projections.
-/
structure LucasParams where
  /-- The discriminant of the Lucas parameter pair. -/
  D : ℤ
  /-- The first recurrence parameter. -/
  P : ℤ
  /-- The second recurrence parameter. -/
  Q : ℤ
  /-- The discriminant equation relating `D`, `P`, and `Q`. -/
  discr : D = P * P - 4 * Q

/--
Package integer `D`, `P`, `Q` with the supplied proof of `D = P * P - 4 * Q`.
Return a `LucasParams` record with exactly these fields and invariant; no computation or
parameter search is performed. Executable-to-propositional specification lemmas use this
constructor to state correctness for APIs accepting three explicit integers.
-/
def LucasParams.ofDiscriminant (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) : LucasParams :=
  ⟨D, P, Q, hdisc⟩

/--
Expose the discriminant invariant of `param` as an equality theorem.
The conclusion is `param.D = param.P * param.P - 4 * param.Q`, with no additional premise.
The proof is the stored `discr` field. Lucas criteria use this projection when a theorem
expects an explicit discriminant equation rather than the record itself.
-/
theorem LucasParams.discriminant (param : LucasParams) :
    param.D = param.P * param.P - 4 * param.Q := by exact param.discr

/--
Integer Lucas `U` sequence at index `k` using the recurrence pair stored in `param`.
Return `lucasU param.P param.Q k`; the discriminant proof is not evaluated.
This projection supplies convenient sequence notation for proof-carrying parameters.
-/
def LucasParams.u (param : LucasParams) (k : ℕ) : ℤ :=
  lucasU param.P param.Q k

/--
Integer Lucas `V` sequence at index `k` using the recurrence pair stored in `param`.
Return `lucasV param.P param.Q k`; no modulus is applied and no discriminant computation
is needed. This is the companion sequence projection to `LucasParams.u`.
-/
def LucasParams.v (param : LucasParams) (k : ℕ) : ℤ :=
  lucasV param.P param.Q k

/--
The record-based `U` projection agrees with `lucasU param.P param.Q k` for every `k`.
The equality is definitional and the proof is reflexivity. It lets proofs move between
record-based sequence notation and the explicit recurrence-parameter API.
-/
theorem LucasParams.u_eq (param : LucasParams) (k : ℕ) : param.u k = lucasU param.P param.Q k := by
  rfl

/--
The record-based `V` projection agrees with `lucasV param.P param.Q k` for every `k`.
The proof unfolds no arithmetic: the equality is reflexivity. This aligns record-based
sequence notation with the explicit recurrence-parameter API.
-/
theorem LucasParams.v_eq (param : LucasParams) (k : ℕ) : param.v k = lucasV param.P param.Q k := by
  rfl

end PseudoPrime.PrimeTest
