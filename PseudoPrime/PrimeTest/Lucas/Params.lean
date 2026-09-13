/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Lucas.Defs

/-!
# Lucas parameters

This structure keeps the discriminant equation available to proofs while the
executable Lucas APIs continue to accept explicit integer parameters.
-/

namespace PseudoPrime.PrimeTest

/-- Parameters for a Lucas sequence together with its discriminant equation.

`D` is the discriminant, while `P` and `Q` are the recurrence parameters.  The
field `discr` is the invariant `D = P^2 - 4 Q` used by Lucas prime criteria.
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

/-- Construct proof-carrying Lucas parameters from an explicit discriminant equation. -/
def LucasParams.ofDiscriminant (D P Q : ℤ) (hdisc : D = P * P - 4 * Q) : LucasParams :=
  ⟨D, P, Q, hdisc⟩

/-- The discriminant equation of a Lucas parameter, exposed as a theorem. -/
theorem LucasParams.discriminant (param : LucasParams) :
    param.D = param.P * param.P - 4 * param.Q := by exact param.discr

/-- A Lucas `U` value obtained from proof-carrying parameters. -/
def LucasParams.u (param : LucasParams) (k : ℕ) : ℤ :=
  lucasU param.P param.Q k

/-- A Lucas `V` value obtained from proof-carrying parameters. -/
def LucasParams.v (param : LucasParams) (k : ℕ) : ℤ :=
  lucasV param.P param.Q k

/-- The `U` sequence attached to parameters agrees with the base definition. -/
theorem LucasParams.u_eq (param : LucasParams) (k : ℕ) : param.u k = lucasU param.P param.Q k := by
  rfl

/-- The `V` sequence attached to parameters agrees with the base definition. -/
theorem LucasParams.v_eq (param : LucasParams) (k : ℕ) : param.v k = lucasV param.P param.Q k := by
  rfl

end PseudoPrime.PrimeTest
