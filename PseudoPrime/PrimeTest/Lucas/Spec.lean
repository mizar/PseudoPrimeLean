/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Defs

/-! # Lucas sequence specifications -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
The dedicated modular `U` sequence equals the cast of its integer sequence at every index.
Natural modulus `n`, integer parameters `P`, `Q`, and natural `k` are arbitrary.
The proof is reflexivity because `lucasUZMod` is defined by this cast.
This bridges integer recurrence identities to residue-ring specifications.
-/
theorem lucasUZMod_eq_cast (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZMod n P Q k = (lucasU P Q k : ZMod n) := by rfl

/--
The dedicated modular `V` sequence equals the cast of its integer sequence at every index.
For arbitrary `n`, `P`, `Q`, and `k`, the equality is definitional and proved by reflexivity.
It transfers integer companion-sequence identities to residue-ring test conditions.
-/
theorem lucasVZMod_eq_cast (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZMod n P Q k = (lucasV P Q k : ZMod n) := by rfl

/--
The modular Lucas sequence satisfies `U_(k+2) = P * U_(k+1) - Q * U_k` in `ZMod n`.
The modulus `n`, signed recurrence parameters `P`, `Q`, and index `k` are unrestricted.
Rewrite the corresponding integer sequence identity and preserve its arithmetic through casting.
This supplies the residue-ring identity used by modular recurrence arguments.
-/
theorem lucasUZMod_succ_succ (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZMod n P Q (k + 2) =
      (P : ZMod n) * lucasUZMod n P Q (k + 1) - (Q : ZMod n) * lucasUZMod n P Q k := by
  change (lucasU P Q (k + 2) : ZMod n) = _
  rw [lucasU_succ_succ]
  simp only [lucasUZMod, Int.cast_mul, Int.cast_sub]

/--
The modular Lucas sequence satisfies `V_(k+2) = P * V_(k+1) - Q * V_k` in `ZMod n`.
The modulus `n`, signed recurrence parameters `P`, `Q`, and index `k` are unrestricted.
Rewrite the corresponding integer sequence identity and preserve its arithmetic through casting.
This supplies the residue-ring identity used by modular companion recurrence arguments.
-/
theorem lucasVZMod_succ_succ (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZMod n P Q (k + 2) =
      (P : ZMod n) * lucasVZMod n P Q (k + 1) - (Q : ZMod n) * lucasVZMod n P Q k := by
  change (lucasV P Q (k + 2) : ZMod n) = _
  rw [lucasV_succ_succ]
  simp only [lucasVZMod, Int.cast_mul, Int.cast_sub]

/--
The modular Lucas sequence satisfies `U_(2k) = U_k * V_k` in `ZMod n`.
The modulus `n`, signed recurrence parameters `P`, `Q`, and index `k` are unrestricted.
Rewrite the corresponding integer sequence identity and preserve its arithmetic through casting.
This supplies the residue-ring identity used by Strong Lucas doubling and zero-factor arguments.
-/
theorem lucasUZMod_two_mul (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZMod n P Q (2 * k) = lucasUZMod n P Q k * lucasVZMod n P Q k := by
  change (lucasU P Q (2 * k) : ZMod n) = _
  rw [lucasU_two_mul]
  simp only [lucasUZMod, lucasVZMod, Int.cast_mul]

/--
The modular Lucas sequence satisfies `U_(2k+1) = U_(k+1)^2 - Q * U_k^2` in `ZMod n`.
The modulus `n`, signed recurrence parameters `P`, `Q`, and index `k` are unrestricted.
Rewrite the corresponding integer sequence identity and preserve its arithmetic through casting.
This supplies the residue-ring identity used by binary `U` evaluation.
-/
theorem lucasUZMod_two_mul_add_one (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasUZMod n P Q (2 * k + 1) =
      lucasUZMod n P Q (k + 1) ^ 2 - (Q : ZMod n) * lucasUZMod n P Q k ^ 2 := by
  change (lucasU P Q (2 * k + 1) : ZMod n) = _
  rw [lucasU_two_mul_add_one]
  simp only [lucasUZMod, Int.cast_sub, Int.cast_pow, Int.cast_mul]

/--
The modular Lucas sequence satisfies `V_(2k) = V_k^2 - 2 * Q^k` in `ZMod n`.
The modulus `n`, signed recurrence parameters `P`, `Q`, and index `k` are unrestricted.
Rewrite the corresponding integer sequence identity and preserve its arithmetic through casting.
This supplies the residue-ring identity used by shared `V` and `Q` doubling scans.
-/
theorem lucasVZMod_two_mul (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZMod n P Q (2 * k) = lucasVZMod n P Q k ^ 2 - 2 * (lucasQPow Q k : ZMod n) := by
  change (lucasV P Q (2 * k) : ZMod n) = _
  rw [lucasV_two_mul]
  simp only [lucasVZMod, Int.cast_sub, Int.cast_pow, Int.cast_mul, Int.cast_ofNat]

/--
The modular Lucas sequence satisfies `V_(2k+1) = V_(k+1) * V_k - P * Q^k` in `ZMod n`.
The modulus `n`, signed recurrence parameters `P`, `Q`, and index `k` are unrestricted.
Rewrite the corresponding integer sequence identity and preserve its arithmetic through casting.
This supplies the residue-ring identity used by binary companion-sequence evaluation.
-/
theorem lucasVZMod_two_mul_add_one (n : ℕ) (P Q : ℤ) (k : ℕ) :
    lucasVZMod n P Q (2 * k + 1) =
      lucasVZMod n P Q (k + 1) * lucasVZMod n P Q k - (P : ZMod n) * (lucasQPow Q k : ZMod n) := by
  change (lucasV P Q (2 * k + 1) : ZMod n) = _
  rw [lucasV_two_mul_add_one]
  simp only [lucasVZMod, Int.cast_sub, Int.cast_mul]

end PseudoPrime.PrimeTest
