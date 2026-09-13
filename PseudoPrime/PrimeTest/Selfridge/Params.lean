/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.PrimeTest.Lucas.Params
import Mathlib.Tactic.Ring

/-! # Selfridge Method A and Method A* parameter constructors -/

namespace PseudoPrime.PrimeTest

/-- Construct the standard Selfridge Method A parameters from an admissible `D`.

The input congruence says that `(1 - D) / 4` is an integer, and the resulting
parameters satisfy `P = 1`, `Q = (1 - D) / 4`, and `D = P^2 - 4 Q`.
-/
def LucasParams.methodA (D : ℤ) (hmod : (1 - D) % 4 = 0) : LucasParams :=
  let Q := (1 - D) / 4
  have hdiv : (4 : ℤ) ∣ 1 - D := Int.dvd_iff_emod_eq_zero.mpr hmod
  have hquot : Q * 4 = 1 - D := Int.ediv_mul_cancel hdiv
  ⟨D, 1, Q, by
    dsimp [Q]
    calc
      D = 1 - (1 - D) := by ring
      _ = 1 - ((1 - D) / 4 * 4) := by rw [hquot]
      _ = 1 * 1 - 4 * ((1 - D) / 4) := by ring⟩

/-- The Method A constructor has the expected recurrence parameters. -/
theorem LucasParams.methodA_P (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodA D hmod).P = 1 := by rfl

/-- The Method A constructor preserves the selected discriminant. -/
theorem LucasParams.methodA_D (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodA D hmod).D = D := by rfl

/-- The Method A constructor has the expected second recurrence parameter. -/
theorem LucasParams.methodA_Q (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodA D hmod).Q = (1 - D) / 4 := by rfl

/-- Construct the Selfridge Method A* parameters, with the special `D = 5` branch. -/
def LucasParams.methodAStar (D : ℤ) (hmod : (1 - D) % 4 = 0) : LucasParams :=
  if hD : D = 5 then
    ⟨D, 5, 5, by
      subst D; ring⟩
  else LucasParams.methodA D hmod

/-- The Method A* discriminant invariant is preserved in both parameter branches. -/
theorem LucasParams.methodAStar_discriminant (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodAStar D hmod).D =
      (LucasParams.methodAStar D hmod).P * (LucasParams.methodAStar D hmod).P -
        4 * (LucasParams.methodAStar D hmod).Q := by
  exact (LucasParams.methodAStar D hmod).discr

/-- The special Method A* branch uses `P = 5` when `D = 5`. -/
theorem LucasParams.methodAStar_P_of_eq_five (hmod : (1 - (5 : ℤ)) % 4 = 0) :
    (LucasParams.methodAStar 5 hmod).P = 5 := by simp only [LucasParams.methodAStar, ↓reduceDIte]

/-- The special Method A* branch uses `Q = 5` when `D = 5`. -/
theorem LucasParams.methodAStar_Q_of_eq_five (hmod : (1 - (5 : ℤ)) % 4 = 0) :
    (LucasParams.methodAStar 5 hmod).Q = 5 := by simp only [LucasParams.methodAStar, ↓reduceDIte]

/-- Away from `D = 5`, Method A* has exactly the Method A parameters. -/
theorem LucasParams.methodAStar_eq_methodA_of_ne_five {D : ℤ} (hmod : (1 - D) % 4 = 0)
    (hD : D ≠ 5) : LucasParams.methodAStar D hmod = LucasParams.methodA D hmod := by
  simp only [LucasParams.methodAStar, hD, ↓reduceDIte]

end PseudoPrime.PrimeTest
