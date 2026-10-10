/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.Lucas.Params
public import Mathlib.Tactic.Ring

/-! # Selfridge Method A and Method A* parameter constructors -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/--
Construct Method A parameters from integer `D` with `(1 - D) % 4 = 0`.
Set `P = 1` and `Q = (1 - D) / 4`, and return the original `D` with its discriminant proof.
The proof converts the congruence to divisibility, cancels integer division, and checks
`D = P * P - 4 * Q` algebraically. Selfridge wrappers use this without selecting `D` themselves.
-/
def LucasParams.methodA (D : ℤ) (hmod : (1 - D) % 4 = 0) : LucasParams :=
  let Q := (1 - D) / 4
  have hdiv : (4 : ℤ) ∣ 1 - D := Int.dvd_iff_emod_eq_zero.mpr hmod
  have hquot : Q * 4 = 1 - D := Int.ediv_mul_cancel hdiv
  ⟨D, 1, Q, by
    dsimp only [Q]
    calc
      D = 1 - (1 - D) := by ring
      _ = 1 - ((1 - D) / 4 * 4) := by rw [hquot]
      _ = 1 * 1 - 4 * ((1 - D) / 4) := by ring⟩

/--
The Method A constructor has first recurrence parameter `P = 1`.
The admissibility proof `(1 - D) % 4 = 0` is supplied to the constructor; its first parameter
projection reduces by reflexivity. This rewrites the record-based Strong Lucas wrapper.
-/
theorem LucasParams.methodA_P (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodA D hmod).P = 1 := by rfl

/--
Method A preserves the supplied discriminant `D` exactly.
For any admissibility proof `hmod`, the record's `D` projection reduces by reflexivity.
Search-to-parameter bridges use this to retain the selected Jacobi condition and magnitude bound.
-/
theorem LucasParams.methodA_D (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodA D hmod).D = D := by rfl

/--
Method A has second recurrence parameter `Q = (1 - D) / 4`.
Under the constructor's admissibility hypothesis, the equality is definitional and proved by
reflexivity. It exposes the integer quotient when relating record-based and explicit execution.
-/
theorem LucasParams.methodA_Q (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodA D hmod).Q = (1 - D) / 4 := by rfl

/--
Construct Method A* parameters for an admissible integer discriminant `D`.
When `D = 5`, choose `(P, Q) = (5, 5)` and verify the discriminant equation by arithmetic;
otherwise use Method A's `(1, (1 - D) / 4)`. Both branches retain `D` and carry the invariant.
Top-level Selfridge tests use this parameter choice after the discriminant search succeeds.
-/
def LucasParams.methodAStar (D : ℤ) (hmod : (1 - D) % 4 = 0) : LucasParams :=
  if hD : D = 5 then
    ⟨D, 5, 5, by
      subst D
      ring⟩
  else LucasParams.methodA D hmod

/--
Method A* satisfies the discriminant equation in both constructor branches.
The input is `D` with its congruence proof `hmod`; the conclusion relates the returned
record's `D`, `P`, and `Q`. The proof is its stored invariant, so no branch split is needed.
Prime-pass theorems consume this equality for the selected Method A* parameters.
-/
theorem LucasParams.methodAStar_discriminant (D : ℤ) (hmod : (1 - D) % 4 = 0) :
    (LucasParams.methodAStar D hmod).D =
      (LucasParams.methodAStar D hmod).P * (LucasParams.methodAStar D hmod).P -
        4 * (LucasParams.methodAStar D hmod).Q := by
  exact (LucasParams.methodAStar D hmod).discr

/--
At discriminant `5`, Method A* returns first parameter `P = 5`.
Given the required congruence proof for `5`, simplify the true constructor branch.
This identifies the exceptional parameter pair in Method A/A* comparisons.
-/
theorem LucasParams.methodAStar_P_of_eq_five (hmod : (1 - (5 : ℤ)) % 4 = 0) :
    (LucasParams.methodAStar 5 hmod).P = 5 := by simp only [LucasParams.methodAStar, ↓reduceDIte]

/--
At discriminant `5`, Method A* returns second parameter `Q = 5`.
The congruence proof makes the constructor available; simplification selects its special branch.
This fixes the exceptional base used by the strengthened Lucas and Euler comparisons.
-/
theorem LucasParams.methodAStar_Q_of_eq_five (hmod : (1 - (5 : ℤ)) % 4 = 0) :
    (LucasParams.methodAStar 5 hmod).Q = 5 := by simp only [LucasParams.methodAStar, ↓reduceDIte]

/--
For any admissible `D ≠ 5`, Method A* and Method A return the same complete record.
Simplify the false branch of the Method A* conditional using the inequality hypothesis.
This equality includes the discriminant invariant and transfers sequence and test results
between the two parameter choices away from the exceptional discriminant.
-/
theorem LucasParams.methodAStar_eq_methodA_of_ne_five {D : ℤ} (hmod : (1 - D) % 4 = 0)
    (hD : D ≠ 5) : LucasParams.methodAStar D hmod = LucasParams.methodA D hmod := by
  simp only [LucasParams.methodAStar, hD, ↓reduceDIte]

end PseudoPrime.PrimeTest
