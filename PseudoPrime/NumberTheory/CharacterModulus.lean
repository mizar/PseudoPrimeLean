/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.NumberTheory.OddNonsquare
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Bounds for the quadratic-character modulus

The induced quadratic character is used at the uniform level `4 * n`.  This file records the
elementary natural-number and logarithmic bounds needed to replace an individual admissible
input by the endpoint of a finite range.
-/

namespace PseudoPrime.NumberTheory

/-- The uniform level `4 * n` used for the quadratic character attached to `n`. -/
def characterModulus (n : ℕ) : ℕ :=
  4 * n

/-- The character modulus is positive when its input is positive. -/
theorem characterModulus_pos {n : ℕ} (hn : 0 < n) : 0 < characterModulus n := by
  rw [characterModulus]
  exact Nat.mul_pos (by norm_num only) hn

/-- Multiplying an input bound by `4` gives the corresponding character-modulus bound. -/
theorem characterModulus_le {n B : ℕ} (hnB : n ≤ B) : characterModulus n ≤ characterModulus B := by
  simpa only [characterModulus] using Nat.mul_le_mul_left 4 hnB

/-- The logarithm of the character modulus is monotone on positive bounded inputs. -/
theorem log_characterModulus_le {n B : ℕ} (hn : 0 < n) (hnB : n ≤ B) :
    Real.log (characterModulus n : ℝ) ≤ Real.log (characterModulus B : ℝ) := by
  apply Real.log_le_log
  · exact_mod_cast characterModulus_pos hn
  · exact_mod_cast characterModulus_le hnB

/-- An admissible input has positive character modulus. -/
theorem Admissible.characterModulus_pos {B n : ℕ} (hn : Admissible B n) : 0 < characterModulus n :=
  NumberTheory.characterModulus_pos hn.pos

/-- The character modulus of an admissible input is bounded by the endpoint modulus. -/
theorem Admissible.characterModulus_le {B n : ℕ} (hn : Admissible B n) :
    characterModulus n ≤ characterModulus B :=
  NumberTheory.characterModulus_le hn.le

/-- The log modulus of an admissible input is bounded by the log modulus at the endpoint. -/
theorem Admissible.log_characterModulus_le {B n : ℕ} (hn : Admissible B n) :
    Real.log (characterModulus n : ℝ) ≤ Real.log (characterModulus B : ℝ) :=
  NumberTheory.log_characterModulus_le hn.pos hn.le

end PseudoPrime.NumberTheory
