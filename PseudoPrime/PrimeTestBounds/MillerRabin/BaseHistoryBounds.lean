/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Basic.Real.Basic

/-! # The small recurrence core for cumulative MR history

Only the profile type, its entrance and coefficient maps, and a real-scale base are inputs.
This core has no project imports or fixed numerical certificates. Actual MR witness contracts,
selected profiles and comparisons with the old history live in the downstream consumer.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Assemble the MR history recursion from entrance and coefficient maps and a real-scale base.
The empty family uses the base; each new profile retains the earlier bound at its entrance.
The arbitrary profile type prevents fixed certificate modules from entering this core. -/
noncomputable def baseHistory {P : Type*} (entry coeff : P → ℝ) (B : ℝ → ℝ) : List P → ℝ → ℝ
  | [], L => B L
  | f :: fs, L =>
    min (baseHistory entry coeff B fs L)
      (max (baseHistory entry coeff B fs (entry f)) (coeff f * L ^ 2))

/-- For any profile list and real scale, the assembled history is below its supplied base.
Follow the left minimum by induction; this retains improvements to the cumulative base. -/
theorem baseHistory_le_base {P : Type*} (entry coeff : P → ℝ) (B : ℝ → ℝ) (fs : List P) (L : ℝ) :
    baseHistory entry coeff B fs L ≤ B L := by
  induction fs with
  | nil => exact le_rfl
  | cons f fs ih => exact (min_le_left _ _).trans ih

/-- A nonnegative base yields nonnegative histories for arbitrary profile maps and scales.
Induct through minima and the retained-history side of each maximum. -/
theorem baseHistory_nonneg {P : Type*} (entry coeff : P → ℝ) (B : ℝ → ℝ) (hB : ∀ L, 0 ≤ B L)
    (fs : List P) (L : ℝ) : 0 ≤ baseHistory entry coeff B fs L := by
  induction fs generalizing L with
  | nil => exact hB L
  | cons f fs ih => exact le_min (ih L) ((ih (entry f)).trans (le_max_left _ _))

/-- Pointwise ordered bases yield ordered histories with identical profile maps and lists.
Induct through the two recursive occurrences; no monotonicity in the scale is required. -/
theorem baseHistory_mono {P : Type*} (entry coeff : P → ℝ) (B D : ℝ → ℝ) (hBD : ∀ L, B L ≤ D L)
    (fs : List P) (L : ℝ) : baseHistory entry coeff B fs L ≤ baseHistory entry coeff D fs L := by
  induction fs generalizing L with
  | nil => exact hBD L
  | cons f fs ih => exact min_le_min (ih L) (max_le_max (ih (entry f)) le_rfl)

end PseudoPrime.PrimeTestBounds.MillerRabin
