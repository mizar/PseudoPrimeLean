/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianUniformScalarWitness

/-! # Explicit Gaussian parameters for logarithmic scale at least 1000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Gaussian radius `377L/1000` at logarithmic scale `L`.
Its square sets the smoothing scale and its cutoff remains below `3L²/10`. -/
noncomputable def gaussian030Radius (L : ℝ) : ℝ :=
  (377 / 1000 : ℝ) * L

/-- The positive Gaussian smoothing scale is the square of the chosen radius.
It is used as the scale argument in the certified principal deficit. -/
noncomputable def gaussian030Scale (L : ℝ) : ℝ :=
  gaussian030Radius L ^ 2

/-- The relative Chebyshev width `7/(20 sqrt(r))` at the chosen radius.
For logarithmic scale at least 1000 it lies in the certified narrow-width range. -/
noncomputable def gaussian030Width (L : ℝ) : ℝ :=
  7 / (20 * Real.sqrt (gaussian030Radius L))

/-- At logarithmic scale at least 1000, the explicit Gaussian scale and width
satisfy the analytic entrance conditions. The associated cutoff is at least
50000 and at most `3L²/10`, so its rejecting prime meets the target radius. -/
theorem gaussian030_parameters {L : ℝ} (hL : 1000 ≤ L) :
    1 ≤ gaussian030Scale L ∧
      0 < gaussian030Width L ∧
      gaussian030Width L ≤ 1 / 32 ∧
      50000 ≤ (21 / 10 : ℝ) * gaussian030Scale L ∧
      (21 / 10 : ℝ) * gaussian030Scale L ≤ (3 / 10 : ℝ) * L ^ 2 := by
  have hr : 377 ≤ gaussian030Radius L := by
    dsimp only [gaussian030Radius]
    linarith only [hL]
  have hr0 : 0 < gaussian030Radius L := by linarith only [hr]
  have ht : (19 : ℝ) ≤ Real.sqrt (gaussian030Radius L) := by
    apply (Real.le_sqrt (by norm_num only) hr0.le).2
    nlinarith only [hr]
  have hs : (Real.sqrt (gaussian030Radius L)) ^ 2 = gaussian030Radius L := Real.sq_sqrt hr0.le
  have hx : (377 : ℝ) ^ 2 ≤ gaussian030Scale L := by
    dsimp only [gaussian030Scale]
    nlinarith only [hr]
  have hw : 0 < gaussian030Width L := by
    dsimp only [gaussian030Width]
    exact div_pos (by norm_num only) (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hr0))
  have hw1 : gaussian030Width L ≤ 1 / 32 := by
    dsimp only [gaussian030Width]
    apply (div_le_iff₀ (mul_pos (by norm_num only) (Real.sqrt_pos.mpr hr0))).2
    nlinarith only [ht]
  refine ⟨?_, hw, hw1, ?_, ?_⟩
  · nlinarith only [hx]
  · nlinarith only [hx]
  · dsimp only [gaussian030Scale, gaussian030Radius]
    nlinarith only [sq_nonneg L]

end PseudoPrime.PrimeTestBounds.MillerRabin
