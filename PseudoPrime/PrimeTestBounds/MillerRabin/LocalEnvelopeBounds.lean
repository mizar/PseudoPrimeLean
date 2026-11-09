/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEnvelopeMonotone

/-! # Explicit local envelope bounds -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The local envelope is bounded by the plain squared logarithmic scale, one of its
defining candidates. This comparison is valid for every real scale. -/
theorem local_full_le_sq (s : ℝ) : localFullEnvelope s ≤ s ^ 2 := by
  exact (min_le_left _ _).trans (min_le_left _ _)

/-- The local envelope is bounded by its interpolated moderate-scale guard. This follows
directly from the nested minima defining the common local envelope. -/
theorem local_full_le_guard (s : ℝ) : localFullEnvelope s ≤ localInterpolatedGuard s := by
  exact (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- At scales at most 25, the local envelope is at most the minimum of the plain square
and the maximum of 61 and the `81/100` quadratic. The interpolation weight vanishes on
this range, exposing both explicit candidates used by the finite semiprime cells. -/
theorem local_full_le_low {s : ℝ} (hs : s ≤ 25) :
    localFullEnvelope s ≤ min (s ^ 2) (max 61 ((81 / 100 : ℝ) * s ^ 2)) := by
  have hw : localInterpolationWeight s = 0 := by
    dsimp only [localInterpolationWeight]
    rw [max_eq_left (by linarith only [hs] : s - 25 ≤ 0)]
    exact min_eq_right (by norm_num only)
  have hg : localInterpolatedGuard s = max 61 ((81 / 100 : ℝ) * s ^ 2) := by
    dsimp only [localInterpolatedGuard]
    rw [hw]
    norm_num only [sub_zero, one_mul, zero_mul, add_zero]
  exact le_min (local_full_le_sq s) (hg ▸ local_full_le_guard s)

/-- At scales at least 25, the local envelope is bounded by the finer logarithmic radius
squared. The adaptive radius is nonnegative and no larger than the finer radius, so their
squares preserve this comparison. This bound supports rational high-scale cell checks. -/
theorem local_full_le_finer {s : ℝ} (hs : 25 ≤ s) :
    localFullEnvelope s ≤ (Analysis.finerPart2CutoffRoot s) ^ 2 := by
  have hfr := Analysis.finerPart2Root_ge_36_5_of_639_100_le (L := s) (by linarith only [hs])
  have hr := Analysis.adaptivePart2Root_bounds (L := s) (by linarith only [hfr])
  have had : (0 : ℝ) ≤ Analysis.adaptivePart2CutoffRoot s := by
    have h := adaptive_clamped_radius_ge_seven s
    rw [max_eq_right (by linarith only [hs] : (7 : ℝ) ≤ s)] at h
    linarith only [h]
  have hsq :=
    (sq_le_sq₀ had (by linarith only [hfr] : (0 : ℝ) ≤ Analysis.finerPart2CutoffRoot s)).mpr hr.2.le
  have hfull : localFullEnvelope s ≤ (Analysis.adaptivePart2CutoffRoot (max 7 s)) ^ 2 :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  rw [max_eq_right (by linarith only [hs] : (7 : ℝ) ≤ s)] at hfull
  exact hfull.trans hsq

end PseudoPrime.PrimeTestBounds.MillerRabin
