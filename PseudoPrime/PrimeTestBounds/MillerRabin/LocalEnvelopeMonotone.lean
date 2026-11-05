/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalFullEnvelope

/-! # Monotonicity of the common local witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The clamped adaptive radius squared is nondecreasing on the real line.
Its radius is positive and nondecreasing after clamping at seven. -/
theorem local_adaptive_square_mono {x y : ℝ} (hxy : x ≤ y) :
    (Analysis.adaptivePart2CutoffRoot (max 7 x)) ^ 2 ≤
      (Analysis.adaptivePart2CutoffRoot (max 7 y)) ^ 2 := by
  have hx : 7 ≤ max 7 x := le_max_left _ _
  have hm := adaptive_local_radius_mono hx (max_le_max_left 7 hxy)
  have ha := adaptive_clamped_radius_ge_seven x
  exact (sq_le_sq₀ (by linarith only [ha]) (by linarith only [ha, hm])).mpr hm

/-- Interpolation is monotone when both endpoints and the weight increase,
the first weight lies in `[0, 1]`, and the second upper endpoint dominates its
lower endpoint. The three nonnegative differences prove the comparison. -/
private theorem interpolation_mono {a b c d u v : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) (huv : u ≤ v)
    (hac : a ≤ c) (hbd : b ≤ d) (hcd : c ≤ d) : (1 - u) * a + u * b ≤ (1 - v) * c + v * d := by
  have h1 := mul_nonneg (sub_nonneg.mpr hu1) (sub_nonneg.mpr hac)
  have h2 := mul_nonneg hu (sub_nonneg.mpr hbd)
  have h3 := mul_nonneg (sub_nonneg.mpr huv) (sub_nonneg.mpr hcd)
  nlinarith only [h1, h2, h3]

/-- The interpolated guard is nondecreasing above 25. Both constituent bounds
and the interpolation weight increase, and the adaptive bound dominates the
quadratic throughout this range. -/
private theorem local_guard_mono_high {s t : ℝ} (hs : 25 ≤ s) (hst : s ≤ t) :
    localInterpolatedGuard s ≤ localInterpolatedGuard t := by
  have hA : (81 / 100 : ℝ) * s ^ 2 ≤ (81 / 100 : ℝ) * t ^ 2 :=
    mul_le_mul_of_nonneg_left
      ((sq_le_sq₀ (by linarith only [hs]) (by linarith only [hs, hst])).mpr hst) (by norm_num only)
  have hB := local_adaptive_square_mono hst
  have hwt : localInterpolationWeight s ≤ localInterpolationWeight t :=
    min_le_min_left _ (max_le_max_left _ (sub_le_sub_right hst _))
  have hw0 : 0 ≤ localInterpolationWeight s := le_min (by norm_num only) (le_max_left _ _)
  have hw1 : localInterpolationWeight s ≤ 1 := min_le_left _ _
  have hcomp : (81 / 100 : ℝ) * t ^ 2 ≤ (Analysis.adaptivePart2CutoffRoot (max 7 t)) ^ 2 := by
    rw [max_eq_right (by linarith only [hs, hst] : 7 ≤ t)]
    exact (LLS.PaperStatements.fullEndpoint_eightyOne_lt_adaptive (by linarith only [hs, hst])).le
  exact max_le_max_left _ (interpolation_mono hw0 hw1 hwt hA hB hcomp)

/-- Through scale 25, the interpolation weight vanishes, so the guard is the
maximum of 61 and the `81/100` quadratic. -/
private theorem local_guard_low {s : ℝ} (hs : s ≤ 25) :
    localInterpolatedGuard s = max 61 ((81 / 100 : ℝ) * s ^ 2) := by
  have ht : localInterpolationWeight s = 0 := by
    dsimp only [localInterpolationWeight]
    rw [max_eq_left (by linarith only [hs] : s - 25 ≤ 0)]
    exact min_eq_right (by norm_num only)
  dsimp only [localInterpolatedGuard]
  rw [ht]
  norm_num only [sub_zero, one_mul, zero_mul, add_zero]

/-- On nonnegative scales through 25, the guard is nondecreasing because its
quadratic term is nondecreasing. -/
private theorem local_guard_mono_low {s t : ℝ} (hs0 : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ 25) :
    localInterpolatedGuard s ≤ localInterpolatedGuard t := by
  rw [local_guard_low (hst.trans ht), local_guard_low ht]
  exact
    max_le_max_left _
      (mul_le_mul_of_nonneg_left ((sq_le_sq₀ hs0 (hs0.trans hst)).mpr hst) (by norm_num only))

/-- The interpolated guard is nondecreasing on nonnegative scales. Join the
quadratic and interpolation ranges at 25. This supports monotone local-factor
substitution in the global coverage. -/
theorem local_guard_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    localInterpolatedGuard s ≤ localInterpolatedGuard t := by
  by_cases hs25 : s ≤ 25
  · by_cases ht25 : t ≤ 25
    · exact local_guard_mono_low hs hst ht25
    · exact
        (local_guard_mono_low hs hs25 le_rfl).trans
          (local_guard_mono_high le_rfl (le_of_not_ge ht25))
  · exact local_guard_mono_high (le_of_not_ge hs25) hst

/-- The common local envelope is nondecreasing on nonnegative scales. Each
of its squared, adaptive, interpolated and even candidates is nondecreasing
on this range, so their minima are also nondecreasing. This supports replacing
actual local logarithms by factor-type scale bounds. -/
theorem localFullEnvelope_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    localFullEnvelope s ≤ localFullEnvelope t := by
  have hsquare : s ^ 2 ≤ t ^ 2 := (sq_le_sq₀ hs (hs.trans hst)).mpr hst
  exact
    min_le_min
      (min_le_min hsquare (min_le_min (local_adaptive_square_mono hst) (local_guard_mono hs hst)))
      (localEvenEnvelope_mono hst)

end PseudoPrime.PrimeTestBounds.MillerRabin
