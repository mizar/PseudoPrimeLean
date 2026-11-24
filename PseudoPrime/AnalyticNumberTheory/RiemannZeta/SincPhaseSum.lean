/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SincPhaseRational
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds

/-! # Rounded upper sum at a phase endpoint -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Sum the 29 contributions after rounding each upward to the common dyadic grid. -/
def sincPhaseUpper (v : ℚ) : ℚ :=
  (∑ i : Fin 29, ⌈(2 ^ 48 : ℚ) * phaseBoxUpper v (lowZero100Lower i)⌉ : ℤ) / (2 ^ 48 : ℚ)

private theorem box_range :
    ∀ i : Fin 29, 0 < lowZero100Lower i ∧ lowZero100Lower i + 1 / 200 ≤ 100 := by decide +kernel

private theorem le_round_up (q : ℚ) : (q : ℝ) ≤ (⌈2 ^ 48 * q⌉ : ℤ) / (2 ^ 48 : ℝ) := by
  apply (le_div_iff₀ (by norm_num only : (0 : ℝ) < 2 ^ 48)).2
  rw [mul_comm]
  have h := (Rat.cast_le (K := ℝ)).mpr (Int.le_ceil ((2 ^ 48 : ℚ) * q))
  simpa only [Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_intCast] using h

/-- Every ordinate tuple in the certified boxes satisfies the computed phase bound for
rational log heights from zero through 27, including all shifted phase endpoints. -/
theorem sincPhaseUpper_sound (v : ℚ) (hv : 0 ≤ v) (hv' : v ≤ 27) (g : Fin 29 → ℝ)
    (hl : LowZero100LowerBounds g) (hu : LowZero100UpperBounds g) :
    zeroHeadPhase g (v : ℝ) ≤ (sincPhaseUpper v : ℝ) := by
  rw [zeroHeadPhase_eq_sum_terms]
  rw [sincPhaseUpper, Rat.cast_div, Rat.cast_intCast, Int.cast_sum, Finset.sum_div]
  simp only [Rat.cast_pow, Rat.cast_ofNat]
  apply Finset.sum_le_sum
  intro i _
  have ha := (box_range i).1
  have hc : 0 ≤ lowZero100Lower i + 1 / 200 := by linarith only [ha]
  have hm := mul_le_mul (box_range i).2 hv' hv (by norm_num only : (0 : ℚ) ≤ 100)
  have hab : |(((lowZero100Lower i + 1 / 200) * v : ℚ) : ℝ)| ≤ 4096 := by
    rw [abs_of_nonneg (Rat.cast_nonneg.mpr (mul_nonneg hc hv))]
    exact_mod_cast (show (lowZero100Lower i + 1 / 200) * v ≤ 4096 by linarith only [hm])
  have h := phaseBoxUpper_sound (Rat.cast_nonneg.mpr hv) (Rat.cast_pos.mpr ha) ⟨hl i, hu i⟩ hab
  exact h.trans (le_round_up _)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
