/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028FiniteCell

/-! # Monotonicity of the finite-cutoff principal weight -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The first finite cutoff has logarithm below `57/10`. The rational
logarithm checker supplies the strict margin needed for the weight derivative. -/
theorem target028_log252_upper : Real.log 252 ≤ (57 / 10 : ℝ) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 252 8 32 5 (57 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  exact h

/-- On the range used by the first finite cutoff, the principal weight is
nonincreasing. Its logarithmic coordinate stays between zero and nine, making
the explicit derivative nonpositive. This enables interval-wise lower bounds
for the finite principal sum. -/
theorem target028_weight_antitone_first : AntitoneOn refinedWeight (Set.Icc (1 / 252 : ℝ) 1) := by
  apply
    antitoneOn_of_hasDerivWithinAt_nonpos (convex_Icc (1 / 252 : ℝ) 1)
      (fun u hu ↦
        (refinedWeight_hasDerivAt (by linarith only [hu.1])).continuousAt.continuousWithinAt)
      (fun u hu ↦
        (refinedWeight_hasDerivAt
            (by
              have h := interior_subset hu; linarith only [h.1])).hasDerivWithinAt)
  intro u hu
  have hm : u ∈ Set.Icc (1 / 252 : ℝ) 1 := interior_subset hu
  have hu0 : 0 < u := by linarith only [hm.1]
  have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 1 / 252) hm.1
  have hu1 := Real.log_nonpos hu0.le hm.2
  have hlog : -(57 / 10 : ℝ) ≤ Real.log u := by
    rw [show (1 / 252 : ℝ) = (252 : ℝ)⁻¹ by norm_num only, Real.log_inv] at hl
    linarith only [hl, target028_log252_upper]
  have hc0 : 0 ≤ refinedCoord u := by
    dsimp only [refinedCoord]
    linarith only [hu1]
  have hc9 : refinedCoord u ≤ 9 := by
    dsimp only [refinedCoord]
    linarith only [hlog]
  have hpoly : (29 / 50 : ℝ) * refinedCoord u ^ 5 - (27 / 5 : ℝ) * refinedCoord u ^ 4 ≤ 0 := by
    have h :=
      mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hc0 4)
        (show (29 / 50 : ℝ) * refinedCoord u - 27 / 5 ≤ 0 by linarith only [hc9])
    nlinarith only [h]
  dsimp only [refinedWeightDeriv]
  exact
    mul_nonpos_of_nonneg_of_nonpos
      (div_nonneg (Real.exp_pos _).le
        (mul_nonneg (mul_nonneg (by norm_num only) hu0.le) (Real.sqrt_nonneg _)))
      hpoly

end PseudoPrime.PrimeTestBounds.MillerRabin
