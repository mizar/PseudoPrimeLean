/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CubicCharacterExclusion

/-! # Cubic radii absorbing the squarefree ramification cost -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For conductor envelope G and square-factor prime logarithm budget E,
define B+sqrt(B²+(8/3)E), B=(10/13)G+35. Its square is the improved witness
bound after absorbing the ramified support into the conductor radius. -/
noncomputable def cubicSquareFactorRadius (G E : ℝ) : ℝ :=
  ((10 / 13 : ℝ) * G + 35) + Real.sqrt ((((10 / 13 : ℝ) * G + 35) ^ 2) + (8 / 3 : ℝ) * E)

/-- For nonnegative G,E, increasing the radius constant from 34 to 35 absorbs
the conductor-linear part of the exclusion cost G+2E. Compare the nonnegative
square roots by their squares. This yields the explicit square-factor radius. -/
theorem cubicExclusionRadius_le_square_factor {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    cubicExclusionRadius G (G + 2 * E) ≤ cubicSquareFactorRadius G E := by
  have ht :
    ((10 / 13 : ℝ) * G + 35) ≤ Real.sqrt ((((10 / 13 : ℝ) * G + 35) ^ 2) + (8 / 3 : ℝ) * E) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hE])
  have hrad :
    0 ≤ (((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 + (4 / 3 : ℝ) * (G + 2 * E) := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 34), hG, hE]
  have hrad' : 0 ≤ (((10 / 13 : ℝ) * G + 35) ^ 2) + (8 / 3 : ℝ) * E := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 35), hE]
  have hs := Real.sq_sqrt hrad
  have hs' := Real.sq_sqrt hrad'
  have hn :=
    Real.sqrt_nonneg
      ((((10 / 13 : ℝ) * G + 34) ^ 2) + (8 / 5 : ℝ) * G + 33 + (4 / 3 : ℝ) * (G + 2 * E))
  dsimp only [cubicExclusionRadius, cubicSquareFactorRadius]
  nlinarith only [hs, hs', hn, ht, hG]

/-- Nonnegative budgets give a radius at least 70 solving r²=2Br+(8/3)E.
Use the square-root identity and sqrt(B²+(8/3)E) at least B. The identity
supports comparisons with arbitrary positive target radii. -/
theorem cubicSquareFactorRadius_data {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    70 ≤ cubicSquareFactorRadius G E ∧
      (cubicSquareFactorRadius G E) ^ 2 =
        2 * ((10 / 13 : ℝ) * G + 35) * cubicSquareFactorRadius G E + (8 / 3 : ℝ) * E := by
  have hr : 0 ≤ (((10 / 13 : ℝ) * G + 35) ^ 2) + (8 / 3 : ℝ) * E := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + 35), hE]
  have hs := Real.sq_sqrt hr
  have ht :
    ((10 / 13 : ℝ) * G + 35) ≤ Real.sqrt ((((10 / 13 : ℝ) * G + 35) ^ 2) + (8 / 3 : ℝ) * E) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hE])
  unfold cubicSquareFactorRadius
  constructor <;> nlinarith only [hs, ht, hG]

/-- A positive target radius T dominates the square-factor radius whenever
T² is at least 2BT+(8/3)E, for nonnegative G,E. Compare the quadratic identities
on the increasing branch. This is a generic interface for subquadratic targets. -/
theorem cubicSquareFactorRadius_le_of_quadratic {G E T : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) (hT : 0 < T)
    (hquad : 2 * ((10 / 13 : ℝ) * G + 35) * T + (8 / 3 : ℝ) * E ≤ T ^ 2) :
    cubicSquareFactorRadius G E ≤ T := by
  have hd := cubicSquareFactorRadius_data hG hE
  have htB : 2 * ((10 / 13 : ℝ) * G + 35) ≤ T := by
    by_contra h
    have hm := mul_pos hT (sub_pos.mpr (lt_of_not_ge h))
    nlinarith only [hquad, hE, hm]
  by_contra hn
  have hlt := lt_of_not_ge hn
  have hm :=
    mul_pos (sub_pos.mpr hlt)
      (show 0 < cubicSquareFactorRadius G E + T - 2 * ((10 / 13 : ℝ) * G + 35) by
        linarith only [hd.1, htB])
  nlinarith only [hd.2, hquad, hm]

/-- For G at least 16 and E nonnegative, the squared cubic square-factor
radius is below the selected reciprocal polynomial envelope. Use its polynomial
root estimate, compare the positive conductor radii, and retain the smaller
coefficient of E. This certifies improvement throughout the old entrance range. -/
theorem cubicSquareFactorRadius_sq_le_selected {G E : ℝ} (hG : 16 ≤ G) (hE : 0 ≤ E) :
    (cubicSquareFactorRadius G E) ^ 2 ≤
      4 * (selectedReciprocalRadius G + 1) ^ 2 + (28 / 5 : ℝ) * E := by
  have hl := Real.log_nonneg (show 1 ≤ G by linarith only [hG])
  have hb : (10 / 13 : ℝ) * G + 35 ≤ selectedReciprocalRadius G + 1 := by
    dsimp only [selectedReciprocalRadius]
    linarith only [hG, hl]
  have hn : 0 ≤ (10 / 13 : ℝ) * G + 35 := by linarith only [hG]
  have hs := pow_le_pow_left₀ hn hb 2
  have hp :=
    root_radius_sq_le_polynomial (show 0 ≤ (8 / 3 : ℝ) * E by nlinarith only [hE]) (B :=
      (10 / 13 : ℝ) * G + 35)
  change (cubicSquareFactorRadius G E) ^ 2 ≤ _ at hp
  nlinarith only [hp, hs, hE]

end PseudoPrime.LLS.PaperStatements
