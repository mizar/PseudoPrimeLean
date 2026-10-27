/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.CubicSquareFactorBounds

/-! # Explicit linear and square-root envelopes for conductor root bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For nonnegative B,D, the squared positive quadratic root is at most
D+4B²+2B sqrt(D). Bound sqrt(B²+D) by B+sqrt(D) and retain the exact
quadratic identity. This preserves the leading coefficient of a growing D. -/
theorem root_radius_sq_le_linear_sqrt {B D : ℝ} (hB : 0 ≤ B) (hD : 0 ≤ D) :
    (B + Real.sqrt (B ^ 2 + D)) ^ 2 ≤ D + 4 * B ^ 2 + 2 * B * Real.sqrt D := by
  have hs := Real.sq_sqrt (add_nonneg (sq_nonneg B) hD)
  have ht := Real.sq_sqrt hD
  have hn := Real.sqrt_nonneg (B ^ 2 + D)
  have hm := Real.sqrt_nonneg D
  have hu : Real.sqrt (B ^ 2 + D) ≤ B + Real.sqrt D := by
    nlinarith only [hs, ht, hn, hm, hB, mul_nonneg hB hm]
  have hp := mul_le_mul_of_nonneg_left hu hB
  nlinarith only [hs, hp]

/-- For G,L real, define (4/3)L+4B²+2B sqrt((4/3)L), B=(10/13)G+35.
Applications use G,L nonnegative and E at most L/2. For fixed G its leading
term is (4/3)L and its remaining growing term is proportional to sqrt L. -/
noncomputable def cubicSquareFactorLinearEnvelope (G L : ℝ) : ℝ :=
  (4 / 3 : ℝ) * L + 4 * ((10 / 13 : ℝ) * G + 35) ^ 2 +
    2 * ((10 / 13 : ℝ) * G + 35) * Real.sqrt ((4 / 3 : ℝ) * L)

/-- For nonnegative G,E with E at most L/2, the squared cubic square-factor
radius is at most the explicit linear and square-root envelope. Preserve the
linear coefficient of E, then use square-root monotonicity. This removes the
factorization-dependent cost from a coarse envelope for fixed G. -/
theorem cubicSquareFactorRadius_sq_le_linear_envelope {G E L : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E)
    (hEL : E ≤ L / 2) :
    (cubicSquareFactorRadius G E) ^ 2 ≤ cubicSquareFactorLinearEnvelope G L := by
  have hB : 0 ≤ (10 / 13 : ℝ) * G + 35 := by linarith only [hG]
  have hD : 0 ≤ (8 / 3 : ℝ) * E := mul_nonneg (by norm_num only) hE
  have hDL : (8 / 3 : ℝ) * E ≤ (4 / 3 : ℝ) * L := by linarith only [hEL]
  have hp := root_radius_sq_le_linear_sqrt hB hD
  have hs := Real.sqrt_le_sqrt hDL
  have hm :=
    mul_le_mul_of_nonneg_left hs (show 0 ≤ 2 * ((10 / 13 : ℝ) * G + 35) by linarith only [hB])
  change (cubicSquareFactorRadius G E) ^ 2 ≤ _ at hp
  dsimp only [cubicSquareFactorLinearEnvelope]
  nlinarith only [hp, hDL, hm]

/-- For nonnegative G,L the linear envelope is at least 4900. Use the zero-cost
cubic radius, which is at least 70, and the proved envelope comparison.
This absorbs small exceptional Selfridge candidates into the same bound. -/
theorem cubicSquareFactorLinearEnvelope_ge {G L : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L) :
    4900 ≤ cubicSquareFactorLinearEnvelope G L := by
  have hc :=
    cubicSquareFactorRadius_sq_le_linear_envelope (E := 0) hG le_rfl
      (show (0 : ℝ) ≤ L / 2 by linarith only [hL])
  have hr := (cubicSquareFactorRadius_data (E := 0) hG (le_refl 0)).1
  nlinarith only [hc, hr]

/-- For nonnegative G,L and delta positive, the two explicit cutoff inequalities
8B²≤delta L and 64B²≤delta² L imply that the linear envelope is at most
(4/3+delta)L. Bound sqrt((4/3)L) by 2sqrt L and absorb the remaining terms.
This makes the fixed-G leading coefficient 4/3 quantitatively effective. -/
theorem cubicSquareFactorLinearEnvelope_le_coefficient {G L δ : ℝ} (hG : 0 ≤ G) (hL : 0 ≤ L)
    (hδ : 0 < δ) (hc₁ : 8 * ((10 / 13 : ℝ) * G + 35) ^ 2 ≤ δ * L)
    (hc₂ : 64 * ((10 / 13 : ℝ) * G + 35) ^ 2 ≤ δ ^ 2 * L) :
    cubicSquareFactorLinearEnvelope G L ≤ (4 / 3 + δ) * L := by
  have hB : 0 ≤ (10 / 13 : ℝ) * G + 35 := by linarith only [hG]
  have hsL := Real.sq_sqrt hL
  have hsD := Real.sq_sqrt (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 3) hL)
  have ht : Real.sqrt ((4 / 3 : ℝ) * L) ≤ 2 * Real.sqrt L := by
    nlinarith only [hsL, hsD, Real.sqrt_nonneg L, Real.sqrt_nonneg ((4 / 3 : ℝ) * L)]
  have htB : 8 * ((10 / 13 : ℝ) * G + 35) ≤ δ * Real.sqrt L := by
    apply
      (sq_le_sq₀ (show 0 ≤ 8 * ((10 / 13 : ℝ) * G + 35) by linarith only [hB])
          (mul_nonneg hδ.le (Real.sqrt_nonneg L))).mp
    simp only [mul_pow, Real.sq_sqrt hL]
    nlinarith only [hc₂]
  have hm := mul_le_mul_of_nonneg_right htB (Real.sqrt_nonneg L)
  simp only [mul_assoc, ← pow_two, Real.sq_sqrt hL] at hm
  have hu :=
    mul_le_mul_of_nonneg_left ht (show 0 ≤ 2 * ((10 / 13 : ℝ) * G + 35) by linarith only [hB])
  dsimp only [cubicSquareFactorLinearEnvelope]
  nlinarith only [hc₁, hm, hu]

/-- For G at least 16 and L nonnegative, the new linear envelope is below the
previous selected reciprocal linear envelope. Bound the square-root cross term
by B²+(4/3)L and compare the nonnegative conductor radii. This certifies the
improvement over the complete entrance range of the old estimate. -/
theorem cubicSquareFactorLinearEnvelope_le_selected {G L : ℝ} (hG : 16 ≤ G) (hL : 0 ≤ L) :
    cubicSquareFactorLinearEnvelope G L ≤
      4 * (selectedReciprocalRadius G + 1) ^ 2 + (14 / 5 : ℝ) * L := by
  have hl := Real.log_nonneg (show 1 ≤ G by linarith only [hG])
  have hB : 0 ≤ (10 / 13 : ℝ) * G + 35 := by linarith only [hG]
  have hOld : (3 / 2 : ℝ) * ((10 / 13 : ℝ) * G + 35) ≤ selectedReciprocalRadius G + 1 := by
    dsimp only [selectedReciprocalRadius]
    linarith only [hG, hl]
  have hsq :=
    pow_le_pow_left₀ (show 0 ≤ (3 / 2 : ℝ) * ((10 / 13 : ℝ) * G + 35) by linarith only [hB]) hOld 2
  have hs := Real.sq_sqrt (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 4 / 3) hL)
  have hu := sq_nonneg (((10 / 13 : ℝ) * G + 35) - Real.sqrt ((4 / 3 : ℝ) * L))
  dsimp only [cubicSquareFactorLinearEnvelope]
  nlinarith only [hsq, hs, hu, hL, sq_nonneg ((10 / 13 : ℝ) * G + 35)]

end PseudoPrime.LLS.PaperStatements
