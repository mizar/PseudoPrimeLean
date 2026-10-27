/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TightCubicConductorBounds

/-! # Parameterized cubic square-factor absorption -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The square-factor radius with free additive constant c is
B+sqrt(B²+(8/3)E), B=(10/13)G+c. Inputs are conductor and exclusion
budgets; the square is the witness upper bound after absorption. -/
noncomputable def cubicSquareFactorRadiusWithConstant (c G E : ℝ) : ℝ :=
  ((10 / 13 : ℝ) * G + c) + Real.sqrt ((((10 / 13 : ℝ) * G + c) ^ 2) + (8 / 3 : ℝ) * E)

/-- For nonnegative E, the parameterized radius is at least 2B and solves
r²=2Br+(8/3)E. No sign condition on B is needed. These exact algebraic
facts support absorption for an arbitrary admissible additive constant. -/
theorem cubicSquareFactorRadiusWithConstant_data {c G E : ℝ} (hE : 0 ≤ E) :
    2 * ((10 / 13 : ℝ) * G + c) ≤ cubicSquareFactorRadiusWithConstant c G E ∧
      (cubicSquareFactorRadiusWithConstant c G E) ^ 2 =
        2 * ((10 / 13 : ℝ) * G + c) * cubicSquareFactorRadiusWithConstant c G E +
          (8 / 3 : ℝ) * E := by
  have hr : 0 ≤ (((10 / 13 : ℝ) * G + c) ^ 2) + (8 / 3 : ℝ) * E := by
    nlinarith only [sq_nonneg ((10 / 13 : ℝ) * G + c), hE]
  have hs := Real.sq_sqrt hr
  have ht : ((10 / 13 : ℝ) * G + c) ≤ Real.sqrt ((((10 / 13 : ℝ) * G + c) ^ 2) + (8 / 3 : ℝ) * E) :=
    Real.le_sqrt_of_sq_le (by nlinarith only [hE])
  dsimp only [cubicSquareFactorRadiusWithConstant]
  constructor <;> nlinarith only [hs, ht]

/-- For G,E≥0, a constant c≥63/2 absorbs the conductor cost if
44/15≤4(c-63/2)(10/13) and 28≤4(c-63/2)c. Use the parameterized quadratic
identity and compare nonnegative square roots. This generic theorem avoids
repeating the argument for each rational constant. -/
theorem tightCubicExclusionRadius_le_square_factor_with_constant {c G E : ℝ} (hG : 0 ≤ G)
    (hE : 0 ≤ E) (hc : 63 / 2 ≤ c) (hcoeff : 44 / 15 ≤ 4 * (c - 63 / 2) * (10 / 13 : ℝ))
    (hconst : 28 ≤ 4 * (c - 63 / 2) * c) :
    tightCubicExclusionRadius G (G + 2 * E) ≤ cubicSquareFactorRadiusWithConstant c G E := by
  let r := cubicSquareFactorRadiusWithConstant c G E
  have hd := cubicSquareFactorRadiusWithConstant_data (c := c) (G := G) hE
  have hh := mul_le_mul_of_nonneg_left hd.1 (show (0 : ℝ) ≤ 2 * (c - 63 / 2) by linarith only [hc])
  have hbudget : (44 / 15 : ℝ) * G + 28 ≤ 4 * (c - 63 / 2) * ((10 / 13 : ℝ) * G + c) := by
    have h := add_le_add (mul_le_mul_of_nonneg_right hcoeff hG) hconst
    convert h using 1
    ring
  have habsorb : (44 / 15 : ℝ) * G + 28 ≤ 2 * (c - 63 / 2) * r := by
    apply hbudget.trans
    convert hh using 1
    ring
  have hdiff : 0 ≤ r - ((10 / 13 : ℝ) * G + 63 / 2) := by
    dsimp only [r]
    linarith only [hd.1, hG, hc]
  have hquad :
    (((10 / 13 : ℝ) * G + 63 / 2) ^ 2) + (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * (G + 2 * E) ≤
      (r - ((10 / 13 : ℝ) * G + 63 / 2)) ^ 2 := by
    have hid : r ^ 2 = 2 * ((10 / 13 : ℝ) * G + c) * r + (8 / 3 : ℝ) * E := hd.2
    nlinarith only [hid, habsorb]
  have hs := (Real.sqrt_le_left hdiff).mpr hquad
  dsimp only [tightCubicExclusionRadius]
  linarith only [hs]

/-- The square-factor radius with additive constant 2434/75. It is an
instance of the parameterized radius, used for negative Jacobi and Selfridge
bounds after absorbing the ramified conductor contribution. -/
noncomputable def cubicSquareFactorRadius2434 (G E : ℝ) : ℝ :=
  cubicSquareFactorRadiusWithConstant (2434 / 75) G E

/-- For G,E≥0 the constant 2434/75 absorbs the conductor cost G+2E.
Instantiate the generic absorption theorem with exact rational inequalities.
This improves the former square-factor additive constant 65/2. -/
theorem tightCubicExclusionRadius_le_square_factor2434 {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    tightCubicExclusionRadius G (G + 2 * E) ≤ cubicSquareFactorRadius2434 G E := by
  exact
    tightCubicExclusionRadius_le_square_factor_with_constant hG hE (by norm_num only)
      (by norm_num only) (by norm_num only)

/-- For G,E≥0 the 2434/75 radius is at least 4868/75 and obeys its
quadratic identity. Transfer the parameterized data and discard the
nonnegative conductor term; this also controls small Selfridge exceptions. -/
theorem cubicSquareFactorRadius2434_data {G E : ℝ} (hG : 0 ≤ G) (hE : 0 ≤ E) :
    4868 / 75 ≤ cubicSquareFactorRadius2434 G E ∧
      (cubicSquareFactorRadius2434 G E) ^ 2 =
        2 * ((10 / 13 : ℝ) * G + 2434 / 75) * cubicSquareFactorRadius2434 G E +
          (8 / 3 : ℝ) * E := by
  have hd := cubicSquareFactorRadiusWithConstant_data (c := 2434 / 75) (G := G) hE
  dsimp only [cubicSquareFactorRadius2434]
  exact ⟨by linarith only [hd.1, hG], hd.2⟩

/-- For G≥0 and any E, the 2434/75 radius is strictly smaller than the
65/2 radius. Compare the positive affine terms and their squared radicands.
Thus the improvement holds throughout the former nonnegative budget range. -/
theorem cubicSquareFactorRadius2434_lt_tight {G E : ℝ} (hG : 0 ≤ G) :
    cubicSquareFactorRadius2434 G E < tightCubicSquareFactorRadius G E := by
  have hB : 0 ≤ (10 / 13 : ℝ) * G + 2434 / 75 := by linarith only [hG]
  have hBB : (10 / 13 : ℝ) * G + 2434 / 75 < (10 / 13 : ℝ) * G + 65 / 2 := by linarith only
  have hs := Real.sqrt_le_sqrt (add_le_add_right (pow_le_pow_left₀ hB hBB.le 2) ((8 / 3 : ℝ) * E))
  exact add_lt_add_of_lt_of_le hBB (by simpa only [add_comm] using hs)

end PseudoPrime.LLS.PaperStatements
