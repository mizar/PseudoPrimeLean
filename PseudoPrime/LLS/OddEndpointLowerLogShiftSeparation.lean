/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.OddEndpointLogShiftSeparation

/-! # Coupled logarithm certificates below the radius one hundred twenty -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For nonnegative t,u, the shifted polynomial is positive by its positive
coefficients. Explicit monomial nonnegativity proves the continuous certificate.
This is used with t=y-94 and u=z-4543/1000-(y-94)/120. -/
theorem oddEndpoint_lower_shifted_0_pos {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 <
      1373250000 * (t) ^ 5 + 164790000000 * (t) ^ 4 * (u) ^ 1 + 506125736425 * (t) ^ 4 +
        62072816451000 * (t) ^ 3 * (u) ^ 1 +
        69776577486818 * (t) ^ 3 +
        659160000000 * (t) ^ 2 * (u) ^ 2 +
        8773716430731000 * (t) ^ 2 * (u) ^ 1 +
        4265138861778093 * (t) ^ 2 +
        122933340000000 * (t) ^ 1 * (u) ^ 2 +
        551511228761820000 * (t) ^ 1 * (u) ^ 1 +
        97623413192187000 * (t) ^ 1 +
        5731725780000000 * (u) ^ 2 +
        13008226214743848000 * (u) ^ 1 +
        7773035786234244 := by
  have h0 : 0 ≤ t ^ 5 * u ^ 0 := mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 0)
  have h1 : 0 ≤ t ^ 4 * u ^ 1 := mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 1)
  have h2 : 0 ≤ t ^ 4 * u ^ 0 := mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 0)
  have h3 : 0 ≤ t ^ 3 * u ^ 1 := mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 1)
  have h4 : 0 ≤ t ^ 3 * u ^ 0 := mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 0)
  have h5 : 0 ≤ t ^ 2 * u ^ 2 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 2)
  have h6 : 0 ≤ t ^ 2 * u ^ 1 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 1)
  have h7 : 0 ≤ t ^ 2 * u ^ 0 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 0)
  have h8 : 0 ≤ t ^ 1 * u ^ 2 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 2)
  have h9 : 0 ≤ t ^ 1 * u ^ 1 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 1)
  have h10 : 0 ≤ t ^ 1 * u ^ 0 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 0)
  have h11 : 0 ≤ t ^ 0 * u ^ 2 := mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 2)
  have h12 : 0 ≤ t ^ 0 * u ^ 1 := mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 1)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- For y>=94, the coupled logarithm lower bound and the tangent coupling
imply positivity of the rational branch polynomial. A ring identity splits the
numerator into a positive shifted polynomial and nonnegative coupling slack. -/
theorem oddEndpoint_lower_branch_0_polynomial_pos {L y z : ℝ} (hy : 94 ≤ y)
    (hz : 4543 / 1000 + (y - 94) / 120 ≤ z) (hlink : (y - 1) * L ≤ (y - 1) * y + y * (z - 11 / 4)) :
    0 < oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) := by
  have hz0 : 0 ≤ z := by linarith only [hy, hz]
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy1]
  have hc : 0 ≤ (y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1)) :=
    add_nonneg (mul_nonneg (sq_nonneg _) hz0)
      (mul_nonneg (by linarith only [hy, hz0]) (mul_nonneg (by norm_num only) hs))
  have hm := mul_nonneg hc (sub_nonneg.mpr hlink)
  have hp :=
    oddEndpoint_lower_shifted_0_pos (by linarith only [hy] : 0 ≤ y - 94)
      (by linarith only [hz] : 0 ≤ z - 4543 / 1000 - (y - 94) / 120)
  have he :
    164790000000 * (y - 1) *
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) =
      (1373250000 * (y - 94) ^ 5 +
          164790000000 * (y - 94) ^ 4 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          506125736425 * (y - 94) ^ 4 +
          62072816451000 * (y - 94) ^ 3 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          69776577486818 * (y - 94) ^ 3 +
          659160000000 * (y - 94) ^ 2 * (z - 4543 / 1000 - (y - 94) / 120) ^ 2 +
          8773716430731000 * (y - 94) ^ 2 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          4265138861778093 * (y - 94) ^ 2 +
          122933340000000 * (y - 94) ^ 1 * (z - 4543 / 1000 - (y - 94) / 120) ^ 2 +
          551511228761820000 * (y - 94) ^ 1 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          97623413192187000 * (y - 94) ^ 1 +
          5731725780000000 * (z - 4543 / 1000 - (y - 94) / 120) ^ 2 +
          13008226214743848000 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          7773035786234244) +
        164790000000 * ((y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1))) *
          ((y - 1) * y + y * (z - 11 / 4) - (y - 1) * L) := by
    unfold oddEndpointTwoCostPolynomial fullEndpointPolynomial
    ring
  have hpos :
    0 <
      164790000000 * (y - 1) *
        oddEndpointTwoCostPolynomial (L + 7 / 5) (2096 / 1831) y z (7 / 10) (2 * z ^ 2) := by
    nlinarith only [he, hp, hm]
  exact (mul_pos_iff_of_pos_left (by linarith only [hy] : 0 < (164790000000 : ℝ) * (y - 1))).mp hpos

/-- For nonnegative t,u, the shifted polynomial is positive by its positive
coefficients. Explicit monomial nonnegativity proves the continuous certificate.
This is used with t=y-94 and u=z-4543/1000-(y-94)/120. -/
theorem oddEndpoint_lower_shifted_1_pos {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    0 <
      1373250000 * (t) ^ 5 + 164790000000 * (t) ^ 4 * (u) ^ 1 + 661211436425 * (t) ^ 4 +
        62226620451000 * (t) ^ 3 * (u) ^ 1 +
        128665770758818 * (t) ^ 3 +
        659160000000 * (t) ^ 2 * (u) ^ 2 +
        8816935354731000 * (t) ^ 2 * (u) ^ 1 +
        12648903208960093 * (t) ^ 2 +
        122933340000000 * (t) ^ 1 * (u) ^ 2 +
        555559119335820000 * (t) ^ 1 * (u) ^ 1 +
        627982313948319000 * (t) ^ 1 +
        5731725780000000 * (u) ^ 2 +
        13134592888477848000 * (u) ^ 1 +
        12586690839289796244 := by
  have h0 : 0 ≤ t ^ 5 * u ^ 0 := mul_nonneg (pow_nonneg ht 5) (pow_nonneg hu 0)
  have h1 : 0 ≤ t ^ 4 * u ^ 1 := mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 1)
  have h2 : 0 ≤ t ^ 4 * u ^ 0 := mul_nonneg (pow_nonneg ht 4) (pow_nonneg hu 0)
  have h3 : 0 ≤ t ^ 3 * u ^ 1 := mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 1)
  have h4 : 0 ≤ t ^ 3 * u ^ 0 := mul_nonneg (pow_nonneg ht 3) (pow_nonneg hu 0)
  have h5 : 0 ≤ t ^ 2 * u ^ 2 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 2)
  have h6 : 0 ≤ t ^ 2 * u ^ 1 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 1)
  have h7 : 0 ≤ t ^ 2 * u ^ 0 := mul_nonneg (pow_nonneg ht 2) (pow_nonneg hu 0)
  have h8 : 0 ≤ t ^ 1 * u ^ 2 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 2)
  have h9 : 0 ≤ t ^ 1 * u ^ 1 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 1)
  have h10 : 0 ≤ t ^ 1 * u ^ 0 := mul_nonneg (pow_nonneg ht 1) (pow_nonneg hu 0)
  have h11 : 0 ≤ t ^ 0 * u ^ 2 := mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 2)
  have h12 : 0 ≤ t ^ 0 * u ^ 1 := mul_nonneg (pow_nonneg ht 0) (pow_nonneg hu 1)
  nlinarith only [h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12]

/-- For y>=94, the coupled logarithm lower bound and the tangent coupling
imply positivity of the rational branch polynomial. A ring identity splits the
numerator into a positive shifted polynomial and nonnegative coupling slack. -/
theorem oddEndpoint_lower_branch_1_polynomial_pos {L y z : ℝ} (hy : 94 ≤ y)
    (hz : 4543 / 1000 + (y - 94) / 120 ≤ z) (hlink : (y - 1) * L ≤ (y - 1) * y + y * (z - 11 / 4)) :
    0 < oddEndpointTwoCostPolynomial (L) (2096 / 1831) y z (14 / 15) (2 * z ^ 2 + 7 / 5 * z) := by
  have hz0 : 0 ≤ z := by linarith only [hy, hz]
  have hy1 : 1 ≤ y := by linarith only [hy]
  have hs : 0 ≤ y ^ 2 - 1 := by nlinarith only [hy1]
  have hc : 0 ≤ (y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1)) :=
    add_nonneg (mul_nonneg (sq_nonneg _) hz0)
      (mul_nonneg (by linarith only [hy, hz0]) (mul_nonneg (by norm_num only) hs))
  have hm := mul_nonneg hc (sub_nonneg.mpr hlink)
  have hp :=
    oddEndpoint_lower_shifted_1_pos (by linarith only [hy] : 0 ≤ y - 94)
      (by linarith only [hz] : 0 ≤ z - 4543 / 1000 - (y - 94) / 120)
  have he :
    164790000000 * (y - 1) *
        oddEndpointTwoCostPolynomial (L) (2096 / 1831) y z (14 / 15) (2 * z ^ 2 + 7 / 5 * z) =
      (1373250000 * (y - 94) ^ 5 +
          164790000000 * (y - 94) ^ 4 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          661211436425 * (y - 94) ^ 4 +
          62226620451000 * (y - 94) ^ 3 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          128665770758818 * (y - 94) ^ 3 +
          659160000000 * (y - 94) ^ 2 * (z - 4543 / 1000 - (y - 94) / 120) ^ 2 +
          8816935354731000 * (y - 94) ^ 2 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          12648903208960093 * (y - 94) ^ 2 +
          122933340000000 * (y - 94) ^ 1 * (z - 4543 / 1000 - (y - 94) / 120) ^ 2 +
          555559119335820000 * (y - 94) ^ 1 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          627982313948319000 * (y - 94) ^ 1 +
          5731725780000000 * (z - 4543 / 1000 - (y - 94) / 120) ^ 2 +
          13134592888477848000 * (z - 4543 / 1000 - (y - 94) / 120) ^ 1 +
          12586690839289796244) +
        164790000000 * ((y - 1) ^ 2 * z + (2 * y + 2 * z + 2) * ((1 / 2 : ℝ) * (y ^ 2 - 1))) *
          ((y - 1) * y + y * (z - 11 / 4) - (y - 1) * L) := by
    unfold oddEndpointTwoCostPolynomial fullEndpointPolynomial
    ring
  have hpos :
    0 <
      164790000000 * (y - 1) *
        oddEndpointTwoCostPolynomial (L) (2096 / 1831) y z (14 / 15) (2 * z ^ 2 + 7 / 5 * z) := by
    nlinarith only [he, hp, hm]
  exact (mul_pos_iff_of_pos_left (by linarith only [hy] : 0 < (164790000000 : ℝ) * (y - 1))).mp hpos

end PseudoPrime.LLS.PaperStatements
