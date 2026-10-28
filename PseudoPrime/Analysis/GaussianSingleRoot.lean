/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianMR1000Numerics

/-! # Single-root Gaussian budgets with the sharp 1000 prefix -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The single large-index root with floor ten; no index-four root is used. -/
noncomputable def gaussianSingleRoot (L : ℝ) : ℝ :=
  max 10 (gaussian1000LargeRoot L)

/-- The radius is the square of the floored single root. Its square is the Mellin scale. -/
noncomputable def gaussianSingleRadius (L : ℝ) : ℝ :=
  gaussianSingleRoot L ^ 2

/-- The new prime-witness cutoff is six fifths of the squared single-root radius. -/
noncomputable def gaussianSingleBound (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * gaussianSingleRadius L ^ 2

/-- The combined root is at least ten for every L, by its maximum floor.
This is the anchor for the paired inverse-power residual bound. -/
theorem gaussianSingle_root_ten (L : ℝ) : (10 : ℝ) ≤ gaussianSingleRoot L :=
  le_max_left _ _

/-- The combined root is positive for every L because it is at least ten.
This supplies positive denominators and a positive Mellin scale. -/
theorem gaussianSingle_root_pos (L : ℝ) : 0 < gaussianSingleRoot L := by
  linarith only [gaussianSingle_root_ten L]

/-- The combined radius is at least one hundred. Square the nonnegative
root floor to establish the smaller tail domain independently of L. -/
theorem gaussianSingle_radius_hundred (L : ℝ) : (100 : ℝ) ≤ gaussianSingleRadius L := by
  have hs := gaussianSingle_root_ten L
  dsimp only [gaussianSingleRadius]
  nlinarith only [hs, sq_nonneg (gaussianSingleRoot L - 10)]

/-- The cutoff is at least 12000 for every L. Square the radius floor and
rescale by six fifths, ensuring coverage of the certified 1000 prefix. -/
theorem gaussianSingle_cutoff_floor (L : ℝ) : (12000 : ℝ) ≤ gaussianSingleBound L := by
  have hr := gaussianSingle_radius_hundred L
  dsimp only [gaussianSingleBound]
  nlinarith only [hr, sq_nonneg (gaussianSingleRadius L - 100)]

/-- For L>=0, the combined radius satisfies the large-index budget
inequality. Compare the maximum with the raw root and use ten*d>beta.
No equality is asserted for the combined root. -/
theorem gaussianSingle_large_budget {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * gaussianSingleRoot L + 163 / 20 ≤
      gaussianMRRefinedD * gaussianSingleRadius L := by
  have hc : 0 ≤ gaussianMRRefinedConductor := by norm_num only [gaussianMRRefinedConductor]
  have hcoef : gaussianMRRefinedBeta < gaussianMRRefinedD * gaussianSingleRoot L := by
    have hs :=
      mul_le_mul_of_nonneg_left (gaussianSingle_root_ten L) gaussianMRRefined_coefficients.1.le
    have hb : gaussianMRRefinedBeta < 10 * gaussianMRRefinedD := by
      norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    linarith only [hs, hb]
  have he :=
    gaussianBudget_of_root_le gaussianMRRefined_coefficients.1 gaussianMRRefined_coefficients.2
      (add_nonneg (mul_nonneg hc hL) (by norm_num only : (0 : ℝ) ≤ 163 / 20)) hcoef
      (le_max_right _ _)
  change _ ≤ gaussianMRRefinedD * gaussianSingleRadius L at he
  linarith only [he]

/-- For L>=0 and log q<=L, paired inverse-power checks and a strict rational
anchor imply a strict normalized Gaussian error cap. Retain the signed pole terms
and use the radius-100 tail estimates. This serves both index branches. -/
theorem gaussianSingle_error_cap {L eta eps D s : ℝ} {q : ℕ} (hs0 : 10 ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + 163 / 20 ≤
        gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L) (h1 : 0 ≤ gaussian1000ResidualA eta * 10 + gaussian1000ResidualV eta)
    (h2 : 0 ≤ gaussian1000ResidualA eta * 10 + 2 * gaussian1000ResidualV eta)
    (hstrict :
      (12871 / 1000 : ℝ) - 2 * (7191 / 2000) +
          7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
          gaussian1000ResidualA eta / 10 +
          gaussian1000ResidualV eta / 100 +
          eps +
          273 / 1000 <
        D) :
    let r := s ^ 2
    eta *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        eps +
        LLS.PaperStatements.gaussianPrefixError (7191 / 2000) q (r ^ 2) <
      D := by
  intro r
  have hr100 : (100 : ℝ) ≤ r := by
    dsimp only [r]
    nlinarith only [hs0, sq_nonneg (s - 10)]
  have hspos : 0 < s := by linarith only [hs0]
  have hrpos : 0 < r := by linarith only [hr100]
  have hreq : r = s ^ 2 := rfl
  have hpole := gaussianBudget_pole_bound hrpos hreq hG
  have hqPole :
    gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log q + 4) / r) ≤
      gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply mul_le_mul_of_nonneg_left
    · apply div_le_div_of_nonneg_right
      · have hmul := mul_le_mul_of_nonneg_left hq (by norm_num only : (0 : ℝ) ≤ 7 / 6)
        linarith only [hmul]
      · exact hrpos.le
    · norm_num only [gaussianMR6FifthsEndpoint]
  have htail := gaussian1000_tail hr100
  have hinverse := inverse_pair_le_anchor (by norm_num only : (0 : ℝ) < 10) hs0 h1 h2
  have hid :
    eta *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
            (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
                (6 * gaussianMRRefinedConductor)) /
              s +
          (gaussianMR6FifthsEndpoint * (4 - 7 * (163 / 20) / (6 * gaussianMRRefinedConductor))) /
            s ^ 2) =
      7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) +
        gaussian1000ResidualA eta / s +
        gaussian1000ResidualV eta / s ^ 2 := by
    rw [hreq]
    dsimp only [gaussian1000ResidualA, gaussian1000ResidualV]
    ring
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hrpos.le]
  dsimp only [gaussianMR6FifthsEndpoint] at hpole hqPole hid hstrict ⊢
  linarith only [hpole, hqPole, htail.1, htail.2, hid, hinverse, hstrict]

/-- For L>=0, index m>=10^9 and log q<=L, the normalized error is below
163/20. Bound the ratio and independent error by their large-index caps,
then apply the common paired residual estimate. -/
theorem gaussianSingle_large_error {L m : ℝ} {q : ℕ} (hL : 0 ≤ L) (hm : gaussianMR6FifthsIndex ≤ m)
    (hq : Real.log q ≤ L) :
    let s := gaussianSingleRoot L
    let r := gaussianSingleRadius L
    (m / (m - 1)) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (m - 1) +
        LLS.PaperStatements.gaussianPrefixError (7191 / 2000) q (r ^ 2) <
      163 / 20 := by
  intro s r
  have hc := gaussian1000_large_checks
  have herr :=
    gaussianSingle_error_cap (gaussianSingle_root_ten L) (gaussianSingle_large_budget hL) hq
      hc.2.2.1.le hc.2.2.2.1.le hc.2.2.2.2
  have hs : 0 < s := gaussianSingle_root_pos L
  have hr : 0 < r := sq_pos_of_pos hs
  have hmain :
    0 ≤
      21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
        1839 * gaussianMR6FifthsEndpoint / (1000 * r) := by
    exact
      add_nonneg
        (div_nonneg (by norm_num only [gaussianMR6FifthsEndpoint])
          (mul_nonneg (by norm_num only [gaussianMRRefinedWidth]) hs.le))
        (div_nonneg (by norm_num only [gaussianMR6FifthsEndpoint])
          (mul_nonneg (by norm_num only) hr.le))
  have hcoef := gaussianMRRefined_index_coeffs hm
  have hratio := mul_le_mul_of_nonneg_right hcoef.2.1 hmain
  have hden : gaussianMR6FifthsIndex - 1 ≤ m - 1 := by linarith only [hm]
  have heps :=
    div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 13)
      (by norm_num only [gaussianMR6FifthsIndex] : 0 < gaussianMR6FifthsIndex - 1) hden
  change _ + _ + LLS.PaperStatements.gaussianPrefixError (7191 / 2000) q (r ^ 2) < _ at herr
  change
    (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * r)) +
        13 / (gaussianMR6FifthsIndex - 1) +
        LLS.PaperStatements.gaussianPrefixError (7191 / 2000) q (r ^ 2) <
      163 / 20 at herr
  linarith only [herr, hratio, heps]

/-- For L>=63, the combined radius exceeds 5L/8. The exact conductor
coefficient exceeds 5d/8 and the remaining budget terms are positive. -/
theorem gaussianSingle_radius_linear {L : ℝ} (hL : 63 ≤ L) :
    (5 / 8 : ℝ) * L < gaussianSingleRadius L := by
  have hG := gaussianSingle_large_budget (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hp := mul_pos gaussianMRRefined_coefficients.2 (gaussianSingle_root_pos L)
  have hD : (0 : ℝ) < 163 / 20 := by norm_num only
  have hcoef : 0 < gaussianMRRefinedConductor - (5 / 8 : ℝ) * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedConductor, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hm := mul_pos hcoef (by linarith only [hL] : (0 : ℝ) < L)
  have hd := gaussianMRRefined_coefficients.1
  nlinarith only [hG, hp, hD, hm, hd]

/-- For L>=63, the cutoff exceeds 15 L squared/32. Square the positive
linear radius lower bound. This covers the local subgroup witness envelope. -/
theorem gaussianSingle_bound_lower {L : ℝ} (hL : 63 ≤ L) :
    (15 / 32 : ℝ) * L ^ 2 < gaussianSingleBound L := by
  have hr := gaussianSingle_radius_linear hL
  have hpos : (0 : ℝ) ≤ (5 / 8) * L := by linarith only [hL]
  have hs := (sq_lt_sq₀ hpos (hpos.trans hr.le)).mpr hr
  change _ < (6 / 5 : ℝ) * gaussianSingleRadius L ^ 2
  nlinarith only [hs]

/-- The single root never exceeds the original two-root maximum. -/
theorem gaussianSingle_root_le (L : ℝ) : gaussianSingleRoot L ≤ gaussian1000Root L := by
  exact max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _))

/-- The single-root cutoff is no larger than the previously certified Gaussian cutoff. -/
theorem gaussianSingle_bound_le (L : ℝ) : gaussianSingleBound L ≤ gaussian1000Bound L := by
  have hs := gaussianSingle_root_le L
  have hp := gaussianSingle_root_pos L
  have hs2 := (sq_le_sq₀ hp.le (hp.le.trans hs)).mpr hs
  have hrr :=
    (sq_le_sq₀ (sq_nonneg (gaussianSingleRoot L)) (sq_nonneg (gaussian1000Root L))).mpr hs2
  exact mul_le_mul_of_nonneg_left hrr (by norm_num only : (0 : ℝ) ≤ 6 / 5)

end PseudoPrime.Analysis
