/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianSingleRoot

/-! # Scaled index-four error budgets for the one-root Gaussian cutoff -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- The inverse-root coefficient after scaling the index-four radius by three quarters. -/
noncomputable def gaussianSingleFourA : ℝ :=
  (16 / 3 : ℝ) * (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth)) -
    4 * (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta / (6 * gaussianMRRefinedConductor))

/-- Given residual allowance D, retain its signed inverse-radius contribution after pole
elimination. -/
noncomputable def gaussianSingleFourV (D : ℝ) : ℝ :=
  (16 / 3 : ℝ) * (1839 * gaussianMR6FifthsEndpoint / 1000) +
    4 * gaussianMR6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor))

/-- Exact rational checks certify the paired inverse-power hypotheses and residual below 41. -/
theorem gaussianSingle_four_checks :
    0 ≤ gaussianSingleFourA * 10 + gaussianSingleFourV (163 / 20) ∧
      0 ≤ gaussianSingleFourA * 10 + 2 * gaussianSingleFourV (163 / 20) ∧
      3 * ((12871 / 1000 : ℝ) - 2 * (7191 / 2000)) +
          4 *
            (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD /
              (6 * gaussianMRRefinedConductor)) +
          13 +
          1125 / 1000 +
          gaussianSingleFourA / 10 +
          gaussianSingleFourV (163 / 20) / 100 <
        41 := by
  norm_num only [gaussianSingleFourA, gaussianSingleFourV, gaussianMR6FifthsEndpoint,
    gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
    gaussianMR6FifthsIndex, gaussianMRRefinedConductor, and_self]

/-- For radius at least 75, bound the two actual tails using the scale 17/10 and positive
denominators. -/
theorem gaussianSingle_four_tail {r : ℝ} (hr : 75 ≤ r) :
    (473 / 10 : ℝ) * (r ^ 2) ^ (-9 / 16 : ℝ) ≤ 371 / 1000 ∧ (512 / 27 : ℝ) / r ^ 2 ≤ 4 / 1000 := by
  have hp : 0 < r := by linarith only [hr]
  have hx : (17 / 10 : ℝ) ^ 16 ≤ r ^ 2 := by
    norm_num only
    nlinarith only [hr]
  have hdec :=
    LLS.PaperStatements.rpow_neg_nine_sixteenths_le_div_scale_sqrt (a := 17 / 10) (by norm_num only)
      hx
  rw [Real.sqrt_sq hp.le] at hdec
  have hl := mul_le_mul_of_nonneg_left hdec (by norm_num only : (0 : ℝ) ≤ 473 / 10)
  constructor
  · have hc : (473 / 10 : ℝ) / ((17 / 10 : ℝ) * r) ≤ 371 / 1000 := by
      rw [div_le_iff₀ (mul_pos (by norm_num only) hp)]
      nlinarith only [hr]
    have he :
      (473 / 10 : ℝ) * (1 / ((17 / 10 : ℝ) * r)) = (473 / 10 : ℝ) / ((17 / 10 : ℝ) * r) := by ring
    exact (hl.trans_eq he).trans hc
  · rw [div_le_iff₀ (sq_pos_of_pos hp)]
    nlinarith only [hr]

/-- Given a root above ten, its large-index budget and rational residual checks, the actual scaled
index-four error is below 41. Keep the signed inverse-power pair and use the radius-75 tails. -/
theorem gaussianSingle_four_error {L s P D : ℝ} (hs : 10 ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * s ^ 2)
    (h1 : 0 ≤ gaussianSingleFourA * 10 + gaussianSingleFourV D)
    (h2 : 0 ≤ gaussianSingleFourA * 10 + 2 * gaussianSingleFourV D)
    (hstrict :
      3 * ((12871 / 1000 : ℝ) - 2 * P) +
          4 *
            (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD /
              (6 * gaussianMRRefinedConductor)) +
          13 +
          1125 / 1000 +
          gaussianSingleFourA / 10 +
          gaussianSingleFourV D / 100 <
        41)
    {n : ℕ} (hn : Real.log n ≤ L) :
    let r := s ^ 2
    4 *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (3 / 4) * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * (3 / 4) * r)) +
        13 +
        3 * LLS.PaperStatements.gaussianPrefixError P n (((3 / 4 : ℝ) * r) ^ 2) <
      41 := by
  intro r
  have hspos : 0 < s := by linarith only [hs]
  have hr100 : 100 ≤ r := by
    dsimp only [r]; nlinarith only [hs]
  have hrpos : 0 < r := by linarith only [hr100]
  have hscaled : 75 ≤ (3 / 4 : ℝ) * r := by linarith only [hr100]
  have hscaledpos : 0 ≤ (3 / 4 : ℝ) * r := by linarith only [hscaled]
  have hpole := gaussianBudget_pole_bound hrpos (show r = s ^ 2 from rfl) hG
  have hqPole :
    gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / r) ≤
      gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * L + 4) / r) := by
    apply mul_le_mul_of_nonneg_left
    · apply div_le_div_of_nonneg_right
      · have hh := mul_le_mul_of_nonneg_left hn (by norm_num only : (0 : ℝ) ≤ 7 / 6)
        linarith only [hh]
      · exact hrpos.le
    · norm_num only [gaussianMR6FifthsEndpoint]
  have htail := gaussianSingle_four_tail hscaled
  have hinverse := inverse_pair_le_anchor (by norm_num only : (0 : ℝ) < 10) hs h1 h2
  have hid :
    4 *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (3 / 4) * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * (3 / 4) * r)) +
        4 *
          (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor) -
              (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedBeta /
                  (6 * gaussianMRRefinedConductor)) /
                s +
            (gaussianMR6FifthsEndpoint * (4 - 7 * D / (6 * gaussianMRRefinedConductor))) / s ^ 2) =
      4 * (7 * gaussianMR6FifthsEndpoint * gaussianMRRefinedD / (6 * gaussianMRRefinedConductor)) +
        gaussianSingleFourA / s +
        gaussianSingleFourV D / s ^ 2 := by
    dsimp only [gaussianSingleFourA, gaussianSingleFourV, r]
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  have hpoleEq :
    3 * (gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / ((3 / 4 : ℝ) * r))) =
      4 * (gaussianMR6FifthsEndpoint * (((7 / 6 : ℝ) * Real.log n + 4) / r)) := by
    simp only [div_eq_mul_inv, mul_inv_rev]
    norm_num only
    ring
  dsimp only [LLS.PaperStatements.gaussianPrefixError]
  rw [Real.sqrt_sq hscaledpos]
  dsimp only [gaussianMR6FifthsEndpoint] at hpole hqPole hid hstrict hpoleEq ⊢
  linarith only [hpole, hqPole, htail.1, htail.2, hid, hinverse, hstrict, hpoleEq]

/-- For root at least ten and allowance at least 8.14, the quadratic difference between scaled
index-four and twice the large-index budgets exceeds 42. -/
theorem gaussianSingle_four_margin {s D : ℝ} (hs : 10 ≤ s) (hD : 407 / 50 ≤ D) :
    42 <
      ((3 / 4 : ℝ) * (10971611 / 5000000) - 2 * gaussianMRRefinedD) * s ^ 2 -
          ((98882333 / 50000000 : ℝ) - 2 * gaussianMRRefinedBeta) * s +
        2 * D := by
  norm_num only [gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
    gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint, gaussianMRRefinedWidth]
  nlinarith only [hs, hD, sq_nonneg (s - 10)]

/-- The large-index budget and an index-four residual below 41 contradict the certified margin
above 42. This closes both old and recovered-prefix scalar branches. -/
theorem gaussianSingle_four_contradiction {L s D R : ℝ} (hs : 10 ≤ s) (hD : 407 / 50 ≤ D)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + D ≤ gaussianMRRefinedD * s ^ 2)
    (hR : R < 41)
    (hcmp :
      (3 / 4 : ℝ) * (10971611 / 5000000) * s ^ 2 ≤
        2 * gaussianMRRefinedConductor * L + (98882333 / 50000000) * s + R) :
    False := by
  have hmargin := gaussianSingle_four_margin hs hD
  nlinarith only [hG, hR, hcmp, hmargin]

end PseudoPrime.Analysis
