/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianLowFloorNumerics

/-! # Four tuned Gaussian profile certificates -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Four floor/residual certificates reuse the fixed Gaussian mass and width.
Low and bridge use the existing prefix; middle and upper use the moment prefix. -/
inductive GaussianTunedProfile
  | low
  | bridge
  | middle
  | upper
  deriving DecidableEq

namespace GaussianTunedProfile

/-- The root floor fixes the rational anchor used for tail estimates. -/
noncomputable def floor : GaussianTunedProfile → ℝ
  | .low => 91 / 10
  | .bridge => 93 / 10
  | .middle => 237 / 25
  | .upper => 979 / 100

/-- The residual allowance is the constant term of the large-index budget. -/
noncomputable def residual : GaussianTunedProfile → ℝ
  | .low => 929 / 100
  | .bridge => 87 / 10
  | .middle => 1629 / 200
  | .upper => 65 / 8

/-- The resolvent prefix lower bound is passed to the actual comparison. -/
noncomputable def prefixValue : GaussianTunedProfile → ℝ
  | .low => 901 / 250
  | .bridge => 901 / 250
  | .middle => 722517 / 200000
  | .upper => 722517 / 200000

/-- The combined large-index tail cap is valid above the profile floor. -/
noncomputable def tail : GaussianTunedProfile → ℝ
  | .low => 333 / 1000
  | .bridge => 317 / 1000
  | .middle => 303 / 1000
  | .upper => 282 / 1000

/-- The combined scaled index-four tail cap is valid above the profile floor. -/
noncomputable def fourTail : GaussianTunedProfile → ℝ
  | .low => 458 / 1000
  | .bridge => 435 / 1000
  | .middle => 417 / 1000
  | .upper => 417 / 1000

/-- The floored quadratic root at logarithmic scale L. -/
noncomputable def root (f : GaussianTunedProfile) (L : ℝ) : ℝ :=
  gaussianLowRoot f.floor f.residual L

/-- The square of the floored root is the comparison radius. -/
noncomputable def radius (f : GaussianTunedProfile) (L : ℝ) : ℝ :=
  f.root L ^ 2

/-- Six fifths of the squared radius bounds a rejecting prime. -/
noncomputable def bound (f : GaussianTunedProfile) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * f.radius L ^ 2

/-- Every profile has floor at least 9.1 and positive residual. -/
theorem signs (f : GaussianTunedProfile) : (91 / 10 : ℝ) ≤ f.floor ∧ 0 < f.residual := by
  cases f <;> norm_num only [floor, residual, and_self]

/-- The floored root satisfies its quadratic large-index budget for nonnegative L. -/
theorem budget (f : GaussianTunedProfile) {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * f.root L + f.residual ≤
      gaussianMRRefinedD * f.radius L := by
  have hu : (9 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
  have hD : (0 : ℝ) ≤ f.residual := by cases f <;> norm_num only [residual]
  exact gaussianLow_budget hu hD hL

/-- Each positive rational radius and scale certificate bounds the combined
large-index tail above the profile floor, without increasing the floor. -/
theorem tail_bound (f : GaussianTunedProfile) {s : ℝ} (hs : f.floor ≤ s) :
    (473 / 10 : ℝ) * ((s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / (s ^ 2) ^ 2 ≤ f.tail := by
  have hp : 0 ≤ s := by
    have hu : (0 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
    exact hu.trans hs
  have hsq := (sq_le_sq₀ (by cases f <;> norm_num only [floor] : 0 ≤ f.floor) hp).mpr hs
  cases f
  · exact
      gaussianLow_tail (R0 := (91 / 10 : ℝ) ^ 2) (q := 173 / 100) (by norm_num only) hsq
        (by norm_num only) (by norm_num only) (by norm_num only [tail])
  · exact
      gaussianLow_tail (R0 := (93 / 10 : ℝ) ^ 2) (q := 87 / 50) (by norm_num only) hsq
        (by norm_num only) (by norm_num only) (by norm_num only [tail])
  · exact
      gaussianLow_tail (R0 := (237 / 25 : ℝ) ^ 2) (q := 877 / 500) (by norm_num only) hsq
        (by norm_num only) (by norm_num only) (by norm_num only [tail])
  · exact
      gaussianLow_tail (R0 := (979 / 100 : ℝ) ^ 2) (q := 53 / 30) (by norm_num only) hsq
        (by norm_num only) (by norm_num only) (by norm_num only [tail])

/-- Each scaled radius uses its own rational scale and tail cap, retaining
width k/s and scale 7559/10000 in the index-four comparison. -/
theorem four_tail_bound (f : GaussianTunedProfile) {s : ℝ} (hs : f.floor ≤ s) :
    (473 / 10 : ℝ) * (((7559 / 10000 : ℝ) * s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) +
        (512 / 27 : ℝ) / ((7559 / 10000 : ℝ) * s ^ 2) ^ 2 ≤
      f.fourTail := by
  have hp : 0 ≤ s := by
    have hu : (0 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
    exact hu.trans hs
  have hsq := (sq_le_sq₀ (by cases f <;> norm_num only [floor] : 0 ≤ f.floor) hp).mpr hs
  have hm := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 7559 / 10000)
  cases f
  · exact
      gaussianLow_tail (R0 := (7559 / 10000 : ℝ) * (91 / 10) ^ 2) (q := 167 / 100)
        (by norm_num only) hm (by norm_num only) (by norm_num only) (by norm_num only [fourTail])
  · exact
      gaussianLow_tail (R0 := (7559 / 10000 : ℝ) * (93 / 10) ^ 2) (q := 337 / 200)
        (by norm_num only) hm (by norm_num only) (by norm_num only) (by norm_num only [fourTail])
  · exact
      gaussianLow_tail (R0 := (7559 / 10000 : ℝ) * (237 / 25) ^ 2) (q := 169 / 100)
        (by norm_num only) hm (by norm_num only) (by norm_num only) (by norm_num only [fourTail])
  · exact
      gaussianLow_tail (R0 := (7559 / 10000 : ℝ) * (979 / 100) ^ 2) (q := 169 / 100)
        (by norm_num only) hm (by norm_num only) (by norm_num only) (by norm_num only [fourTail])

/-- The floored profile root is at least its floor for every L. -/
theorem root_floor (f : GaussianTunedProfile) (L : ℝ) : f.floor ≤ f.root L :=
  le_max_left _ _

/-- The positive floor makes the profile root positive for every L. -/
theorem root_pos (f : GaussianTunedProfile) (L : ℝ) : 0 < f.root L := by
  have hu : (0 : ℝ) < f.floor := by cases f <;> norm_num only [floor]
  exact hu.trans_le (le_max_left _ _)

/-- Every profile cutoff is monotone on the whole real logarithmic scale. -/
theorem bound_mono (f : GaussianTunedProfile) : Monotone f.bound := by
  intro L K hLK
  have hs := gaussianLow_root_mono (u := f.floor) (D := f.residual) hLK
  have hp : 0 ≤ f.root L := by
    have hu : (0 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
    exact hu.trans (le_max_left _ _)
  have hsq := (sq_le_sq₀ hp (hp.trans hs)).mpr hs
  have hsq2 := (sq_le_sq₀ (sq_nonneg (f.root L)) (sq_nonneg (f.root K))).mpr hsq
  exact mul_le_mul_of_nonneg_left hsq2 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Every radius is at least the square of 9.1. -/
theorem radius_floor (f : GaussianTunedProfile) (L : ℝ) : (91 / 10 : ℝ) ^ 2 ≤ f.radius L := by
  have hs := f.signs.1.trans (f.root_floor L)
  exact (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 91 / 10) (le_trans (by norm_num only) hs)).mpr hs

/-- For L at least 63 the budget forces radius greater than 5L/8. -/
theorem radius_linear (f : GaussianTunedProfile) {L : ℝ} (hL : 63 ≤ L) :
    (5 / 8 : ℝ) * L < f.radius L := by
  have hG := f.budget (by linarith only [hL] : (0 : ℝ) ≤ L)
  have hp := mul_pos gaussianMRRefined_coefficients.2 (f.root_pos L)
  have hcoef : 0 < gaussianMRRefinedConductor - (5 / 8 : ℝ) * gaussianMRRefinedD := by
    norm_num only [gaussianMRRefinedConductor, gaussianMRRefinedD, gaussianMRRefinedMass,
      gaussianMR6FifthsEndpoint, gaussianMR6FifthsIndex]
  have hm := mul_pos hcoef (by linarith only [hL] : (0 : ℝ) < L)
  have hd := gaussianMRRefined_coefficients.1
  have hD := f.signs.2
  nlinarith only [hG, hp, hD, hm, hd]

/-- Every profile bounds the actual scaled index-four residual below 204/5. -/
theorem four_error (f : GaussianTunedProfile) {L s : ℝ} {q : ℕ} (hs : f.floor ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + f.residual ≤
        gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L) :
    4 *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * (7559 / 10000) * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * (7559 / 10000) * s ^ 2)) +
        13 +
        3 *
          LLS.PaperStatements.gaussianPrefixError f.prefixValue q
            (((7559 / 10000 : ℝ) * s ^ 2) ^ 2) <
      204 / 5 := by
  apply
    gaussianLow_four_error (u := f.floor) (T := f.fourTail)
      (by
        have h := f.signs.1; linarith only [h])
      hs hG
  · cases f <;>
      norm_num only [floor, residual, gaussianLowFourA, gaussianLowFourV, gaussianMR6FifthsEndpoint,
        gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMR6FifthsIndex, gaussianMRRefinedConductor]
  · cases f <;>
      norm_num only [floor, residual, gaussianLowFourA, gaussianLowFourV, gaussianMR6FifthsEndpoint,
        gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMR6FifthsIndex, gaussianMRRefinedConductor]
  · cases f <;>
      norm_num only [floor, residual, prefixValue, fourTail, gaussianLowFourA, gaussianLowFourV,
        gaussianMR6FifthsEndpoint, gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
        gaussianMRRefinedWidth, gaussianMR6FifthsIndex, gaussianMRRefinedConductor]
  · exact f.four_tail_bound hs
  · exact hq

/-- The scaled index-four main quadratic exceeds 204/5 above every profile floor. -/
theorem four_margin (f : GaussianTunedProfile) {s : ℝ} (hs : f.floor ≤ s) :
    (204 / 5 : ℝ) <
      ((7559 / 10000 : ℝ) * (10971611 / 5000000) - 2 * gaussianMRRefinedD) * s ^ 2 -
          (4 * ((7559 / 10000 : ℝ) * (81470555 / 100000000) * (2 / 5) + 1 / (10 * (2 / 5))) -
              2 * gaussianMRRefinedBeta) *
            s +
        2 * f.residual := by
  cases f
  · norm_num only [floor] at hs
    norm_num only [residual, gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint, gaussianMRRefinedWidth]
    nlinarith only [hs, sq_nonneg (s - (91 / 10))]
  · norm_num only [floor] at hs
    norm_num only [residual, gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint, gaussianMRRefinedWidth]
    nlinarith only [hs, sq_nonneg (s - (93 / 10))]
  · norm_num only [floor] at hs
    norm_num only [residual, gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint, gaussianMRRefinedWidth]
    nlinarith only [hs, sq_nonneg (s - (237 / 25))]
  · norm_num only [floor] at hs
    norm_num only [residual, gaussianMRRefinedD, gaussianMRRefinedBeta, gaussianMRRefinedMass,
      gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint, gaussianMRRefinedWidth]
    nlinarith only [hs, sq_nonneg (s - (979 / 100))]

/-- All four profiles have a strict fixed large-index residual cap. Low and
bridge use the coarse pole; middle and upper use the signed inverse pair. -/
theorem large_cap (f : GaussianTunedProfile) {L s : ℝ} {q : ℕ} (hs : f.floor ≤ s)
    (hG :
      gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * s + f.residual ≤
        gaussianMRRefinedD * s ^ 2)
    (hq : Real.log q ≤ L) :
    (gaussianMR6FifthsIndex / (gaussianMR6FifthsIndex - 1)) *
          (21 * gaussianMR6FifthsEndpoint / (10 * gaussianMRRefinedWidth * s) +
            1839 * gaussianMR6FifthsEndpoint / (1000 * s ^ 2)) +
        13 / (gaussianMR6FifthsIndex - 1) +
        LLS.PaperStatements.gaussianPrefixError f.prefixValue q ((s ^ 2) ^ 2) <
      f.residual := by
  have htail := f.tail_bound hs
  cases f
  · apply
      gaussianLow_coarse_error (u := 91 / 10) (P := 901 / 250) (T := 333 / 1000) (by norm_num only)
        hs (by norm_num only [residual]) hG hq
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · exact htail
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  · apply
      gaussianLow_coarse_error (u := 93 / 10) (P := 901 / 250) (T := 317 / 1000) (by norm_num only)
        hs (by norm_num only [residual]) hG hq
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · exact htail
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  · apply
      gaussianLow_error_cap (u := 237 / 25) (P := 722517 / 200000) (T := 303 / 1000)
        (by norm_num only) hs hG hq
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · exact htail
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
  · apply
      gaussianLow_error_cap (u := 979 / 100) (P := 722517 / 200000) (T := 282 / 1000)
        (by norm_num only) hs hG hq
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]
    · exact htail
    · norm_num only [residual, gaussian1000ResidualA, gaussianLowResidualV, gaussianMRRefinedD,
        gaussianMRRefinedBeta, gaussianMRRefinedMass, gaussianMRRefinedWidth,
        gaussianMRRefinedConductor, gaussianMR6FifthsIndex, gaussianMR6FifthsEndpoint]

end GaussianTunedProfile

/-- The final Gaussian family is the minimum of all four certified cutoffs. -/
noncomputable def gaussianTunedFamily (L : ℝ) : ℝ :=
  min (GaussianTunedProfile.low.bound L)
    (min (GaussianTunedProfile.bridge.bound L)
      (min (GaussianTunedProfile.middle.bound L) (GaussianTunedProfile.upper.bound L)))

/-- The two-profile early family uses only the existing 1000-term prefix. -/
noncomputable def gaussianTunedEarlyFamily (L : ℝ) : ℝ :=
  min (GaussianTunedProfile.low.bound L) (GaussianTunedProfile.bridge.bound L)

end PseudoPrime.Analysis
