/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianLowFloorNumerics

/-! # Low-floor profile constants -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Five certified floor/residual pairs: the low profile, two old-prefix
profiles, and two fine-prefix profiles. The final family uses low, middle, upper. -/
inductive GaussianLowProfile
  | low
  | middleOld
  | upperOld
  | middle
  | upper
  deriving DecidableEq

namespace GaussianLowProfile

/-- The positive root floor fixes the tail domain of each profile. -/
noncomputable def floor : GaussianLowProfile → ℝ
  | .low => 91 / 10
  | .middleOld | .middle => 19 / 2
  | .upperOld | .upper => 49 / 5

/-- The residual allowance in the quadratic large-index budget. -/
noncomputable def residual : GaussianLowProfile → ℝ
  | .low => 93 / 10
  | .middleOld => 204 / 25
  | .upperOld => 407 / 50
  | .middle => 163 / 20
  | .upper => 813 / 100

/-- The actual resolvent prefix lower bound used by the comparison. -/
noncomputable def prefixValue : GaussianLowProfile → ℝ
  | .low | .middleOld | .upperOld => 901 / 250
  | .middle | .upper => 721769 / 200000

/-- The cap for the two large-index tail terms. -/
noncomputable def tail : GaussianLowProfile → ℝ
  | .low => 333 / 1000
  | .middleOld | .middle => 301 / 1000
  | .upperOld | .upper => 281 / 1000

/-- The cap for the scaled index-four tail terms. -/
noncomputable def fourTail : GaussianLowProfile → ℝ
  | .low => 458 / 1000
  | _ => 415 / 1000

/-- The floored quadratic root at logarithmic scale L. -/
noncomputable def root (f : GaussianLowProfile) (L : ℝ) : ℝ :=
  gaussianLowRoot f.floor f.residual L

/-- The square of the floored root is the comparison radius. -/
noncomputable def radius (f : GaussianLowProfile) (L : ℝ) : ℝ :=
  f.root L ^ 2

/-- Six fifths of the squared radius bounds a rejecting prime. -/
noncomputable def bound (f : GaussianLowProfile) (L : ℝ) : ℝ :=
  (6 / 5 : ℝ) * f.radius L ^ 2

/-- Every profile has floor at least 9.1 and positive residual. -/
theorem signs (f : GaussianLowProfile) : (91 / 10 : ℝ) ≤ f.floor ∧ 0 < f.residual := by
  cases f <;> norm_num only [floor, residual, and_self]

/-- The floored root satisfies its quadratic large-index budget for nonnegative L. -/
theorem budget (f : GaussianLowProfile) {L : ℝ} (hL : 0 ≤ L) :
    gaussianMRRefinedConductor * L + gaussianMRRefinedBeta * f.root L + f.residual ≤
      gaussianMRRefinedD * f.radius L := by
  have hu : (9 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
  have hD : (0 : ℝ) ≤ f.residual := by cases f <;> norm_num only [residual]
  exact gaussianLow_budget hu hD hL

/-- The large-index tail cap holds above the profile floor. -/
theorem tail_bound (f : GaussianLowProfile) {s : ℝ} (hs : f.floor ≤ s) :
    (473 / 10 : ℝ) * ((s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / (s ^ 2) ^ 2 ≤ f.tail := by
  have hp : 0 ≤ s := by
    have hu : (0 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
    exact hu.trans hs
  have hsq := (sq_le_sq₀ (by cases f <;> norm_num only [floor] : 0 ≤ f.floor) hp).mpr hs
  cases f
  · exact gaussianLow_tail_low hsq
  · exact gaussianLow_tail_middle hsq
  · exact gaussianLow_tail_upper hsq
  · exact gaussianLow_tail_middle hsq
  · exact gaussianLow_tail_upper hsq

/-- The scaled index-four tail cap holds above the profile floor. -/
theorem four_tail_bound (f : GaussianLowProfile) {s : ℝ} (hs : f.floor ≤ s) :
    (473 / 10 : ℝ) * (((7559 / 10000 : ℝ) * s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) +
        (512 / 27 : ℝ) / ((7559 / 10000 : ℝ) * s ^ 2) ^ 2 ≤
      f.fourTail := by
  have hp : 0 ≤ s := by
    have hu : (0 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
    exact hu.trans hs
  have hsq := (sq_le_sq₀ (by cases f <;> norm_num only [floor] : 0 ≤ f.floor) hp).mpr hs
  have hm := mul_le_mul_of_nonneg_left hsq (by norm_num only : (0 : ℝ) ≤ 7559 / 10000)
  cases f
  · exact gaussianLow_tail_four_low hm
  · exact gaussianLow_tail_four_upper hm
  · apply gaussianLow_tail_four_upper
    dsimp only [floor] at hm
    linarith only [hm]
  · exact gaussianLow_tail_four_upper hm
  · apply gaussianLow_tail_four_upper
    dsimp only [floor] at hm
    linarith only [hm]

/-- The floored profile root is at least its floor for every L. -/
theorem root_floor (f : GaussianLowProfile) (L : ℝ) : f.floor ≤ f.root L :=
  le_max_left _ _

/-- The positive floor makes the profile root positive for every L. -/
theorem root_pos (f : GaussianLowProfile) (L : ℝ) : 0 < f.root L := by
  have hu : (0 : ℝ) < f.floor := by cases f <;> norm_num only [floor]
  exact hu.trans_le (le_max_left _ _)

/-- Every profile cutoff is monotone on the whole real logarithmic scale. -/
theorem bound_mono (f : GaussianLowProfile) : Monotone f.bound := by
  intro L K hLK
  have hs := gaussianLow_root_mono (u := f.floor) (D := f.residual) hLK
  have hp : 0 ≤ f.root L := by
    have hu : (0 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
    exact hu.trans (le_max_left _ _)
  have hsq := (sq_le_sq₀ hp (hp.trans hs)).mpr hs
  have hsq2 := (sq_le_sq₀ (sq_nonneg (f.root L)) (sq_nonneg (f.root K))).mpr hsq
  exact mul_le_mul_of_nonneg_left hsq2 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Every radius is at least the square of 9.1. -/
theorem radius_floor (f : GaussianLowProfile) (L : ℝ) : (91 / 10 : ℝ) ^ 2 ≤ f.radius L := by
  have hs := f.signs.1.trans (f.root_floor L)
  exact (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 91 / 10) (le_trans (by norm_num only) hs)).mpr hs

/-- For L at least 63 the budget forces radius greater than 5L/8. -/
theorem radius_linear (f : GaussianLowProfile) {L : ℝ} (hL : 63 ≤ L) :
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
theorem four_error (f : GaussianLowProfile) {L s : ℝ} {q : ℕ} (hs : f.floor ≤ s)
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
theorem four_margin (f : GaussianLowProfile) {s : ℝ} (hs : f.floor ≤ s) :
    (204 / 5 : ℝ) <
      ((7559 / 10000 : ℝ) * (10971611 / 5000000) - 2 * gaussianMRRefinedD) * s ^ 2 -
          (4 * ((7559 / 10000 : ℝ) * (81470555 / 100000000) * (2 / 5) + 1 / (10 * (2 / 5))) -
              2 * gaussianMRRefinedBeta) *
            s +
        2 * f.residual := by
  cases f
  · exact gaussianLow_four_margin_low hs (by norm_num only [residual])
  · exact gaussianLow_four_margin_upper hs (by norm_num only [residual])
  · apply gaussianLow_four_margin_upper
    · dsimp only [floor] at hs
      linarith only [hs]
    · norm_num only [residual]
  · exact gaussianLow_four_margin_upper hs (by norm_num only [residual])
  · apply gaussianLow_four_margin_upper
    · dsimp only [floor] at hs
      linarith only [hs]
    · norm_num only [residual]

/-- The fixed large-index cap is strict for all five profiles. The low
profile uses a coarse pole; the others retain signed inverse-pair credit. -/
theorem large_cap (f : GaussianLowProfile) {L s : ℝ} {q : ℕ} (hs : f.floor ≤ s)
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
  have htail :
    (473 / 10 : ℝ) * ((s ^ 2) ^ 2) ^ (-9 / 16 : ℝ) + (512 / 27 : ℝ) / (s ^ 2) ^ 2 ≤ f.tail := by
    have hp : 0 ≤ s := by
      have hu : (0 : ℝ) ≤ f.floor := by cases f <;> norm_num only [floor]
      exact hu.trans hs
    have hsq := (sq_le_sq₀ (by cases f <;> norm_num only [floor] : 0 ≤ f.floor) hp).mpr hs
    cases f
    · exact gaussianLow_tail_low hsq
    · exact gaussianLow_tail_middle hsq
    · exact gaussianLow_tail_upper hsq
    · exact gaussianLow_tail_middle hsq
    · exact gaussianLow_tail_upper hsq
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
      gaussianLow_error_cap (u := 19 / 2) (P := 901 / 250) (T := 301 / 1000) (by norm_num only) hs
        hG hq
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
      gaussianLow_error_cap (u := 49 / 5) (P := 901 / 250) (T := 281 / 1000) (by norm_num only) hs
        hG hq
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
      gaussianLow_error_cap (u := 19 / 2) (P := 721769 / 200000) (T := 301 / 1000)
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
      gaussianLow_error_cap (u := 49 / 5) (P := 721769 / 200000) (T := 281 / 1000)
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

end GaussianLowProfile

/-- The fine-prefix Gaussian family is the minimum of its three certified cutoffs. -/
noncomputable def gaussianLowFamily (L : ℝ) : ℝ :=
  min (GaussianLowProfile.low.bound L)
    (min (GaussianLowProfile.middle.bound L) (GaussianLowProfile.upper.bound L))

/-- The old-prefix family retains the low floor and its two old-prefix companions. -/
noncomputable def gaussianLowOldFamily (L : ℝ) : ℝ :=
  min (GaussianLowProfile.low.bound L)
    (min (GaussianLowProfile.middleOld.bound L) (GaussianLowProfile.upperOld.bound L))

end PseudoPrime.Analysis
