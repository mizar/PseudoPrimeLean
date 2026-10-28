/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianTunedProfiles
public import PseudoPrime.Analysis.GaussianLowSwitches

/-! # Strict and monotone comparisons for tuned Gaussian profiles -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Lowering both a nonnegative root floor and the residual strictly lowers the cutoff.
Compare positive budget roots and square the resulting strict root inequality twice. -/
theorem gaussianLowBound_lt_params {u v D E L : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (huv : u < v)
    (hDE : D < E) (hC : 0 ≤ gaussianMRRefinedConductor * L + D) :
    gaussianLowBound u D L < gaussianLowBound v E L := by
  have hraw :=
    gaussianBudgetRoot_strictMono (b := gaussianMRRefinedBeta) gaussianMRRefined_coefficients.1 hC
      (by linarith only [hDE] :
        gaussianMRRefinedConductor * L + D < gaussianMRRefinedConductor * L + E)
  have hr : gaussianLowRoot u D L < gaussianLowRoot v E L :=
    max_lt (huv.trans_le (le_max_left _ _)) (hraw.trans_le (le_max_right _ _))
  have hp : 0 ≤ gaussianLowRoot u D L := hu.trans (le_max_left _ _)
  have hq : 0 ≤ gaussianLowRoot v E L := hv.trans (le_max_left _ _)
  have hs := (sq_lt_sq₀ hp hq).mpr hr
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
  exact mul_lt_mul_of_pos_left hs' (by norm_num only : (0 : ℝ) < 6 / 5)

/-- A smaller residual strictly lowers a fixed-floor cutoff once the old root exceeds its floor.
The raw roots compare strictly, and the displayed floor assumption excludes a shared plateau. -/
theorem gaussianLowBound_lt_residual {u D E L : ℝ} (hu : 0 ≤ u) (hDE : D < E)
    (hC : 0 ≤ gaussianMRRefinedConductor * L + D) (hfloor : u < gaussianLowRoot u E L) :
    gaussianLowBound u D L < gaussianLowBound u E L := by
  have hraw :=
    gaussianBudgetRoot_strictMono (b := gaussianMRRefinedBeta) gaussianMRRefined_coefficients.1 hC
      (by linarith only [hDE] :
        gaussianMRRefinedConductor * L + D < gaussianMRRefinedConductor * L + E)
  have hr : gaussianLowRoot u D L < gaussianLowRoot u E L :=
    max_lt hfloor (hraw.trans_le (le_max_right _ _))
  have hp : 0 ≤ gaussianLowRoot u D L := hu.trans (le_max_left _ _)
  have hq : 0 ≤ gaussianLowRoot u E L := hu.trans (le_max_left _ _)
  have hs := (sq_lt_sq₀ hp hq).mpr hr
  have hs' := (sq_lt_sq₀ (sq_nonneg _) (sq_nonneg _)).mpr hs
  exact mul_lt_mul_of_pos_left hs' (by norm_num only : (0 : ℝ) < 6 / 5)

/-- Above scale 100 the old low root exceeds its floor, so the tuned residual improves it. -/
theorem gaussianTunedLow_lt_low {L : ℝ} (hL : 100 ≤ L) :
    GaussianTunedProfile.low.bound L < GaussianLowProfile.low.bound L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  have hswitch : gaussianLowSwitch (91 / 10) (93 / 10) < (100 : ℝ) := by
    norm_num only [gaussianLowSwitch, gaussianMRRefinedD, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsIndex,
      gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor]
  have hraw :
    (91 / 10 : ℝ) <
      gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
        (gaussianMRRefinedConductor * L + 93 / 10) := by
    apply lt_of_not_ge
    intro hr
    have hle :=
      (gaussianLow_raw_le_iff (by norm_num only : (9 : ℝ) ≤ 91 / 10)
            (by norm_num only : (0 : ℝ) ≤ 93 / 10) h0).mp
        hr
    linarith only [hle, hswitch, hL]
  exact
    gaussianLowBound_lt_residual (by norm_num only : (0 : ℝ) ≤ 91 / 10)
      (by norm_num only : (929 / 100 : ℝ) < 93 / 10)
      (by
        norm_num only [gaussianMRRefinedConductor, GaussianTunedProfile.residual]
        linarith only [h0])
      (hraw.trans_le (le_max_right _ _))

/-- Every tuned profile cutoff is monotone, so their minimum is monotone. -/
theorem gaussianTunedFamily_mono : Monotone gaussianTunedFamily := by
  intro L K hLK
  exact
    min_le_min (GaussianTunedProfile.low.bound_mono hLK)
      (min_le_min (GaussianTunedProfile.bridge.bound_mono hLK)
        (min_le_min (GaussianTunedProfile.middle.bound_mono hLK)
          (GaussianTunedProfile.upper.bound_mono hLK)))

/-- The new middle profile lowers both the floor and residual of the current middle. -/
theorem gaussianTunedMiddle_lt_middle {L : ℝ} (hL : 0 ≤ L) :
    GaussianTunedProfile.middle.bound L < GaussianLowProfile.middle.bound L := by
  exact
    gaussianLowBound_lt_params (by norm_num only : (0 : ℝ) ≤ 237 / 25)
      (by norm_num only : (0 : ℝ) ≤ 19 / 2) (by norm_num only : (237 / 25 : ℝ) < 19 / 2)
      (by norm_num only : (1629 / 200 : ℝ) < 163 / 20)
      (by
        norm_num only [gaussianMRRefinedConductor, GaussianTunedProfile.residual]
        linarith only [hL])

/-- The new upper profile lowers both the floor and residual of the current upper. -/
theorem gaussianTunedUpper_lt_upper {L : ℝ} (hL : 0 ≤ L) :
    GaussianTunedProfile.upper.bound L < GaussianLowProfile.upper.bound L := by
  exact
    gaussianLowBound_lt_params (by norm_num only : (0 : ℝ) ≤ 979 / 100)
      (by norm_num only : (0 : ℝ) ≤ 49 / 5) (by norm_num only : (979 / 100 : ℝ) < 49 / 5)
      (by norm_num only : (65 / 8 : ℝ) < 813 / 100)
      (by
        norm_num only [gaussianMRRefinedConductor, GaussianTunedProfile.residual]
        linarith only [hL])

/-- The family is no larger than any one of its four certified components. -/
theorem gaussianTunedFamily_le (f : GaussianTunedProfile) (L : ℝ) :
    gaussianTunedFamily L ≤ f.bound L := by
  cases f
  · exact min_le_left _ _
  · exact (min_le_right _ _).trans (min_le_left _ _)
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  · exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))

/-- On the entire half-line from scale 100, each current Gaussian candidate has a
strictly better corresponding tuned candidate. Taking the minimum preserves strictness. -/
theorem gaussianTunedFamily_lt_lowFamily {L : ℝ} (hL : 100 ≤ L) :
    gaussianTunedFamily L < gaussianLowFamily L := by
  have h0 : (0 : ℝ) ≤ L := by linarith only [hL]
  exact
    lt_min ((gaussianTunedFamily_le .low L).trans_lt (gaussianTunedLow_lt_low hL))
      (lt_min ((gaussianTunedFamily_le .middle L).trans_lt (gaussianTunedMiddle_lt_middle h0))
        ((gaussianTunedFamily_le .upper L).trans_lt (gaussianTunedUpper_lt_upper h0)))

end PseudoPrime.Analysis
