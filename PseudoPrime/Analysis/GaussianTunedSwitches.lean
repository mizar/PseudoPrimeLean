/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianTunedOrder

/-! # Seven exact switches of the tuned Gaussian family -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Ordered tuned roots yield ordered cutoffs by two nonnegative square comparisons. -/
theorem gaussianTuned_bound_le {f g : GaussianTunedProfile} {L : ℝ} (h : f.root L ≤ g.root L) :
    f.bound L ≤ g.bound L := by
  have hsq := (sq_le_sq₀ (f.root_pos L).le (g.root_pos L).le).mpr h
  have hsq2 := (sq_le_sq₀ (sq_nonneg (f.root L)) (sq_nonneg (g.root L))).mpr hsq
  exact mul_le_mul_of_nonneg_left hsq2 (by norm_num only : (0 : ℝ) ≤ 6 / 5)

/-- Before a cross-floor switch the smaller-floor tuned profile dominates. -/
theorem gaussianTuned_before {f g : GaussianTunedProfile} {L : ℝ} (hL : 0 ≤ L)
    (hfloor : f.floor ≤ g.floor) (h : L ≤ gaussianLowSwitch g.floor f.residual) :
    f.bound L ≤ g.bound L := by
  have hg : (9 : ℝ) ≤ g.floor := by
    have hs := g.signs.1; linarith only [hs]
  apply gaussianTuned_bound_le
  exact gaussianLow_roots_before hfloor ((gaussianLow_raw_le_iff hg f.signs.2.le hL).mpr h)

/-- After a cross-floor switch the smaller-residual tuned profile dominates. -/
theorem gaussianTuned_after {f g : GaussianTunedProfile} {L : ℝ} (hL : 0 ≤ L)
    (hres : g.residual ≤ f.residual) (h : gaussianLowSwitch g.floor f.residual ≤ L) :
    g.bound L ≤ f.bound L := by
  have hg : (9 : ℝ) ≤ g.floor := by
    have hs := g.signs.1; linarith only [hs]
  apply gaussianTuned_bound_le
  exact gaussianLow_roots_after hres ((gaussianLow_raw_ge_iff hg f.signs.2.le hL).mpr h)

/-- The seven exact boundaries alternate each profile's floor switch and the next
cross-floor switch. The four fixed floors increase while their residuals decrease. -/
noncomputable def gaussianTunedSwitch (i : Fin 7) : ℝ :=
  if i.val = 0 then gaussianLowSwitch (91 / 10) (929 / 100)
  else
    if i.val = 1 then gaussianLowSwitch (93 / 10) (929 / 100)
    else
      if i.val = 2 then gaussianLowSwitch (93 / 10) (87 / 10)
      else
        if i.val = 3 then gaussianLowSwitch (237 / 25) (87 / 10)
        else
          if i.val = 4 then gaussianLowSwitch (237 / 25) (1629 / 200)
          else
            if i.val = 5 then gaussianLowSwitch (979 / 100) (1629 / 200)
            else gaussianLowSwitch (979 / 100) (65 / 8)

/-- All seven boundaries are strictly ordered rational logarithmic scales. -/
theorem gaussianTunedSwitch_strictMono : StrictMono gaussianTunedSwitch := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> norm_num only [Fin.mk_lt_mk] at hij <;>
    dsimp only [gaussianTunedSwitch] <;>
    norm_num only [gaussianLowSwitch, gaussianMRRefinedD, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsIndex,
      gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor, ite_true, ite_false]

/-- Each tuned profile switches from its floor to its raw root at its own exact boundary. -/
theorem gaussianTuned_floor_selection (f : GaussianTunedProfile) {L : ℝ} (hL : 0 ≤ L) :
    f.root L =
      if L ≤ gaussianLowSwitch f.floor f.residual then f.floor
      else
        gaussianBudgetRoot gaussianMRRefinedD gaussianMRRefinedBeta
          (gaussianMRRefinedConductor * L + f.residual) := by
  have hu : (9 : ℝ) ≤ f.floor := by
    have hs := f.signs.1; linarith only [hs]
  have hiff := gaussianLow_raw_le_iff hu f.signs.2.le hL
  by_cases h : L ≤ gaussianLowSwitch f.floor f.residual
  · rw [ite_eq_left h]
    exact max_eq_left (hiff.mpr h)
  · rw [ite_eq_right h]
    exact max_eq_right (le_of_not_ge (fun hr ↦ h (hiff.mp hr)))

/-- On nonnegative scales, three exact cross-floor switches select the winning tuned profile.
Together with the four individual floor switches these are all seven family boundaries. -/
theorem gaussianTunedFamily_selection {L : ℝ} (hL : 0 ≤ L) :
    gaussianTunedFamily L =
      if L ≤ gaussianLowSwitch (93 / 10) (929 / 100) then GaussianTunedProfile.low.bound L
      else
        if L ≤ gaussianLowSwitch (237 / 25) (87 / 10) then GaussianTunedProfile.bridge.bound L
        else
          if L ≤ gaussianLowSwitch (979 / 100) (1629 / 200) then GaussianTunedProfile.middle.bound L
          else GaussianTunedProfile.upper.bound L := by
  have h13 : gaussianLowSwitch (93 / 10) (929 / 100) ≤ gaussianLowSwitch (237 / 25) (87 / 10) := by
    norm_num only [gaussianLowSwitch, gaussianMRRefinedD, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsIndex,
      gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor]
  have h35 :
    gaussianLowSwitch (237 / 25) (87 / 10) ≤ gaussianLowSwitch (979 / 100) (1629 / 200) := by
    norm_num only [gaussianLowSwitch, gaussianMRRefinedD, gaussianMRRefinedBeta,
      gaussianMRRefinedMass, gaussianMRRefinedWidth, gaussianMR6FifthsIndex,
      gaussianMR6FifthsEndpoint, gaussianMRRefinedConductor]
  by_cases h1 : L ≤ gaussianLowSwitch (93 / 10) (929 / 100)
  · rw [ite_eq_left h1]
    have ha : GaussianTunedProfile.low.bound L ≤ GaussianTunedProfile.bridge.bound L :=
      gaussianTuned_before hL (by norm_num only [GaussianTunedProfile.floor]) h1
    have hb : GaussianTunedProfile.bridge.bound L ≤ GaussianTunedProfile.middle.bound L :=
      gaussianTuned_before hL (by norm_num only [GaussianTunedProfile.floor]) (h1.trans h13)
    have hc : GaussianTunedProfile.middle.bound L ≤ GaussianTunedProfile.upper.bound L :=
      gaussianTuned_before hL (by norm_num only [GaussianTunedProfile.floor])
        (h1.trans (h13.trans h35))
    exact min_eq_left (le_min ha (le_min (ha.trans hb) ((ha.trans hb).trans hc)))
  · rw [ite_eq_right h1]
    have ha : GaussianTunedProfile.bridge.bound L ≤ GaussianTunedProfile.low.bound L :=
      gaussianTuned_after hL (by norm_num only [GaussianTunedProfile.residual]) (le_of_not_ge h1)
    by_cases h3 : L ≤ gaussianLowSwitch (237 / 25) (87 / 10)
    · rw [ite_eq_left h3]
      have hb : GaussianTunedProfile.bridge.bound L ≤ GaussianTunedProfile.middle.bound L :=
        gaussianTuned_before hL (by norm_num only [GaussianTunedProfile.floor]) h3
      have hc : GaussianTunedProfile.middle.bound L ≤ GaussianTunedProfile.upper.bound L :=
        gaussianTuned_before hL (by norm_num only [GaussianTunedProfile.floor]) (h3.trans h35)
      change min _ (min _ (min _ _)) = _
      rw [min_eq_left (le_min hb (hb.trans hc)), min_eq_right ha]
    · rw [ite_eq_right h3]
      have hb : GaussianTunedProfile.middle.bound L ≤ GaussianTunedProfile.bridge.bound L :=
        gaussianTuned_after hL (by norm_num only [GaussianTunedProfile.residual]) (le_of_not_ge h3)
      by_cases h5 : L ≤ gaussianLowSwitch (979 / 100) (1629 / 200)
      · rw [ite_eq_left h5]
        have hc : GaussianTunedProfile.middle.bound L ≤ GaussianTunedProfile.upper.bound L :=
          gaussianTuned_before hL (by norm_num only [GaussianTunedProfile.floor]) h5
        change min _ (min _ (min _ _)) = _
        rw [min_eq_left hc, min_eq_right hb, min_eq_right (hb.trans ha)]
      · rw [ite_eq_right h5]
        have hc : GaussianTunedProfile.upper.bound L ≤ GaussianTunedProfile.middle.bound L :=
          gaussianTuned_after hL (by norm_num only [GaussianTunedProfile.residual])
            (le_of_not_ge h5)
        change min _ (min _ (min _ _)) = _
        rw [min_eq_right hc, min_eq_right (hc.trans hb), min_eq_right ((hc.trans hb).trans ha)]

end PseudoPrime.Analysis
