/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.AdaptivePhaseIntervalTree
public import PseudoPrime.Analysis.Phase64FirstScaleCell

/-! # Continuous scale bounds from adaptive phase trees -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a scale in the first level cell and a successful rational adaptive tree check.
Claim: the actual signed Gamma phase is bounded throughout the initial ordinate interval.
Proof: supply the uniform logarithmic cell enclosure to generic tree soundness.
Role: attach computed tree certificates to the continuous scale parameter. -/
theorem phaseCell64_adaptive_tree_sound {x : ℝ} (hlo : (163840 / 99 : ℝ) ≤ x)
    (hhi : x ≤ (4096128001 / 2475000 : ℝ)) (tree : RationalIntervalTree) (a b : ℚ)
    (hcheck :
      rationalIntervalTreeCheck
          (scaledPhaseIntervalCheck (10 ^ 12) phaseCell64Center phaseCell64Uncertainty) a b tree =
        true) :
    ∀ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
        finiteSignedResolvent phaseResolvent64Coefficients t := by
  have hx : 0 < x := lt_of_lt_of_le (by norm_num only) hlo
  apply
    scaledPhaseIntervalTree_sound hx (log_scale64_small_cell_abs_le_eight hlo hhi)
      (by norm_num only : 0 < 10 ^ 12) phaseCell64Center phaseCell64Uncertainty _ tree a b hcheck
  intro s
  obtain ⟨hl, hu⟩ := log_phase_scale64_small_cell hlo hhi
  have hlQ : ((1295670321 / 100000000 : ℚ) : ℝ) ≤ Real.log (256 * x) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact hl
  have huQ : Real.log (256 * x) ≤ ((1295673447 / 100000000 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    exact hu
  exact phase_enclosure_of_rational_log_interval hlQ huQ s

/-- Input: a positive scale and actual phase majorant only on [0,5].
Claim: the majorant holds for every real ordinate.
Proof: reflect the low interval by evenness and use the proved Gamma norm tail outside it.
Role: avoid duplicated negative-ordinate computations in global spectral certificates. -/
theorem phase64_signed_phase_le_of_positive_low {x : ℝ} (hx : 0 < x)
    (hc :
      ∀ t : ℝ,
        t ∈ Set.Icc 0 5 →
          -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
            finiteSignedResolvent phaseResolvent64Coefficients t)
    (t : ℝ) :
    -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      finiteSignedResolvent phaseResolvent64Coefficients t := by
  apply phase64_signed_phase_le_of_low hx _ t
  intro u hu
  have h := hc |u| ⟨abs_nonneg u, hu⟩
  have hR :
    finiteSignedResolvent phaseResolvent64Coefficients |u| =
      finiteSignedResolvent phaseResolvent64Coefficients u := by
    simp only [finiteSignedResolvent, sq_abs]
  rw [hR] at h
  by_cases h0 : 0 ≤ u
  · simpa only [abs_of_nonneg h0] using h
  · rw [abs_of_neg (lt_of_not_ge h0), gammaHalf_phase_re_neg hx] at h
    exact h

end PseudoPrime.Analysis
