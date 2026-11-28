/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowerIntegral632
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterContour600
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCoefficients
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal600
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Principal error bounds for the five comparisons through logarithm 632 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The logarithmic coordinate of the physical cutoff stays between 14 and
15 at radii from 313 to 316, so the uniform trivial-zero estimate applies. -/
private theorem principal_coord632 {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    quarterCoord570 (r ^ 2) 1 ∈ Set.Icc 14 15 := by
  have h₀ : 0 < r := by linarith only [hr.1]
  have h₁ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 20) (lo := 57 / 10) (hi := 6)
        (by decide +kernel)).1
  have h₂ :=
    (Analysis.rationalLogIntervalCheck_sound (N := 316) (j := 8) (n := 20) (lo := 5) (hi := 29 / 5)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h₁ h₂
  unfold quarterCoord570
  rw [one_div, Real.log_inv, sub_neg_eq_add, Real.log_pow, Nat.cast_ofNat]
  norm_num only
  exact
    ⟨by linarith only [h₁, Real.log_le_log (by norm_num only) hr.1], by
      linarith only [h₂, Real.log_le_log h₀ hr.2]⟩

/-- At radii at least 313 the logarithmic boundary weight is at most 0.00256. -/
theorem quarter_weight_cap_313 {r : ℝ} (hr : 313 ≤ r) : quarterWeight570 (r ^ 2) 1 ≤ 0.00256 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 32) (lo := 5) (hi :=
        5746203194 / 10 ^ 9) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 313) (p := 26) (d := 25)
        (lo := 0) (hi := 2538831564 / 10 ^ 12) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_pow, neg_div] at hl hp
  have h := quarter_conductor_box (by norm_num only : (1 : ℝ) ≤ 313) hl hp
  rw [section99_conductor_eq_density (by norm_num only)] at h
  rw [section99_weight_eq_density (show 1 ≤ r by linarith only [hr])]
  apply (section99_boundary_antitone (by norm_num only) hr).trans
  linarith only [h]

private theorem section99_endpoint_lower_632 {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    -(0.001148 : ℝ) ≤
      3 * quarterWeight570 (r ^ 2) 1 -
        4 * r * (∫ u in (0 : ℝ)..1 / r ^ 2, (quarterKernel570.transform u).re / Real.sqrt u) := by
  have hpos : 0 < r := by linarith only [hr.1]
  have hX := one_le_pow₀ (show 1 ≤ r by linarith only [hr.1]) (n := 2)
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 20) (lo := 57 / 10) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hz : 14 ≤ 14 / 5 + Real.log (r ^ 2) := by
    rw [Real.log_pow, Nat.cast_ofNat]
    linarith only [h, Real.log_le_log (by norm_num only) hr.1]
  have hm := quarter_missing_mass_ratio632 hX hz
  rw [Real.sqrt_sq hpos.le] at hm
  have hw := quarter_weight_cap_313 hr.1
  linarith only [hm, hw]

/-- On the five-comparison radius range a lower bound on the nontrivial-zero
Abel action gives a lower bound on the principal error. The trivial zeros
and physical lower endpoint cost at most 0.002696 together. -/
theorem principal_error_of_phase_632 {r B : ℝ} (hr : r ∈ Set.Icc 313 316)
    (hB :
      B ≤
        section99AbelAction (r ^ 2)
          (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re)) :
    B - 0.002696 ≤ section99PrincipalError r := by
  have hl : 292 ≤ r := (by norm_num only : (292 : ℝ) ≤ 313).trans hr.1
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ (by linarith only [hr.1]) (n := 2)
  have he := section99_error_eq_action r
  dsimp only at he
  rw [section99_abel_zero_split hx] at he
  obtain ⟨hb, hu⟩ := principal_coord632 hr
  linarith only [he, hB, quarter_trivial_upper_weight hl hb hu, quarter_weight_cap_313 hr.1,
    section99_endpoint_lower_632 hr]

/-- The six phase endpoints and curvature bound give a signed principal
error lower bound on each of the five radius intervals. -/
theorem principal_error_lower_632 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 313 316) :
    (if r ≤ 1568 / 5 then -0.008176
      else
        if r ≤ 314 then -0.007866
        else if r ≤ 6289 / 20 then -0.007706 else if r ≤ 315 then -0.007546 else -0.007446) ≤
      section99PrincipalError r := by
  by_cases h₁ : r ≤ 1568 / 5
  · rw [ite_eq_left h₁]
    linarith only [principal_error_of_phase_632 hr (section99_abel_to3136 hRH ⟨hr.1, h₁⟩)]
  rw [ite_eq_right h₁]
  by_cases h₂ : r ≤ 314
  · rw [ite_eq_left h₂]
    linarith only [principal_error_of_phase_632 hr (section99_abel_to314 hRH ⟨le_of_not_ge h₁, h₂⟩)]
  rw [ite_eq_right h₂]
  by_cases h₃ : r ≤ 6289 / 20
  · rw [ite_eq_left h₃]
    linarith only [principal_error_of_phase_632 hr
        (section99_abel_to31445 hRH ⟨le_of_not_ge h₂, h₃⟩)]
  rw [ite_eq_right h₃]
  by_cases h₄ : r ≤ 315
  · rw [ite_eq_left h₄]
    linarith only [principal_error_of_phase_632 hr (section99_abel_to315 hRH ⟨le_of_not_ge h₃, h₄⟩)]
  rw [ite_eq_right h₄]
  linarith only [principal_error_of_phase_632 hr (section99_abel_to316 hRH ⟨le_of_not_ge h₄, hr.2⟩)]

end PseudoPrime.PrimeTestBounds.MillerRabin
