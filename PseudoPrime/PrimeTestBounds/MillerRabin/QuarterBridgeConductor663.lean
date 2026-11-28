/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663

/-! # Principal and shifted conductor estimates on the quarter-square bridge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem bridge_decay {l : ℝ} {n : ℕ} {P : ℚ} (hl : 0 ≤ l) (hn₀ : 0 < n)
    (hn : (n : ℝ) ≤ l ^ 2)
    (hc : AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck n 0 P 3 5 = true) :
    l ^ (-(6 / 5) : ℝ) ≤ (P : ℝ) := by
  have h := (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound hc).2
  rw [show (-(6 / 5 : ℝ)) = ((2 : ℕ) : ℝ) * (-(3 / 5)) by norm_num only, Real.rpow_natCast_mul hl]
  exact
    (Real.rpow_le_rpow_of_nonpos (Nat.cast_pos.mpr hn₀) hn (by norm_num only)).trans
      (by simpa only [Rat.cast_natCast, Nat.cast_ofNat, neg_div] using h)

private theorem main_from_right {r u z P C : ℝ} (hr : 328 ≤ r) (hu : r ≤ u)
    (hz : 2 * Real.log u ≤ z) (hP : u ^ (-(6 / 5) : ℝ) ≤ P)
    (hc : (11 / 10 : ℝ) ^ 5 / 30 * P * (0.055715328 * (z + 21 / 8) ^ 5) ≤ C)
    (hd : (11 / 10 : ℝ) ^ 5 / 30 * 0.00000365 * (0.055715328 * (z + 21 / 8) ^ 5) ≤ 0.007) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C + 0.007 * (u - r) := by
  exact main_conductor_box ((by norm_num only : (322 : ℝ) ≤ 328).trans hr) hu hz hP hc hd

/-- The main conductor term at radius 329, with an affine allowance to its left. -/
theorem quarter_bridge_main_658 {r : ℝ} (hr : r ∈ Set.Icc 328 329) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.656685 + 0.007 * (329 - r) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 329) (j := 9) (n := 27) (lo := 5) (hi :=
        11.592116 / 2) (by decide +kernel)).2
  have hd :=
    bridge_decay (l := 329) (n := 108241) (P := 0.000953598) (by norm_num only) (by decide)
      (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlog hd
  exact
    main_from_right (z := 11.592116) hr.1 hr.2 (by linarith only [hlog]) hd (by norm_num only)
      (by norm_num only)

/-- The main conductor term at radius 330, with an affine allowance to its left. -/
theorem quarter_bridge_main_660 {r : ℝ} (hr : r ∈ Set.Icc 329 330) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.654188 + 0.007 * (330 - r) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 330) (j := 9) (n := 27) (lo := 5) (hi :=
        11.598186 / 2) (by decide +kernel)).2
  have hd :=
    bridge_decay (l := 330) (n := 108900) (P := 0.000950131) (by norm_num only) (by decide)
      (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlog hd
  exact
    main_from_right (z := 11.598186) ((by norm_num only : (328 : ℝ) ≤ 329).trans hr.1) hr.2
      (by linarith only [hlog]) hd (by norm_num only) (by norm_num only)

/-- The main conductor term at radius 663/2, with an affine allowance to its left. -/
theorem quarter_bridge_main_663 {r : ℝ} (hr : r ∈ Set.Icc 330 (663 / 2)) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.650466 + 0.007 * (663 / 2 - r) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 27) (lo := 5) (hi :=
        11.607256 / 2) (by decide +kernel)).2
  have hd :=
    bridge_decay (l := 663 / 2) (n := 109892) (P := 0.000944976) (by norm_num only) (by decide)
      (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlog hd
  exact
    main_from_right (z := 11.607256) ((by norm_num only : (328 : ℝ) ≤ 330).trans hr.1) hr.2
      (by linarith only [hlog]) hd (by norm_num only) (by norm_num only)

private theorem aux_from_endpoints {l u r a b P C : ℝ} (hl : 0 < l) (hr : r ∈ Set.Icc l u)
    (ha : 0 ≤ a) (hlo : a ≤ 2 * Real.log l - 23 / 2) (hhi : 2 * Real.log u - 23 / 2 ≤ b)
    (hP : l ^ (-(6 / 5) : ℝ) ≤ P) (hB : 0 ≤ thetaIntervalUpper663 a b)
    (hC : C ≤ -(11 / 10) ^ 5 / 30 * P * thetaIntervalUpper663 a b + 18.29172549 / u) :
    C ≤ quarterAuxTheta663 r + quarterAuxNegPole663 / r := by
  have hp := hl.trans_le hr.1
  have hlog₁ := Real.log_le_log hl hr.1
  have hlog₂ := Real.log_le_log hp hr.2
  exact
    hC.trans
      (theta_pole_lower_663 hp hr.2 ha
        ⟨by linarith only [hlo, hlog₁], by linarith only [hhi, hlog₂]⟩
        ((Real.rpow_le_rpow_of_nonpos hl hr.1 (by norm_num only)).trans hP) hB)

/-- The shifted conductor and negative half-point residue have one lower
bound on the quarter-square interval ending at log 658. -/
theorem quarter_bridge_aux_658 {r : ℝ} (hr : r ∈ Set.Icc 328 (329)) :
    -2.46920 ≤ quarterAuxTheta663 r + quarterAuxNegPole663 / r := by
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo :=
        (23 / 2 + 0.086027) / 2) (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 329) (j := 9) (n := 27) (lo := 5) (hi :=
        (23 / 2 + 0.092116) / 2) (by decide +kernel)).2
  have hd :=
    bridge_decay (l := 328) (n := 107584) (P := 0.000957087) (by norm_num only) (by decide)
      (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hhi hd
  apply
    aux_from_endpoints (a := 0.086027) (b := 0.092116) (by norm_num only) hr (by norm_num only)
      (by linarith only [hlo]) (by linarith only [hhi]) hd
  all_goals
    norm_num only [thetaIntervalUpper663, thetaCoeffUpper663, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Rat.cast_ofScientific,
      Rat.cast_neg, ite_eq_left, ite_eq_right]

/-- The shifted conductor and negative half-point residue have one lower
bound on the quarter-square interval ending at log 660. -/
theorem quarter_bridge_aux_660 {r : ℝ} (hr : r ∈ Set.Icc 329 (330)) :
    -2.46430 ≤ quarterAuxTheta663 r + quarterAuxNegPole663 / r := by
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 329) (j := 9) (n := 27) (lo :=
        (23 / 2 + 0.092115) / 2) (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 330) (j := 9) (n := 27) (lo := 5) (hi :=
        (23 / 2 + 0.098186) / 2) (by decide +kernel)).2
  have hd :=
    bridge_decay (l := 329) (n := 108241) (P := 0.000953598) (by norm_num only) (by decide)
      (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hhi hd
  apply
    aux_from_endpoints (a := 0.092115) (b := 0.098186) (by norm_num only) hr (by norm_num only)
      (by linarith only [hlo]) (by linarith only [hhi]) hd
  all_goals
    norm_num only [thetaIntervalUpper663, thetaCoeffUpper663, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Rat.cast_ofScientific,
      Rat.cast_neg, ite_eq_left, ite_eq_right]

/-- The shifted conductor and negative half-point residue have one lower
bound on the quarter-square interval ending at log 663. -/
theorem quarter_bridge_aux_663 {r : ℝ} (hr : r ∈ Set.Icc 330 (663 / 2)) :
    -2.46157 ≤ quarterAuxTheta663 r + quarterAuxNegPole663 / r := by
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 330) (j := 9) (n := 27) (lo :=
        (23 / 2 + 0.098185) / 2) (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 27) (lo := 5) (hi :=
        (23 / 2 + 0.107256) / 2) (by decide +kernel)).2
  have hd :=
    bridge_decay (l := 330) (n := 108900) (P := 0.000950131) (by norm_num only) (by decide)
      (by norm_num only) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hhi hd
  apply
    aux_from_endpoints (a := 0.098185) (b := 0.107256) (by norm_num only) hr (by norm_num only)
      (by linarith only [hlo]) (by linarith only [hhi]) hd
  all_goals
    norm_num only [thetaIntervalUpper663, thetaCoeffUpper663, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Rat.cast_ofScientific,
      Rat.cast_neg, ite_eq_left, ite_eq_right]

private theorem bridge_conductor_combine {r u a C : ℝ} (hr : 0 ≤ r) (hu : r ≤ u)
    (ha : a ≤ quarterAuxTheta663 r + quarterAuxNegPole663 / r)
    (hC : 4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ C + 0.007 * (u - r)) :
    -0.0319746789 * u + a - C ≤
      -(3 / 4 - 0.71780481 + quarterAuxMix663 quarterConductorProfile663 + quarterAuxHalfCoeff663) *
            r +
          quarterAuxTheta663 r +
          quarterAuxNegPole663 / r -
        4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re := by
  linarith only [quarter_aux_deficit_663 hr, hu, ha, hC]

/-- On each bridge cell, use the right endpoint for the combined linear
deficit and principal conductor, and enclose the shifted terms separately. -/
theorem quarter_bridge_conductor_lower {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    (if r ≤ 329 then -14.645555 else if r ≤ 330 then -14.670133 else -14.711643) ≤
      -(3 / 4 - 0.71780481 + quarterAuxMix663 quarterConductorProfile663 + quarterAuxHalfCoeff663) *
            r +
          quarterAuxTheta663 r +
          quarterAuxNegPole663 / r -
        4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re := by
  have h₀ : (0 : ℝ) ≤ r := (by norm_num only : (0 : ℝ) ≤ 328).trans hr.1
  by_cases h₁ : r ≤ 329
  · rw [ite_eq_left h₁]
    exact
      (by norm_num only : (-14.645555 : ℝ) ≤ -0.0319746789 * 329 - 2.46920 - 1.656685).trans
        (bridge_conductor_combine h₀ h₁ (quarter_bridge_aux_658 ⟨hr.1, h₁⟩)
          (quarter_bridge_main_658 ⟨hr.1, h₁⟩))
  by_cases h₂ : r ≤ 330
  · rw [ite_eq_right h₁, ite_eq_left h₂]
    have hr₂ : r ∈ Set.Icc 329 330 := ⟨le_of_not_ge h₁, h₂⟩
    exact
      (by norm_num only : (-14.670133 : ℝ) ≤ -0.0319746789 * 330 - 2.46430 - 1.654188).trans
        (bridge_conductor_combine h₀ h₂ (quarter_bridge_aux_660 hr₂) (quarter_bridge_main_660 hr₂))
  · rw [ite_eq_right h₁, ite_eq_right h₂]
    have hr₃ : r ∈ Set.Icc 330 (663 / 2) := ⟨le_of_not_ge h₂, hr.2⟩
    have hn : (-14.711643 : ℝ) ≤ -0.0319746789 * (663 / 2) - 2.46157 - 1.650466 := by norm_num only
    exact
      hn.trans
        (bridge_conductor_combine h₀ hr.2 (quarter_bridge_aux_663 hr₃)
          (quarter_bridge_main_663 hr₃))

end PseudoPrime.PrimeTestBounds.MillerRabin
