/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.HadamardLimit
public import PseudoPrime.Analysis.EulerMascheroniBounds
public import PseudoPrime.Analysis.NumericalLogBounds
public import Mathlib.Tactic

/-! # General bounds and arithmetic certificates -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- A coarse rational upper bound for the Riemann zero-mass constant used by downstream modules. -/
theorem riemannZeroMass_lt_three_twentieths : riemannZeroMass < (3 / 20 : ℝ) := by
  have hlogPiLower : Real.log 3 < Real.log Real.pi :=
    Real.strictMonoOn_log (by norm_num only [Set.mem_Ioi]) Real.pi_pos Real.pi_gt_three
  have hlogPiUpper : Real.log Real.pi < Real.log 4 :=
    Real.strictMonoOn_log Real.pi_pos (by norm_num only [Set.mem_Ioi]) Real.pi_lt_four
  rw [Real.log_four_eq] at hlogPiUpper
  have hgammaLower := Real.one_half_lt_eulerMascheroniConstant
  have hgammaUpper := Real.eulerMascheroniConstant_lt_two_thirds
  rw [riemannZeroMass, abs_lt]
  rw [Real.log_mul (by norm_num only) Real.pi_ne_zero, Real.log_four_eq]
  constructor <;>
    nlinarith only [hlogPiLower, hlogPiUpper, hgammaLower, hgammaUpper, Real.log_two_gt_d9,
      Real.log_two_lt_d9, Real.log_three_gt_d9]

/-- The existing strict zero-mass estimate also supplies the closed upper bound used here. -/
theorem riemannZeroMass_le_three_twentieths : riemannZeroMass ≤ (3 / 20 : ℝ) :=
  riemannZeroMass_lt_three_twentieths.le

/-- A rational zero-mass bound strong enough for the strict S2 comparison.
The closed formula is bounded using certified estimates for the Euler constant,
`log 2`, `log 3`, and `log(4/π)`; no numerical oracle is used. -/
theorem riemannZeroMass_le_one_sixteenth : riemannZeroMass ≤ (1 / 16 : ℝ) := by
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 3) Real.pi_gt_three.le
  have hhi := Analysis.log_four_sub_log_pi_gt_twenty_four
  rw [Real.log_four_eq] at hhi
  rw [riemannZeroMass, abs_le, Real.log_mul (by norm_num only) Real.pi_ne_zero, Real.log_four_eq]
  constructor <;>
    nlinarith only [hlo, hhi, Real.log_two_gt_d9, Real.log_two_lt_d9, Real.log_three_gt_d9,
      Real.one_half_lt_eulerMascheroniConstant,
      Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths]

/-- The Riemann zero mass is at most `1/40`.
Rational bounds for the Euler constant, pi, and elementary logarithms control both
signs of its closed formula. This yields coefficient `1/20` in RH weighted-sum errors. -/
theorem riemannZeroMass_le_one_fortieth : riemannZeroMass ≤ (1 / 40 : ℝ) := by
  have hpi : Real.pi ≤ (22 / 7 : ℝ) := Real.pi_lt_d4.le.trans (by norm_num only)
  have hlo :=
    Analysis.log_gt_affine_of_anchor (a := (3 : ℝ)) (b := 22 / 7) (y := Real.pi) (L := 1.0986122885)
      (by norm_num only) (by norm_num only) Real.pi_gt_three.le hpi Real.log_three_gt_d9
  have hhi := Analysis.log_four_sub_log_pi_gt_twenty_four
  rw [Real.log_four_eq] at hhi
  rw [riemannZeroMass, abs_le, Real.log_mul (by norm_num only) Real.pi_ne_zero, Real.log_four_eq]
  constructor <;>
    nlinarith only [hlo, hhi, Real.pi_gt_d4, Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.one_half_lt_eulerMascheroniConstant,
      Analysis.eulerMascheroniConstant_lt_twentyNine_fiftieths]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
