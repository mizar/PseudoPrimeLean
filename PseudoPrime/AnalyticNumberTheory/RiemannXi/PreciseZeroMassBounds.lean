/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.MidpointEulerBounds
public import PseudoPrime.Analysis.PrecisePiLogBound
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-! # Precise rational bound for the Riemann zero mass -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The Riemann zero mass is at most 233/10000.
Use the midpoint upper bound for the Euler constant and the certified lower
bound 2096/1831 for log pi in the closed formula. The other sign follows
from the existing coarse bounds. This supports correction constants 1.407 and 4.602. -/
theorem riemannZeroMass_le_233_div_10000 : riemannZeroMass ≤ (233 / 10000 : ℝ) := by
  have hlo := Analysis.log_pi_ge_2096_div_1831
  have hhi := Analysis.log_four_sub_log_pi_gt_twenty_four
  rw [Real.log_four_eq] at hhi
  rw [riemannZeroMass, abs_le, Real.log_mul (by norm_num only) Real.pi_ne_zero, Real.log_four_eq]
  constructor <;>
    nlinarith only [hlo, hhi, Real.log_two_gt_d9, Real.log_two_lt_d9,
      Real.one_half_lt_eulerMascheroniConstant, Analysis.eulerMascheroniConstant_le_5773_div_10000]

end PseudoPrime.AnalyticNumberTheory.RiemannXi
