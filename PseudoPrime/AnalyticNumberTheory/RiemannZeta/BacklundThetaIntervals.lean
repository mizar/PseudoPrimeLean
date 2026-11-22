/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundTheta
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith

/-! # Endpoint bounds for the elementary main Gamma phase -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Rational bounds for pi and logarithms at positive ratio endpoints enclose the
main Gamma phase at a nonnegative height. The proof first bounds t/(2*pi), then
uses logarithm monotonicity; concrete endpoint certificates supply the inputs. -/
theorem backlund_main_bounds {t p P a b l u : ℝ} (ht : 0 ≤ t) (hpπ : p ≤ Real.pi)
    (hπP : Real.pi ≤ P) (ha : 0 < a) (hb : 0 ≤ b) (hat : 2 * P * a ≤ t) (htb : t ≤ 2 * p * b)
    (hl : l ≤ Real.log a) (hu : Real.log b ≤ u) :
    t / 2 * l - t / 2 - P / 8 ≤ backlundThetaMain t ∧
      backlundThetaMain t ≤ t / 2 * u - t / 2 - p / 8 := by
  have hd : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hla : a ≤ t / (2 * Real.pi) := by
    apply (le_div_iff₀ hd).2
    nlinarith only [hat, mul_le_mul_of_nonneg_right hπP ha.le]
  have hub : t / (2 * Real.pi) ≤ b := by
    apply (div_le_iff₀ hd).2
    nlinarith only [htb, mul_le_mul_of_nonneg_right hpπ hb]
  have hlogl := hl.trans (Real.log_le_log ha hla)
  have hlogu := (Real.log_le_log (ha.trans_le hla) hub).trans hu
  unfold backlundThetaMain
  constructor <;>
    nlinarith only [mul_le_mul_of_nonneg_left hlogl ht, mul_le_mul_of_nonneg_left hlogu ht, hpπ,
      hπP]

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
