/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundCountPhase
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundPhaseNumerics
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundRiemannVonMangoldt
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.BacklundGammaCellPrimitive
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountRightLimit

/-! # Explicit zero-count budget under RH -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The good-height phase bound extends to all positive heights by right
continuity of the zero count and continuity of the explicit error budget. -/
private theorem sharp_count_of_euler_phase {E : ℝ → ℝ} (hid : EulerPhaseCountIdentity E)
    (hE : ∀ t : ℝ, 2 * Real.pi * Real.exp 1 ≤ t → |E t| ≤ 1 / (5 * t)) :
    ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
      |positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        (3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t) := by
  intro t ht
  have ha : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have ht0 : 0 < t := lt_of_lt_of_le ha ht
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := ne_of_gt (mul_pos (by norm_num only) Real.pi_pos)
  have hv : t / (2 * Real.pi) ≠ 0 := div_ne_zero ht0.ne' hpi
  have hdiv : ContinuousAt (fun u : ℝ ↦ u / (2 * Real.pi)) t := continuousAt_id.div_const _
  have hc : ContinuousAt (fun u : ℝ ↦ (3 / 8 : ℝ) * Real.log u + 8 / 5 + 1 / (5 * u)) t :=
    ((continuousAt_const.mul (Real.continuousAt_log ht0.ne')).add continuousAt_const).add
      (continuousAt_const.div (continuousAt_const.mul continuousAt_id)
        (mul_ne_zero (by norm_num only) ht0.ne'))
  apply
    positiveZeroCount_bound_of_good ha.le ht
      (((hdiv.mul (hdiv.log hv)).sub hdiv).add continuousAt_const) hc
  intro u hu hgood
  have hp : (157 / 50 : ℝ) ≤ Real.pi := by linarith only [Real.pi_gt_d2]
  have he : (163 / 60 : ℝ) ≤ Real.exp 1 := by linarith only [Real.exp_one_gt_d9]
  have hpe := mul_le_mul hp he (by norm_num only : (0 : ℝ) ≤ 163 / 60) Real.pi_pos.le
  have hu17 : (17 : ℝ) ≤ u := by nlinarith only [hpe, hu]
  obtain ⟨φ, hcont, hpolar, hnorm, hbound⟩ := exists_euler_arg_coarse hu17 hgood
  change
    |positiveZeroCount u -
          (u / (2 * Real.pi) * Real.log (u / (2 * Real.pi)) - u / (2 * Real.pi) + 7 / 8)| ≤
      (3 / 8 : ℝ) * Real.log u + 8 / 5 + 1 / (5 * u)
  rw [hid u hu hgood φ hcont hpolar hnorm]
  have hS : |φ (1 / 2) / Real.pi| ≤ (3 / 8 : ℝ) * Real.log u + 8 / 5 := by
    simpa only [abs_div, abs_of_pos Real.pi_pos] using hbound
  calc
    |φ (1 / 2) / Real.pi + E u| ≤ |φ (1 / 2) / Real.pi| + |E u| := abs_add_le _ _
    _ ≤ (3 / 8 : ℝ) * Real.log u + 8 / 5 + 1 / (5 * u) := add_le_add hS (hE u hu)

/-- Under RH, the positive-height zero-count error is at most
`(3/8) * log t + 8/5 + 1/(5*t)` for every `t ≥ 2πe`. The good-height
phase estimate is extended to zero ordinates by the right-limit theorem. -/
theorem positive_zero_count_budget_of_RH (hRH : RiemannHypothesis) :
    ∀ t ∈ Set.Ici (2 * Real.pi * Real.exp 1),
      |positiveZeroCount t -
            (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)| ≤
        (3 / 8 : ℝ) * Real.log t + 8 / 5 + 1 / (5 * t) := by
  apply
    sharp_count_of_euler_phase
      (euler_phase_count_of_riemann_von_mangoldt (euler_riemann_von_mangoldt_of_RH hRH))
  intro t ht
  have hbase : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have hR :=
    gamma_remainder_bounds_of_integral
      (gamma_remainder_identity_of_complex backlund_gamma_complex_identity) t ht
  have hG := backlundTheta_error_of_signed_remainder (hbase.trans_le ht) hR.1 hR.2
  exact theta_error_le_of_phase (hbase.trans_le ht) hG

/-- Under RH, the two-sided zero-count error at each `t ≥ 2πe` is at most
`(3/4) * log t + 16/5 + 2/(5*t)`. Conjugation transfers the positive-height
budget to the symmetric count used in zero-tail estimates. -/
theorem zero_count_budget_of_RH (hRH : RiemannHypothesis) {t : ℝ}
    (ht : 2 * Real.pi * Real.exp 1 ≤ t) :
    |zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4)| ≤
      (3 / 4 : ℝ) * Real.log t + 16 / 5 + 2 / (5 * t) := by
  have hbase : 0 < 2 * Real.pi * Real.exp 1 :=
    mul_pos (mul_pos (by norm_num only) Real.pi_pos) (Real.exp_pos 1)
  have ht0 : 0 < t := hbase.trans_le ht
  have hpi : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have hlog := Real.log_div ht0.ne' hpi.ne'
  have hcount := zeroCount_eq_two_positive hRH ht0.le
  have hterm := positive_zero_count_budget_of_RH hRH t ht
  have heq :
    zeroCount t - ((1 / Real.pi) * t * (Real.log t - Real.log (2 * Real.pi) - 1) + 7 / 4) =
      2 *
        (positiveZeroCount t -
          (t / (2 * Real.pi) * Real.log (t / (2 * Real.pi)) - t / (2 * Real.pi) + 7 / 8)) := by
    rw [hcount, hlog]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  have h := mul_le_mul_of_nonneg_left hterm (show (0 : ℝ) ≤ 2 by norm_num only)
  convert h using 1
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
