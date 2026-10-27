/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRefinedTailGeometry
public import PseudoPrime.LLS.GammaNonOneRefinedNumerics
public import PseudoPrime.LLS.GammaVariablePrincipalBounds

/-! # Explicit error budgets at logarithmic scales at least 15000 -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For L at least 15000, root at least (9/16)L and Q at most L+2,
the pole error is at most 21/10. Clear the positive root denominator
and compare rational coefficients. This does not require a fixed profile. -/
theorem gamma_tail_pole_budget {L x Q : ℝ} (hL : 15000 ≤ L) (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x)
    (hQ : Q ≤ L + 2) : ((7 / 6 : ℝ) * Q + 4) / Real.sqrt x ≤ 21 / 10 := by
  have hs : 0 < Real.sqrt x := by linarith only [hL, hroot]
  rw [div_le_iff₀ hs]
  nlinarith only [hL, hroot, hQ]

/-- For L at least 15000, x at least 3^16 and root at least (9/16)L,
the sharp left-contour error is at most one when 0 ≤ Q ≤ L+2.
Use the decay anchor three and clear the positive denominator.
This retains the sharp left moments rather than the older coarse envelope. -/
theorem gamma_tail_sharp_left_budget {L x Q : ℝ} (hL : 15000 ≤ L) (hx : (3 : ℝ) ^ 16 ≤ x)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hQ0 : 0 ≤ Q) (hQ : Q ≤ L + 2) :
    x ^ (-9 / 16 : ℝ) * ((3 / 2) * (Q + 28) + 1) ≤ 1 := by
  have hs : 0 < Real.sqrt x := by linarith only [hroot, hL]
  have hC : 0 ≤ (3 / 2 : ℝ) * (Q + 28) + 1 := by linarith only [hQ0]
  have hm :=
    mul_le_mul_of_nonneg_right
      (rpow_neg_nine_sixteenths_le_div_scale_sqrt (by norm_num only : (0 : ℝ) < 3) hx) hC
  apply hm.trans
  rw [one_div, mul_comm, ← div_eq_mul_inv,
    div_le_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 3) hs)]
  nlinarith only [hroot, hL, hQ]

/-- If L is at least 15000, root is at least (9/16)L and log X is
at most (20/15000)L, the combined principal and ramp envelope is at most
15. The coefficient 174 includes the two log x terms of the principal bound.
Clear the positive denominator and compare rational coefficients. -/
theorem gamma_tail_principal_ramp_envelope {L x X : ℝ} (hL : 15000 ≤ L)
    (hroot : (9 / 16 : ℝ) * L ≤ Real.sqrt x) (hlog : Real.log X ≤ (20 / 15000 : ℝ) * L) :
    (109 / 8 : ℝ) + (174 * (1839 / 1000) * Real.log X + 188217 / 1000) / Real.sqrt x ≤ 15 := by
  have hs : 0 < Real.sqrt x := by linarith only [hroot, hL]
  have hnum :
    174 * (1839 / 1000 : ℝ) * Real.log X + 188217 / 1000 ≤ (15 - 109 / 8) * Real.sqrt x := by
    nlinarith only [hroot, hL, hlog]
  have hd := (div_le_iff₀ hs).mpr hnum
  linarith only [hd]

/-- Under RH, every tail profile with L at least 15000 and shift between
ten and fifteen has actual combined principal and ramp error at most 15.
Combine the variable-scale one-sided bounds before applying the certified
rational envelope. This supplies the principal input of the tail comparison. -/
theorem gamma_tail_actual_principal_ramp_error (hRH : RiemannHypothesis) {L c : ℝ} (hL : 15000 ≤ L)
    (hc : 10 ≤ c) (hcu : c ≤ 15) :
    let x := Analysis.gammaTailProfileScale L c
    (∑' n : ℕ, gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re -
          2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) +
        (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x ≤
      15 := by
  dsimp only
  let x := Analysis.gammaTailProfileScale L c
  have hx : 1 ≤ x :=
    (by norm_num only : (1 : ℝ) ≤ 3 ^ 16).trans (Analysis.gamma_tail_scale_large hL hc)
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hp := LLS.gamma_level_one_sum_upper_variable hRH hx
  have hr := LLS.gamma_ramp_sum_lower_variable hRH hx
  have hlog : Real.log x ≤ Real.log ((99 / 40 : ℝ) * x) :=
    Real.log_le_log (zero_lt_one.trans_le hx) (by nlinarith only [hx] : x ≤ (99 / 40 : ℝ) * x)
  have he :=
    gamma_tail_principal_ramp_envelope hL (Analysis.gamma_tail_scale_sqrt_lower hL hc)
      (Analysis.gamma_tail_cutoff_log_upper hL hc hcu)
  change
    (109 / 8 : ℝ) +
        (174 * (1839 / 1000) * Real.log ((99 / 40 : ℝ) * x) + 188217 / 1000) / Real.sqrt x ≤
      15 at he
  have hn :=
    (div_le_iff₀ hs).mp
      (show
        (174 * (1839 / 1000 : ℝ) * Real.log ((99 / 40 : ℝ) * x) + 188217 / 1000) / Real.sqrt x ≤
          15 - 109 / 8
        by linarith only [he])
  have hd :
    ((Real.sqrt x / 8 + (1839 / 1000 : ℝ) * (2 * Real.log x + 3) + 21 / 10) +
          2 *
            ((135 / 20 : ℝ) * Real.sqrt x +
              86 * ((1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20))) /
        Real.sqrt x ≤
      15 := by
    rw [div_le_iff₀ hs, mul_comm x (99 / 40)]
    nlinarith only [hn, hlog]
  rw [add_div, mul_div_assoc] at hd
  linarith only [hp, hr, hd]

end PseudoPrime.LLS.PaperStatements
