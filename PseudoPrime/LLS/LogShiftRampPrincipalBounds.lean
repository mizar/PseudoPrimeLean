/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.VariableRampPrincipalBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogShiftStencilBounds

/-! # Principal comparison retaining the logarithmic correction in the stencil -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH at t greater than one, the corrected smoothed error has absolute
value at most sqrt(t)/20+21/20. Retain log(2 pi)log t in the explicit formula and bound
only the zero mass and trivial-zero tail. This avoids a logarithmic stencil error. -/
theorem logWeightedMangoldtSum_log_shift_error_le (hRH : RiemannHypothesis) {t : ℝ} (ht : 1 < t) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t +
          Real.log (2 * Real.pi) * Real.log t| ≤
      Real.sqrt t / 20 + 21 / 20 := by
  have he := abs_le.mp (abs_logWeightedMangoldtSum_error_le hRH ht)
  have hm :=
    mul_le_mul_of_nonneg_right AnalyticNumberTheory.RiemannXi.riemannZeroMass_le_one_fortieth
      (add_nonneg (Real.sqrt_nonneg t) zero_le_one)
  have hb :=
    AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries_le_pi_sq_div_twenty_four ht
  have hz : 0 ≤ AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries t := by
    apply tsum_nonneg
    intro k
    exact
      div_nonneg (pow_nonneg (inv_nonneg.mpr (zero_lt_one.trans ht).le) _)
        (mul_nonneg (by norm_num only) (sq_nonneg _))
  rw [abs_le]
  constructor
  · linarith only [he.1, hm, hb]
  · nlinarith only [he.2, hm, hz, Real.pi_lt_four, Real.pi_pos, sq_nonneg (Real.pi - 4)]

/-- The corrected three-point envelope sqrt(x)/10+21/20 on the enlarged ramp.
It applies for x at least one, width at most x and all three arguments greater than one.
The logarithmic correction remains in the arithmetic function instead of this envelope. -/
noncomputable def logShiftRampEnvelope (x : ℝ) : ℝ :=
  Real.sqrt x / 10 + 21 / 20

/-- Under RH, x at least one and t greater than one below (139/40)x, the corrected
smoothed error is bounded by the logarithm-free envelope. Bound sqrt t by 2sqrt x.
This supplies each endpoint of a variable-width corrected stencil. -/
theorem logWeighted_log_shift_error_le_ramp (hRH : RiemannHypothesis) {x t : ℝ} (hx : 1 ≤ x)
    (ht : 1 < t) (htb : t ≤ (139 / 40 : ℝ) * x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t +
          Real.log (2 * Real.pi) * Real.log t| ≤
      logShiftRampEnvelope x := by
  have he := logWeightedMangoldtSum_log_shift_error_le hRH ht
  have hs : Real.sqrt t ≤ 2 * Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    exact
      ⟨mul_nonneg (by norm_num only) (Real.sqrt_nonneg x), by
        nlinarith only [htb, Real.sq_sqrt (by linarith only [hx] : 0 ≤ x)]⟩
  dsimp only [logShiftRampEnvelope]
  linarith only [he, hs]

/-- The short-ramp error allowance retaining log(2 pi) in the stencil.
For scale x and positive width h it equals [x/200+h+2E(x)((99/40)x+h)/h+log(2 pi)]/494.
It bounds the actual uncorrected smoothed-error increment and feeds the joint comparison. -/
noncomputable def logShiftRampIncrement (x h : ℝ) : ℝ :=
  (x / 200 + h + 2 * logShiftRampEnvelope x * ((99 / 40 : ℝ) * x + h) / h +
      Real.log (2 * Real.pi)) /
    494

/-- Under RH at x at least one and 0<h<=x, the actual short-ramp smoothed-error
increment is at most the corrected allowance. Apply the logarithm-shift stencil at all
three arguments and normalize the ramp endpoint ratio. This connects the removed logarithmic
stencil cost to the arithmetic sum used by witness extraction. -/
theorem logWeighted_error_increment_log_shift_ramp (hRH : RiemannHypothesis) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) :
    |(AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (99 / 40)) - x * (99 / 40)) -
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (247 / 100)) -
            x * (247 / 100))| ≤
      logShiftRampIncrement x h := by
  have hx0 : 0 < x := by linarith only [hx]
  have ha : 0 < x * (247 / 100 : ℝ) - h := by nlinarith only [hx, hhx]
  have hab : x * (247 / 100 : ℝ) ≤ x * (99 / 40 : ℝ) := by nlinarith only [hx]
  have hc : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
  have hE :
    ∀ t ∈ Set.Icc (x * (247 / 100 : ℝ)) (x * (99 / 40 : ℝ)),
      |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (t - h) - (t - h) +
              Real.log (2 * Real.pi) * Real.log (t - h)| ≤
          logShiftRampEnvelope x ∧
        |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t +
              Real.log (2 * Real.pi) * Real.log t| ≤
          logShiftRampEnvelope x ∧
        |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (t + h) - (t + h) +
              Real.log (2 * Real.pi) * Real.log (t + h)| ≤
          logShiftRampEnvelope x := by
    intro t ht
    have hl : 1 < t - h := by nlinarith only [hx, hhx, ht.1]
    have ht0 : 1 < t := by linarith only [hl, hh]
    exact
      ⟨logWeighted_log_shift_error_le_ramp hRH hx hl (by nlinarith only [ht.2, hx, hh]),
        logWeighted_log_shift_error_le_ramp hRH hx ht0 (by nlinarith only [ht.2, hx]),
        logWeighted_log_shift_error_le_ramp hRH hx (by linarith only [ht0, hh])
          (by nlinarith only [ht.2, hhx])⟩
  have he :=
    AnalyticNumberTheory.Arithmetic.logWeighted_error_increment_le_of_log_shift_stencil hc hh ha hab
      hE
  have hid :
    ((x * (99 / 40 : ℝ) - x * (247 / 100)) +
            (h + 2 * logShiftRampEnvelope x * (x * (99 / 40) + h) / h + Real.log (2 * Real.pi))) *
          (x * (99 / 40) - x * (247 / 100)) /
        (x * (247 / 100)) =
      logShiftRampIncrement x h := by
    dsimp only [logShiftRampIncrement]
    field_simp (disch :=
      first
      | exact hx0.ne'
      | exact hh.ne'
      | norm_num only)
    ring
  exact he.trans_eq hid

/-- The joint error budget with a freely chosen stencil width h at scale x.
Replace only the short-ramp increment allowance in the existing joint comparison.
The resulting bound retains the common-error cancellation through the principal series. -/
noncomputable def logShiftRampPrincipalErrorNumerator (x h : ℝ) : ℝ :=
  (17 / 10 : ℝ) *
      (Real.sqrt x / 20 * (63 / 40 : ℝ) + (1839 / 1000 : ℝ) * Real.log (x * (99 / 40)) + 21 / 20) +
    84 * logShiftRampIncrement x h +
    (21 / 100 : ℝ) * (Real.sqrt x / 40 + (1839 / 1000 : ℝ) * Real.log x + 21 / 20) +
    (13 / 16 : ℝ) * (Real.sqrt x / 40 + 1839 / 1000)

/-- Under RH and x at least one, the actual scaled Mangoldt error has its joint functional
bounded uniformly at every principal cutoff beyond the ramp. Supply continuity on that finite
interval, the compact RH envelope, the short-ramp increment and the affine tail envelope.
This transfers common-density cancellation to the arithmetic function. -/
theorem jointRampPrincipal_actual_error_bound_log_shift_width (hRH : RiemannHypothesis) {x y h : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (hy : (99 / 40 : ℝ) ≤ y) :
    |AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional
          (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) y| ≤
      logShiftRampPrincipalErrorNumerator x h := by
  have hx0 := zero_lt_one.trans_le hx
  have hf :
    ContinuousOn (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.Icc 0 y) :=
    (AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx0 y).sub
      (continuous_const.mul continuous_id).continuousOn
  apply AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional_abs_le hy hf
  · intro u hu
    have hs :=
      mul_le_mul_of_nonneg_left (Analysis.sqrt_le_ramp_right hu.2)
        (div_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 20))
    have he := logWeightedMangoldtSum_scaled_ramp_error hRH hx hu.1 hu.2
    linarith only [he, hs]
  · exact logWeighted_error_increment_log_shift_ramp hRH hx hh hhx
  · linarith only [Real.sqrt_nonneg x, Real.log_nonneg hx]
  · linarith only [Real.sqrt_nonneg x]
  · intro u hu
    have he := logWeighted_error_le_exponential_affine hRH hx (show 0 ≤ u by linarith only [hu.1])
    exact he.trans_eq (by ring)

/-- Under RH and x at least one, every finite exponential Mangoldt sum is bounded by x plus
twice the actual ramp error and the joint error budget. Use the lower side of the joint
functional norm bound, the exact main integral and the eventual-cutoff transfer. This preserves
the same ramp error through the passage to the principal series. -/
theorem exponentialMangoldtSum_upper_joint_error_log_shift_width (hRH : RiemannHypothesis) {x h : ℝ}
    (hx : 1 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (N : ℕ) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      x +
        (2 *
            AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
              (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
          logShiftRampPrincipalErrorNumerator x h) := by
  apply exponentialMangoldtSum_upper_of_eventual_integral_cap hRH hx (99 / 40)
  intro y hy0 hy
  rw [logWeighted_exponential_integral_eq_main_add_error (zero_lt_one.trans_le hx) hy0]
  have hb := (abs_le.mp (jointRampPrincipal_actual_error_bound_log_shift_width hRH hx hh hhx hy)).1
  dsimp only [AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional,
    Analysis.exponentialRampVariationLeft] at hb
  have ht : 0 ≤ x * (y ^ 2 + y + 1) * Real.exp (-y) := by
    apply mul_nonneg _ (Real.exp_pos _).le
    exact mul_nonneg (zero_lt_one.trans_le hx).le (by nlinarith only [sq_nonneg y, hy0])
  linarith only [hb, ht]

/-- The lower cap on twice the normalized ramp sum minus the principal Gamma sum. Its main
term is (2M-1)sqrt x and its error is the joint budget divided by sqrt x. The cap retains the
cancellation of the common arithmetic error before taking norms. -/
noncomputable def logShiftRampPrincipalLower (x h : ℝ) : ℝ :=
  (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x -
    logShiftRampPrincipalErrorNumerator x h / Real.sqrt x

/-- Under RH at any scale at least one, the joint lower cap bounds the actual difference of
twice the normalized ramp sum and the full principal Gamma series. Bound every finite principal
sum using the same ramp error, pass to the summable series, and cancel that error with the exact
ramp identity. This is the common principal input for witness extraction. -/
theorem logShiftRampPrincipalLower_le_actual (hRH : RiemannHypothesis) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) :
    logShiftRampPrincipalLower x h ≤
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        (∑' n : ℕ,
            PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hR :=
    AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum_normalized_eq_main_add_error hx0
  have hP :
    (∑' n : ℕ, PaperStatements.gammaMellinKernel.summand (1 : DirichletCharacter ℂ 1) x n).re ≤
      2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
        logShiftRampPrincipalLower x h := by
    apply PaperStatements.gamma_level_one_sum_upper_of_finite_upper hx0
    intro N
    have heq := PaperStatements.gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx0
    rw [Nat.floor_natCast] at heq
    rw [heq]
    apply (div_le_iff₀ hs).mpr
    have hb := exponentialMangoldtSum_upper_joint_error_log_shift_width hRH hx hh hhx N
    have he :
      (2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            logShiftRampPrincipalLower x h) *
          Real.sqrt x =
        x +
          (2 *
              AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
            logShiftRampPrincipalErrorNumerator x h) := by
      rw [hR]
      dsimp only [logShiftRampPrincipalLower]
      calc
        _ =
            (Real.sqrt x) ^ 2 +
              2 *
                ((AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                      (fun u ↦
                        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) /
                    Real.sqrt x) *
                  Real.sqrt x) +
              (logShiftRampPrincipalErrorNumerator x h / Real.sqrt x) * Real.sqrt x :=
          by ring
        _ = _ := by
          rw [Real.sq_sqrt hx0.le, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
          ring
    exact hb.trans_eq he.symm
  linarith only [hP]

/-- For x at least one and h positive, the corrected increment plus 1/494 is
strictly below the previous variable-width increment. Bound the removed logarithmic envelope
below using log three and bound log(2 pi) above. This verifies a uniform strict gain. -/
theorem logShiftRampIncrement_add_margin_lt_variable {x h : ℝ} (hx : 1 ≤ x) (hh : 0 < h) :
    logShiftRampIncrement x h + (1 / 494 : ℝ) < variableRampIncrement x h := by
  have hx0 : 0 < x := by linarith only [hx]
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 3)
      (show (3 : ℝ) ≤ (139 / 40 : ℝ) * x by linarith only [hx])
  have hlog : 1 ≤ Real.log ((139 / 40 : ℝ) * x) := by linarith only [hl, Real.log_three_gt_d9]
  have hp : h ≤ Real.log ((139 / 40 : ℝ) * x) * ((99 / 40 : ℝ) * x + h) := by
    have hm :=
      mul_le_mul_of_nonneg_right hlog (show 0 ≤ (99 / 40 : ℝ) * x + h by linarith only [hx0, hh])
    nlinarith only [hm, hx0]
  have hd : 1 ≤ Real.log ((139 / 40 : ℝ) * x) * ((99 / 40 : ℝ) * x + h) / h :=
    (le_div_iff₀ hh).mpr (by simpa only [one_mul] using hp)
  have he :
    variableRampIncrement x h - logShiftRampIncrement x h =
      ((1839 / 500 : ℝ) * (Real.log ((139 / 40 : ℝ) * x) * ((99 / 40 : ℝ) * x + h) / h) -
          Real.log (2 * Real.pi)) /
        494 := by
    dsimp only [variableRampIncrement, variableRampEnvelope, logShiftRampIncrement,
      logShiftRampEnvelope]
    ring
  have hc : Real.log (2 * Real.pi) ≤ (1839 / 1000 : ℝ) := Analysis.log_two_mul_pi_lt.le
  linarith only [hd, he, hc]

/-- For x at least one and positive width, the corrected principal cap exceeds
the previous cap by more than (42/247)/sqrt x. The increment occurs with coefficient 84.
Divide its strict gain by the positive square root. This establishes improvement at every
common scale rather than only at sampled inputs. -/
theorem logShiftRampPrincipalLower_gt_variable {x h : ℝ} (hx : 1 ≤ x) (hh : 0 < h) :
    variableRampPrincipalLower x h + (42 / 247 : ℝ) / Real.sqrt x <
      logShiftRampPrincipalLower x h := by
  have hd := logShiftRampIncrement_add_margin_lt_variable hx hh
  have hs := Real.sqrt_pos.mpr (zero_lt_one.trans_le hx)
  have hn :
    logShiftRampPrincipalErrorNumerator x h + (42 / 247 : ℝ) <
      variableRampPrincipalErrorNumerator x h := by
    dsimp only [logShiftRampPrincipalErrorNumerator, variableRampPrincipalErrorNumerator]
    linarith only [hd]
  have he := (div_lt_div_iff_of_pos_right hs).mpr hn
  dsimp only [variableRampPrincipalLower, logShiftRampPrincipalLower]
  rw [add_div] at he
  linarith only [he]

end PseudoPrime.LLS
