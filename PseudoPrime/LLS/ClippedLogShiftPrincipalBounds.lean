/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.LogShiftRampPrincipalBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.JointRampPrincipalLinearity
public import PseudoPrime.LLS.CertifiedRampPrincipalBounds

/-! # Continuous clipped logarithmic correction in the full principal comparison -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under RH at every nonnegative t, the smoothed error corrected by
log(2 pi)log(max(1,t)) is at most sqrt(t)/20+21/20. Use the explicit formula above one
and the vanishing arithmetic sum below one. This supplies a continuous global correction. -/
theorem logWeightedMangoldtSum_clipped_shift_error_le (hRH : RiemannHypothesis) {t : ℝ}
    (ht : 0 ≤ t) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t +
          Real.log (2 * Real.pi) * Real.log (max 1 t)| ≤
      Real.sqrt t / 20 + 21 / 20 := by
  by_cases h : 1 < t
  · rw [max_eq_right h.le]
    exact logWeightedMangoldtSum_log_shift_error_le hRH h
  · have hs := le_of_not_gt h
    rw [logWeightedMangoldtSum_eq_zero_of_le_one hs, max_eq_left hs, Real.log_one, mul_zero,
      add_zero, zero_sub, abs_neg, abs_of_nonneg ht]
    linarith only [hs, Real.sqrt_nonneg t]

/-- At positive scale x, the clipped logarithmic atom at 1/x equals log(max(1,xu))
for every real u. Compare xu with one and select the corresponding atom branch.
This identifies the continuous atom with the arithmetic correction. -/
theorem clippedLogAtom_eq_log_max {x u : ℝ} (hx : 0 < x) :
    Analysis.positiveLogRatio (1 / x) u = Real.log (max 1 (x * u)) := by
  by_cases h : x * u ≤ 1
  · have ha : u ≤ 1 / x := (le_div_iff₀ hx).mpr (by simpa only [mul_comm] using h)
    rw [Analysis.positiveLogRatio_zero ha, max_eq_left h, Real.log_one]
  · have ht := le_of_lt (lt_of_not_ge h)
    have ha : 1 / x ≤ u := (div_le_iff₀ hx).mpr (by simpa only [mul_comm] using ht)
    rw [Analysis.positiveLogRatio_eq_log ha, max_eq_right ht]
    congr 1
    field_simp (disch := exact hx.ne')

/-- The globally clipped corrected arithmetic error S(xu)-xu+c log(max(1,xu)),
where c=log(2 pi). Define the correction by the continuous positive logarithmic atom at 1/x.
Its uniform RH bound and exact atom reconstruction are used in the full principal comparison. -/
noncomputable def clippedShiftError (x u : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u +
    Real.log (2 * Real.pi) * Analysis.positiveLogRatio (1 / x) u

/-- At positive scale x, the corrected error is continuous on every [0,y].
Combine continuity of the finite clipped Mangoldt representation and the logarithmic atom.
This removes the origin obstruction without an improper-integral assumption. -/
theorem clippedShiftError_continuousOn {x : ℝ} (hx : 0 < x) (y : ℝ) :
    ContinuousOn (clippedShiftError x) (Set.Icc 0 y) := by
  have hA := AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx y
  have hL := Analysis.positiveLogRatio_continuous (one_div_pos.mpr hx)
  exact
    (hA.sub (continuous_const.mul continuous_id).continuousOn).add
      (continuous_const.mul hL).continuousOn

/-- Under RH, positive x and nonnegative u, the corrected error is bounded by
sqrt(xu)/20+21/20. Rewrite the atom as log(max(1,xu)) and use the global corrected bound.
This is the logarithm-free input for compact and tail envelopes. -/
theorem clippedShiftError_abs_le (hRH : RiemannHypothesis) {x u : ℝ} (hx : 0 < x) (hu : 0 ≤ u) :
    |clippedShiftError x u| ≤ Real.sqrt (x * u) / 20 + 21 / 20 := by
  dsimp only [clippedShiftError]
  rw [clippedLogAtom_eq_log_max hx]
  exact logWeightedMangoldtSum_clipped_shift_error_le hRH (mul_nonneg hx.le hu)

/-- For x at least one and y beyond the ramp, the joint functional of the clipped
logarithmic correction equals exp(-1/x)+exp(-y)(1+y log(xy)). Apply the exact ramp and
principal atom reconstructions. This retains both the finite endpoint and the constant term. -/
theorem clippedLogAtom_jointFunctional_eq {x y : ℝ} (hx : 1 ≤ x) (hy : (99 / 40 : ℝ) ≤ y) :
    AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional (Analysis.positiveLogRatio (1 / x))
        y =
      Real.exp (-(1 / x)) + Real.exp (-y) * (1 + y * Real.log (x * y)) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hv : 0 < 1 / x := one_div_pos.mpr hx0
  have hv1 : 1 / x ≤ 1 := (div_le_iff₀ hx0).mpr (by linarith only [hx])
  have hvy : 1 / x ≤ y := by linarith only [hv1, hy]
  have hR := Analysis.exponentialRampLogKernel_eq_weight hv
  change
    AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
        (Analysis.positiveLogRatio (1 / x)) =
      Analysis.exponentialRampWeight (1 / x) at hR
  have hP := Analysis.exponential_log_atom hv hvy
  have hlog : y / (1 / x) = x * y := by field_simp (disch := exact hx0.ne')
  rw [hlog] at hP
  dsimp only [AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional,
    Analysis.exponentialRampVariationLeft]
  rw [hR]
  rw [Analysis.exponentialRampWeight_eq_exp_of_le_left
      (by linarith only [hv1] : 1 / x ≤ (247 / 100 : ℝ))]
  linarith only [hP]

/-- At x at least one and y beyond the ramp, the corrected joint functional equals
the raw arithmetic functional plus the exact clipped-log contribution. Use finite-interval
linearity and the atom identity. No singular correction is inserted at the origin. -/
theorem jointFunctional_clippedShiftError_eq {x y : ℝ} (hx : 1 ≤ x) (hy : (99 / 40 : ℝ) ≤ y) :
    AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional (clippedShiftError x) y =
      AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional
          (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) y +
        Real.log (2 * Real.pi) *
          (Real.exp (-(1 / x)) + Real.exp (-y) * (1 + y * Real.log (x * y))) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hA := AnalyticNumberTheory.Arithmetic.continuousOn_logWeightedMangoldtSum_scaled hx0 y
  have hf :
    ContinuousOn (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u)
      (Set.Icc 0 y) :=
    hA.sub (continuous_const.mul continuous_id).continuousOn
  have hg :
    ContinuousOn (fun u ↦ Real.log (2 * Real.pi) * Analysis.positiveLogRatio (1 / x) u)
      (Set.Icc 0 y) :=
    (continuous_const.mul (Analysis.positiveLogRatio_continuous (one_div_pos.mpr hx0))).continuousOn
  have he := AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional_add hy hf hg
  change
    AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional
        (fun u ↦
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
            Real.log (2 * Real.pi) * Analysis.positiveLogRatio (1 / x) u)
        y =
      _
  rw [he, AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional_const_mul,
    clippedLogAtom_jointFunctional_eq hx hy]

/-- For x at least one, y beyond the ramp and c at most two, the logarithmic boundary
cost c(1+y log(xy)) is at most x(y^2+y+1). Use a logarithmic tangent at two.
This absorbs the retained finite endpoint into the negative principal endpoint term. -/
theorem clippedLog_boundary_cost_le {x y c : ℝ} (hx : 1 ≤ x) (hy : (99 / 40 : ℝ) ≤ y) (hc : c ≤ 2) :
    c * (1 + y * Real.log (x * y)) ≤ x * (y ^ 2 + y + 1) := by
  have hx0 : 0 < x := by linarith only [hx]
  have hy0 : 0 < y := by linarith only [hy]
  have hxy0 := mul_pos hx0 hy0
  have ht := Real.log_le_sub_one_of_pos (div_pos hxy0 (by norm_num only : (0 : ℝ) < 2))
  rw [Real.log_div hxy0.ne' (by norm_num only : (2 : ℝ) ≠ 0)] at ht
  have hlog : Real.log (x * y) ≤ x * y / 2 := by linarith only [ht, Real.log_two_lt_d9]
  have hp : 1 ≤ x * y := by
    have hm := mul_le_mul_of_nonneg_right hx hy0.le
    nlinarith only [hm, hy]
  have hl0 := Real.log_nonneg hp
  have hm := mul_le_mul_of_nonneg_right hc (mul_nonneg hy0.le hl0)
  have hh := mul_le_mul_of_nonneg_left hlog hy0.le
  have hlin : c ≤ x * (y + 1) := by
    have hprod := mul_nonneg (sub_nonneg.mpr hx) (show 0 ≤ y + 1 by linarith only [hy])
    nlinarith only [hprod, hc, hy]
  nlinarith only [hm, hh, hlin]

/-- Under RH, x at least one and u in the compact ramp support, the corrected error
is at most (63/800)sqrt x+21/20. Use the square-root endpoint cap.
The compact envelope contains no log x term. -/
theorem clippedShiftError_compact_le (hRH : RiemannHypothesis) {x u : ℝ} (hx : 1 ≤ x) (hu : 0 ≤ u)
    (hub : u ≤ (99 / 40 : ℝ)) :
    |clippedShiftError x u| ≤ (63 / 800 : ℝ) * Real.sqrt x + 21 / 20 := by
  have he := clippedShiftError_abs_le hRH (zero_lt_one.trans_le hx) hu
  rw [Real.sqrt_mul (by linarith only [hx] : 0 ≤ x)] at he
  have hs :=
    mul_le_mul_of_nonneg_left (Analysis.sqrt_le_ramp_right hub)
      (div_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 20))
  linarith only [he, hs]

/-- Under RH, x at least one and u nonnegative, the corrected error has the affine
envelope sqrt x/40+21/20+(sqrt x/40)u. Use sqrt u at most (u+1)/2.
Both tail coefficients are free of log x. -/
theorem clippedShiftError_tail_le (hRH : RiemannHypothesis) {x u : ℝ} (hx : 1 ≤ x) (hu : 0 ≤ u) :
    |clippedShiftError x u| ≤ (Real.sqrt x / 40 + 21 / 20) + (Real.sqrt x / 40) * u := by
  have he := clippedShiftError_abs_le hRH (zero_lt_one.trans_le hx) hu
  rw [Real.sqrt_mul (by linarith only [hx] : 0 ≤ x)] at he
  have hs :=
    mul_le_mul_of_nonneg_left (sqrt_le_half_add_one hu)
      (div_nonneg (Real.sqrt_nonneg x) (by norm_num only : (0 : ℝ) ≤ 20))
  linarith only [he, hs]

/-- Under RH and an admissible stencil width, the corrected ramp increment is at
most the logarithm-shift allowance plus 1/200. Retain the exact deterministic endpoint
logarithmic difference and bound it by a rational constant. This controls the paired jumps. -/
theorem clippedShiftError_increment_le (hRH : RiemannHypothesis) {x h : ℝ} (hx : 1 ≤ x) (hh : 0 < h)
    (hhx : h ≤ x) :
    |clippedShiftError x (99 / 40) - clippedShiftError x (247 / 100)| ≤
      logShiftRampIncrement x h + 1 / 200 := by
  have hx0 := zero_lt_one.trans_le hx
  have hc0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
  have hl0 : 0 ≤ Real.log (99 / 40 : ℝ) - Real.log (247 / 100 : ℝ) :=
    sub_nonneg.mpr (Real.log_le_log (by norm_num only) (by norm_num only))
  have ht :=
    Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < (99 / 40 : ℝ) / (247 / 100 : ℝ))
  rw [Real.log_div (by norm_num only : (99 / 40 : ℝ) ≠ 0)
      (by norm_num only : (247 / 100 : ℝ) ≠ 0)] at ht
  have hsmall : Real.log (99 / 40 : ℝ) - Real.log (247 / 100 : ℝ) ≤ 1 / 494 := by linarith only [ht]
  have hm := mul_le_mul_of_nonneg_left hsmall hc0
  have hc :
    Real.log (2 * Real.pi) * (Real.log (99 / 40 : ℝ) - Real.log (247 / 100 : ℝ)) ≤ 1 / 200 := by
    linarith only [hm, Analysis.log_two_mul_pi_lt.le]
  have he :
    clippedShiftError x (99 / 40) - clippedShiftError x (247 / 100) =
      ((AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (99 / 40)) - x * (99 / 40)) -
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (247 / 100)) -
            x * (247 / 100))) +
        Real.log (2 * Real.pi) * (Real.log (99 / 40) - Real.log (247 / 100)) := by
    dsimp only [clippedShiftError]
    rw [clippedLogAtom_eq_log_max hx0, clippedLogAtom_eq_log_max hx0,
      max_eq_right (show 1 ≤ x * (99 / 40 : ℝ) by nlinarith only [hx]),
      max_eq_right (show 1 ≤ x * (247 / 100 : ℝ) by nlinarith only [hx]),
      Real.log_mul hx0.ne' (by norm_num only : (99 / 40 : ℝ) ≠ 0),
      Real.log_mul hx0.ne' (by norm_num only : (247 / 100 : ℝ) ≠ 0)]
    ring
  rw [he]
  have ha :=
    abs_add_le
      ((AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (99 / 40)) - x * (99 / 40)) -
        (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (247 / 100)) -
          x * (247 / 100)))
      (Real.log (2 * Real.pi) * (Real.log (99 / 40) - Real.log (247 / 100)))
  rw [abs_mul, abs_of_nonneg hc0, abs_of_nonneg hl0] at ha
  linarith only [ha, hc, logWeighted_error_increment_log_shift_ramp hRH hx hh hhx]

/-- The joint corrected-error numerator at scale x and width h. Combine the
logarithm-free compact and affine tail envelopes with the corrected increment allowance.
The exact atom term log(2 pi)exp(-1/x) is retained separately in the principal lower cap. -/
noncomputable def clippedShiftPrincipalErrorNumerator (x h : ℝ) : ℝ :=
  (17 / 10 : ℝ) * ((63 / 800 : ℝ) * Real.sqrt x + 21 / 20) +
    84 * (logShiftRampIncrement x h + 1 / 200) +
    (21 / 100 : ℝ) * (Real.sqrt x / 40 + 21 / 20) +
    (13 / 16 : ℝ) * (Real.sqrt x / 40)

/-- Under RH, x at least one, admissible width and a cutoff beyond the ramp,
the corrected joint functional has the displayed logarithm-free numerator bound.
Apply the common-error theorem to the continuous corrected function and the three envelopes. -/
theorem jointFunctional_clippedShiftError_abs_le (hRH : RiemannHypothesis) {x y h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (hy : (99 / 40 : ℝ) ≤ y) :
    |AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional (clippedShiftError x) y| ≤
      clippedShiftPrincipalErrorNumerator x h := by
  apply
    AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional_abs_le hy
      (clippedShiftError_continuousOn (zero_lt_one.trans_le hx) y)
  · intro u hu
    exact clippedShiftError_compact_le hRH hx hu.1 hu.2
  · exact clippedShiftError_increment_le hRH hx hh hhx
  · linarith only [Real.sqrt_nonneg x]
  · linarith only [Real.sqrt_nonneg x]
  · intro u hu
    exact clippedShiftError_tail_le hRH hx (by linarith only [hu.1])

/-- Under RH at x at least one and an admissible width, every finite exponential
Mangoldt sum satisfies the corrected principal bound. Keep the exact clipped-log identity,
absorb its finite endpoint into the negative main endpoint, then use the eventual-cutoff
transfer. This connects the logarithm-free numerator to the actual arithmetic sum. -/
theorem exponentialMangoldtSum_upper_clipped_shift (hRH : RiemannHypothesis) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) (N : ℕ) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      x +
        (2 *
            AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
              (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
          clippedShiftPrincipalErrorNumerator x h +
          Real.log (2 * Real.pi) * Real.exp (-(1 / x))) := by
  apply exponentialMangoldtSum_upper_of_eventual_integral_cap hRH hx (99 / 40)
  intro y hy0 hy
  rw [logWeighted_exponential_integral_eq_main_add_error (zero_lt_one.trans_le hx) hy0]
  have hb := (abs_le.mp (jointFunctional_clippedShiftError_abs_le hRH hx hh hhx hy)).1
  have he := jointFunctional_clippedShiftError_eq hx hy
  have hc : Real.log (2 * Real.pi) ≤ 2 := by linarith only [Analysis.log_two_mul_pi_lt.le]
  have ht :=
    mul_le_mul_of_nonneg_right (clippedLog_boundary_cost_le hx hy hc) (Real.exp_pos (-y)).le
  dsimp only [AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional,
    Analysis.exponentialRampVariationLeft] at he hb
  linarith only [hb, he, ht]

/-- The principal lower cap with exact ramp mass and corrected numerator plus
log(2 pi)exp(-1/x), divided by sqrt x. It bounds twice the normalized ramp sum minus the
full principal Gamma series. Witness criteria can accept this cap as their principal input. -/
noncomputable def clippedShiftPrincipalLower (x h : ℝ) : ℝ :=
  (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x -
    (clippedShiftPrincipalErrorNumerator x h + Real.log (2 * Real.pi) * Real.exp (-(1 / x))) /
      Real.sqrt x

/-- Under RH at x at least one and an admissible width, the corrected cap bounds
the actual principal difference. Transfer the finite exponential estimates to the summable
Gamma series and use the exact ramp identity. This completes the infinite-series consumer. -/
theorem clippedShiftPrincipalLower_le_actual (hRH : RiemannHypothesis) {x h : ℝ} (hx : 1 ≤ x)
    (hh : 0 < h) (hhx : h ≤ x) :
    clippedShiftPrincipalLower x h ≤
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
        clippedShiftPrincipalLower x h := by
    apply PaperStatements.gamma_level_one_sum_upper_of_finite_upper hx0
    intro N
    have heq := PaperStatements.gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx0
    rw [Nat.floor_natCast] at heq
    rw [heq]
    apply (div_le_iff₀ hs).mpr
    have hb := exponentialMangoldtSum_upper_clipped_shift hRH hx hh hhx N
    rw [add_assoc] at hb
    have he :
      (2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            clippedShiftPrincipalLower x h) *
          Real.sqrt x =
        x +
          (2 *
              AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
            (clippedShiftPrincipalErrorNumerator x h +
              Real.log (2 * Real.pi) * Real.exp (-(1 / x)))) := by
      rw [hR]
      dsimp only [clippedShiftPrincipalLower]
      calc
        _ =
            (Real.sqrt x) ^ 2 +
              2 *
                ((AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                      (fun u ↦
                        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) /
                    Real.sqrt x) *
                  Real.sqrt x) +
              ((clippedShiftPrincipalErrorNumerator x h +
                    Real.log (2 * Real.pi) * Real.exp (-(1 / x))) /
                  Real.sqrt x) *
                Real.sqrt x :=
          by ring
        _ = _ := by
          rw [Real.sq_sqrt hx0.le, div_mul_cancel₀ _ hs.ne', div_mul_cancel₀ _ hs.ne']
          ring
    exact hb.trans_eq he.symm
  linarith only [hP]

/-- For every scale and width, replacing the exact ramp mass by its certified
lower bound 133/160 weakens the corrected principal cap. Multiply by the nonnegative
square root. This is a scalar input for explicit separation inequalities. -/
theorem clippedShiftPrincipalLower_ge_mass133 (x h : ℝ) :
    (133 / 160 : ℝ) * Real.sqrt x -
        (clippedShiftPrincipalErrorNumerator x h + Real.log (2 * Real.pi) * Real.exp (-(1 / x))) /
          Real.sqrt x ≤
      clippedShiftPrincipalLower x h := by
  have hm :=
    mul_le_mul_of_nonneg_right Analysis.ramp_mass_coefficient_ge_133_160 (Real.sqrt_nonneg x)
  dsimp only [clippedShiftPrincipalLower]
  linarith only [hm]

/-- At x at least one, the full corrected principal cap exceeds the previous
stencil-only corrected cap by more than 1/sqrt x. Bound the removed logarithmic costs below
and the retained atom term above. This proves a strict gain on the entire common domain. -/
theorem clippedShiftPrincipalLower_gt_logShift {x h : ℝ} (hx : 1 ≤ x) :
    logShiftRampPrincipalLower x h + 1 / Real.sqrt x < clippedShiftPrincipalLower x h := by
  have hx0 := zero_lt_one.trans_le hx
  have hl :=
    Real.log_le_log (by norm_num only : (0 : ℝ) < 2)
      (show (2 : ℝ) ≤ (99 / 40 : ℝ) * x by linarith only [hx])
  have he : Real.exp (-(1 / x)) ≤ 1 := by
    have hp := Real.exp_le_exp.mpr (neg_nonpos.mpr (one_div_nonneg.mpr hx0.le))
    simpa only [Real.exp_zero] using hp
  have hc0 : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
  have hc := mul_le_mul_of_nonneg_left he hc0
  have hbudget :
    clippedShiftPrincipalErrorNumerator x h + Real.log (2 * Real.pi) * Real.exp (-(1 / x)) + 1 <
      logShiftRampPrincipalErrorNumerator x h := by
    dsimp only [clippedShiftPrincipalErrorNumerator, logShiftRampPrincipalErrorNumerator]
    rw [mul_comm x (99 / 40 : ℝ)]
    linarith only [hl, Real.log_two_gt_d9, Real.log_nonneg hx, hc, Analysis.log_two_mul_pi_lt.le]
  have hs := Real.sqrt_pos.mpr hx0
  have hd := (div_lt_div_iff_of_pos_right hs).mpr hbudget
  dsimp only [logShiftRampPrincipalLower, clippedShiftPrincipalLower]
  rw [add_div] at hd
  linarith only [hd]

end PseudoPrime.LLS
