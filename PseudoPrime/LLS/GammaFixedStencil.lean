/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ClippedLogShiftPrincipalBounds

/-! # Fixed-width stencil bounds with the tighter three-point root envelope -/

@[expose] public section

namespace PseudoPrime.LLS

/-- The fixed-width three-point envelope at scale x. It bounds corrected errors
through 511x/200 by using sqrt(t)<=8sqrt(x)/5, and supplies the improved increment. -/
noncomputable def fixedStencilEnvelope (x : ℝ) : ℝ :=
  (2 / 25 : ℝ) * Real.sqrt x + 21 / 20

/-- The actual raw-error increment allowance at width 2x/25. Keep the logarithmic
atom and the exact endpoint ratio; both principal and variation consumers use this value. -/
noncomputable def fixedStencilIncrement (x : ℝ) : ℝ :=
  (x / 200 + (2 / 25) * x +
      2 * fixedStencilEnvelope x * ((99 / 40 : ℝ) * x + (2 / 25) * x) / ((2 / 25) * x) +
      Real.log (2 * Real.pi)) /
    494

/-- Under RH the corrected error through 511x/200 is bounded by the fixed
stencil envelope for x>=1 and t>1. Compare the two square roots before scaling by 1/20. -/
theorem fixedStencil_error_le (hRH : RiemannHypothesis) {x t : ℝ} (hx : 1 ≤ x) (ht : 1 < t)
    (hb : t ≤ (511 / 200 : ℝ) * x) :
    |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t +
          Real.log (2 * Real.pi) * Real.log t| ≤
      fixedStencilEnvelope x := by
  have he := logWeightedMangoldtSum_log_shift_error_le hRH ht
  have hs : Real.sqrt t ≤ (8 / 5 : ℝ) * Real.sqrt x := by
    apply Real.sqrt_le_iff.mpr
    exact
      ⟨mul_nonneg (by norm_num only) (Real.sqrt_nonneg x), by
        nlinarith only [hb, Real.sq_sqrt (by linarith only [hx] : 0 ≤ x)]⟩
  dsimp only [fixedStencilEnvelope]
  linarith only [he, hs]

/-- Under RH and x>=1, the raw smoothed-error increment on the ramp is bounded
by the tighter fixed-width allowance. The three stencil arguments all exceed one. -/
theorem fixedStencil_raw_increment (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |(AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (99 / 40)) - x * (99 / 40)) -
          (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * (247 / 100)) -
            x * (247 / 100))| ≤
      fixedStencilIncrement x := by
  let h : ℝ := (2 / 25) * x
  have hx0 : 0 < x := by linarith only [hx]
  have hh : 0 < h := mul_pos (by norm_num only : (0 : ℝ) < 2 / 25) hx0
  have ha : 0 < x * (247 / 100 : ℝ) - h := by
    dsimp only [h]; nlinarith only [hx]
  have hab : x * (247 / 100 : ℝ) ≤ x * (99 / 40 : ℝ) := by nlinarith only [hx]
  have hc : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith only [Real.pi_gt_three] : 1 ≤ 2 * Real.pi)
  have hE :
    ∀ t ∈ Set.Icc (x * (247 / 100 : ℝ)) (x * (99 / 40 : ℝ)),
      |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (t - h) - (t - h) +
              Real.log (2 * Real.pi) * Real.log (t - h)| ≤
          fixedStencilEnvelope x ∧
        |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum t - t +
              Real.log (2 * Real.pi) * Real.log t| ≤
          fixedStencilEnvelope x ∧
        |AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (t + h) - (t + h) +
              Real.log (2 * Real.pi) * Real.log (t + h)| ≤
          fixedStencilEnvelope x := by
    intro t ht
    have hl : 1 < t - h := by
      dsimp only [h]; nlinarith only [hx, ht.1]
    have ht0 : 1 < t := by linarith only [hl, hh]
    refine
      ⟨fixedStencil_error_le hRH hx hl ?_, fixedStencil_error_le hRH hx ht0 ?_,
        fixedStencil_error_le hRH hx (by linarith only [ht0, hh]) ?_⟩
    · dsimp only [h]; nlinarith only [ht.2, hx]
    · nlinarith only [ht.2, hx]
    · dsimp only [h]; nlinarith only [ht.2, hx]
  have he :=
    AnalyticNumberTheory.Arithmetic.logWeighted_error_increment_le_of_log_shift_stencil hc hh ha hab
      hE
  have hid :
    ((x * (99 / 40 : ℝ) - x * (247 / 100)) +
            (h + 2 * fixedStencilEnvelope x * (x * (99 / 40) + h) / h + Real.log (2 * Real.pi))) *
          (x * (99 / 40) - x * (247 / 100)) /
        (x * (247 / 100)) =
      fixedStencilIncrement x := by
    dsimp only [fixedStencilIncrement, h]
    apply
      (div_eq_div_iff (mul_ne_zero hx0.ne' (by norm_num only : (247 / 100 : ℝ) ≠ 0))
          (by norm_num only : (494 : ℝ) ≠ 0)).mpr
    ring
  exact he.trans_eq hid

/-- Under RH and the fixed stencil width 2x/25, the corrected ramp increment is at
most the logarithm-shift allowance plus 1/200. Retain the exact deterministic endpoint
logarithmic difference and bound it by a rational constant. This controls the paired jumps. -/
theorem fixedShiftError_increment (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    |clippedShiftError x (99 / 40) - clippedShiftError x (247 / 100)| ≤
      fixedStencilIncrement x + 1 / 200 := by
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
  linarith only [ha, hc, fixedStencil_raw_increment hRH hx]

/-- The joint corrected-error numerator at scale x and width h. Combine the
logarithm-free compact and affine tail envelopes with the corrected increment allowance.
The exact atom term log(2 pi)exp(-1/x) is retained separately in the principal lower cap. -/
noncomputable def fixedShiftPrincipalError (x : ℝ) : ℝ :=
  (17 / 10 : ℝ) * ((63 / 800 : ℝ) * Real.sqrt x + 21 / 20) +
    84 * (fixedStencilIncrement x + 1 / 200) +
    (21 / 100 : ℝ) * (Real.sqrt x / 40 + 21 / 20) +
    (13 / 16 : ℝ) * (Real.sqrt x / 40)

/-- Under RH, x at least one, fixed width 2x/25 and a cutoff beyond the ramp,
the corrected joint functional has the displayed logarithm-free numerator bound.
Apply the common-error theorem to the continuous corrected function and the three envelopes. -/
theorem fixedShift_joint_bound (hRH : RiemannHypothesis) {x y : ℝ} (hx : 1 ≤ x)
    (hy : (99 / 40 : ℝ) ≤ y) :
    |AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional (clippedShiftError x) y| ≤
      fixedShiftPrincipalError x := by
  apply
    AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional_abs_le hy
      (clippedShiftError_continuousOn (zero_lt_one.trans_le hx) y)
  · intro u hu
    exact clippedShiftError_compact_le hRH hx hu.1 hu.2
  · exact fixedShiftError_increment hRH hx
  · linarith only [Real.sqrt_nonneg x]
  · linarith only [Real.sqrt_nonneg x]
  · intro u hu
    exact clippedShiftError_tail_le hRH hx (by linarith only [hu.1])

/-- Under RH at x at least one and an fixed width 2x/25, every finite exponential
Mangoldt sum satisfies the corrected principal bound. Keep the exact clipped-log identity,
absorb its finite endpoint into the negative main endpoint, then use the eventual-cutoff
transfer. This connects the logarithm-free numerator to the actual arithmetic sum. -/
theorem fixedShift_exp_sum_upper (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) (N : ℕ) :
    AnalyticNumberTheory.Arithmetic.exponentialMangoldtSum x (N : ℝ) ≤
      x +
        (2 *
            AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
              (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
          fixedShiftPrincipalError x +
          Real.log (2 * Real.pi) * Real.exp (-(1 / x))) := by
  apply exponentialMangoldtSum_upper_of_eventual_integral_cap hRH hx (99 / 40)
  intro y hy0 hy
  rw [logWeighted_exponential_integral_eq_main_add_error (zero_lt_one.trans_le hx) hy0]
  have hb := (abs_le.mp (fixedShift_joint_bound hRH hx hy)).1
  have he := jointFunctional_clippedShiftError_eq hx hy
  have hc : Real.log (2 * Real.pi) ≤ 2 := by linarith only [Analysis.log_two_mul_pi_lt.le]
  have ht :=
    mul_le_mul_of_nonneg_right (clippedLog_boundary_cost_le hx hy hc) (Real.exp_pos (-y)).le
  dsimp only [AnalyticNumberTheory.Arithmetic.jointRampPrincipalFunctional,
    Analysis.exponentialRampVariationLeft] at he hb
  linarith only [hb, he, ht]

/-- The fixed-stencil principal cap retains exact ramp mass and the clipped logarithmic
atom. Its error numerator uses the same tighter increment as the ramp variation bound. -/
noncomputable def fixedShiftPrincipalLower (x : ℝ) : ℝ :=
  (2 * (∫ u in (0 : ℝ)..(99 / 40), Analysis.exponentialRampWeight u) - 1) * Real.sqrt x -
    (fixedShiftPrincipalError x + Real.log (2 * Real.pi) * Real.exp (-(1 / x))) / Real.sqrt x

/-- Under RH at x at least one and an fixed width 2x/25, the corrected cap bounds
the actual principal difference. Transfer the finite exponential estimates to the summable
Gamma series and use the exact ramp identity. This completes the infinite-series consumer. -/
theorem fixedShiftPrincipal_le_actual (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    fixedShiftPrincipalLower x ≤
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
        fixedShiftPrincipalLower x := by
    apply PaperStatements.gamma_level_one_sum_upper_of_finite_upper hx0
    intro N
    have heq := PaperStatements.gamma_level_one_sum_eq_exponential (y := (N : ℝ)) hx0
    rw [Nat.floor_natCast] at heq
    rw [heq]
    apply (div_le_iff₀ hs).mpr
    have hb := fixedShift_exp_sum_upper hRH hx N
    rw [add_assoc] at hb
    have he :
      (2 * (AnalyticNumberTheory.Arithmetic.exponentialRampMangoldtSum x / Real.sqrt x) -
            fixedShiftPrincipalLower x) *
          Real.sqrt x =
        x +
          (2 *
              AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                (fun u ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) +
            (fixedShiftPrincipalError x + Real.log (2 * Real.pi) * Real.exp (-(1 / x)))) := by
      rw [hR]
      dsimp only [fixedShiftPrincipalLower]
      calc
        _ =
            (Real.sqrt x) ^ 2 +
              2 *
                ((AnalyticNumberTheory.Arithmetic.exponentialRampVariationFunctional
                      (fun u ↦
                        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (x * u) - x * u) /
                    Real.sqrt x) *
                  Real.sqrt x) +
              ((fixedShiftPrincipalError x + Real.log (2 * Real.pi) * Real.exp (-(1 / x))) /
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
theorem fixedShiftPrincipal_ge_mass133 (x : ℝ) :
    (133 / 160 : ℝ) * Real.sqrt x -
        (fixedShiftPrincipalError x + Real.log (2 * Real.pi) * Real.exp (-(1 / x))) / Real.sqrt x ≤
      fixedShiftPrincipalLower x := by
  have hm :=
    mul_le_mul_of_nonneg_right Analysis.ramp_mass_coefficient_ge_133_160 (Real.sqrt_nonneg x)
  dsimp only [fixedShiftPrincipalLower]
  linarith only [hm]

end PseudoPrime.LLS
