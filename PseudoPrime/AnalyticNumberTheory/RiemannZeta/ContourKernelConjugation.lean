/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedGeometry
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FarLeftContourAssembly
import PseudoPrime.AnalyticNumberTheory.General.PoleResidueCalculus
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.JensenNeg

/-!
# Conjugation symmetry for the Riemann contour kernels

This file transfers the upper-horizontal estimates to the lower horizontal edge.  Since the cutoff
`x` is positive, both kernels commute with complex conjugation.  The same is consequently true of
their interval integrals along horizontal lines.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Both contour kernels are interval-integrable along every upper unified horizontal segment. -/
theorem intervalIntegrable_riemannZetaKernels_unified_upper {x a b : ℝ} (hx : 0 < x) (m : ℕ) :
    IntervalIntegrable
        (fun σ : ℝ ↦
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) +
              unifiedContourHeightSeq m * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable
        (fun σ : ℝ ↦
          riemannZetaLogContourKernel x
            ((σ : ℂ) +
              unifiedContourHeightSeq m * Complex.I))
        MeasureTheory.volume a b := by
  have hUpos : 0 < unifiedContourHeightSeq m :=
    (farLeftHeightSeq_pos m).trans_le
      (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  constructor <;>
    apply
      RectangleGeometry.intervalIntegrable_horizontal_of_continuousAt <;>
    intro σ _
  · apply
      (differentiableAt_riemannZetaReciprocalContourKernel
          hx ?_ ?_ ?_).continuousAt
    · intro hs
      have him := congrArg Complex.im hs
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.zero_im] at him
      linarith only [him, hUpos]
    · intro hs
      have him := congrArg Complex.im hs
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im] at him
      linarith only [him, hUpos]
    · exact riemannZeta_ne_zero_on_unified_upper m σ
  · apply
      (differentiableAt_riemannZetaLogContourKernel hx
          ?_ ?_ ?_).continuousAt
    · intro hs
      have him := congrArg Complex.im hs
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.zero_im] at him
      linarith only [him, hUpos]
    · intro hs
      have him := congrArg Complex.im hs
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        mul_one, Complex.I_re, mul_zero, add_zero, zero_add, Complex.one_im] at him
      linarith only [him, hUpos]
    · exact riemannZeta_ne_zero_on_unified_upper m σ

/-- Both contour kernels are interval-integrable along every lower unified horizontal segment. -/
theorem intervalIntegrable_riemannZetaKernels_unified_lower {x a b : ℝ} (hx : 0 < x) (m : ℕ) :
    IntervalIntegrable
        (fun σ : ℝ ↦
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) -
              unifiedContourHeightSeq m * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable
        (fun σ : ℝ ↦
          riemannZetaLogContourKernel x
            ((σ : ℂ) -
              unifiedContourHeightSeq m * Complex.I))
        MeasureTheory.volume a b := by
  have hUpos : 0 < unifiedContourHeightSeq m :=
    (farLeftHeightSeq_pos m).trans_le
      (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  constructor
  · convert
      RectangleGeometry.intervalIntegrable_horizontal_of_continuousAt
        (riemannZetaReciprocalContourKernel x)
        (-(unifiedContourHeightSeq m)) a b ?_ using
      1
    · funext σ
      apply
        congrArg (riemannZetaReciprocalContourKernel x)
      push_cast
      ring
    · intro σ _
      apply
        (differentiableAt_riemannZetaReciprocalContourKernel
            hx ?_ ?_ ?_).continuousAt
      · intro hs
        have him := congrArg Complex.im hs
        simp only [Complex.ofReal_neg, neg_mul, Complex.add_im, Complex.ofReal_im, Complex.neg_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
          add_zero, zero_add, Complex.zero_im, neg_eq_zero] at him
        linarith only [him, hUpos]
      · intro hs
        have him := congrArg Complex.im hs
        simp only [Complex.ofReal_neg, neg_mul, Complex.add_im, Complex.ofReal_im, Complex.neg_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
          add_zero, zero_add, Complex.one_im, neg_eq_zero] at him
        linarith only [him, hUpos]
      · have heq :
          (σ : ℂ) +
              ((-(unifiedContourHeightSeq m) : ℝ) :
                  ℂ) *
                Complex.I =
            (σ : ℂ) -
              unifiedContourHeightSeq m *
                Complex.I := by
          push_cast
          ring
        rw [heq]
        exact riemannZeta_ne_zero_on_unified_lower m σ
  · convert
      RectangleGeometry.intervalIntegrable_horizontal_of_continuousAt
        (riemannZetaLogContourKernel x)
        (-(unifiedContourHeightSeq m)) a b ?_ using
      1
    · funext σ
      apply congrArg (riemannZetaLogContourKernel x)
      push_cast
      ring
    · intro σ _
      apply
        (differentiableAt_riemannZetaLogContourKernel
            hx ?_ ?_ ?_).continuousAt
      · intro hs
        have him := congrArg Complex.im hs
        simp only [Complex.ofReal_neg, neg_mul, Complex.add_im, Complex.ofReal_im, Complex.neg_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
          add_zero, zero_add, Complex.zero_im, neg_eq_zero] at him
        linarith only [him, hUpos]
      · intro hs
        have him := congrArg Complex.im hs
        simp only [Complex.ofReal_neg, neg_mul, Complex.add_im, Complex.ofReal_im, Complex.neg_im,
          Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
          add_zero, zero_add, Complex.one_im, neg_eq_zero] at him
        linarith only [him, hUpos]
      · have heq :
          (σ : ℂ) +
              ((-(unifiedContourHeightSeq m) : ℝ) :
                  ℂ) *
                Complex.I =
            (σ : ℂ) -
              unifiedContourHeightSeq m *
                Complex.I := by
          push_cast
          ring
        rw [heq]
        exact riemannZeta_ne_zero_on_unified_lower m σ

/-- Each upper horizontal unified contour integral splits at the finite-contour line. -/
theorem intervalIntegral_riemannZetaLogContourKernel_unified_upper_split {x a c : ℝ} (hx : 0 < x)
    (m : ℕ) :
    (∫ σ in a..c,
        riemannZetaLogContourKernel x
          ((σ : ℂ) +
            (unifiedContourHeightSeq m : ℂ) *
              Complex.I)) =
      (∫ σ in a..(-1 / 2),
          riemannZetaLogContourKernel x
            ((σ : ℂ) +
              (unifiedContourHeightSeq m : ℂ) *
                Complex.I)) +
        ∫ σ in (-1 / 2)..c,
          riemannZetaLogContourKernel x
            ((σ : ℂ) +
              (unifiedContourHeightSeq m : ℂ) *
                Complex.I) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · exact
      (intervalIntegrable_riemannZetaKernels_unified_upper
          hx m (a := a) (b := -1 / 2)).2
  · exact
      (intervalIntegrable_riemannZetaKernels_unified_upper
          hx m (a := -1 / 2) (b := c)).2

/-- Each upper horizontal reciprocal contour integral splits at the finite-contour line. -/
theorem intervalIntegral_riemannZetaReciprocalContourKernel_unified_upper_split {x a c : ℝ}
    (hx : 0 < x) (m : ℕ) :
    (∫ σ in a..c,
        riemannZetaReciprocalContourKernel x
          ((σ : ℂ) +
            (unifiedContourHeightSeq m : ℂ) *
              Complex.I)) =
      (∫ σ in a..(-1 / 2),
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) +
              (unifiedContourHeightSeq m : ℂ) *
                Complex.I)) +
        ∫ σ in (-1 / 2)..c,
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) +
              (unifiedContourHeightSeq m : ℂ) *
                Complex.I) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · exact
      (intervalIntegrable_riemannZetaKernels_unified_upper
          hx m (a := a) (b := -1 / 2)).1
  · exact
      (intervalIntegrable_riemannZetaKernels_unified_upper
          hx m (a := -1 / 2) (b := c)).1

/-- Each lower horizontal unified contour integral splits at the finite-contour line. -/
theorem intervalIntegral_riemannZetaLogContourKernel_unified_lower_split {x a c : ℝ} (hx : 0 < x)
    (m : ℕ) :
    (∫ σ in a..c,
        riemannZetaLogContourKernel x
          ((σ : ℂ) -
            (unifiedContourHeightSeq m : ℂ) *
              Complex.I)) =
      (∫ σ in a..(-1 / 2),
          riemannZetaLogContourKernel x
            ((σ : ℂ) -
              (unifiedContourHeightSeq m : ℂ) *
                Complex.I)) +
        ∫ σ in (-1 / 2)..c,
          riemannZetaLogContourKernel x
            ((σ : ℂ) -
              (unifiedContourHeightSeq m : ℂ) *
                Complex.I) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · exact
      (intervalIntegrable_riemannZetaKernels_unified_lower
          hx m (a := a) (b := -1 / 2)).2
  · exact
      (intervalIntegrable_riemannZetaKernels_unified_lower
          hx m (a := -1 / 2) (b := c)).2

/-- Each lower horizontal reciprocal contour integral splits at the finite-contour line. -/
theorem intervalIntegral_riemannZetaReciprocalContourKernel_unified_lower_split {x a c : ℝ}
    (hx : 0 < x) (m : ℕ) :
    (∫ σ in a..c,
        riemannZetaReciprocalContourKernel x
          ((σ : ℂ) -
            (unifiedContourHeightSeq m : ℂ) *
              Complex.I)) =
      (∫ σ in a..(-1 / 2),
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) -
              (unifiedContourHeightSeq m : ℂ) *
                Complex.I)) +
        ∫ σ in (-1 / 2)..c,
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) -
              (unifiedContourHeightSeq m : ℂ) *
                Complex.I) := by
  rw [← intervalIntegral.integral_add_adjacent_intervals]
  · exact
      (intervalIntegrable_riemannZetaKernels_unified_lower
          hx m (a := a) (b := -1 / 2)).1
  · exact
      (intervalIntegrable_riemannZetaKernels_unified_lower
          hx m (a := -1 / 2) (b := c)).1

/-- The logarithmic far-left horizontal integral has a `length / height` majorant. -/
theorem norm_intervalIntegral_riemannZetaLogContourKernel_unified_farLeft_le {x : ℝ} (hx : 1 < x)
    (m : ℕ) :
    ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaLogContourKernel x
            ((σ : ℂ) +
              unifiedContourHeightSeq m * Complex.I)‖ ≤
      unifiedFarLeftLinearConst * x ^ (-(1 : ℝ) / 2) *
          (2 * (m : ℝ) + 1 / 2) /
        unifiedContourHeightSeq m := by
  set T := unifiedContourHeightSeq m
  have hT1 : (1 : ℝ) ≤ T :=
    (one_le_farLeftHeightSeq m).trans
      (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hTpos : 0 < T := one_pos.trans_le hT1
  have hbase :=
    norm_intervalIntegral_riemannZetaLogContourKernel_farLeft_le
      hx (m := m) (t := T) hTpos.ne'
  have hlog := farLeftZetaLogDerivBound_unified_le m
  have hxpow : 0 < x ^ (-(1 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  calc
    ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
            riemannZetaLogContourKernel x
              ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        farLeftZetaLogDerivBound m T *
              x ^ (-(1 : ℝ) / 2) /
            T ^ 2 *
          (-1 / 2 - (-(2 * (m : ℝ) + 1))) :=
      hbase
    _ ≤
        (unifiedFarLeftLinearConst * T) *
              x ^ (-(1 : ℝ) / 2) /
            T ^ 2 *
          (2 * (m : ℝ) + 1 / 2) :=
      by
      rw [show -1 / 2 - (-(2 * (m : ℝ) + 1)) = 2 * (m : ℝ) + 1 / 2 by ring]
      gcongr
    _ =
        unifiedFarLeftLinearConst *
            x ^ (-(1 : ℝ) / 2) *
            (2 * (m : ℝ) + 1 / 2) /
          T :=
      by field_simp

/-- The reciprocal far-left horizontal integral has the same `length / height` majorant. -/
theorem norm_intervalIntegral_riemannZetaReciprocalContourKernel_unified_farLeft_le {x : ℝ}
    (hx : 1 < x) (m : ℕ) :
    ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) +
              unifiedContourHeightSeq m * Complex.I)‖ ≤
      unifiedFarLeftLinearConst * x ^ (-(3 : ℝ) / 2) *
          (2 * (m : ℝ) + 1 / 2) /
        unifiedContourHeightSeq m := by
  set T := unifiedContourHeightSeq m
  have hT1 : (1 : ℝ) ≤ T :=
    (one_le_farLeftHeightSeq m).trans
      (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hTpos : 0 < T := one_pos.trans_le hT1
  have hbase :=
    norm_intervalIntegral_riemannZetaReciprocalContourKernel_farLeft_le
      hx (m := m) (t := T) hTpos.ne'
  have hlog := farLeftZetaLogDerivBound_unified_le m
  have hxpow : 0 < x ^ (-(3 : ℝ) / 2) := Real.rpow_pos_of_pos (by linarith) _
  calc
    ‖∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
            riemannZetaReciprocalContourKernel x
              ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
        farLeftZetaLogDerivBound m T *
              x ^ (-(3 : ℝ) / 2) /
            T ^ 2 *
          (-1 / 2 - (-(2 * (m : ℝ) + 1))) :=
      hbase
    _ ≤
        (unifiedFarLeftLinearConst * T) *
              x ^ (-(3 : ℝ) / 2) /
            T ^ 2 *
          (2 * (m : ℝ) + 1 / 2) :=
      by
      rw [show -1 / 2 - (-(2 * (m : ℝ) + 1)) = 2 * (m : ℝ) + 1 / 2 by ring]
      gcongr
    _ =
        unifiedFarLeftLinearConst *
            x ^ (-(3 : ℝ) / 2) *
            (2 * (m : ℝ) + 1 / 2) /
          T :=
      by field_simp

/-- The upper growing logarithmic far-left segment vanishes on the unified sequence. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_unified_farLeft {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaLogContourKernel x
            ((σ : ℂ) +
              unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm
      (fun m =>
        norm_intervalIntegral_riemannZetaLogContourKernel_unified_farLeft_le
          hx m)
  convert
      tendsto_farLeftLength_div_unifiedContourHeightSeq.const_mul
        (unifiedFarLeftLinearConst *
          x ^ (-(1 : ℝ) / 2)) using
      1 <;>
    ring_nf

/-- The upper growing reciprocal far-left segment vanishes on the unified sequence. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unified_farLeft {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) +
              unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm
      (fun m =>
        norm_intervalIntegral_riemannZetaReciprocalContourKernel_unified_farLeft_le
          hx m)
  convert
      tendsto_farLeftLength_div_unifiedContourHeightSeq.const_mul
        (unifiedFarLeftLinearConst *
          x ^ (-(3 : ℝ) / 2)) using
      1 <;>
    ring_nf

/-- The logarithmic left-vertical integral has a square-height geometric majorant. -/
theorem norm_intervalIntegral_riemannZetaLogContourKernel_unified_leftVertical_le {x : ℝ}
    (hx : 1 < x) (m : ℕ) :
    ‖∫ t in
          (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
          riemannZetaLogContourKernel x
            (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * unifiedLeftVerticalLinearConst *
        x ^ (-(1 : ℝ)) *
        (unifiedContourHeightSeq m ^ 2 *
          (x ^ (-(2 : ℝ))) ^ m) := by
  set T := unifiedContourHeightSeq m
  have hTpos : 0 < T :=
    (farLeftHeightSeq_pos m).trans_le (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hbase :=
    norm_intervalIntegral_riemannZetaLogContourKernel_leftVertical_le
      (x := x) (by linarith only [hx]) (m := m) (T := T) hTpos.le
  have hlog := leftVerticalZetaLogDerivBound_unified_le m
  change leftVerticalZetaLogDerivBound m T ≤ unifiedLeftVerticalLinearConst * T at hlog
  have hxpow : 0 < x ^ (-(2 * (m : ℝ) + 1)) := Real.rpow_pos_of_pos (by linarith only [hx]) _
  have hden : (1 : ℝ) ≤ (2 * (m : ℝ) + 1) ^ 2 := by nlinarith only [Nat.cast_nonneg (α := ℝ) m]
  have hnonneg :
    0 ≤ leftVerticalZetaLogDerivBound m T :=
    le_trans (norm_nonneg _) (norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform m T)
  have hxeq : x ^ (-(2 * (m : ℝ) + 1)) = x ^ (-(1 : ℝ)) * (x ^ (-(2 : ℝ))) ^ m := by
    rw [show -(2 * (m : ℝ) + 1) = -(2 : ℝ) * (m : ℝ) + -(1 : ℝ) by ring,
      Real.rpow_add (by linarith only [hx]), Real.rpow_mul (by linarith only [hx] : 0 ≤ x),
      Real.rpow_natCast]
    ring
  calc
    ‖∫ t in (-T)..T,
            riemannZetaLogContourKernel x
              (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        leftVerticalZetaLogDerivBound m T *
              x ^ (-(2 * (m : ℝ) + 1)) /
            (2 * (m : ℝ) + 1) ^ 2 *
          (2 * T) :=
      hbase
    _ ≤
        (unifiedLeftVerticalLinearConst * T) *
          x ^ (-(2 * (m : ℝ) + 1)) *
          (2 * T) :=
      by
      calc
        _ ≤
            leftVerticalZetaLogDerivBound m T *
                  x ^ (-(2 * (m : ℝ) + 1)) /
                1 *
              (2 * T) :=
          by gcongr
        _ ≤
            (unifiedLeftVerticalLinearConst * T) *
              x ^ (-(2 * (m : ℝ) + 1)) *
              (2 * T) :=
          by
          gcongr
          simpa only [div_one] using mul_le_mul_of_nonneg_right hlog hxpow.le
    _ =
        2 * unifiedLeftVerticalLinearConst *
          x ^ (-(1 : ℝ)) *
          (T ^ 2 * (x ^ (-(2 : ℝ))) ^ m) :=
      by
      rw [hxeq]; ring

/-- The reciprocal left-vertical integral has the analogous geometric majorant. -/
theorem norm_intervalIntegral_riemannZetaReciprocalContourKernel_unified_leftVertical_le {x : ℝ}
    (hx : 1 < x) (m : ℕ) :
    ‖∫ t in
          (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
          riemannZetaReciprocalContourKernel x
            (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * unifiedLeftVerticalLinearConst *
        x ^ (-(2 : ℝ)) *
        (unifiedContourHeightSeq m ^ 2 *
          (x ^ (-(2 : ℝ))) ^ m) := by
  set T := unifiedContourHeightSeq m
  have hTpos : 0 < T :=
    (farLeftHeightSeq_pos m).trans_le (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hbase :=
    norm_intervalIntegral_riemannZetaReciprocalContourKernel_leftVertical_le
    (x := x) (by linarith) (m := m) (T := T) hTpos.le
  have hlog :=
    leftVerticalZetaLogDerivBound_unified_le m
  change leftVerticalZetaLogDerivBound m T ≤ unifiedLeftVerticalLinearConst * T at hlog
  have hxpow : 0 < x ^ (-(2 * (m : ℝ) + 2)) := Real.rpow_pos_of_pos (by linarith) _
  have hden : (1 : ℝ) ≤ (2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2) := by
    nlinarith only [Nat.cast_nonneg (α := ℝ) m]
  have hnonneg : 0 ≤ leftVerticalZetaLogDerivBound m T := le_trans (norm_nonneg _)
      (norm_logDeriv_riemannZeta_neg_odd_add_mul_I_le_uniform m T)
  have hxeq : x ^ (-(2 * (m : ℝ) + 2)) = x ^ (-(2 : ℝ)) * (x ^ (-(2 : ℝ))) ^ m := by
    rw [show -(2 * (m : ℝ) + 2) = -(2 : ℝ) * (m : ℝ) + -(2 : ℝ) by ring,
      Real.rpow_add (by linarith), Real.rpow_mul (by linarith : 0 ≤ x), Real.rpow_natCast]
    ring
  calc
    ‖∫ t in (-T)..T,
            riemannZetaReciprocalContourKernel x
              (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        leftVerticalZetaLogDerivBound m T *
              x ^ (-(2 * (m : ℝ) + 2)) /
            ((2 * (m : ℝ) + 1) * (2 * (m : ℝ) + 2)) *
          (2 * T) :=
      hbase
    _ ≤
        (unifiedLeftVerticalLinearConst * T) *
          x ^ (-(2 * (m : ℝ) + 2)) *
          (2 * T) :=
      by
      calc
        _ ≤
            leftVerticalZetaLogDerivBound m T *
                  x ^ (-(2 * (m : ℝ) + 2)) /
                1 *
              (2 * T) :=
          by gcongr
        _ ≤
            (unifiedLeftVerticalLinearConst * T) *
              x ^ (-(2 * (m : ℝ) + 2)) *
              (2 * T) :=
          by
          gcongr
          simpa only [div_one] using mul_le_mul_of_nonneg_right hlog hxpow.le
    _ =
        2 * unifiedLeftVerticalLinearConst *
          x ^ (-(2 : ℝ)) *
          (T ^ 2 * (x ^ (-(2 : ℝ))) ^ m) :=
      by
      rw [hxeq]; ring

/-- The logarithmic left-vertical edge vanishes on the unified contour sequence. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_unified_leftVertical {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ t in
          (-(unifiedContourHeightSeq
              m))..(unifiedContourHeightSeq m),
          riemannZetaLogContourKernel x
            (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm
      (fun m =>
        norm_intervalIntegral_riemannZetaLogContourKernel_unified_leftVertical_le
          hx m)
  have hrpos : 0 ≤ x ^ (-(2 : ℝ)) := by positivity
  have hrlt : x ^ (-(2 : ℝ)) < 1 := by
    rw [show (-(2 : ℝ)) = -(2 : ℕ) by norm_num only, Real.rpow_neg (by linarith), Real.rpow_natCast,
      inv_lt_one_iff₀]
    right
    nlinarith only [hx, sq_nonneg (x - 1)]
  simpa only [Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, inv_pow, mul_zero] using
    (tendsto_unifiedContourHeightSeq_sq_mul_pow_of_lt_one
          hrpos hrlt).const_mul
      (2 * unifiedLeftVerticalLinearConst *
        x ^ (-(1 : ℝ)))

/-- The reciprocal left-vertical edge vanishes on the unified contour sequence. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unified_leftVertical {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ t in
          (-(unifiedContourHeightSeq
              m))..(unifiedContourHeightSeq m),
          riemannZetaReciprocalContourKernel x
            (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))
      Filter.atTop (nhds 0) := by
  apply
    squeeze_zero_norm
      (fun m =>
        norm_intervalIntegral_riemannZetaReciprocalContourKernel_unified_leftVertical_le
          hx m)
  have hrpos : 0 ≤ x ^ (-(2 : ℝ)) := by positivity
  have hrlt : x ^ (-(2 : ℝ)) < 1 := by
    rw [show (-(2 : ℝ)) = -(2 : ℕ) by norm_num only, Real.rpow_neg (by linarith), Real.rpow_natCast,
      inv_lt_one_iff₀]
    right
    nlinarith only [hx, sq_nonneg (x - 1)]
  simpa only [Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, inv_pow, mul_zero] using
    (tendsto_unifiedContourHeightSeq_sq_mul_pow_of_lt_one
          hrpos hrlt).const_mul
      (2 * unifiedLeftVerticalLinearConst *
        x ^ (-(2 : ℝ)))

/-- The logarithmic Riemann contour kernel commutes with conjugation for positive `x`. -/
theorem riemannZetaLogContourKernel_conj {x : ℝ} (hx : 0 < x) (s : ℂ) :
    riemannZetaLogContourKernel x (starRingEnd ℂ s) =
      starRingEnd ℂ
        (riemannZetaLogContourKernel x s) := by
  rw [riemannZetaLogContourKernel, riemannZetaLogContourKernel, deriv_riemannZeta_conj s,
    riemannZeta_conj]
  rw [Complex.cpow_conj]
  · rw [Complex.conj_ofReal]
    simp only [map_neg, map_div₀, map_mul, map_pow, starRingEnd_apply]
  · rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm

/-- The reciprocal Riemann contour kernel commutes with conjugation for positive `x`. -/
theorem riemannZetaReciprocalContourKernel_conj {x : ℝ} (hx : 0 < x) (s : ℂ) :
    riemannZetaReciprocalContourKernel x
        (starRingEnd ℂ s) =
      starRingEnd ℂ
        (riemannZetaReciprocalContourKernel x s) := by
  rw [riemannZetaReciprocalContourKernel, riemannZetaReciprocalContourKernel,
    deriv_riemannZeta_conj s, riemannZeta_conj]
  have hexp : starRingEnd ℂ s - 1 = starRingEnd ℂ (s - 1) := by simp only [map_sub, map_one]
  rw [hexp, Complex.cpow_conj]
  · rw [Complex.conj_ofReal]
    simp only [map_neg, map_div₀, map_mul, map_sub, map_one, starRingEnd_apply]
  · rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact Real.pi_ne_zero.symm

/-- A lower horizontal logarithmic-kernel integral is the conjugate of the upper one. -/
theorem intervalIntegral_riemannZetaLogContourKernel_neg_height {x : ℝ} (hx : 0 < x) {a b T : ℝ}
    (hab : a ≤ b) :
    (∫ σ in a..b,
        riemannZetaLogContourKernel x
          ((σ : ℂ) - (T : ℂ) * Complex.I)) =
      starRingEnd ℂ
        (∫ σ in a..b,
          riemannZetaLogContourKernel x
            ((σ : ℂ) + (T : ℂ) * Complex.I)) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  simp_rw [show
      (fun σ : ℝ =>
          riemannZetaLogContourKernel x
            ((σ : ℂ) - (T : ℂ) * Complex.I)) =
        fun σ : ℝ =>
        starRingEnd ℂ
          (riemannZetaLogContourKernel x
            ((σ : ℂ) + (T : ℂ) * Complex.I))
      by
      funext σ
      have hs : (σ : ℂ) - (T : ℂ) * Complex.I = starRingEnd ℂ ((σ : ℂ) + (T : ℂ) * Complex.I) := by
        rw [sub_eq_add_neg]
        simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, mul_neg]
      rw [hs, riemannZetaLogContourKernel_conj hx]]
  rw [integral_conj]

/-- A lower horizontal reciprocal-kernel integral is the conjugate of the upper one. -/
theorem intervalIntegral_riemannZetaReciprocalContourKernel_neg_height {x : ℝ} (hx : 0 < x)
    {a b T : ℝ} (hab : a ≤ b) :
    (∫ σ in a..b,
        riemannZetaReciprocalContourKernel x
          ((σ : ℂ) - (T : ℂ) * Complex.I)) =
      starRingEnd ℂ
        (∫ σ in a..b,
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) + (T : ℂ) * Complex.I)) := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
  simp_rw [show
      (fun σ : ℝ =>
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) - (T : ℂ) * Complex.I)) =
        fun σ : ℝ =>
        starRingEnd ℂ
          (riemannZetaReciprocalContourKernel x
            ((σ : ℂ) + (T : ℂ) * Complex.I))
      by
      funext σ
      have hs : (σ : ℂ) - (T : ℂ) * Complex.I = starRingEnd ℂ ((σ : ℂ) + (T : ℂ) * Complex.I) := by
        rw [sub_eq_add_neg]
        simp only [map_add, Complex.conj_ofReal, map_mul, Complex.conj_I, mul_neg]
      rw [hs, riemannZetaReciprocalContourKernel_conj hx]]
  rw [integral_conj]

/-- The fixed lower-right logarithmic segment vanishes along the unified contour heights. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_neg_unifiedHeightSeq {x : ℝ}
    (hx : 0 < x) {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in lam..tau,
          riemannZetaLogContourKernel x
            ((σ : ℂ) -
              unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  have hu :=
    tendsto_intervalIntegral_riemannZetaLogContourKernel_unifiedHeightSeq
      hx hlam hlamtau htau
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp hu
  convert hc using 1
  · funext m
    exact
      intervalIntegral_riemannZetaLogContourKernel_neg_height
        hx hlamtau
  · simp only [map_zero]

/-- The fixed lower-right reciprocal segment vanishes along the unified contour heights. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_neg_unifiedHeightSeq {x : ℝ}
    (hx : 0 < x) {lam tau : ℝ} (hlam : -(1 : ℝ) / 2 ≤ lam) (hlamtau : lam ≤ tau) (htau : tau ≤ 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in lam..tau,
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) -
              unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  have hu :=
    tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unifiedHeightSeq
      hx hlam hlamtau htau
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp hu
  convert hc using 1
  · funext m
    exact
      intervalIntegral_riemannZetaReciprocalContourKernel_neg_height
        hx hlamtau
  · simp only [map_zero]

/--
The three vanishing far-left rectangle edges for the logarithmic kernel.

The terms are respectively the lower horizontal edge, the oppositely oriented upper horizontal
edge, and the left vertical edge with its factor `-I`.
-/
noncomputable def riemannZetaLogThreeFarLeftEdges (x : ℝ) (m : ℕ) : ℂ :=
  (∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
      riemannZetaLogContourKernel x
        ((σ : ℂ) -
          (farLeftHeightSeq m : ℂ) * Complex.I)) -
    (∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
      riemannZetaLogContourKernel x
        ((σ : ℂ) +
          (farLeftHeightSeq m : ℂ) * Complex.I)) -
    Complex.I •
      (∫ t in
        (-(farLeftHeightSeq m))..(farLeftHeightSeq m),
        riemannZetaLogContourKernel x
          (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))

/-- The lower growing logarithmic far-left segment vanishes on the unified sequence. -/
theorem tendsto_intervalIntegral_riemannZetaLogContourKernel_neg_unified_farLeft {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaLogContourKernel x
            ((σ : ℂ) -
              unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  have hu :=
    tendsto_intervalIntegral_riemannZetaLogContourKernel_unified_farLeft
      hx
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp hu
  convert hc using 1
  · funext m
    apply
      intervalIntegral_riemannZetaLogContourKernel_neg_height
        (by linarith only [hx])
    linarith only [Nat.cast_nonneg (α := ℝ) m]
  · simp only [map_zero]

/-- The lower growing reciprocal far-left segment vanishes on the unified sequence. -/
theorem tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_neg_unified_farLeft {x : ℝ}
    (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ =>
        ∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
          riemannZetaReciprocalContourKernel x
            ((σ : ℂ) -
              unifiedContourHeightSeq m * Complex.I))
      Filter.atTop (nhds 0) := by
  have hu :=
    tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unified_farLeft
      hx
  have hc := Complex.continuous_conj.continuousAt.tendsto.comp hu
  convert hc using 1
  · funext m
    apply
      intervalIntegral_riemannZetaReciprocalContourKernel_neg_height
        (by linarith)
    linarith
  · simp only [map_zero]

/-- The three non-right logarithmic rectangle edges on the unified contour sequence. -/
noncomputable def riemannZetaLogThreeUnifiedEdges (x : ℝ) (m : ℕ) : ℂ :=
  (∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
      riemannZetaLogContourKernel x
        ((σ : ℂ) -
          unifiedContourHeightSeq m * Complex.I)) -
    (∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
      riemannZetaLogContourKernel x
        ((σ : ℂ) +
          unifiedContourHeightSeq m * Complex.I)) -
    Complex.I •
      (∫ t in
        (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
        riemannZetaLogContourKernel x
          (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZetaLogThreeUnifiedEdges`. -/
noncomputable def riemannZetaReciprocalThreeUnifiedEdges (x : ℝ) (m : ℕ) : ℂ :=
  (∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
      riemannZetaReciprocalContourKernel x
        ((σ : ℂ) -
          unifiedContourHeightSeq m * Complex.I)) -
    (∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
      riemannZetaReciprocalContourKernel x
        ((σ : ℂ) +
          unifiedContourHeightSeq m * Complex.I)) -
    Complex.I •
      (∫ t in
        (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
        riemannZetaReciprocalContourKernel x
          (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I))

/-- The three non-right logarithmic edges vanish on the single good-height sequence. -/
theorem tendsto_riemannZetaLogThreeUnifiedEdges_atTop {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto (riemannZetaLogThreeUnifiedEdges x)
      Filter.atTop (nhds 0) := by
  have hlower :=
    tendsto_intervalIntegral_riemannZetaLogContourKernel_neg_unified_farLeft
      hx
  have hupper :=
    tendsto_intervalIntegral_riemannZetaLogContourKernel_unified_farLeft
      hx
  have hleft :=
    tendsto_intervalIntegral_riemannZetaLogContourKernel_unified_leftVertical
      hx
  convert hlower.sub hupper |>.sub (hleft.const_smul Complex.I) using 1
  · funext m
    rfl
  · simp only [sub_self, smul_eq_mul, mul_zero]

/-- The three non-right reciprocal edges vanish on the single good-height sequence. -/
theorem tendsto_riemannZetaReciprocalThreeUnifiedEdges_atTop {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (riemannZetaReciprocalThreeUnifiedEdges x)
      Filter.atTop (nhds 0) := by
  have hlower :=
    tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_neg_unified_farLeft
      hx
  have hupper :=
    tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unified_farLeft
      hx
  have hleft :=
    tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unified_leftVertical
      hx
  convert hlower.sub hupper |>.sub (hleft.const_smul Complex.I) using 1
  · funext m
    rfl
  · simp only [sub_self, smul_eq_mul, mul_zero]

/-- All non-right logarithmic pieces when the right boundary is at `Re s = τ`. -/
noncomputable def riemannZetaLogUnifiedBoundaryError (x τ : ℝ) (m : ℕ) : ℂ :=
  riemannZetaLogThreeUnifiedEdges x m +
      (∫ σ in (-1 / 2)..τ,
        riemannZetaLogContourKernel x
          ((σ : ℂ) -
            unifiedContourHeightSeq m * Complex.I)) -
    (∫ σ in (-1 / 2)..τ,
      riemannZetaLogContourKernel x
        ((σ : ℂ) +
          unifiedContourHeightSeq m * Complex.I))

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZetaLogUnifiedBoundaryError`. -/
noncomputable def riemannZetaReciprocalUnifiedBoundaryError (x τ : ℝ) (m : ℕ) : ℂ :=
  riemannZetaReciprocalThreeUnifiedEdges x m +
      (∫ σ in (-1 / 2)..τ,
        riemannZetaReciprocalContourKernel x
          ((σ : ℂ) -
            unifiedContourHeightSeq m * Complex.I)) -
    (∫ σ in (-1 / 2)..τ,
      riemannZetaReciprocalContourKernel x
        ((σ : ℂ) +
          unifiedContourHeightSeq m * Complex.I))

/-- The logarithmic boundary at `τ` is the finite-contour boundary error plus its truncated
right edge. -/
theorem rectangleBoundaryIntegral_log_unified_tau_eq {x τ : ℝ} (hx : 0 < x) (m : ℕ) :
    RectangleGeometry.rectangleBoundaryIntegral
        (riemannZetaLogContourKernel x)
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper τ m) =
      riemannZetaLogUnifiedBoundaryError x τ m +
        Complex.I •
          (∫ t in
            (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
            riemannZetaLogContourKernel x
              ((τ : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold RectangleGeometry.rectangleBoundaryIntegral
  simp only [unifiedRectangleLower,
    unifiedTauRectangleUpper]
  have hbottom :
    (∫ σ in (-(2 * (m : ℝ) + 1))..τ,
        riemannZetaLogContourKernel x
          ((σ : ℂ) +
            ((-(unifiedContourHeightSeq m) : ℝ) : ℂ) *
              Complex.I)) =
      ∫ σ in (-(2 * (m : ℝ) + 1))..τ,
        riemannZetaLogContourKernel x
          ((σ : ℂ) -
            unifiedContourHeightSeq m *
              Complex.I) := by
    apply intervalIntegral.integral_congr
    intro σ _
    apply congrArg (riemannZetaLogContourKernel x)
    push_cast
    ring
  have hleft :
    (∫ t in
        (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
        riemannZetaLogContourKernel x
          (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t in
        (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
        riemannZetaLogContourKernel x
          (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    apply congrArg (riemannZetaLogContourKernel x)
    push_cast
    ring
  rw [hbottom, hleft,
    intervalIntegral_riemannZetaLogContourKernel_unified_lower_split
      hx m,
    intervalIntegral_riemannZetaLogContourKernel_unified_upper_split
      hx m]
  unfold riemannZetaLogUnifiedBoundaryError riemannZetaLogThreeUnifiedEdges
  abel

/-- The reciprocal boundary at `τ` is the finite-contour boundary error plus its truncated
right edge. -/
theorem rectangleBoundaryIntegral_reciprocal_unified_tau_eq {x τ : ℝ} (hx : 0 < x) (m : ℕ) :
    RectangleGeometry.rectangleBoundaryIntegral
        (riemannZetaReciprocalContourKernel x)
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper τ m) =
      riemannZetaReciprocalUnifiedBoundaryError x τ m +
        Complex.I •
          (∫ t in
            (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
            riemannZetaReciprocalContourKernel x
              ((τ : ℂ) + (t : ℂ) * Complex.I)) := by
  unfold RectangleGeometry.rectangleBoundaryIntegral
  simp only [unifiedRectangleLower, unifiedTauRectangleUpper]
  have hbottom :
    (∫ σ in (-(2 * (m : ℝ) + 1))..τ,
        riemannZetaReciprocalContourKernel x
          ((σ : ℂ) +
            ((-(unifiedContourHeightSeq m) : ℝ) : ℂ) *
              Complex.I)) =
      ∫ σ in (-(2 * (m : ℝ) + 1))..τ,
        riemannZetaReciprocalContourKernel x
          ((σ : ℂ) -
            unifiedContourHeightSeq m *
              Complex.I) := by
    apply intervalIntegral.integral_congr
    intro σ _
    apply
      congrArg (riemannZetaReciprocalContourKernel x)
    push_cast
    ring
  have hleft :
    (∫ t in
        (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
        riemannZetaReciprocalContourKernel x
          (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t in
        (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
        riemannZetaReciprocalContourKernel x
          (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    apply
      congrArg (riemannZetaReciprocalContourKernel x)
    push_cast
    ring
  rw [hbottom, hleft,
    intervalIntegral_riemannZetaReciprocalContourKernel_unified_lower_split hx m,
    intervalIntegral_riemannZetaReciprocalContourKernel_unified_upper_split hx m]
  unfold riemannZetaReciprocalUnifiedBoundaryError riemannZetaReciprocalThreeUnifiedEdges
  abel

/-- Both finite contour identities apply to every unified rectangle ending at `τ > 1`. -/
theorem riemannZetaFiniteContourIdentities_unified_tau {x τ : ℝ} (hx : 0 < x) (hτ : 1 < τ) (m : ℕ) :
    RiemannZetaReciprocalFiniteContourIdentity x
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper τ m) ∧
      RiemannZetaLogFiniteContourIdentity x
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper τ m) := by
  apply
    riemannZetaFiniteContourIdentities_of_regular hx
  · simp only [unifiedRectangleLower,
      unifiedTauRectangleUpper]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  · simp only [unifiedRectangleLower,
      unifiedTauRectangleUpper]
    have hUpos : 0 < unifiedContourHeightSeq m :=
      (farLeftHeightSeq_pos m).trans_le
        (farLeftHeightSeq_le_unifiedContourHeightSeq m)
    linarith
  · exact
      llsRiemannRectangleBoundaryIsRegular_unified_tau
        hτ m

/-- The logarithmic rectangle boundary splits into the three vanishing edges and the right edge. -/
theorem rectangleBoundaryIntegral_log_unified_eq (x : ℝ) (m : ℕ) :
    RectangleGeometry.rectangleBoundaryIntegral
        (riemannZetaLogContourKernel x)
        (unifiedRectangleLower m)
        (unifiedRectangleUpper m) =
      riemannZetaLogThreeUnifiedEdges x m +
        Complex.I •
          (∫ t in
            (-(unifiedContourHeightSeq
                m))..(unifiedContourHeightSeq m),
            riemannZetaLogContourKernel x
              ((-1 / 2 : ℝ) + (t : ℂ) * Complex.I)) := by
  unfold RectangleGeometry.rectangleBoundaryIntegral
  simp only [unifiedRectangleLower,
    unifiedRectangleUpper]
  have hbottom :
    (∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
        riemannZetaLogContourKernel x
          ((σ : ℂ) +
            ((-(unifiedContourHeightSeq m) : ℝ) : ℂ) *
              Complex.I)) =
      ∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
        riemannZetaLogContourKernel x
          ((σ : ℂ) -
            unifiedContourHeightSeq m *
              Complex.I) := by
    apply intervalIntegral.integral_congr
    intro σ _
    apply congrArg (riemannZetaLogContourKernel x)
    push_cast
    ring
  have hleft :
    (∫ t in
        (-(unifiedContourHeightSeq
            m))..(unifiedContourHeightSeq m),
        riemannZetaLogContourKernel x
          (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t in
        (-(unifiedContourHeightSeq
            m))..(unifiedContourHeightSeq m),
        riemannZetaLogContourKernel x
          (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    apply congrArg (riemannZetaLogContourKernel x)
    push_cast
    ring
  rw [hbottom, hleft]
  unfold riemannZetaLogThreeUnifiedEdges
  abel

/-- The reciprocal rectangle boundary has the same four-edge decomposition. -/
theorem rectangleBoundaryIntegral_reciprocal_unified_eq (x : ℝ) (m : ℕ) :
    RectangleGeometry.rectangleBoundaryIntegral
        (riemannZetaReciprocalContourKernel x)
        (unifiedRectangleLower m)
        (unifiedRectangleUpper m) =
      riemannZetaReciprocalThreeUnifiedEdges x m +
        Complex.I •
          (∫ t in
            (-(unifiedContourHeightSeq
                m))..(unifiedContourHeightSeq m),
            riemannZetaReciprocalContourKernel x
              ((-1 / 2 : ℝ) + (t : ℂ) * Complex.I)) := by
  unfold RectangleGeometry.rectangleBoundaryIntegral
  simp only [unifiedRectangleLower, unifiedRectangleUpper]
  have hbottom :
    (∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
        riemannZetaReciprocalContourKernel x
          ((σ : ℂ) +
            ((-(unifiedContourHeightSeq m) : ℝ) : ℂ) *
              Complex.I)) =
      ∫ σ in (-(2 * (m : ℝ) + 1))..(-1 / 2),
        riemannZetaReciprocalContourKernel x
          ((σ : ℂ) -
            unifiedContourHeightSeq m *
              Complex.I) := by
    apply intervalIntegral.integral_congr
    intro σ _
    apply
      congrArg (riemannZetaReciprocalContourKernel x)
    push_cast
    ring
  have hleft :
    (∫ t in
        (-(unifiedContourHeightSeq
            m))..(unifiedContourHeightSeq m),
        riemannZetaReciprocalContourKernel x
          (((-(2 * (m : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
      ∫ t in
        (-(unifiedContourHeightSeq
            m))..(unifiedContourHeightSeq m),
        riemannZetaReciprocalContourKernel x
          (-(2 * m + 1 : ℂ) + (t : ℂ) * Complex.I) := by
    apply intervalIntegral.integral_congr
    intro t _
    apply
      congrArg (riemannZetaReciprocalContourKernel x)
    push_cast
    ring
  rw [hbottom, hleft]
  unfold riemannZetaReciprocalThreeUnifiedEdges
  abel

/-- Every non-right logarithmic boundary piece vanishes on the unified sequence. -/
theorem tendsto_riemannZetaLogUnifiedBoundaryError_atTop {x : ℝ} (hx : 1 < x) {τ : ℝ} (hτ : 1 < τ)
    (hτ2 : τ ≤ 2) :
    Filter.Tendsto
      (riemannZetaLogUnifiedBoundaryError x τ)
      Filter.atTop (nhds 0) := by
  have hfar :=
    tendsto_riemannZetaLogThreeUnifiedEdges_atTop hx
  have hlower :=
    tendsto_intervalIntegral_riemannZetaLogContourKernel_neg_unifiedHeightSeq
      (x := x) (by linarith) (lam := -1 / 2) (tau := τ) le_rfl (by linarith) hτ2
  have hupper :=
    tendsto_intervalIntegral_riemannZetaLogContourKernel_unifiedHeightSeq
      (x := x) (by linarith) (lam := -1 / 2) (tau := τ) le_rfl (by linarith) hτ2
  convert hfar.add hlower |>.sub hupper using 1
  · funext m
    rfl
  · simp only [add_zero, sub_self]

/-- Every non-right reciprocal boundary piece vanishes on the unified sequence. -/
theorem tendsto_riemannZetaReciprocalUnifiedBoundaryError_atTop {x : ℝ} (hx : 1 < x) {τ : ℝ}
    (hτ : 1 < τ) (hτ2 : τ ≤ 2) :
    Filter.Tendsto
      (riemannZetaReciprocalUnifiedBoundaryError x τ)
      Filter.atTop (nhds 0) := by
  have hfar :=
    tendsto_riemannZetaReciprocalThreeUnifiedEdges_atTop
      hx
  have hlower :=
    tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_neg_unifiedHeightSeq
      (x := x) (by linarith) (lam := -1 / 2) (tau := τ) le_rfl (by linarith) hτ2
  have hupper :=
    tendsto_intervalIntegral_riemannZetaReciprocalContourKernel_unifiedHeightSeq
      (x := x) (by linarith) (lam := -1 / 2) (tau := τ) le_rfl (by linarith) hτ2
  convert hfar.add hlower |>.sub hupper using 1
  · funext m
    rfl
  · simp only [add_zero, sub_self]

/-- The fully assembled logarithmic contour expression before residue identification. -/
noncomputable def riemannZetaLogUnifiedContourAssembly (x τ : ℝ) (m : ℕ) : ℂ :=
  riemannZetaLogUnifiedBoundaryError x τ m +
    Complex.I •
      (∫ t in
        (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
        riemannZetaLogContourKernel x
          ((τ : ℂ) + (t : ℂ) * Complex.I))

/-- The reciprocal-kernel analogue of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.riemannZetaLogUnifiedContourAssembly`. -/
noncomputable def riemannZetaReciprocalUnifiedContourAssembly (x τ : ℝ) (m : ℕ) : ℂ :=
  riemannZetaReciprocalUnifiedBoundaryError x τ m +
    Complex.I •
      (∫ t in
        (-(unifiedContourHeightSeq m))..(unifiedContourHeightSeq m),
        riemannZetaReciprocalContourKernel x
          ((τ : ℂ) + (t : ℂ) * Complex.I))

/-- The assembled logarithmic contour is exactly the finite-contour logarithmic residue ledger. -/
theorem riemannZetaLogUnifiedContourAssembly_eq_residueLedger {x τ : ℝ} (hx : 0 < x) (hτ : 1 < τ)
    (m : ℕ) :
    riemannZetaLogUnifiedContourAssembly x τ m =
      2 * Real.pi * Complex.I *
        riemannZetaLogContourResidueLedger x
          (unifiedRectangleLower m)
          (unifiedTauRectangleUpper τ m) := by
  unfold riemannZetaLogUnifiedContourAssembly
  rw [←
    rectangleBoundaryIntegral_log_unified_tau_eq hx m]
  exact
    (riemannZetaFiniteContourIdentities_unified_tau hx
        hτ m).2

/-- The assembled reciprocal contour is exactly the finite-contour reciprocal residue ledger. -/
theorem riemannZetaReciprocalUnifiedContourAssembly_eq_residueLedger {x τ : ℝ} (hx : 0 < x)
    (hτ : 1 < τ) (m : ℕ) :
    riemannZetaReciprocalUnifiedContourAssembly x τ m =
      2 * Real.pi * Complex.I *
        riemannZetaReciprocalContourResidueLedger x
          (unifiedRectangleLower m)
          (unifiedTauRectangleUpper τ m) := by
  unfold riemannZetaReciprocalUnifiedContourAssembly
  rw [←
    rectangleBoundaryIntegral_reciprocal_unified_tau_eq
      hx m]
  exact
    (riemannZetaFiniteContourIdentities_unified_tau hx
        hτ m).1

/-- The assembled logarithmic contour converges to the full right vertical integral. -/
theorem tendsto_riemannZetaLogUnifiedContourAssembly_atTop {x : ℝ} (hx : 1 < x) {τ : ℝ} (hτ : 1 < τ)
    (hτ2 : τ ≤ 2) :
    Filter.Tendsto
      (riemannZetaLogUnifiedContourAssembly x τ)
      Filter.atTop
      (nhds
        (Complex.I •
          ∫ t : ℝ,
            riemannZetaLogContourKernel x
              ((τ : ℂ) + (t : ℂ) * Complex.I))) := by
  have herr :=
    tendsto_riemannZetaLogUnifiedBoundaryError_atTop hx
      hτ hτ2
  have hright :=
    (tendsto_intervalIntegral_riemannZetaLogContourKernel
          (x := x) (by linarith) hτ).comp
      tendsto_unifiedContourHeightSeq_atTop
  convert herr.add (hright.const_smul Complex.I) using 1
  · funext m
    rfl
  · simp only [smul_eq_mul, zero_add]

/-- The assembled reciprocal contour converges to the full right vertical integral. -/
theorem tendsto_riemannZetaReciprocalUnifiedContourAssembly_atTop {x : ℝ} (hx : 1 < x) {τ : ℝ}
    (hτ : 1 < τ) (hτ2 : τ ≤ 2) :
    Filter.Tendsto
      (riemannZetaReciprocalUnifiedContourAssembly x τ)
      Filter.atTop
      (nhds
        (Complex.I •
          ∫ t : ℝ,
            riemannZetaReciprocalContourKernel x
              ((τ : ℂ) + (t : ℂ) * Complex.I))) := by
  have herr :=
    tendsto_riemannZetaReciprocalUnifiedBoundaryError_atTop
      hx hτ hτ2
  have hright :=
    (tendsto_intervalIntegral_riemannZetaReciprocalContourKernel
          (x := x) (by linarith) hτ).comp
      tendsto_unifiedContourHeightSeq_atTop
  convert herr.add (hright.const_smul Complex.I) using 1
  · funext m
    rfl
  · simp only [smul_eq_mul, zero_add]

/-- For every unified rectangle with `τ > 1`, the logarithmic Mellin-pole
ledger is the sum of the residues at zero and one. -/
theorem riemannZetaLogMellinPoleLedger_unifiedTau_eq {x τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    riemannZetaLogMellinPoleLedger x
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper τ m) =
      riemannZetaLogResidueAtZero x +
        riemannZetaLogResidueAtOne x := by
  unfold riemannZetaLogMellinPoleLedger
  rw [ite_eq_left (zero_mem_unifiedTauRectangle hτ m),
    ite_eq_left (one_mem_unifiedTauRectangle hτ m)]

/-- The reciprocal Mellin-pole ledger is the constant sum of both (fully closed-form) residues,
for every unified `τ`-rectangle with `τ > 1`. -/
theorem riemannZetaReciprocalMellinPoleLedger_unifiedTau_eq {x τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    riemannZetaReciprocalMellinPoleLedger x
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper τ m) =
      riemannZetaReciprocalResidueAtZero x +
        riemannZetaReciprocalResidueAtOne x := by
  unfold riemannZetaReciprocalMellinPoleLedger
  rw [ite_eq_left (zero_mem_unifiedTauRectangle hτ m),
    ite_eq_left (one_mem_unifiedTauRectangle hτ m)]

/-- The logarithmic residue ledger splits into the constant Mellin-pole part and the growing
zero-ledger part, for every unified `τ`-rectangle with `τ > 1`. -/
theorem riemannZetaLogContourResidueLedger_unifiedTau_eq {x τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    riemannZetaLogContourResidueLedger x
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper τ m) =
      (riemannZetaLogResidueAtZero x +
          riemannZetaLogResidueAtOne x) +
        riemannZetaLogContourZeroLedger x
          (unifiedRectangleLower m)
          (unifiedTauRectangleUpper τ m) := by
  unfold riemannZetaLogContourResidueLedger
  rw [riemannZetaLogMellinPoleLedger_unifiedTau_eq hτ]

/-- The reciprocal residue ledger splits into the constant Mellin-pole part and the growing
zero-ledger part, for every unified `τ`-rectangle with `τ > 1`. -/
theorem riemannZetaReciprocalContourResidueLedger_unifiedTau_eq {x τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    riemannZetaReciprocalContourResidueLedger x
        (unifiedRectangleLower m)
        (unifiedTauRectangleUpper τ m) =
      (riemannZetaReciprocalResidueAtZero x +
          riemannZetaReciprocalResidueAtOne x) +
        riemannZetaReciprocalContourZeroLedger x
          (unifiedRectangleLower m)
          (unifiedTauRectangleUpper τ m) := by
  unfold riemannZetaReciprocalContourResidueLedger
  rw [riemannZetaReciprocalMellinPoleLedger_unifiedTau_eq hτ]

/-- For `x > 1` and `1 < τ ≤ 2`, the finite logarithmic residue ledger times
`2πi` converges along the unified rectangles to `I` times the full right
vertical-line integral. -/
theorem tendsto_riemannZetaLogContourResidueLedger_atTop {x : ℝ} (hx : 1 < x) {τ : ℝ} (hτ : 1 < τ)
    (hτ2 : τ ≤ 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        2 * Real.pi * Complex.I *
          riemannZetaLogContourResidueLedger x
            (unifiedRectangleLower m)
            (unifiedTauRectangleUpper τ m))
      Filter.atTop
      (nhds
        (Complex.I •
          ∫ t : ℝ,
            riemannZetaLogContourKernel x
              ((τ : ℂ) + (t : ℂ) * Complex.I))) := by
  have heq :
    (fun m : ℕ =>
        2 * Real.pi * Complex.I *
          riemannZetaLogContourResidueLedger x
            (unifiedRectangleLower m)
            (unifiedTauRectangleUpper τ m)) =
      riemannZetaLogUnifiedContourAssembly x τ := by
    funext m
    exact
      (riemannZetaLogUnifiedContourAssembly_eq_residueLedger
          (zero_lt_one.trans hx) hτ m).symm
  rw [heq]
  exact
    tendsto_riemannZetaLogUnifiedContourAssembly_atTop
      hx hτ hτ2

/-- For `x > 1` and `1 < τ ≤ 2`, the finite reciprocal residue ledger times
`2πi` converges along the unified rectangles to `I` times the full right
vertical-line integral. -/
theorem tendsto_riemannZetaReciprocalContourResidueLedger_atTop {x : ℝ} (hx : 1 < x) {τ : ℝ}
    (hτ : 1 < τ) (hτ2 : τ ≤ 2) :
    Filter.Tendsto
      (fun m : ℕ =>
        2 * Real.pi * Complex.I *
          riemannZetaReciprocalContourResidueLedger x
            (unifiedRectangleLower m)
            (unifiedTauRectangleUpper τ m))
      Filter.atTop
      (nhds
        (Complex.I •
          ∫ t : ℝ,
            riemannZetaReciprocalContourKernel x
              ((τ : ℂ) + (t : ℂ) * Complex.I))) := by
  have heq :
    (fun m : ℕ =>
        2 * Real.pi * Complex.I *
          riemannZetaReciprocalContourResidueLedger x
            (unifiedRectangleLower m)
            (unifiedTauRectangleUpper τ m)) =
      riemannZetaReciprocalUnifiedContourAssembly x
        τ := by
    funext m
    exact
      (riemannZetaReciprocalUnifiedContourAssembly_eq_residueLedger
          (zero_lt_one.trans hx) hτ m).symm
  rw [heq]
  exact
    tendsto_riemannZetaReciprocalUnifiedContourAssembly_atTop
      hx hτ hτ2

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
