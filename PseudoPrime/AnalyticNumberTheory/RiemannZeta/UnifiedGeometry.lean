/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

import PseudoPrime.AnalyticNumberTheory.RiemannZeta.UnifiedHeight
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LeftVerticalLogDeriv
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SingularityGeometry
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogDerivBound

/-! # Kernel-independent height and rectangle constructions -/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- The growing far-left segment length divided by the unified height tends to zero. -/
theorem tendsto_farLeftLength_div_unifiedContourHeightSeq :
    Filter.Tendsto (fun m : ℕ => (2 * (m : ℝ) + 1 / 2) / unifiedContourHeightSeq m) Filter.atTop
      (nhds 0) := by
  have hbound :
    ∀ m : ℕ, (2 * (m : ℝ) + 1 / 2) / unifiedContourHeightSeq m ≤ 3 / (farLeftBTerm m + 1) := by
    intro m
    have hUpos : 0 < unifiedContourHeightSeq m :=
      (farLeftHeightSeq_pos m).trans_le (farLeftHeightSeq_le_unifiedContourHeightSeq m)
    have hlength : 2 * (m : ℝ) + 1 / 2 ≤ 3 * ((m : ℝ) + 1) := by
      linarith only [Nat.cast_nonneg (α := ℝ) m]
    calc
      (2 * (m : ℝ) + 1 / 2) / unifiedContourHeightSeq m ≤
          (2 * (m : ℝ) + 1 / 2) / farLeftHeightSeq m :=
        by
        exact
          div_le_div_of_nonneg_left (by positivity) (farLeftHeightSeq_pos m)
            (farLeftHeightSeq_le_unifiedContourHeightSeq m)
      _ ≤ (3 * ((m : ℝ) + 1)) / farLeftHeightSeq m :=
        div_le_div_of_nonneg_right hlength (farLeftHeightSeq_pos m).le
      _ = 3 / (farLeftBTerm m + 1) := by
        simp only [farLeftHeightSeq]
        field_simp
  have hden : Filter.Tendsto (fun m : ℕ => farLeftBTerm m + 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_add_const_right Filter.atTop 1 tendsto_farLeftBTerm_atTop
  have hrhs : Filter.Tendsto (fun m : ℕ => 3 / (farLeftBTerm m + 1)) Filter.atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, Pi.inv_apply, mul_zero] using hden.inv_tendsto_atTop.const_mul 3
  exact
    squeeze_zero
      (fun m =>
        div_nonneg (by positivity)
          ((farLeftHeightSeq_pos m).trans_le (farLeftHeightSeq_le_unifiedContourHeightSeq m)).le)
      hbound hrhs

/-- The unified height still has polynomial growth and is absorbed by geometric decay. -/
theorem tendsto_unifiedContourHeightSeq_sq_mul_pow_of_lt_one {r : ℝ} (hr : 0 ≤ r) (h'r : r < 1) :
    Filter.Tendsto (fun m : ℕ => unifiedContourHeightSeq m ^ 2 * r ^ m) Filter.atTop (nhds 0) := by
  have hpow := tendsto_farLeftHeightSeq_sq_mul_pow_of_lt_one hr h'r
  have hrpow := tendsto_pow_atTop_nhds_zero_of_lt_one hr h'r
  have hmajor :
    Filter.Tendsto (fun m : ℕ => (2 * farLeftHeightSeq m ^ 2 + 200) * r ^ m) Filter.atTop
      (nhds 0) := by
    have hsum := (hpow.const_mul 2).add (hrpow.const_mul 200)
    convert hsum using 1
    · funext m
      ring
    · ring_nf
  apply squeeze_zero (fun m => by positivity) (fun m => ?_) hmajor
  have hUle : unifiedContourHeightSeq m ≤ farLeftHeightSeq m + 10 :=
    (unifiedContourHeightSeq_lt_farLeftHeightSeq_add_ten m).le
  have hFnn : 0 ≤ farLeftHeightSeq m := (farLeftHeightSeq_pos m).le
  have hUnn : 0 ≤ unifiedContourHeightSeq m :=
    hFnn.trans (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hsquare : unifiedContourHeightSeq m ^ 2 ≤ 2 * farLeftHeightSeq m ^ 2 + 200 := by
    nlinarith only [hUle, hFnn, hUnn, sq_nonneg (farLeftHeightSeq m - 10)]
  exact mul_le_mul_of_nonneg_right hsquare (by positivity)

/-- Zeta has no zero on the upper horizontal line selected by the unified good-height sequence. -/
theorem riemannZeta_ne_zero_on_unified_upper (m : ℕ) (σ : ℝ) :
    riemannZeta ((σ : ℂ) + unifiedContourHeightSeq m * Complex.I) ≠ 0 := by
  exact
    riemannZeta_ne_zero_of_good_height
      (by linarith only [goodHeightSeq_mem (farLeftGoodHeightIndex m) |>.1])
      (goodHeightSeq_mem (farLeftGoodHeightIndex m)) (unifiedContourHeightSeq_good m) σ

/-- Zeta has no zero on the conjugate lower horizontal line of the unified sequence. -/
theorem riemannZeta_ne_zero_on_unified_lower (m : ℕ) (σ : ℝ) :
    riemannZeta ((σ : ℂ) - unifiedContourHeightSeq m * Complex.I) ≠ 0 := by
  intro hzero
  apply riemannZeta_ne_zero_on_unified_upper m σ
  have hconj :
    (σ : ℂ) + unifiedContourHeightSeq m * Complex.I =
      starRingEnd ℂ ((σ : ℂ) - unifiedContourHeightSeq m * Complex.I) := by
    rw [sub_eq_add_neg]
    simp only [map_add, Complex.conj_ofReal, map_neg, map_mul, Complex.conj_I, mul_neg, neg_neg]
  rw [hconj, riemannZeta_conj, hzero]
  simp only [map_zero]

/-- A uniform linear coefficient for the far-left zeta logarithmic-derivative bound. -/
noncomputable def unifiedFarLeftLinearConst : ℝ :=
  |qMinusOneHorizontalFarLeftConst| +
    Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi / 2) ^ 2) +
    (1 + 20 * Real.pi)

/-- On the unified heights, the far-left logarithmic-derivative majorant is linear in height. -/
theorem farLeftZetaLogDerivBound_unified_le (m : ℕ) :
    farLeftZetaLogDerivBound m (unifiedContourHeightSeq m) ≤
      unifiedFarLeftLinearConst * unifiedContourHeightSeq m := by
  set T := unifiedContourHeightSeq m
  have hT1 : (1 : ℝ) ≤ T :=
    (one_le_farLeftHeightSeq m).trans (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hTpos : 0 < T := one_pos.trans_le hT1
  have hsinh : Real.sinh (Real.pi / 2) ≤ Real.sinh (Real.pi * T / 2) :=
    Real.sinh_le_sinh.mpr (by nlinarith only [Real.pi_pos, hT1])
  have hsinhpos : 0 < Real.sinh (Real.pi / 2) := by
    rw [show (0 : ℝ) = Real.sinh 0 from Real.sinh_zero.symm]
    exact Real.sinh_lt_sinh.mpr (by positivity)
  have hD :
    Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi * T / 2) ^ 2) ≤
      Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi / 2) ^ 2) := by
    gcongr
  have hB : farLeftBTerm m ≤ T :=
    (farLeftBTerm_le_farLeftHeightSeq m).trans (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  unfold farLeftZetaLogDerivBound unifiedFarLeftLinearConst
  rw [abs_of_pos hTpos]
  have hA := le_abs_self qMinusOneHorizontalFarLeftConst
  have hDnn : 0 ≤ Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi / 2) ^ 2) := by positivity
  have hconst :
    |qMinusOneHorizontalFarLeftConst| +
        Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi / 2) ^ 2) ≤
      (|qMinusOneHorizontalFarLeftConst| +
          Real.pi / 2 * Real.sqrt (1 + 1 / Real.sinh (Real.pi / 2) ^ 2)) *
        T :=
    le_mul_of_one_le_right (by positivity) hT1
  nlinarith only [hA, hDnn, hconst, hD, hB]

/-- A uniform linear coefficient for the left-vertical zeta bound. -/
noncomputable def unifiedLeftVerticalLinearConst : ℝ :=
  |qMinusOneLeftVerticalConst| + 4 * Real.pi + 2

/-- The left-vertical logarithmic-derivative bound is linear on the unified heights. -/
theorem leftVerticalZetaLogDerivBound_unified_le (m : ℕ) :
    leftVerticalZetaLogDerivBound m (unifiedContourHeightSeq m) ≤
      unifiedLeftVerticalLinearConst * unifiedContourHeightSeq m := by
  set T := unifiedContourHeightSeq m
  have hT1 : (1 : ℝ) ≤ T :=
    (one_le_farLeftHeightSeq m).trans (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hTm : (m : ℝ) + 1 ≤ T :=
    (add_one_le_farLeftHeightSeq m).trans (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hTpos : 0 < T := one_pos.trans_le hT1
  unfold leftVerticalZetaLogDerivBound unifiedLeftVerticalLinearConst
  rw [abs_of_pos hTpos]
  have hC := le_abs_self qMinusOneLeftVerticalConst
  have hCT : |qMinusOneLeftVerticalConst| ≤ |qMinusOneLeftVerticalConst| * T :=
    le_mul_of_one_le_right (abs_nonneg _) hT1
  nlinarith only [hC, hCT, hTm]

/-- The lower-left corner of the unified far-left rectangle. -/
noncomputable def unifiedRectangleLower (m : ℕ) : ℂ :=
  ⟨-(2 * (m : ℝ) + 1), -(unifiedContourHeightSeq m)⟩

/-- The upper-right corner of the unified far-left rectangle. -/
noncomputable def unifiedRectangleUpper (m : ℕ) : ℂ :=
  ⟨-1 / 2, unifiedContourHeightSeq m⟩

/-- The upper-right corner of a unified rectangle whose right edge is `τ`. -/
noncomputable def unifiedTauRectangleUpper (τ : ℝ) (m : ℕ) : ℂ :=
  ⟨τ, unifiedContourHeightSeq m⟩

/-- The unified rectangle ending at `τ > 1` has no kernel singularity on its boundary. -/
theorem llsRiemannRectangleBoundaryIsRegular_unified_tau {τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    RiemannZetaRectangleBoundaryIsRegular (unifiedRectangleLower m)
      (unifiedTauRectangleUpper τ m) := by
  intro s hs
  have hUpos : 0 < unifiedContourHeightSeq m :=
    (farLeftHeightSeq_pos m).trans_le (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hre : (unifiedRectangleLower m).re < (unifiedTauRectangleUpper τ m).re := by
    simp only [unifiedRectangleLower, unifiedTauRectangleUpper]
    have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    linarith
  have him : (unifiedRectangleLower m).im < (unifiedTauRectangleUpper τ m).im := by
    simp only [unifiedRectangleLower, unifiedTauRectangleUpper]
    linarith
  have hsbox := hs.1
  by_cases hsleft : s.re = (unifiedRectangleLower m).re
  · refine ⟨?_, ?_, ?_⟩
    · intro hs0
      have hreal := congrArg Complex.re hs0
      rw [hsleft] at hreal
      simp only [unifiedRectangleLower, Complex.zero_re] at hreal
      nlinarith
    · intro hs1
      have hreal := congrArg Complex.re hs1
      rw [hsleft] at hreal
      simp only [unifiedRectangleLower, Complex.one_re] at hreal
      nlinarith
    · apply riemannZeta_ne_zero_of_re_neg
      · rw [hsleft]
        simp only [unifiedRectangleLower]
        nlinarith
      · intro n hsn
        have hreal := congrArg Complex.re hsn
        rw [hsleft] at hreal
        simp only [unifiedRectangleLower, Complex.neg_re, Complex.mul_re, Complex.add_re,
          Complex.natCast_re] at hreal
        have hreal' : (2 : ℝ) * m + 1 = 2 * ((n : ℝ) + 1) := by
          norm_num only [Complex.neg_re, Complex.neg_im, Complex.one_re, Complex.one_im,
            Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.natCast_re,
            Complex.natCast_im, Complex.im_ofNat, RCLike.ofNat_re, RCLike.ofNat_im, zero_mul,
            mul_zero, one_mul, mul_one, sub_zero, add_zero, zero_add] at hreal ⊢
          have h2re : Complex.re (2 : ℂ) = 2 := by
            change (2 : ℝ) = 2
            rfl
          rw [h2re] at hreal
          linarith [hreal]
        have hcast : (2 : ℤ) * m + 1 = 2 * ((n : ℤ) + 1) := by exact_mod_cast hreal'
        omega
  by_cases hsright : s.re = (unifiedTauRectangleUpper τ m).re
  · refine ⟨?_, ?_, ?_⟩
    · intro hs0
      have hreal := congrArg Complex.re hs0
      rw [hsright] at hreal
      simp only [unifiedTauRectangleUpper, Complex.zero_re] at hreal
      linarith
    · intro hs1
      have hreal := congrArg Complex.re hs1
      rw [hsright] at hreal
      simp only [unifiedTauRectangleUpper, Complex.one_re] at hreal
      linarith
    · apply riemannZeta_ne_zero_of_one_lt_re
      rw [hsright]
      simpa only [unifiedTauRectangleUpper] using hτ
  by_cases hslower : s.im = (unifiedRectangleLower m).im
  · have hne : riemannZeta s ≠ 0 := by
      have heq : s = (s.re : ℂ) - unifiedContourHeightSeq m * Complex.I := by
        apply Complex.ext
        · simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, sub_zero]
        · rw [hslower]
          simp only [unifiedRectangleLower, neg_add_rev, Complex.sub_im, Complex.ofReal_im,
            Complex.mul_im, Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero,
            add_zero, zero_sub]
      rw [heq]
      exact riemannZeta_ne_zero_on_unified_lower m s.re
    refine ⟨?_, ?_, hne⟩
    · intro hs0
      have himag := congrArg Complex.im hs0
      rw [hslower] at himag
      simp only [unifiedRectangleLower, Complex.zero_im] at himag
      linarith
    · intro hs1
      have himag := congrArg Complex.im hs1
      rw [hslower] at himag
      simp only [unifiedRectangleLower, Complex.one_im] at himag
      linarith
  by_cases hsupper : s.im = (unifiedTauRectangleUpper τ m).im
  · have hne : riemannZeta s ≠ 0 := by
      have heq : s = (s.re : ℂ) + unifiedContourHeightSeq m * Complex.I := by
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
        · rw [hsupper]
          simp only [unifiedTauRectangleUpper, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add]
      rw [heq]
      exact riemannZeta_ne_zero_on_unified_upper m s.re
    refine ⟨?_, ?_, hne⟩
    · intro hs0
      have himag := congrArg Complex.im hs0
      rw [hsupper] at himag
      simp only [unifiedTauRectangleUpper, Complex.zero_im] at himag
      linarith
    · intro hs1
      have himag := congrArg Complex.im hs1
      rw [hsupper] at himag
      simp only [unifiedTauRectangleUpper, Complex.one_im] at himag
      linarith
  exfalso
  apply hs.2
  exact
    RectangleGeometry.mem_rectangleOpenBox_of_mem_closedBox_of_ne hre him hsbox hsleft hsright
      hslower hsupper

/-- Both Mellin singularities lie inside every unified rectangle ending at `τ > 1`. -/
theorem zero_one_mem_llsClosedRectangle_unified_tau {τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    (0 : ℂ) ∈
        Rectangle.rectangleClosedBox (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m) ∧
      (1 : ℂ) ∈
        Rectangle.rectangleClosedBox (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m) := by
  have hUpos : 0 < unifiedContourHeightSeq m :=
    (farLeftHeightSeq_pos m).trans_le (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hleft : -(2 * (m : ℝ) + 1) < τ := by linarith
  have hheight : -unifiedContourHeightSeq m < unifiedContourHeightSeq m := by linarith
  constructor
  · change
      (0 : ℝ) ∈ Set.uIcc (-(2 * (m : ℝ) + 1)) τ ∧
        (0 : ℝ) ∈ Set.uIcc (-unifiedContourHeightSeq m) (unifiedContourHeightSeq m)
    rw [Set.uIcc_of_lt hleft, Set.uIcc_of_lt hheight]
    constructor <;> constructor <;> linarith
  · change
      (1 : ℝ) ∈ Set.uIcc (-(2 * (m : ℝ) + 1)) τ ∧
        (0 : ℝ) ∈ Set.uIcc (-unifiedContourHeightSeq m) (unifiedContourHeightSeq m)
    rw [Set.uIcc_of_lt hleft, Set.uIcc_of_lt hheight]
    constructor <;> constructor <;> linarith

/-- A point with real part in `[-(2m+1),τ]` and imaginary part in `[-H_m,H_m]`
belongs to the corresponding unified rectangle. No separate assumption `τ > 1` is needed. -/
theorem mem_unifiedTauRectangle (τ : ℝ) (m : ℕ) {p : ℂ} (hre1 : -(2 * (m : ℝ) + 1) ≤ p.re)
    (hre2 : p.re ≤ τ) (him1 : -unifiedContourHeightSeq m ≤ p.im)
    (him2 : p.im ≤ unifiedContourHeightSeq m) :
    p ∈ Rectangle.rectangleClosedBox (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m) := by
  unfold Rectangle.rectangleClosedBox unifiedRectangleLower unifiedTauRectangleUpper
  refine ⟨Set.mem_uIcc.mpr (Or.inl ⟨hre1, hre2⟩), Set.mem_uIcc.mpr (Or.inl ⟨him1, him2⟩)⟩

/-- The origin lies in every unified `τ`-rectangle with `τ > 1`. -/
theorem zero_mem_unifiedTauRectangle {τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    (0 : ℂ) ∈
      Rectangle.rectangleClosedBox (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m) := by
  have hH : (1 : ℝ) ≤ unifiedContourHeightSeq m :=
    (one_le_farLeftHeightSeq m).trans (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  exact
    mem_unifiedTauRectangle τ m (p := 0)
      (by
        simp only [neg_add_rev, Complex.zero_re, add_neg_le_iff_le_add, zero_add]; linarith)
      (by
        simp only [Complex.zero_re]; linarith)
      (by
        simp only [Complex.zero_im, Left.neg_nonpos_iff]; linarith)
      (by
        simp only [Complex.zero_im]; linarith)

/-- The point `1` lies in every unified `τ`-rectangle with `τ > 1`. -/
theorem one_mem_unifiedTauRectangle {τ : ℝ} (hτ : 1 < τ) (m : ℕ) :
    (1 : ℂ) ∈
      Rectangle.rectangleClosedBox (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m) := by
  have hH : (1 : ℝ) ≤ unifiedContourHeightSeq m :=
    (one_le_farLeftHeightSeq m).trans (farLeftHeightSeq_le_unifiedContourHeightSeq m)
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  exact
    mem_unifiedTauRectangle τ m (p := 1)
      (by
        simp only [neg_add_rev, Complex.one_re, add_neg_le_iff_le_add]; linarith)
      (by
        simp only [Complex.one_re]; linarith)
      (by
        simp only [Complex.one_im, Left.neg_nonpos_iff]; linarith)
      (by
        simp only [Complex.one_im]; linarith)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
