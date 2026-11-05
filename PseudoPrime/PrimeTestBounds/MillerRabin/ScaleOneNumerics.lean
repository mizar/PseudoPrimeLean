/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.ScaleOneWitness
public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneGap

/-! # Root bounds for the scale-one adaptive Gaussian cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Above scale 25000, the adaptive Gaussian cutoff has the square-root and fourth-root
bounds needed by the scale-one gap. A positive lower bound on the scale's square root
controls the fourth root; the coefficient also stays below 0.29. -/
theorem scaleOne_cutoff_roots {L v : ℝ} (hL : 25000 ≤ L) (hv : 0 < v) (hv2 : v ^ 2 ≤ L) :
    let C := (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2
    let x := C * L ^ 2
    1 < x ∧
      (5313 / 10000 : ℝ) * L ≤ Real.sqrt x ∧
      Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ (147 / 200 : ℝ) * L / v ∧ C ≤ 29 / 100 := by
  let C := (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2
  let x := C * L ^ 2
  have hLp : 0 < L := by linarith only [hL]
  have hC := scaleOne_gaussian_floor L hL
  change (5313 / 10000 : ℝ) ^ 2 ≤ C at hC
  have hC0 : 0 ≤ C := (sq_nonneg (5313 / 10000 : ℝ)).trans hC
  have hslope := scaleOne_gaussian_slope L hL
  have hsquare :=
    pow_le_pow_left₀ (by linarith only [hslope.1] : 0 ≤ adaptiveGaussianA L) hslope.2 2
  have hupper : C ≤ (29 / 100 : ℝ) := by
    dsimp only [C]
    nlinarith only [hsquare]
  have hx0 : 0 ≤ x := mul_nonneg hC0 (sq_nonneg L)
  have hroot : (5313 / 10000 : ℝ) * L ≤ Real.sqrt x := by
    apply (Real.le_sqrt (mul_nonneg (by norm_num only) hLp.le) hx0).mpr
    dsimp only [x]
    nlinarith only [mul_le_mul_of_nonneg_right hC (sq_nonneg L)]
  have hx : 1 < x := by nlinarith only [Real.sq_sqrt hx0, hroot, hL]
  have hrootup : Real.sqrt x ≤ L := by
    apply Real.sqrt_le_iff.mpr
    exact
      ⟨hLp.le, by
        dsimp only [x]; nlinarith only [mul_le_mul_of_nonneg_right hupper (sq_nonneg L)]⟩
  have hrootfine : Real.sqrt x ≤ (147 / 200 : ℝ) ^ 2 * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · exact mul_nonneg (by norm_num only) hLp.le
    · dsimp only [x]
      nlinarith only [mul_le_mul_of_nonneg_right hupper (sq_nonneg L)]
  have hq2 : (x ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt x := by
    have he := Real.rpow_mul (zero_lt_one.trans hx).le (1 / 4) 2
    norm_num only [Real.rpow_two] at he
    rw [Real.sqrt_eq_rpow]
    exact he.symm
  have hq0 : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg (zero_lt_one.trans hx).le _
  have hq : x ^ (1 / 4 : ℝ) ≤ (147 / 200 : ℝ) * Real.sqrt L := by
    have hh : 0 ≤ (147 / 200 : ℝ) * Real.sqrt L :=
      mul_nonneg (by norm_num only) (Real.sqrt_nonneg _)
    nlinarith only [hrootfine, hq2, Real.sq_sqrt hLp.le, hq0, hh]
  have hs : Real.sqrt L ≤ L / v := by
    apply (le_div_iff₀ hv).2
    have hh := Real.sq_sqrt hLp.le
    have hp : 0 ≤ v * Real.sqrt L := mul_nonneg hv.le (Real.sqrt_nonneg _)
    have hm := mul_le_mul_of_nonneg_left hv2 hLp.le
    nlinarith only [hh, hp, hm]
  refine ⟨hx, hroot, hrootup, ?_, hupper⟩
  have hm := mul_le_mul_of_nonneg_left hs (by norm_num only : (0 : ℝ) ≤ 147 / 200)
  exact hq.trans (by simpa only [mul_div_assoc] using hm)

/-- On the first interior cell, exact rational logarithm certificates place the
adaptive cutoff between logarithmic scales 18 and 26. -/
theorem scaleOne_log_first {L : ℝ} (hL : 25000 ≤ L) (hU : L ≤ 500000) :
    (18 : ℝ) ≤ Real.log (((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2) ∧
      Real.log (((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2) ≤ 26 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 176000000 27 32 18 20 = true from by
          decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 72500000000 36 32 25 26 = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat] at hl hu
  have hc := scaleOne_gaussian_floor L hL
  have hh := scaleOne_cutoff_roots (v := 158) hL (by norm_num only) (by nlinarith only [hL])
  dsimp only at hh
  have hpos : 0 < ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2 := by
    have hcpos : 0 < (21 / 10 : ℝ) * adaptiveGaussianA L ^ 2 := lt_of_lt_of_le (by norm_num only) hc
    exact mul_pos hcpos (sq_pos_of_pos (by linarith only [hL]))
  have hbase : (176000000 : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2 := by
    have hs :=
      (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 25000) (by linarith only [hL] : 0 ≤ L)).mpr hL
    have ha := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
    nlinarith only [hs, ha]
  have htop : ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2 ≤ 72500000000 := by
    have hs :=
      (sq_le_sq₀ (by linarith only [hL] : 0 ≤ L) (by norm_num only : (0 : ℝ) ≤ 500000)).mpr hU
    have ha := mul_le_mul_of_nonneg_right hh.2.2.2.2 (sq_nonneg L)
    nlinarith only [hs, ha]
  constructor
  · exact hl.trans (Real.log_le_log (by norm_num only) hbase)
  · exact (Real.log_le_log hpos htop).trans hu

/-- From logarithmic scale 500000, the adaptive cutoff has logarithm at least 24.
A rational logarithm certificate and the coefficient floor give the bound. -/
theorem scaleOne_log_second {L : ℝ} (hL : 500000 ≤ L) :
    (24 : ℝ) ≤ Real.log (((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2) := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 70000000000 36 32 24 26 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hl
  have hc := scaleOne_gaussian_floor L (by linarith only [hL])
  have hbase : (70000000000 : ℝ) ≤ ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2 := by
    have hs :=
      (sq_le_sq₀ (by norm_num only : (0 : ℝ) ≤ 500000) (by linarith only [hL] : 0 ≤ L)).mpr hL
    have ha := mul_le_mul_of_nonneg_right hc (sq_nonneg L)
    nlinarith only [hs, ha]
  exact hl.trans (Real.log_le_log (by norm_num only) hbase)

/-- The two certified rational cells imply the normalized interior margin at every
logarithmic scale from 25000 while the cutoff remains inside triangular support. -/
theorem scaleOne_interior_margin {L : ℝ} (hL : 25000 ≤ L)
    (hu : ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2 ≤ Real.exp 36) :
    let x := ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + (72 - Real.log x) * L +
        9961 <
      (220 - 4 * Real.log x) * Real.sqrt x - (4576 - 78 * Real.log x) * x ^ (1 / 4 : ℝ) := by
  let x := ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2
  have hx := (scaleOne_cutoff_roots (v := 158) hL (by norm_num only) (by nlinarith only [hL])).1
  change 1 < x at hx
  have hlog : Real.log x ≤ 36 := by
    have h := Real.log_le_log (zero_lt_one.trans hx) hu
    simpa only [Real.log_exp] using h
  by_cases hU : L ≤ 500000
  · have hroots := scaleOne_cutoff_roots (v := 158) hL (by norm_num only) (by nlinarith only [hL])
    have hlogs := scaleOne_log_first hL hU
    dsimp only at hroots hlogs
    exact
      LLS.PaperStatements.scaleOne_margin_of_cell (T := 25000) (v := 158) (y0 := 18) (y1 := 26)
        (by norm_num only) hL hlogs.1 hlogs.2 (by norm_num only) hroots.2.1
        (Real.rpow_nonneg (zero_lt_one.trans hx).le _) hroots.2.2.2.1 (by norm_num only)
  · have hlarge : 500000 ≤ L := (le_of_not_ge hU)
    have hroots :=
      scaleOne_cutoff_roots (v := 707) hL (by norm_num only) (by nlinarith only [hlarge])
    have hlogs := scaleOne_log_second hlarge
    dsimp only at hroots
    exact
      LLS.PaperStatements.scaleOne_margin_of_cell (T := 500000) (v := 707) (y0 := 24) (y1 := 36)
        (by norm_num only) hlarge hlogs hlog (by norm_num only) hroots.2.1
        (Real.rpow_nonneg (zero_lt_one.trans hx).le _) hroots.2.2.2.1 (by norm_num only)

/-- A rational logarithm certificate bounds the triangular support endpoint below. -/
theorem scaleOne_exp36_lower : (3000000000000000 : ℝ) < Real.exp 36 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 3000000000000000 51 32 35 (359 / 10) = true from by
          decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  apply (Real.log_lt_iff_lt_exp (by norm_num only : (0 : ℝ) < 3000000000000000)).mp
  linarith only [h]

/-- If the adaptive cutoff lies beyond the triangular support, its logarithmic scale
is at least 100000000. Combine the coefficient cap with the support endpoint bound. -/
theorem scaleOne_outer_scale {L : ℝ} (hL : 25000 ≤ L)
    (hu : Real.exp 36 ≤ ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2) :
    (100000000 : ℝ) ≤ L := by
  by_contra hn
  have hlt : L < 100000000 := lt_of_not_ge hn
  have hs :=
    (sq_le_sq₀ (by linarith only [hL] : 0 ≤ L) (by norm_num only : (0 : ℝ) ≤ 100000000)).mpr hlt.le
  have hroots := scaleOne_cutoff_roots (v := 158) hL (by norm_num only) (by nlinarith only [hL])
  dsimp only at hroots
  have ha := mul_le_mul_of_nonneg_right hroots.2.2.2.2 (sq_nonneg L)
  have he := scaleOne_exp36_lower
  nlinarith only [hu, hs, ha, he]

/-- Beyond the triangular support, the adaptive Gaussian cutoff satisfies the original
all-scale dual gap for every large index. The cutoff forces the scale above 100000000;
its root bounds provide the explicit positive margin. -/
theorem scaleOne_outer_gap {L h : ℝ} (hL : 25000 ≤ L) (hh : 1000000000000 ≤ h)
    (hu : Real.exp 36 ≤ ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2) :
    let x := ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964) <
      h *
        (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
          36 * L / (Real.sqrt x - 1)) := by
  let x := ((21 / 10 : ℝ) * adaptiveGaussianA L ^ 2) * L ^ 2
  have hbig := scaleOne_outer_scale hL hu
  have hLp : 0 < L := by linarith only [hL]
  have hhp : 0 < h := by linarith only [hh]
  have hb := scaleOne_cutoff_roots (v := 10000) hL (by norm_num only) (by nlinarith only [hbig])
  change
    1 < x ∧
      (5313 / 10000 : ℝ) * L ≤ Real.sqrt x ∧
      Real.sqrt x ≤ L ∧ x ^ (1 / 4 : ℝ) ≤ (147 / 200 : ℝ) * L / 10000 ∧ _ at hb
  have hp : LLS.PaperStatements.triangularKernelProfile 18 x = 0 := by
    unfold LLS.PaperStatements.triangularKernelProfile
    have hlog := Real.log_le_log (Real.exp_pos 36) hu
    rw [Real.log_exp] at hlog
    rw [abs_of_nonneg (Real.log_nonneg hb.1.le)]
    norm_num only
    exact max_eq_left (by linarith only [hlog])
  have hinv : x⁻¹ ≤ 1 := (inv_le_one₀ (zero_lt_one.trans hb.1)).2 hb.1.le
  have hinv0 : 0 ≤ x⁻¹ := inv_nonneg.mpr (zero_lt_one.trans hb.1).le
  have hsInv : Real.sqrt x⁻¹ ≤ 1 := Real.sqrt_le_one.mpr hinv
  have hrInv : (x⁻¹) ^ (1 / 4 : ℝ) ≤ 1 := Real.rpow_le_one hinv0 hinv (by norm_num only)
  have hden : 0 < Real.sqrt x - 1 := by nlinarith only [hb.2.1, hL]
  have hpole : 36 * L / (Real.sqrt x - 1) ≤ 100 := by
    apply (div_le_iff₀ hden).mpr
    nlinarith only [hb.2.1, hL]
  have hS : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hQ : 0 ≤ x ^ (1 / 4 : ℝ) := Real.rpow_nonneg (zero_lt_one.trans hb.1).le _
  have hpc : 0 ≤ (36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964 :=
    add_nonneg
      (mul_nonneg
        (add_nonneg (by norm_num only) (LLS.PaperStatements.triangularKernelProfile_nonneg 18 x))
        hLp.le)
      (by norm_num only)
  have hidx := mul_le_mul_of_nonneg_right (by linarith only [] : h - 1 ≤ h) hpc
  have hpr := mul_le_mul_of_nonneg_right hh hS
  have hpq := mul_le_mul_of_nonneg_right hh hQ
  have hcost :
    300000000 * (Real.sqrt x + Real.sqrt x⁻¹) + 1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (h - 1) * ((36 + LLS.PaperStatements.triangularKernelProfile 18 x) * L + 11964) ≤
      h *
        ((3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L +
          11965) := by
    rw [hp] at hidx ⊢
    nlinarith only [hidx, hpr, hpq, hsInv, hrInv, hh]
  have ha := mul_le_mul_of_nonneg_left hb.2.1 (by norm_num only : (0 : ℝ) ≤ 68 - 3 / 10000)
  have hq :=
    mul_le_mul_of_nonneg_left hb.2.2.2.1 (by norm_num only : (0 : ℝ) ≤ 1456 + 13 / 10000000)
  have hm :
    12065 <
      ((68 - 3 / 10000 : ℝ) * (5313 / 10000) - 36 - (1456 + 13 / 10000000) * (147 / 200) / 10000) *
        L := by
    nlinarith only [hbig]
  have hE := mul_nonneg hS (Real.exp_pos (-18)).le
  have hg :
    (3 / 10000 : ℝ) * Real.sqrt x + (13 / 10000000 : ℝ) * x ^ (1 / 4 : ℝ) + 36 * L + 11965 <
      Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
        36 * L / (Real.sqrt x - 1) := by
    nlinarith only [ha, hq, hm, hpole, hE]
  exact hcost.trans_lt (mul_lt_mul_of_pos_left hg hhp)

end PseudoPrime.PrimeTestBounds.MillerRabin
