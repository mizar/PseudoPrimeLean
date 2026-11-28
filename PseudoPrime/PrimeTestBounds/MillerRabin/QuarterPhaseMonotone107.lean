/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseBoxes107
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTwoShiftEuler

/-! # Monotonicity estimates for the section 107 phase remainder -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The forward contribution remains nondecreasing through radius 314. -/
theorem phase_main_recip_increasing_314 :
    MonotoneOn
      (fun x : ℝ ↦
        -4 * (Real.exp (-(13 / 25) * x) * phaseEulerMainPoly107 x) +
          phaseRecip107 * Real.exp (-x / 2))
      (Set.Icc (2 * Real.log 300) (2 * Real.log 314)) := by
  let f := fun x : ℝ ↦
    -4 * (Real.exp (-(13 / 25) * x) * phaseEulerMainPoly107 x) + phaseRecip107 * Real.exp (-x / 2)
  have hd (x : ℝ) :
    HasDerivAt f
      (4 * (Real.exp (-(13 / 25) * x) * weightedEulerPoly (11 / 25) (91 / 200) x) -
        phaseRecip107 * Real.exp (-x / 2) / 2)
      x := by
    have he := (((hasDerivAt_id x).neg).div_const 2).exp
    have hh := ((phase_euler_main_deriv107 x).const_mul (-4)).add (he.const_mul phaseRecip107)
    apply hh.congr_deriv
    simp only [Pi.neg_apply, id]
    ring
  apply
    monotoneOn_of_deriv_nonneg (convex_Icc _ _) (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt)
  intro x hx
  rw [(hd x).deriv]
  have hx' := interior_subset hx
  have hlog : Real.log 90000 = 2 * Real.log 300 := by
    rw [← show (300 : ℝ) ^ 2 = 90000 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
  have hlo : 11 ≤ x := by
    have h := phase_log107_300.1
    rw [hlog] at h
    linarith only [h, hx'.1]
  have hsub : x ≤ Real.log 100000 := by
    have h : (2 : ℝ) * Real.log 314 = Real.log ((314 : ℝ) ^ 2) := by
      rw [Real.log_pow]; norm_num only [Nat.cast_ofNat]
    exact hx'.2.trans (h.le.trans (Real.log_le_log (by norm_num only) (by norm_num only)))
  have hexp : 1 / 550 ≤ Real.exp (-(13 / 25) * x) := by
    have h :=
      (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 100000) (p := 13)
          (d := 25) (lo := 1 / 550) (hi := 1) (by decide +kernel)).1
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h
    rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 100000), mul_comm (Real.log 100000)] at h
    exact h.trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hsub (by norm_num only)))
  have hhalf : Real.exp (-x / 2) ≤ 1 / 300 := by
    have heq : Real.exp (-(2 * Real.log 300) / 2) = 1 / 300 := by
      rw [show -(2 * Real.log 300) / 2 = -Real.log 300 by ring, Real.exp_neg,
        Real.exp_log (by norm_num only), one_div]
    rw [← heq]
    exact Real.exp_le_exp.mpr (by linarith only [hx'.1])
  have hp :=
    mul_le_mul hexp (weighted_euler_gt_eight107 hlo).le (by norm_num only) (Real.exp_pos _).le
  have hr := mul_le_mul phase_recip107_bounds.2 hhalf (Real.exp_pos _).le (by norm_num only)
  linarith only [hp, hr]

/-- The signed shifted conductor term before its constant normalization. -/
@[expose]
noncomputable def phaseShift107 (x : ℝ) : ℝ :=
  Real.exp (-(13 / 25) * x) *
    ((11 / 25) * x ^ 5 - (91 / 200) * Real.exp ((51 / 50) * (1 / 5)) * (x - 1 / 5) ^ 5)

private theorem phaseShift107_deriv (x : ℝ) :
    HasDerivAt phaseShift107
      (Real.exp (-(13 / 25) * x) *
        ((91 / 200) * Real.exp ((51 / 50) * (1 / 5)) * (x - 1 / 5) ^ 4 *
            ((13 / 25) * (x - 1 / 5) - 5) -
          (11 / 25) * x ^ 4 * ((13 / 25) * x - 5)))
      x := by
  have h1 := ((hasDerivAt_id x).pow 5).const_mul (11 / 25 : ℝ)
  have h2 :=
    (((hasDerivAt_id x).sub_const (1 / 5)).pow 5).const_mul
      ((91 / 200 : ℝ) * Real.exp ((51 / 50) * (1 / 5)))
  have he := ((hasDerivAt_id x).const_mul (-(13 / 25 : ℝ))).exp
  apply (he.mul (h1.sub h2)).congr_deriv
  norm_num only [id, Nat.cast_ofNat, Nat.reduceSub, mul_one, Pi.pow_apply, Pi.sub_apply]
  ring

private theorem phaseShift107_nonneg {x : ℝ} (hx : 11.4 ≤ x) : 0 ≤ deriv phaseShift107 x := by
  rw [(phaseShift107_deriv x).deriv]
  apply mul_nonneg (Real.exp_pos _).le
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hA : 0 ≤ (13 / 25 : ℝ) * x - 5 := by linarith only [hx]
  have h₁ : 0.982 * x ≤ x - 1 / 5 := by linarith only [hx]
  have h₂ : 0.887 * ((13 / 25 : ℝ) * x - 5) ≤ (13 / 25) * (x - 1 / 5) - 5 := by linarith only [hx]
  have h₃ :=
    mul_le_mul (pow_le_pow_left₀ (mul_nonneg (by norm_num only) hx0) h₁ 4) h₂
      (mul_nonneg (by norm_num only) hA) (pow_nonneg (by linarith only [hx]) _)
  have he := exp_h.1
  have h :=
    mul_le_mul he h₃
      (mul_nonneg (pow_nonneg (mul_nonneg (by norm_num only) hx0) _)
        (mul_nonneg (by norm_num only) hA))
      (Real.exp_pos _).le
  have hcoef : (11 / 25 : ℝ) ≤ (91 / 200) * 1.22629815 * 0.982 ^ 4 * 0.887 := by norm_num only
  have hbase := mul_le_mul_of_nonneg_right hcoef (mul_nonneg (pow_nonneg hx0 4) hA)
  linarith only [h, hbase]

/-- The shifted conductor contribution increases throughout the section 107
window, by comparing the two fifth-power derivatives above log cutoff 11.4. -/
theorem phase_shift_increasing107 : MonotoneOn phaseShift107 (Set.Ici 11.4) := by
  apply
    monotoneOn_of_deriv_nonneg (convex_Ici _)
      (fun x _ ↦ (phaseShift107_deriv x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (phaseShift107_deriv x).differentiableAt.differentiableWithinAt)
  exact fun _ hx ↦ phaseShift107_nonneg (interior_subset hx)

/-- The forward part of the logarithmic phase remainder, including the
reciprocal pole, but excluding the reflected tail and the constant terms. -/
@[expose]
noncomputable def phaseForward107 (x : ℝ) : ℝ :=
  Real.exp (-(13 / 25) * x) * phaseMainPoly107 x -
      4 * Real.exp (-(51 / 50) * x) * phaseEulerErrorPoly107 x +
    phaseRecip107 * Real.exp (-x / 2)

/-- The forward contribution remains nondecreasing through radius 314. -/
theorem phase_forward_increasing_314 :
    MonotoneOn phaseForward107 (Set.Icc (2 * Real.log 300) (2 * Real.log 314)) := by
  let f := fun x : ℝ ↦ Real.exp (-(51 / 50) * x) * phaseEulerErrorPoly107 x
  have hd (x : ℝ) := phase_euler_error_deriv107 x
  have ha : AntitoneOn f (Set.Ici 11) := by
    apply
      antitoneOn_of_deriv_nonpos (convex_Ici _) (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
        (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt)
    exact fun _ hx ↦ phase_euler_error_deriv_nonpos107 (interior_subset hx)
  have hlo : 11.4 ≤ 2 * Real.log 300 := by
    have h := phase_log107_300.1
    rw [← show (300 : ℝ) ^ 2 = 90000 by norm_num only, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h]
  intro x hx y hy hxy
  have hs := phase_shift_increasing107 (hlo.trans hx.1) (hlo.trans hy.1) hxy
  have hf :=
    ha ((by norm_num only : (11 : ℝ) ≤ 11.4).trans (hlo.trans hx.1))
      ((by norm_num only : (11 : ℝ) ≤ 11.4).trans (hlo.trans hy.1)) hxy
  have hm := phase_main_recip_increasing_314 hx hy hxy
  have hEq (z : ℝ) :
    phaseForward107 z =
      (-4 * (Real.exp (-(13 / 25) * z) * phaseEulerMainPoly107 z) +
            phaseRecip107 * Real.exp (-z / 2)) +
          ((51 / 50 : ℝ) ^ 5 / 30) * phaseShift107 z -
        4 * f z := by
    unfold phaseForward107 phaseMainPoly107 phaseShift107 f
    ring
  rw [hEq, hEq]
  linarith only [hs, hf, hm]

private theorem shifted_exp_antitone107 {b : ℝ} (hb : b ≤ 4) :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-x / 7) * (x - b)) (Set.Ici 11) := by
  have hd (x : ℝ) :
    HasDerivAt (fun y : ℝ ↦ Real.exp (-y / 7) * (y - b)) (Real.exp (-x / 7) * (1 - (x - b) / 7))
      x := by
    have he := (((hasDerivAt_id x).neg).div_const 7).exp
    apply (he.mul ((hasDerivAt_id x).sub_const b)).congr_deriv
    simp only [Pi.neg_apply, id]
    ring
  apply
    antitoneOn_of_deriv_nonpos (convex_Ici _) (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt)
  intro x hx
  have hl : 11 ≤ x := interior_subset hx
  rw [(hd x).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (by linarith only [hl, hb])

/-- A monomial in x-b of degree k is nonnegative and nonincreasing after
allocating k/7 of exponential decay, provided x is at least 11 and b at most 4. -/
theorem phase_shift_power_antitone107 {b : ℝ} (hb : b ≤ 4) (k : ℕ) :
    AntitoneOn (fun x : ℝ ↦ Real.exp (-(k : ℝ) / 7 * x) * (x - b) ^ k) (Set.Ici 11) := by
  intro x hx y hy hxy
  have h₀ : 0 ≤ Real.exp (-y / 7) * (y - b) :=
    mul_nonneg (Real.exp_pos _).le (by linarith only [Set.mem_Ici.mp hy, hb])
  have h := pow_le_pow_left₀ h₀ (shifted_exp_antitone107 hb hx hy hxy) k
  rw [mul_pow, mul_pow, ← Real.exp_natCast_mul, ← Real.exp_natCast_mul] at h
  rw [show (k : ℝ) * (-x / 7) = -(k : ℝ) / 7 * x by ring,
    show (k : ℝ) * (-y / 7) = -(k : ℝ) / 7 * y by ring] at h
  exact h

end PseudoPrime.PrimeTestBounds.MillerRabin
