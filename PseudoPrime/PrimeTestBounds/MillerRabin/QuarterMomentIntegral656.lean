/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCorrection656
public import PseudoPrime.Analysis.MellinLogMoments
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterLowPhase
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCorrection656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterMellinPhase656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit644

/-! # Integrated Mellin moments for the section 132 kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Express the unit weight as a log polynomial times a real power. -/
private theorem unit_weight_power {u : ℝ} (hu : 0 < u) :
    quarterWeight656 1 u =
      (11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120 *
        (u ^ (3 / 5 : ℝ) * (21 / 8 - Real.log u) ^ 5) := by
  unfold quarterWeight656
  dsimp only
  rw [div_one, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hu]
  have he :
    Real.exp (-(11 / 10 * (21 / 8 - Real.log u))) =
      Real.exp (-(21 / 8 * (11 / 10))) *
        (Real.exp (Real.log u * (3 / 5)) * Real.exp (Real.log u * (1 / 2))) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [he]
  field_simp [Real.exp_ne_zero]

/-- The zero moment up to a positive cutoff is a six-term rational function of the
effective Mellin exponent, multiplied by the fixed kernel normalization. -/
theorem quarter_mellin_moment_656 {ρ : ℂ} (hρ : 0 < ρ.re + 3 / 5) (c : ℂ) {y : ℝ} (hy : 0 < y) :
    let s := ρ + (3 / 5 : ℂ)
    (∫ u in (0 : ℝ)..y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u) =
      ((11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120) *
        (c * quarterMoment656 s y).re := by
  intro s
  unfold quarterMoment656
  have hs : 0 < s.re := by
    dsimp only [s]
    norm_num only [Complex.add_re, Complex.div_ofNat_re]
    exact hρ
  let f := fun u : ℝ ↦ (u : ℂ) ^ (s - 1) * ((21 / 8 - Real.log u : ℝ) : ℂ) ^ 5
  have hm := Analysis.complex_log_moment_cutoff 5 (21 / 8) hs hy
  rw [intervalIntegral.integral_of_le hy.le] at hm
  have hi : MeasureTheory.IntegrableOn f (Set.Ioc 0 y) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hy.le).1
      (Analysis.complex_log_moment_integrable 5 (21 / 8) hs hy)
  let C := (11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120
  rw [intervalIntegral.integral_of_le hy.le]
  have hw :
    (∫ u in Set.Ioc (0 : ℝ) y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u) =
      ∫ u in Set.Ioc (0 : ℝ) y, C * (c * f u).re := by
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro u hu
    have hpow : (u : ℂ) ^ (s - 1) = (u : ℂ) ^ (ρ - 1) * ((u ^ (3 / 5 : ℝ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_cpow hu.1.le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr hu.1.ne')]
      congr 1
      dsimp only [s]
      simp only [Complex.ofReal_div, Complex.ofReal_ofNat]
      ring
    dsimp only [f]
    rw [unit_weight_power hu.1, hpow, ← Complex.ofReal_pow]
    simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero]
    dsimp only [C]
    ring
  rw [hw, MeasureTheory.integral_const_mul]
  have hr := integral_re (hi.const_mul c)
  simp only [RCLike.re_eq_complex_re] at hr
  rw [hr, MeasureTheory.integral_const_mul]
  change C * (c * ∫ u in Set.Ioc (0 : ℝ) y, f u).re = _
  rw [show (∫ u in Set.Ioc (0 : ℝ) y, f u) = _ from hm]

private theorem weight_smooth_656 {X : ℝ} (hX : 0 < X) :
    ContDiffOn ℝ 2 (quarterWeight656 X) (Set.Ioi 0) := by
  intro t ht
  have ht' : 0 < t := ht
  have hs : ContDiffAt ℝ 2 Real.sqrt t := Real.contDiffAt_sqrt ht'.ne'
  apply ContDiffAt.contDiffWithinAt
  unfold quarterWeight656
  dsimp only
  fun_prop (disch := positivity)

/-- The physical Mellin integral and boundary contributions from one
nontrivial zero at cutoff X, including its multiplicity. -/
noncomputable def quarterZeroIntegral656 (X : ℝ) (ρ : ℂ) : ℝ :=
  let W := quarterWeight656 X
  let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
  let H := fun t : ℝ ↦ (-m * (t : ℂ) ^ (ρ - 1)).re
  4 * (∫ t in (1 : ℝ)..X, H t * W t) - (∫ t in (1 : ℝ)..X * Real.exp (21 / 8), H t * W t) -
      4 * (-m / ρ * (X : ℂ) ^ ρ).re * W X +
    3 * (-m / ρ).re * W 1

/-- At positive arguments the physical weight at cutoff X is the unit
weight evaluated at the rescaled argument, divided by the square root of X. -/
private theorem quarter_weight_rescale {X u : ℝ} (hX : 0 < X) (hu : 0 < u) :
    quarterWeight656 X (u * X) = (Real.sqrt X)⁻¹ * quarterWeight656 1 u := by
  simp only [quarterWeight656, mul_div_cancel_right₀ _ hX.ne', div_one, Real.sqrt_mul hu.le,
    one_div, mul_inv_rev]
  ring

/-- Rescale each signed power integral in the physical zero contribution
to a unit-cutoff integral. Its lower limit is exactly the physical endpoint
one divided by the cutoff. -/
theorem quarter_power_integral_scale_656 {X b : ℝ} (hX : 0 < X) (hb : 1 ≤ b) (c ρ : ℂ) :
    (∫ t in (1 : ℝ)..b, (c * (t : ℂ) ^ (ρ - 1)).re * quarterWeight656 X t) =
      Real.sqrt X *
        ∫ u in (1 / X : ℝ)..b / X,
          (c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u := by
  let f := fun t : ℝ ↦ (c * (t : ℂ) ^ (ρ - 1)).re * quarterWeight656 X t
  have h := intervalIntegral.integral_comp_mul_right f (a := 1 / X) (b := b / X) hX.ne'
  rw [div_mul_cancel₀ _ hX.ne', div_mul_cancel₀ _ hX.ne', smul_eq_mul] at h
  have he :
    (∫ u in (1 / X : ℝ)..b / X, f (u * X)) =
      ∫ u in (1 / X : ℝ)..b / X,
        (Real.sqrt X)⁻¹ *
          ((c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    rw [Set.uIcc_of_le (div_le_div_of_nonneg_right hb hX.le)] at hu
    have hu0 := (one_div_pos.mpr hX).trans_le hu.1
    dsimp only [f]
    rw [quarter_weight_rescale hX hu0, Complex.ofReal_mul, Complex.ofReal_mul_cpow hu0.le X,
      show c * ((u : ℂ) ^ (ρ - 1) * (X : ℂ) ^ (ρ - 1)) = c * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)
        by ring]
    ring
  rw [he, intervalIntegral.integral_const_mul] at h
  have hh := congrArg (fun y : ℝ ↦ X * y) h
  rw [mul_inv_cancel_left₀ hX.ne'] at hh
  have hs : X * (Real.sqrt X)⁻¹ = Real.sqrt X := by
    rw [← div_eq_mul_inv]
    apply (div_eq_iff (Real.sqrt_pos.mpr hX).ne').mpr
    rw [← sq, Real.sq_sqrt hX.le]
  rw [← mul_assoc, hs] at hh
  exact hh.symm

/-- In the zero coefficient both integrals use the same unit-cutoff
integrand, with upper limits one and the exponential support endpoint. -/
private theorem quarter_zero_integral_scale_656 {X : ℝ} (hX : 1 ≤ X) (ρ : ℂ) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let F := fun u : ℝ ↦ (-m * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u
    quarterZeroIntegral656 X ρ =
      4 * (Real.sqrt X * ∫ u in (1 / X : ℝ)..1, F u) -
          (Real.sqrt X * ∫ u in (1 / X : ℝ)..Real.exp (21 / 8), F u) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight656 X X +
        3 * (-m / ρ).re * quarterWeight656 X 1 := by
  dsimp only [quarterZeroIntegral656]
  have hx := zero_lt_one.trans_le hX
  have hb :=
    hX.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 21 / 8)))
  rw [quarter_power_integral_scale_656 hx hX, quarter_power_integral_scale_656 hx hb,
    div_self hx.ne', mul_div_cancel_left₀ _ hx.ne']

/-- A complex power times the unit weight is integrable down to zero
whenever the effective Mellin exponent has positive real part. -/
private theorem quarter_power_integrable_zero_656 {ρ : ℂ} (hρ : 0 < ρ.re + 3 / 5) (c : ℂ) :
    IntervalIntegrable (fun u : ℝ ↦ (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u)
      MeasureTheory.volume 0 1 := by
  let C := (11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120
  have hC : 0 ≤ C := by
    dsimp only [C]; positivity
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).2
  have hi := ((Analysis.shifted_log_moment 5 (21 / 8) hρ).1.const_mul (‖c‖ * C))
  apply hi.mono'
  · apply ContinuousOn.aestronglyMeasurable _ measurableSet_Ioc
    intro u hu
    have hp := Complex.continuousAt_ofReal_cpow_const u (ρ - 1) (Or.inr hu.1.ne')
    have hW : ContinuousOn (quarterWeight656 1) (Set.Ioi 0) :=
      (weight_smooth_656 (X := 1) zero_lt_one).continuousOn
    have hw := (hW u hu.1).continuousAt (isOpen_Ioi.mem_nhds hu.1)
    exact
      ((Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hp)).mul
          hw).continuousWithinAt
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have hl : 0 ≤ 21 / 8 - Real.log u := by linarith only [Real.log_nonpos hu.1.le hu.2]
    have hw : 0 ≤ quarterWeight656 1 u := by
      rw [unit_weight_power hu.1]
      exact mul_nonneg hC (mul_nonneg (Real.rpow_nonneg hu.1.le _) (pow_nonneg hl _))
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw]
    calc
      _ ≤ ‖c * (u : ℂ) ^ (ρ - 1)‖ * quarterWeight656 1 u :=
        mul_le_mul_of_nonneg_right (Complex.abs_re_le_norm _) hw
      _ = _ := by
        rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hu.1, Complex.sub_re, Complex.one_re,
          unit_weight_power hu.1]
        rw [show ρ.re + 3 / 5 - 1 = (ρ.re - 1) + 3 / 5 by ring, Real.rpow_add hu.1]
        ring

/-- Extending both scaled zero integrals to zero subtracts exactly three
times the omitted lower integral, since both use the same integrand. -/
private theorem quarter_extend_integrals_656 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 3 / 5)
    (c : ℂ) :
    let F := fun u : ℝ ↦ (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u
    4 * (∫ u in (1 / X : ℝ)..1, F u) - (∫ u in (1 / X : ℝ)..Real.exp (21 / 8), F u) =
      4 * (∫ u in (0 : ℝ)..1, F u) - (∫ u in (0 : ℝ)..Real.exp (21 / 8), F u) -
        3 * (∫ u in (0 : ℝ)..1 / X, F u) := by
  intro F
  have hx := zero_lt_one.trans_le hX
  have ha : 0 < 1 / X := one_div_pos.mpr hx
  have ha1 : 1 / X ≤ 1 := by
    rw [one_div]; exact inv_le_one_of_one_le₀ hX
  have h0 : IntervalIntegrable F MeasureTheory.volume 0 (1 / X) :=
    (quarter_power_integrable_zero_656 hρ c).mono_set
      (by
        rw [Set.uIcc_of_le ha.le, Set.uIcc_of_le zero_le_one]
        exact Set.Icc_subset_Icc_right ha1)
  have hi {b : ℝ} (hb : 1 ≤ b) : IntervalIntegrable F MeasureTheory.volume (1 / X) b := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (ha1.trans hb)]
    intro u hu
    have hu0 := ha.trans_le hu.1
    have hp := Complex.continuousAt_ofReal_cpow_const u (ρ - 1) (Or.inr hu0.ne')
    have hw : ContinuousOn (quarterWeight656 1) (Set.Ioi 0) :=
      (weight_smooth_656 (X := 1) zero_lt_one).continuousOn
    exact
      ((Complex.continuous_re.continuousAt.comp (continuousAt_const.mul hp)).mul
          ((hw u hu0).continuousAt (isOpen_Ioi.mem_nhds hu0))).continuousWithinAt
  rw [← intervalIntegral.integral_add_adjacent_intervals h0 (hi le_rfl), ←
    intervalIntegral.integral_add_adjacent_intervals h0 (hi (Real.one_le_exp (by norm_num only)))]
  ring

/-- The zero contribution is the difference of two moments starting at
zero, the common omitted integral, and its explicit boundary terms. -/
private theorem quarter_zero_integral_extended_656 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ}
    (hρ : 0 < ρ.re + 3 / 5) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let F := fun u : ℝ ↦ (-m * (X : ℂ) ^ (ρ - 1) * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u
    quarterZeroIntegral656 X ρ =
      Real.sqrt X *
            (4 * (∫ u in (0 : ℝ)..1, F u) - (∫ u in (0 : ℝ)..Real.exp (21 / 8), F u) -
              3 * (∫ u in (0 : ℝ)..1 / X, F u)) -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight656 X X +
        3 * (-m / ρ).re * quarterWeight656 X 1 := by
  intro m F
  have hs := quarter_zero_integral_scale_656 hX ρ
  have he := quarter_extend_integrals_656 hX hρ (-m * (X : ℂ) ^ (ρ - 1))
  dsimp only at hs he
  rw [hs]
  have hm := congrArg (fun y : ℝ ↦ Real.sqrt X * y) he
  change Real.sqrt X * _ = Real.sqrt X * _ at hm
  dsimp only [F, m] at *
  linarith only [hm]

/-- Evaluate the physical zero coefficient by finite moments at the unit
cutoff, support endpoint and omitted lower endpoint. -/
theorem quarter_zero_integral_formula_656 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 3 / 5) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let c := -m * (X : ℂ) ^ (ρ - 1)
    let s := ρ + (3 / 5 : ℂ)
    let C := (11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120
    quarterZeroIntegral656 X ρ =
      Real.sqrt X * C *
            (c *
                (4 * quarterMoment656 s 1 - quarterMoment656 s (Real.exp (21 / 8)) -
                  3 * quarterMoment656 s (1 / X))).re -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * quarterWeight656 X X +
        3 * (-m / ρ).re * quarterWeight656 X 1 := by
  intro m c s C
  have h := quarter_zero_integral_extended_656 hX hρ
  have hM {y : ℝ} (hy : 0 < y) :
    (∫ u in (0 : ℝ)..y, (c * (u : ℂ) ^ (ρ - 1)).re * quarterWeight656 1 u) =
      C * (c * quarterMoment656 s y).re :=
    quarter_mellin_moment_656 hρ c hy
  change quarterZeroIntegral656 X ρ = _ at h
  rw [h, hM zero_lt_one, hM (Real.exp_pos _), hM (one_div_pos.mpr (zero_lt_one.trans_le hX))]
  have hscale (a : ℝ) (z : ℂ) : (c * ((a : ℂ) * z)).re = a * (c * z).re := by
    rw [← mul_assoc, mul_comm c, mul_assoc]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hlinear (A B D : ℂ) :
    (c * (4 * A - B - 3 * D)).re = 4 * (c * A).re - (c * B).re - 3 * (c * D).re := by
    simp only [mul_sub, Complex.sub_re]
    exact congrArg₂ (· - ·) (congrArg (· - (c * B).re) (hscale 4 A)) (hscale 3 D)
  rw [hlinear]
  ring

/-- Split a zero coefficient into its normalized phase times a fixed kernel
and two corrections from the physical lower cutoff. -/
theorem quarter_zero_phase_split_656 {X : ℝ} (hX : 1 ≤ X) {ρ : ℂ} (hρ : 0 < ρ.re + 3 / 5) :
    let m := (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℂ)
    let p := (X : ℂ) ^ ρ / (Real.sqrt X : ℂ)
    let C := ((11 / 10 : ℝ) ^ 5 * Real.exp (-(21 / 8 * (11 / 10))) / 120 : ℝ)
    quarterZeroIntegral656 X ρ =
      (m * p * quarterMellinPhase656 ρ).re +
        3 * C * (m * p * quarterMoment656 (ρ + 3 / 5) (1 / X)).re +
        3 * (-m / ρ).re * quarterWeight656 X 1 := by
  intro m p C
  have hx := zero_lt_one.trans_le hX
  have hp := cutoff_phase_mul hx ρ
  have hw := quarter_weight_rescale hx (u := 1) zero_lt_one
  rw [one_mul] at hw
  have h := quarter_zero_integral_formula_656 hX hρ
  dsimp only at h
  rw [h, hw]
  let A := 4 * quarterMoment656 (ρ + 3 / 5) 1 - quarterMoment656 (ρ + 3 / 5) (Real.exp (21 / 8))
  let D := quarterMoment656 (ρ + 3 / 5) (1 / X)
  let w := quarterWeight656 1 1
  change
    Real.sqrt X * C * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D)).re -
          4 * (-m / ρ * (X : ℂ) ^ ρ).re * ((Real.sqrt X)⁻¹ * w) +
        3 * (-m / ρ).re * quarterWeight656 X 1 =
      (m * p * (4 * (w : ℂ) / ρ - (C : ℂ) * A)).re + 3 * C * (m * p * D).re +
        3 * (-m / ρ).re * quarterWeight656 X 1
  have hre (a : ℝ) (z : ℂ) : ((a : ℂ) * z).re = a * z.re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have h₁ :
    ((Real.sqrt X : ℂ) * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D))) = -m * p * (A - 3 * D) := by
    dsimp only [p]
    rw [← hp]
    ring
  have h₂ : (((Real.sqrt X)⁻¹ : ℝ) : ℂ) * (-m / ρ * (X : ℂ) ^ ρ) = -m / ρ * p := by
    dsimp only [p]
    rw [Complex.ofReal_inv]
    ring
  have hr₁ := congrArg Complex.re h₁
  have hr₂ := congrArg Complex.re h₂
  rw [hre] at hr₁ hr₂
  have he :
    (m * p * (4 * (w : ℂ) / ρ - (C : ℂ) * A)).re =
      -4 * w * (-m / ρ * p).re - C * (m * p * A).re := by
    rw [mul_sub, Complex.sub_re]
    congr 1
    · rw [← hre (-4 * w)]
      congr 1
      simp only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_ofNat]
      ring
    · rw [← hre C]
      congr 1
      ring
  have hf : (-m * p * (A - 3 * D)).re = -(m * p * A).re + 3 * (m * p * D).re := by
    rw [← hre (3 : ℝ), ← Complex.neg_re, ← Complex.add_re]
    congr 1
    simp only [Complex.ofReal_ofNat]
    ring
  rw [he]
  rw [hf] at hr₁
  calc
    _ =
        C * ((Real.sqrt X) * (-m * (X : ℂ) ^ (ρ - 1) * (A - 3 * D)).re) -
            4 * w * ((Real.sqrt X)⁻¹ * (-m / ρ * (X : ℂ) ^ ρ).re) +
          3 * (-m / ρ).re * quarterWeight656 X 1 :=
      by ring
    _ = _ := by
      rw [hr₁, hr₂]; ring

/-- On the critical line and for radius at least one, the physical zero
contribution is the certified phase summand plus its two lower-cutoff
corrections. This is the pointwise identity for the rectangular ledgers. -/
theorem quarter_physical_phase_656 {r : ℝ} (hr : 1 ≤ r) {ρ : ℂ} (hρ : ρ.re = 1 / 2) :
    quarterZeroIntegral656 (r ^ 2) ρ =
      (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
          (Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) *
              quarterPhaseKernel656 ρ.im).re +
        quarterPhaseCorrection656 (r ^ 2) ρ := by
  have hp : 0 < r := zero_lt_one.trans_le hr
  have hX := one_le_pow₀ hr (n := 2)
  have hρ' : ρ = (1 / 2 : ℂ) + Complex.I * ρ.im := by
    apply Complex.ext <;>
      simp only [hρ, Complex.add_re, Complex.add_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
        Complex.one_re, Complex.one_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
        Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, one_mul, sub_zero, zero_add,
        add_zero, zero_div]
  have hK := quarter_mellin_phase_eq_656 ρ.im
  rw [← hρ'] at hK
  have he :
    ((r ^ 2 : ℝ) : ℂ) ^ ρ / (Real.sqrt (r ^ 2) : ℂ) =
      Complex.exp (Complex.I * ((2 * Real.log r * ρ.im : ℝ) : ℂ)) := by
    conv_lhs => rw [hρ']
    simpa only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, mul_comm] using
      quarter_cutoff_phase_exp (t := ρ.im) hp
  rw [quarter_zero_phase_split_656 hX (by linarith only [hρ])]
  dsimp only [quarterPhaseCorrection656]
  rw [hK, he, mul_assoc]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, add_assoc]

/-- Under RH the physical zero integrals and boundary terms, summed up
to any height at least 100, satisfy the certified section 132 lower bound. -/
theorem quarter_zero_integral_lower_656 (hRH : RiemannHypothesis) {r T : ℝ}
    (hr : r ∈ Set.Icc 322 328) (hT : 100 ≤ T) :
    (-0.002594 : ℝ) ≤
      ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T, quarterZeroIntegral656 (r ^ 2) ρ := by
  apply (quarter_corrected_truncation_656 hRH hr hT).trans_eq
  apply Finset.sum_congr rfl
  intro ρ hρ
  have hm :=
    (AnalyticNumberTheory.RiemannZeta.mem_zerosUpTo
          ((by norm_num only : (0 : ℝ) ≤ 100).trans hT)).mp
      hρ
  have hx := AnalyticNumberTheory.RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hm.1 hm.2.1
  have hline := AnalyticNumberTheory.RiemannXi.xi_zero_re_eq_half_of_riemannHypothesis hRH hx
  rw [quarter_physical_phase_656 ((by norm_num only : (1 : ℝ) ≤ 322).trans hr.1) hline,
    quarter_mellin_cutoff_phase_656 ((by norm_num only : (0 : ℝ) < 322).trans_le hr.1) hline]

end PseudoPrime.PrimeTestBounds.MillerRabin
