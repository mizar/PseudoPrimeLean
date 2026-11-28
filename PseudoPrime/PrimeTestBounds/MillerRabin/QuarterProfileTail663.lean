/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfileAbel663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfileAbel663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxAbel656
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Numerical signed tail bounds for section 137 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The quadratic is negative on the entire range swept out by the
lower cutoff, so removing the interval up to the right endpoint raises
the signed main integral. -/
private theorem main_le_right {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    (∫ t in Set.Ioi (r ^ 2), quarterDensity663 t) ≤
      ∫ t in Set.Ioi ((663 / 2 : ℝ) ^ 2), quarterDensity663 t := by
  have hr₁ := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hx : 1 ≤ r ^ 2 := one_le_pow₀ hr₁
  have hru := pow_le_pow_left₀ (zero_le_one.trans hr₁) hr.2 2
  have hsplit := intervalIntegral.integral_Ioi_sub_Ioi (density_integrable hx) hru
  have hn : (∫ t in (r ^ 2)..((663 / 2 : ℝ) ^ 2), quarterDensity663 t) ≤ 0 := by
    rw [intervalIntegral.integral_of_le hru]
    apply MeasureTheory.setIntegral_nonpos measurableSet_Ioc
    intro t ht
    have ht₀ := (zero_lt_one.trans_le hx).trans ht.1
    have hsq := Real.sq_sqrt ht₀.le
    have hs : Real.sqrt t ∈ Set.Icc 328 (663 / 2) := by
      refine ⟨hr.1.trans ?_, ?_⟩
      · nlinarith only [ht.1, hsq, hr₁, Real.sqrt_nonneg t]
      · nlinarith only [ht.2, hsq, Real.sqrt_nonneg t]
    have hp := (quarter_profile_boundary_663 hs).2
    rw [hsq] at hp
    exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg ht₀.le _) hp.le
  linarith only [hsplit, hn]

/-- Recenter the exact main integral before taking numerical bounds,
so the large uncentered terms do not lose precision by cancellation. -/
private theorem main_centered {x : ℝ} (hx : 1 ≤ x) :
    let v := Real.log x - 23 / 2
    (∫ t in Set.Ioi x, quarterDensity663 t) =
      x ^ (-(3 / 5) : ℝ) *
        ((profileCoeff 0 + profileCoeff 1 * (v + 5 / 3) +
            profileCoeff 2 * (v ^ 2 + (10 / 3) * v + 50 / 9)) /
          (3 / 5)) := by
  rw [profile_main hx]
  dsimp only
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
    Nat.reduceAdd]
  ring

/-- The main integral at radius 331.5 is at most 0.002285. -/
private theorem main_endpoint :
    (∫ t in Set.Ioi ((663 / 2 : ℝ) ^ 2), quarterDensity663 t) ≤ 0.002285 := by
  let x : ℝ := (663 / 2) ^ 2
  let v := Real.log x - 23 / 2
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 439569 / 4) (j := 17) (n := 27) (lo := 11.60725)
      (hi := 11.60726) (by decide +kernel)
  norm_num only [Rat.cast_ofScientific, Rat.cast_ofNat, Rat.cast_div] at hl
  have hlog : 0.10725 ≤ v ∧ v ≤ 0.10726 := by
    dsimp only [v, x]
    rw [show (663 / 2 : ℝ) ^ 2 = 439569 / 4 by norm_num only]
    exact ⟨by linarith only [hl.1], by linarith only [hl.2]⟩
  have hp :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 945) (j := 11) (n := 30) (lo := 6)
        (hi := 6.96434) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hp
  have hd : x ^ (-(3 / 5) : ℝ) ≤ 0.000945 := by
    rw [Real.rpow_def_of_pos (by norm_num only [x] : 0 < x)]
    apply (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 0.000945)).mp
    have h' : Real.log (0.000945 : ℝ)⁻¹ ≤ 6.96434 := by
      norm_num only at hp ⊢
      exact hp
    rw [Real.log_inv] at h'
    dsimp only [v] at hlog
    linarith only [hlog.1, h']
  have hb := profile_coeff_bounds
  have hv₀ : 0 ≤ v := by linarith only [hlog.1]
  have hB :=
    (mul_le_mul_of_nonneg_right hb.2.1.2 (by linarith only [hlog.1] : 0 ≤ v + 5 / 3)).trans
      (mul_le_mul_of_nonpos_left (by linarith only [hlog.1]) (by norm_num only) :
        (-5.446821 : ℝ) * (v + 5 / 3) ≤ -5.446821 * (0.10725 + 5 / 3))
  have hv₂ := pow_le_pow_left₀ hv₀ hlog.2 2
  have hC :=
    (mul_le_mul_of_nonneg_right hb.2.2.2 (by positivity : 0 ≤ v ^ 2 + (10 / 3) * v + 50 / 9)).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hv₂, hlog.2]) (by norm_num only) :
        (3.549580 : ℝ) * (v ^ 2 + (10 / 3) * v + 50 / 9) ≤
          3.549580 * (0.10726 ^ 2 + (10 / 3) * 0.10726 + 50 / 9))
  have hQ :
    (profileCoeff 0 + profileCoeff 1 * (v + 5 / 3) +
          profileCoeff 2 * (v ^ 2 + (10 / 3) * v + 50 / 9)) /
        (3 / 5) ≤
      2.41722 := by
    linarith only [hb.1.2, hB, hC]
  rw [main_centered (x := x) (by norm_num only [x])]
  change x ^ (-(3 / 5) : ℝ) * _ ≤ _
  exact
    ((mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg (by norm_num only [x]) _)).trans
          (mul_le_mul_of_nonneg_right hd (by norm_num only))).trans
      (by norm_num only)

private theorem main_gaussian_box {r vMax Q : ℝ} (hr : 663 / 2 ≤ r)
    (hvMax : Real.log (r ^ 2) - 23 / 2 ≤ vMax)
    (hQMax :
      (-9.917281 - 5.446821 * (0.10725 + 5 / 3) +
            3.549580 * (vMax ^ 2 + (10 / 3) * vMax + 50 / 9)) /
          (3 / 5) ≤
        Q) :
    (∫ t in Set.Ioi (r ^ 2), quarterDensity663 t) ≤ 0.000945 * Q := by
  let x : ℝ := r ^ 2
  let v := Real.log x - 23 / 2
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 439569 / 4) (j := 17) (n := 27) (lo := 11.60725)
      (hi := 11.60726) (by decide +kernel)
  norm_num only [Rat.cast_ofScientific, Rat.cast_ofNat, Rat.cast_div] at hl
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr
  have hx₀ : 0 < x := sq_pos_of_pos hr₀
  have hx₁ : 1 ≤ x := one_le_pow₀ ((by norm_num only : (1 : ℝ) ≤ 663 / 2).trans hr)
  have hlow :=
    Real.log_le_log (sq_pos_of_pos (by norm_num only : (0 : ℝ) < 663 / 2))
      (pow_le_pow_left₀ (by norm_num only) hr 2)
  norm_num only at hlow
  have hlog : 0.10725 ≤ v := by
    dsimp only [v, x]
    linarith only [hl.1, hlow]
  have hp :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 945) (j := 11) (n := 30) (lo := 6)
        (hi := 6.96434) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hp
  have hd : x ^ (-(3 / 5) : ℝ) ≤ 0.000945 := by
    rw [Real.rpow_def_of_pos hx₀]
    apply (Real.le_log_iff_exp_le (by norm_num only : (0 : ℝ) < 0.000945)).mp
    have h' : Real.log (0.000945 : ℝ)⁻¹ ≤ 6.96434 := by
      norm_num only at hp ⊢
      exact hp
    rw [Real.log_inv] at h'
    dsimp only [v] at hlog
    linarith only [hlog, h']
  have hb := profile_coeff_bounds
  have hv₀ : 0 ≤ v := by linarith only [hlog]
  have hB :=
    (mul_le_mul_of_nonneg_right hb.2.1.2 (by linarith only [hlog] : 0 ≤ v + 5 / 3)).trans
      (mul_le_mul_of_nonpos_left (by linarith only [hlog]) (by norm_num only) :
        (-5.446821 : ℝ) * (v + 5 / 3) ≤ -5.446821 * (0.10725 + 5 / 3))
  change v ≤ vMax at hvMax
  have hv₂ := pow_le_pow_left₀ hv₀ hvMax 2
  have hC :=
    (mul_le_mul_of_nonneg_right hb.2.2.2 (by positivity : 0 ≤ v ^ 2 + (10 / 3) * v + 50 / 9)).trans
      (mul_le_mul_of_nonneg_left (by linarith only [hv₂, hvMax]) (by norm_num only) :
        (3.549580 : ℝ) * (v ^ 2 + (10 / 3) * v + 50 / 9) ≤
          3.549580 * (vMax ^ 2 + (10 / 3) * vMax + 50 / 9))
  have hQ :
    (profileCoeff 0 + profileCoeff 1 * (v + 5 / 3) +
          profileCoeff 2 * (v ^ 2 + (10 / 3) * v + 50 / 9)) /
        (3 / 5) ≤
      Q := by
    linarith only [hb.1.2, hB, hC, hQMax]
  rw [main_centered (x := x) hx₁]
  change x ^ (-(3 / 5) : ℝ) * _ ≤ _
  have hvMax₀ : 0 ≤ vMax := hv₀.trans hvMax
  exact
    (mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg hx₀.le _)).trans
      (mul_le_mul_of_nonneg_right hd (by linarith only [hQMax, hvMax₀, sq_nonneg vMax]))

private theorem gaussian_log_upper {r R : ℝ} (hr : 663 / 2 ≤ r) (hR : r ≤ R) {vMax : ℝ}
    (hlog : Real.log (R ^ 2) ≤ vMax + 23 / 2) : Real.log (r ^ 2) - 23 / 2 ≤ vMax := by
  have hpos : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr
  have h := Real.log_le_log (sq_pos_of_pos hpos) (pow_le_pow_left₀ hpos.le hR 2)
  linarith only [h, hlog]

private theorem main_first_gaussian {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 332) :
    (∫ t in Set.Ioi (r ^ 2), quarterDensity663 t) ≤ 0.002345 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 110224) (j := 17) (n := 27) (lo := 11) (hi :=
        11.61028) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h
  have hv :=
    gaussian_log_upper hr.1 hr.2 (vMax := 0.11028)
      (by
        norm_num only; exact h)
  exact (main_gaussian_box hr.1 hv (Q := 2.481) (by norm_num only)).trans (by norm_num only)

private theorem main_next_gaussian {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 333) :
    (∫ t in Set.Ioi (r ^ 2), quarterDensity663 t) ≤ 0.002472 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 110889) (j := 17) (n := 27) (lo := 11) (hi :=
        11.61629) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h
  have hv :=
    gaussian_log_upper hr.1 hr.2 (vMax := 0.11629)
      (by
        norm_num only; exact h)
  exact (main_gaussian_box hr.1 hv (Q := 2.615) (by norm_num only)).trans (by norm_num only)

/-- The signed main integral is bounded on the full comparison range. -/
theorem quarter_main_upper_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    (∫ t in Set.Ioi (r ^ 2), quarterDensity663 t) ≤ 0.002285 :=
  (main_le_right hr).trans main_endpoint

/-- Over the comparison range the low-error decay is bounded by its
outward enclosure at the smallest cutoff. -/
private theorem decay_box {r : ℝ} (hr : 328 ≤ r) : (r ^ 2) ^ (-(11 / 10) : ℝ) ≤ 0.000003 := by
  have hx : (107584 : ℝ) ≤ r ^ 2 := by
    rw [show (107584 : ℝ) = 328 ^ 2 by norm_num only]
    exact pow_le_pow_left₀ (by norm_num only) hr 2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 107584) (p := 11) (d :=
        10) (lo := 0) (hi := 0.000003) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hp
  have h :=
    Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 107584) hx
      (by norm_num only : (-(11 / 10) : ℝ) ≤ 0)
  linarith only [h, hp]

/-- Center the low-error integral before bounding its positive terms. -/
private theorem finite_centered {x : ℝ} (hx : 1 ≤ x) :
    let v := Real.log x - 23 / 2
    (∫ t in Set.Ioi x, finiteMajor t) =
      (4 / 5) *
        (x ^ (-(11 / 10) : ℝ) *
          ((11 + 16 * (v + 10 / 11) + 6 * (v ^ 2 + (20 / 11) * v + 200 / 121)) / (11 / 10))) := by
  have h := aux_integral_quad (d := 11 / 10) (by norm_num only) hx 0 6 16 11 (23 / 2)
  have he (t : ℝ) :
    finiteMajor t =
      (4 / 5) *
        (t ^ (-(11 / 10 : ℝ) - 1) * Real.log t ^ 0 *
          (6 * (Real.log t - 23 / 2) ^ 2 + 16 * (Real.log t - 23 / 2) + 11)) := by
    unfold finiteMajor
    norm_num only [pow_zero, mul_one, show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only]
    ring
  simp only [he, MeasureTheory.integral_const_mul, h, Nat.zero_add]
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  ring

/-- The square-root error integral is bounded by one common constant. -/
private theorem finite_bound {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    (∫ t in Set.Ioi (r ^ 2), finiteMajor t) ≤ 0.000084 := by
  have hr₁ := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 439569 / 4) (j := 17) (n := 27) (lo := 11) (hi :=
        11.60726) (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific, Rat.cast_ofNat, Rat.cast_div] at hlog
  have hru := pow_le_pow_left₀ (zero_le_one.trans hr₁) hr.2 2
  have hu := Real.log_le_log (sq_pos_of_pos (zero_lt_one.trans_le hr₁)) hru
  rw [show (663 / 2 : ℝ) ^ 2 = 439569 / 4 by norm_num only] at hu
  let v := Real.log (r ^ 2) - 23 / 2
  have hv : v ≤ 0.10726 := by
    dsimp only [v]; linarith only [hu, hlog]
  have hv₀ : 0 ≤ v := sub_nonneg.mpr (radius_log_box hr).1
  have hQ :
    ((11 + 16 * (v + 10 / 11) + 6 * (v ^ 2 + (20 / 11) * v + 200 / 121)) / (11 / 10)) ≤ 34.926 := by
    linarith only [hv, pow_le_pow_left₀ hv₀ hv 2]
  have hp := mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg (sq_nonneg r) (-(11 / 10)))
  have hb := mul_le_mul_of_nonneg_right (decay_box hr.1) (by norm_num only : 0 ≤ (34.926 : ℝ))
  rw [finite_centered (one_le_pow₀ hr₁)]
  change (4 / 5) * ((r ^ 2) ^ (-(11 / 10) : ℝ) * _) ≤ _
  dsimp only [v] at hp
  linarith only [hp, hb]

private theorem finite_bound_wide {r : ℝ} (hr : r ∈ Set.Icc 328 333) :
    (∫ t in Set.Ioi (r ^ 2), finiteMajor t) ≤ 0.000085 := by
  have hr₁ := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 110889) (j := 17) (n := 27) (lo := 11) (hi :=
        11.61629) (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific, Rat.cast_ofNat, Rat.cast_div] at hlog
  have hru := pow_le_pow_left₀ (zero_le_one.trans hr₁) hr.2 2
  have hu := Real.log_le_log (sq_pos_of_pos (zero_lt_one.trans_le hr₁)) hru
  rw [show (333 : ℝ) ^ 2 = 110889 by norm_num only] at hu
  let v := Real.log (r ^ 2) - 23 / 2
  have hv : v ≤ 0.11629 := by
    dsimp only [v]; linarith only [hu, hlog]
  have hv₀ : 0 ≤ v := sub_nonneg.mpr (radius_log_box_wide hr).1
  have hQ :
    ((11 + 16 * (v + 10 / 11) + 6 * (v ^ 2 + (20 / 11) * v + 200 / 121)) / (11 / 10)) ≤ 35.16 := by
    linarith only [hv, pow_le_pow_left₀ hv₀ hv 2]
  have hp := mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg (sq_nonneg r) (-(11 / 10)))
  have hb := mul_le_mul_of_nonneg_right (decay_box hr.1) (by norm_num only : 0 ≤ (35.16 : ℝ))
  rw [finite_centered (one_le_pow₀ hr₁)]
  change (4 / 5) * ((r ^ 2) ^ (-(11 / 10) : ℝ) * _) ≤ _
  dsimp only [v] at hp
  linarith only [hp, hb]

/-- The high error integral is evaluated at one million using the
quadratic moments of degrees two through four. -/
private theorem high_bound : (∫ t in Set.Ioi (1000000 : ℝ), highMajor t) ≤ 0.000286 := by
  let x : ℝ := 1000000
  have h :=
    aux_integral_quad (d := 11 / 10) (by norm_num only) (by norm_num only [x] : 1 ≤ x) 2 6 16 11
      (23 / 2)
  have he (t : ℝ) :
    highMajor t =
      (1 / 24) *
        (t ^ (-(11 / 10 : ℝ) - 1) * Real.log t ^ 2 *
          (6 * (Real.log t - 23 / 2) ^ 2 + 16 * (Real.log t - 23 / 2) + 11)) := by
    unfold highMajor
    rw [show -(11 / 10 : ℝ) - 1 = -(21 / 10) by norm_num only]
    ring
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 1000000) (j := 20) (n := 24) (lo := 13.81551)
      (hi := 13.81552) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1000000) (p := 11) (d :=
        10) (lo := 0) (hi := 0.000000251189) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hp
  have hd : 0 < (11 / 10 : ℝ) := by norm_num only
  have h₂ := Analysis.log_power_tail_poly_mono hd (by linarith only [hl.1]) hl.2 2
  have h₃ :=
    Analysis.log_power_tail_poly_mono hd (by norm_num only : (0 : ℝ) ≤ 13.81551)
      (show (13.81551 : ℝ) ≤ Real.log 1000000 by linarith only [hl.1]) 3
  have h₄ := Analysis.log_power_tail_poly_mono hd (by linarith only [hl.1]) hl.2 4
  have hQ :
    6 * Analysis.logPowerTailPoly (11 / 10) 4 (Real.log x) -
          122 * Analysis.logPowerTailPoly (11 / 10) 3 (Real.log x) +
        620.5 * Analysis.logPowerTailPoly (11 / 10) 2 (Real.log x) ≤
      27268 := by
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
      Nat.reduceAdd] at h₂ h₃ h₄ ⊢
    linarith only [h₂, h₃, h₄]
  have hm :=
    mul_le_mul_of_nonneg_left hQ (Real.rpow_nonneg (by norm_num only [x] : 0 ≤ x) (-(11 / 10)))
  have hp' : x ^ (-(11 / 10) : ℝ) ≤ 0.000000251189 := by
    dsimp only [x]; linarith only [hp]
  have hb := mul_le_mul_of_nonneg_right hp' (by norm_num only : (0 : ℝ) ≤ 27268)
  change (∫ t in Set.Ioi x, highMajor t) ≤ _
  simp only [he, MeasureTheory.integral_const_mul, h]
  norm_num only [Nat.reduceAdd]
  linarith only [hm, hb]

/-- The signed reflected tail, including its exact sign in the main
term, is uniformly at most 0.002704 on the section 137 interval. -/
theorem quarter_signed_tail_663 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
      0.002704 := by
  have h := quarter_profile_radius_upper_663 hRH hr
  dsimp only at h
  unfold quarterAbelError663 at h
  linarith only [h, quarter_main_upper_663 hr, decay_box hr.1, finite_bound hr, high_bound]

/-- The existing signed Chebyshev envelope also bounds the tail on the
larger radii of the first K137 cell. -/
theorem quarter_signed_tail_gaussian (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 332) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
      0.002764 := by
  have hb : r ∈ Set.Icc 328 333 :=
    ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hr.1, hr.2.trans (by norm_num only)⟩
  have h := quarter_profile_radius_wide_663 hRH hb
  dsimp only at h
  unfold quarterAbelError663 at h
  linarith only [h, main_first_gaussian hr, decay_box hb.1, finite_bound_wide hb, high_bound]

/-- Bound the signed Chebyshev tail for the next K137 cells, up to radius 333. -/
theorem quarter_signed_tail_gaussian_wide (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 333) :
    (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
        ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
      0.002891 := by
  have hb : r ∈ Set.Icc 328 333 := ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hr.1, hr.2⟩
  have h := quarter_profile_radius_wide_663 hRH hb
  dsimp only at h
  unfold quarterAbelError663 at h
  linarith only [h, main_next_gaussian hr, decay_box hb.1, finite_bound_wide hb, high_bound]

/-- The forward part has finite support, and a bounded common trace
preserves absolute convergence of the reflected series. -/
private theorem common_tail_summable {r : ℝ} (hr : 328 ≤ r) (a : ℕ → ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 4) :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n *
          ((4 - a n) *
              (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
            a n * quarterDensity663 n)) := by
  have hx := sq_pos_of_pos ((by norm_num only : (0 : ℝ) < 328).trans_le hr)
  let f := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n *
      ((4 - a n) * (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0))
  have hf : Summable f := by
    apply summable_of_ne_finset_zero (s := Finset.Iic ⌊Real.exp (21 / 8) * r ^ 2⌋₊)
    intro n hn
    have hn' := Nat.lt_of_floor_lt (lt_of_not_ge (fun hh ↦ hn (Finset.mem_Iic.mpr hh)))
    have hp : 0 < (n : ℝ) := (mul_pos (Real.exp_pos _) hx).trans hn'
    have hs : ¬Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 := by
      intro h
      exact (not_le_of_gt hn') ((div_le_iff₀ hx).mp ((Real.log_le_iff_le_exp (div_pos hp hx)).mp h))
    simp only [f, ite_eq_right hs, mul_zero]
  have hg :
    Summable (fun n : ℕ ↦ a n * (ArithmeticFunction.vonMangoldt n * quarterDensity663 n)) := by
    apply Summable.of_norm_bounded (quarter_profile_summable_663.norm.mul_left 4)
    intro n
    rw [norm_mul, Real.norm_of_nonneg (ha n).1]
    exact mul_le_mul_of_nonneg_right (ha n).2 (norm_nonneg _)
  exact
    (hf.sub hg).congr
      (fun n ↦ by
        dsimp only [f, Pi.sub_apply]; ring)

/-- The finite common Euler comparison passes to the infinite tail.
For a common trace combination with deficit between zero and four, the reflected tail
therefore costs at most four times 0.002704. -/
theorem quarter_euler_tail_lower_663 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Set.Icc 0 4) :
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n *
        ((4 - a n) *
            (if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0) -
          a n * quarterDensity663 n)
    (-0.010816 : ℝ) ≤ (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  intro w
  let g := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterDensity663 n
  have hg :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix g
      (by simp only [g, ArithmeticFunction.map_zero, zero_mul]) quarter_profile_summable_663 (r ^ 2)
  have hw :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix w
      (by simp only [w, ArithmeticFunction.map_zero, zero_mul]) (common_tail_summable hr.1 a ha)
      (r ^ 2)
  have h :=
    le_of_tendsto_of_tendsto (hg.const_mul (-4)) hw
      (Filter.Eventually.of_forall fun N ↦ by
        dsimp only
        have hb :=
          quarter_euler_tail_sum_663 (Finset.Ioc ⌊r ^ 2⌋₊ N) a hr.1
            (fun n hn ↦ (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hn).1).le) (fun n _ ↦ ha n)
        dsimp only [w, g, quarterDensity663] at *
        convert hb using 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        ring)
  have htail := quarter_signed_tail_663 hRH hr
  dsimp only [g] at h
  linarith only [h, htail]

/-- Every retained atom above the cutoff has the full forward contribution.
Its signed reflected contribution is bounded below using F > -20. -/
private theorem retained_atom_lower {r : ℝ} (hr : 328 ≤ r) {n : ℕ} (hn : r ^ 2 ≤ (n : ℝ)) :
    -(20 : ℝ) * (n : ℝ) ^ (-(8 / 5) : ℝ) ≤ quarterDensity663 n := by
  have hx : (107584 : ℝ) ≤ r ^ 2 := by
    rw [show (107584 : ℝ) = 328 ^ 2 by norm_num only]
    exact pow_le_pow_left₀ (by norm_num only) hr 2
  have hc :=
    (Analysis.rationalLogIntervalCheck_sound (N := 107584) (j := 17) (n := 24) (lo := 23 / 2) (hi :=
        12) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hc
  have hl := hc.trans (Real.log_le_log (by norm_num only) (hx.trans hn))
  have hF := (quarter_profile_gt_neg20_663 hl).le
  unfold quarterDensity663
  rw [mul_comm (-(20 : ℝ))]
  exact mul_le_mul_of_nonneg_left hF (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- Retain the known passing atoms in the common Euler comparison while
charging their reflected negative parts. The finite retained set and the
remaining infinite tail use the same trace deficit. -/
theorem quarter_euler_retained_of_tail {r T : ℝ} (hr : 328 ≤ r) (a : ℕ → ℝ)
    (ha : ∀ n, a n ∈ Set.Icc 0 4) (K : Finset ℕ) (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ))
    (hpass : ∀ n ∈ K, a n = 0)
    (hmain :
      (∑' n : ℕ, ArithmeticFunction.vonMangoldt n * quarterDensity663 n) -
          ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, ArithmeticFunction.vonMangoldt n * quarterDensity663 n ≤
        T) :
    let f := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * ((4 - a n) * f n - a n * quarterDensity663 n)
    (-4 * T) + (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * f n)) -
        (∑ n ∈ K, 80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  intro f w
  let g := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterDensity663 n
  let c := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * (4 * f n - 80 * (n : ℝ) ^ (-(8 / 5) : ℝ))
  have hg :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix g
      (by simp only [g, ArithmeticFunction.map_zero, zero_mul]) quarter_profile_summable_663 (r ^ 2)
  have hw :=
    AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix w
      (by simp only [w, ArithmeticFunction.map_zero, zero_mul]) (common_tail_summable hr a ha)
      (r ^ 2)
  have hs :=
    le_of_tendsto_of_tendsto ((hg.const_mul (-4)).add_const (∑ n ∈ K, c n)) hw
      (by
        filter_upwards [Filter.eventually_ge_atTop (K.sup id)] with N hN
        have hKS : K ⊆ Finset.Ioc ⌊r ^ 2⌋₊ N := fun n hn ↦
          Finset.mem_Ioc.mpr
            ⟨Nat.floor_lt (by positivity) |>.mpr (hK n hn), (Finset.le_sup (f := id) hn).trans hN⟩
        rw [Finset.mul_sum, ←
          Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc ⌊r ^ 2⌋₊ N) (p := fun n ↦ n ∈ K)]
        rw [show (Finset.Ioc ⌊r ^ 2⌋₊ N).filter (fun n ↦ n ∈ K) = K
            by
            ext n
            simp only [Finset.mem_filter]
            exact ⟨And.right, fun hn ↦ ⟨hKS hn, hn⟩⟩]
        rw [add_assoc, add_comm _ (∑ n ∈ K, c n), ← add_assoc, ← Finset.sum_add_distrib]
        rw [←
          Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc ⌊r ^ 2⌋₊ N) (p := fun n ↦ n ∈ K)
            (f := w)]
        rw [show (Finset.Ioc ⌊r ^ 2⌋₊ N).filter (fun n ↦ n ∈ K) = K
            by
            ext n
            simp only [Finset.mem_filter]
            exact ⟨And.right, fun hn ↦ ⟨hKS hn, hn⟩⟩]
        apply add_le_add
        · apply Finset.sum_le_sum
          intro n hn
          have h := retained_atom_lower hr (hK n hn).le
          dsimp only [w, g, c]
          rw [hpass n hn]
          linear_combination (4 * ArithmeticFunction.vonMangoldt n) * h
        · apply Finset.sum_le_sum
          intro n hn
          have hn' := (Finset.mem_filter.mp hn).1
          have ht := (Nat.lt_of_floor_lt (Finset.mem_Ioc.mp hn').1).le
          have h :=
            mul_le_mul_of_nonneg_left (quarter_physical_euler_663 hr ht (ha n))
              (ArithmeticFunction.vonMangoldt_nonneg (n := n))
          dsimp only [w, f, g, quarterDensity663]
          linear_combination h)
  have hc (n : ℕ) :
    c n =
      4 * (ArithmeticFunction.vonMangoldt n * f n) -
        80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ)) := by
    dsimp only [c]
    ring
  simp only [hc, Finset.sum_sub_distrib, g] at hs
  linarith only [hs, hmain]

/-- Use the certified tail budget on the original quarter-square interval. -/
theorem quarter_euler_retained_663 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) (a : ℕ → ℝ) (ha : ∀ n, a n ∈ Set.Icc 0 4) (K : Finset ℕ)
    (hK : ∀ n ∈ K, r ^ 2 < (n : ℝ)) (hpass : ∀ n ∈ K, a n = 0) :
    let f := fun n : ℕ ↦
      if Real.log ((n : ℝ) / r ^ 2) ≤ 21 / 8 then quarterWeight656 (r ^ 2) n else 0
    let w := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n * ((4 - a n) * f n - a n * quarterDensity663 n)
    (-0.010816 : ℝ) + (∑ n ∈ K, 4 * (ArithmeticFunction.vonMangoldt n * f n)) -
        (∑ n ∈ K, 80 * (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-(8 / 5) : ℝ))) ≤
      (∑' n : ℕ, w n) - ∑ n ∈ Finset.Ioc 0 ⌊r ^ 2⌋₊, w n := by
  have h := quarter_euler_retained_of_tail hr.1 a ha K hK hpass (quarter_signed_tail_663 hRH hr)
  dsimp only at h ⊢
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
