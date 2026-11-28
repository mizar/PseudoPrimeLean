/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaSeries656
import PseudoPrime.Analysis.LogTaylorBounds

/-! # First Gamma-pole bounds for the two section 132 intervals -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An upper log bound at the reciprocal gives a negative exponential upper bound. -/
private theorem exp_neg_le_of_log_inv {a b : ℝ} (hb : 0 < b) (h : Real.log b⁻¹ ≤ a) :
    Real.exp (-a) ≤ b := by
  apply (Real.le_log_iff_exp_le hb).mp
  rw [Real.log_inv] at h
  exact neg_le.mp h

/-- A lower log bound at the reciprocal gives a negative exponential lower bound. -/
private theorem le_exp_neg_of_log_inv {a b : ℝ} (hb : 0 < b) (h : a ≤ Real.log b⁻¹) :
    b ≤ Real.exp (-a) := by
  apply (Real.log_le_iff_le_exp hb).mp
  rw [Real.log_inv] at h
  exact le_neg.mp h

/-- Bound the truncated polynomial moment from an upper bound on its
positive exponential tail. -/
private theorem first_moment_lower_of_exp {l t m : ℝ} (ht : Real.exp (-(3 / 5) * l) ≤ t)
    (hm : m ≤ Analysis.logPowerTailPoly (3 / 5) 5 0 - t * Analysis.logPowerTailPoly (3 / 5) 5 l)
    (hp : 0 ≤ Analysis.logPowerTailPoly (3 / 5) 5 l) :
    m ≤
      Analysis.logPowerTailPoly (3 / 5) 5 0 -
        Real.exp (-(3 / 5) * l) * Analysis.logPowerTailPoly (3 / 5) 5 l := by
  exact hm.trans (sub_le_sub_left (mul_le_mul_of_nonneg_right ht hp) _)

/-- A rational lower bound for each factor gives a lower bound for the
first pole at every scale in the interval. -/
private theorem first_rectangle_lower {l z u m f c : ℝ} (hl₀ : 0 ≤ l) (hl : l ≤ z) (hu : z ≤ u)
    (hf : f ≤ Real.exp (-(1 / 2) * u))
    (hm :
      m ≤
        Analysis.logPowerTailPoly (3 / 5) 5 0 -
          Real.exp (-(3 / 5) * l) * Analysis.logPowerTailPoly (3 / 5) 5 l)
    (hm₀ : 0 ≤ m) (hc : c ≤ (11 / 10 : ℝ) ^ 5 / 120 * f * m) : c ≤ quarterGammaFirst656 z := by
  refine
    hc.trans
      ((mul_le_mul (mul_le_mul_of_nonneg_left hf (by norm_num only)) hm hm₀
            (mul_nonneg (by norm_num only) (Real.exp_pos _).le)).trans
        ?_)
  exact quarter_first_interval_lower_656 hl₀ hl hu

/-- The first interval's rational endpoint rectangle gives a first-pole
correction of at least 0.02431. -/
private theorem first_rectangle_left_656 {z : ℝ} (hl : 14.1741 ≤ z) (hu : z ≤ 14.19266) :
    0.02431 ≤ quarterGammaFirst656 z := by
  have htail :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000 / 20257) (j := 13) (n := 48) (lo := 8)
        (hi := 8.50445) (by decide +kernel)).2
  have hfront :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000 / 82813) (j := 11) (n := 48) (lo :=
        7.09634) (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at htail hfront
  have ht : Real.exp (-(3 / 5 : ℝ) * 14.1741) ≤ 0.00020257 := by
    rw [neg_mul]
    refine exp_neg_le_of_log_inv (a := (3 / 5 : ℝ) * 14.1741) (by norm_num only) ?_
    norm_num only at htail ⊢
    linarith only [htail]
  have hf : 0.00082813 ≤ Real.exp (-(1 / 2 : ℝ) * 14.19266) := by
    rw [neg_mul]
    refine le_exp_neg_of_log_inv (a := (1 / 2 : ℝ) * 14.19266) (by norm_num only) ?_
    norm_num only at hfront ⊢
    linarith only [hfront]
  have hm :=
    first_moment_lower_of_exp ht (m := 2188)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.02431) (f := 0.00082813) (by norm_num only) hl hu hf hm
      (by norm_num only) (by norm_num only)

/-- The second interval's rational endpoint rectangle gives a first-pole
correction of at least 0.02411. -/
private theorem first_rectangle_right_656 {z : ℝ} (hl : 14.19264 ≤ z) (hu : z ≤ 14.21103) :
    0.02411 ≤ quarterGammaFirst656 z := by
  have htail :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000 / 20033) (j := 13) (n := 48) (lo := 8)
        (hi := 8.51557) (by decide +kernel)).2
  have hfront :=
    (Analysis.rationalLogIntervalCheck_sound (N := 100000000 / 82055) (j := 11) (n := 48) (lo :=
        7.10553) (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at htail hfront
  have ht : Real.exp (-(3 / 5 : ℝ) * 14.19264) ≤ 0.00020033 := by
    rw [neg_mul]
    refine exp_neg_le_of_log_inv (a := (3 / 5 : ℝ) * 14.19264) (by norm_num only) ?_
    norm_num only at htail ⊢
    linarith only [htail]
  have hf : 0.00082055 ≤ Real.exp (-(1 / 2 : ℝ) * 14.21103) := by
    rw [neg_mul]
    refine le_exp_neg_of_log_inv (a := (1 / 2 : ℝ) * 14.21103) (by norm_num only) ?_
    norm_num only at hfront ⊢
    linarith only [hfront]
  have hm :=
    first_moment_lower_of_exp ht (m := 2190)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.02411) (f := 0.00082055) (by norm_num only) hl hu hf hm
      (by norm_num only) (by norm_num only)

/-- The lower and upper endpoint certificates bound the shifted logarithm
throughout both section 132 radius intervals. -/
private theorem first_log_box_656 (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325)) :
    Real.log (r ^ 2) + 21 / 8 ∈
      Set.Icc (if right then 14.19264 else 14.1741) (if right then 14.21103 else 14.19266) := by
  have h322 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 32) (lo := 5.774551) (hi :=
        6) (by decide +kernel)).1
  have h325 :=
    Analysis.rationalLogIntervalCheck_sound (N := 325) (j := 9) (n := 32) (lo := 5.783825) (hi :=
      5.783826) (by decide +kernel)
  have h328 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 32) (lo := 5) (hi :=
        5.793014) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at h322 h325 h328
  rw [Real.log_pow]
  cases right
  · simp only [Bool.false_eq_true, ite_false]
    change r ∈ Set.Icc 322 325 at hr
    have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hr.1
    have hu := Real.log_le_log ((by norm_num only : (0 : ℝ) < 322).trans_le hr.1) hr.2
    exact ⟨by linarith only [hl, h322], by linarith only [hu, h325.2]⟩
  · simp only [ite_true]
    change r ∈ Set.Icc 325 328 at hr
    have hl := Real.log_le_log (by norm_num only : (0 : ℝ) < 325) hr.1
    have hu := Real.log_le_log ((by norm_num only : (0 : ℝ) < 325).trans_le hr.1) hr.2
    exact ⟨by linarith only [hl, h325.1], by linarith only [hu, h328]⟩

/-- The two first-pole lower bounds hold over the respective broad radius
intervals, using the certified endpoint rectangles. -/
theorem quarter_first_rows_lower_656 (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325)) :
    (if right then 0.02411 else 0.02431) ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
  have h := first_log_box_656 right hr
  cases right
  · exact first_rectangle_left_656 h.1 h.2
  · exact first_rectangle_right_656 h.1 h.2

/-- On each broad radius interval the principal Gamma contribution in
the scalar comparison is bounded by the weight at one and a rational credit. -/
theorem quarter_principal_gamma_rows_656 (right : Bool) {r : ℝ}
    (hr : r ∈ Set.Icc (if right then 325 else 322) (if right then 328 else 325)) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - (if right then 0.02411 else 0.02431) := by
  have hr₀ : 322 ≤ r := by
    cases right
    · exact hr.1
    · exact (by norm_num only : (322 : ℝ) ≤ 325).trans hr.1
  exact
    (quarter_principal_gamma_upper_656 hr₀).trans
      (sub_le_sub_left (quarter_first_rows_lower_656 right hr) _)

private theorem first_rectangle_gaussian {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 14.237) :
    0.02385 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 50000000 / 40499) (j := 11) (n := 48) (lo :=
        7.1185005) (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.00080998 ≤ Real.exp (-(1 / 2 : ℝ) * 14.237) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.02385) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 1329/4, covering all three scaled K137 cells. -/
theorem quarter_gamma_gaussian_first {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) (1329 / 4)) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.02385 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1329 / 4) (j := 9) (n := 32) (lo := 5) (hi :=
        5.8059) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.02385 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_gaussian (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem first_rectangle_k197 {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 14.239) :
    0.02382 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 809) (j := 11) (n := 48) (lo := 7.1195)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000809 ≤ Real.exp (-(1 / 2 : ℝ) * 14.239) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.02382) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 665/2, covering the first scaled K197 cell. -/
theorem quarter_gamma_k197_first {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) (665 / 2)) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.02382 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 665 / 2) (j := 9) (n := 32) (lo := 5) (hi :=
        5.807) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.02382 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_k197 (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem first_rectangle_k197_next {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 14.248) :
    0.02367 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 804) (j := 11) (n := 48) (lo := 7.124)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000804 ≤ Real.exp (-(1 / 2 : ℝ) * 14.248) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.02367) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 334, covering the next scaled K197 cell. -/
theorem quarter_gamma_k197_next {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 334) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.02367 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 334) (j := 9) (n := 32) (lo := 5) (hi := 5.81115)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.02367 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_k197_next (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem first_rectangle_k197_wide {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 14.265) :
    0.02349 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 798) (j := 11) (n := 48) (lo := 7.1325)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000798 ≤ Real.exp (-(1 / 2 : ℝ) * 14.265) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.02349) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 336.9, covering the next scaled K197 cell. -/
theorem quarter_gamma_k197_wide {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 336.9) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.02349 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 336.9) (j := 9) (n := 32) (lo := 5) (hi := 5.82)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.02349 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_k197_wide (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem first_rectangle_k197_mid {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 14.301) :
    0.02305 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 783) (j := 11) (n := 48) (lo := 7.1505)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000783 ≤ Real.exp (-(1 / 2 : ℝ) * 14.301) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.02305) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 342.9, covering the middle K197 radii. -/
theorem quarter_gamma_k197_mid {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 342.9) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.02305 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 342.9) (j := 9) (n := 32) (lo := 5) (hi := 5.838)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.02305 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_k197_mid (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem first_rectangle_to34610 {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 14.319) :
    0.0228 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 777) (j := 11) (n := 48) (lo := 7.1600)
        (hi := 8) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000777 ≤ Real.exp (-(1 / 2 : ℝ) * 14.319) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.0228) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 346.1, covering the middle K197 radii. -/
theorem quarter_gamma_k197_to34610 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 346.1) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.0228 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 346.1) (j := 9) (n := 32) (lo := 5) (hi := 5.847)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.0228 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_to34610 (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

end PseudoPrime.PrimeTestBounds.MillerRabin
