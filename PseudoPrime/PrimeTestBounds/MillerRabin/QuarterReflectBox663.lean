/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflect663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflect663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflectTail656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly656

/-! # Uniform numerical bounds for the four reflected tails in section 137 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem cap_rectangle {r h e v D : ℝ} (hr : 0 < r) (hh : h ≤ 2 * Real.log r)
    (he : Real.exp ((11 / 10) * h) ≤ e) (hv : 2 * Real.log r ≤ v) (hD : r ^ (-(11 / 5) : ℝ) ≤ D) :
    quarterAuxReflectCap656 r h 103684 ≤
      ((11 / 10 : ℝ) ^ 5 / 30 * D * e) *
        ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (v - h) ^ (5 - j) * momentBox j := by
  have hz := sub_le_sub_right hv h
  have hv := sub_nonneg.mpr hh
  have he₀ := (Real.exp_pos _).le.trans he
  unfold quarterAuxReflectCap656
  rw [show
      ∀ S : ℝ,
        ((11 / 10 : ℝ) ^ 5 / 120 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h)) * (4 * S) =
          ((11 / 10 : ℝ) ^ 5 / 30 * r ^ (-(11 / 5) : ℝ) * Real.exp ((11 / 10) * h)) * S
      from fun S ↦ by ring]
  have hD₀ := (Real.rpow_nonneg hr.le (-(11 / 5) : ℝ)).trans hD
  gcongr
  all_goals
    first
    | exact cap_numeric _
    | exact cap_nonneg _
    | exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (hv.trans hz) _)
    |
      exact
        Finset.sum_nonneg
          (fun j _ ↦ mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hv _)) (cap_nonneg j))

private theorem cap_log_bound {r R v : ℝ} (hr : 0 < r) (hR : r ≤ R) (hv : Real.log R ≤ v / 2) :
    2 * Real.log r ≤ v := by linarith only [(Real.log_le_log hr hR).trans hv]

private theorem cap_decay_bound {r R D : ℝ} (hR : 0 < R) (hr : R ≤ r)
    (hD : (R ^ (2 : ℕ)) ^ (-(11 / 10) : ℝ) ≤ D) : r ^ (-(11 / 5) : ℝ) ≤ D := by
  rw [← Real.rpow_natCast_mul hR.le] at hD
  norm_num only [Nat.cast_ofNat] at hD
  have h := Real.rpow_le_rpow_of_nonpos hR hr (by norm_num only : (-(11 / 5) : ℝ) ≤ 0)
  linarith only [h, hD]

private theorem cap_log_332 {r : ℝ} (hr : 0 < r) (hu : r ≤ 332) : 2 * Real.log r ≤ 11.611 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 332) (j := 9) (n := 27) (lo := 5) (hi :=
        58055 / 10000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact cap_log_bound hr hu (by linarith only [h])

private theorem cap_log_33225 {r : ℝ} (hr : 0 < r) (hu : r ≤ 1329 / 4) :
    2 * Real.log r ≤ 11.6118 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1329 / 4) (j := 9) (n := 27) (lo := 5) (hi :=
        58059 / 10000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  exact cap_log_bound hr hu (by linarith only [h])

private theorem cap_decay_328 {r : ℝ} (hr : 328 ≤ r) : r ^ (-(11 / 5) : ℝ) ≤ 0.000002917949 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 107584) (p := 11) (d :=
        10) (lo := 0) (hi := 2917949 / 10 ^ 12) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h
  exact
    cap_decay_bound (by norm_num only) hr
      (by
        norm_num only; exact h)

private theorem cap_decay_332 {r : ℝ} (hr : 332 ≤ r) : r ^ (-(11 / 5) : ℝ) ≤ 0.00000285 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 110224) (p := 11) (d :=
        10) (lo := 0) (hi := 285 / 10 ^ 8) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at h
  exact
    cap_decay_bound (by norm_num only) hr
      (by
        norm_num only; exact h)

private theorem shift_exp_upper (h e : ℚ) (hh : |(11 / 10 : ℚ) * h| ≤ 11)
    (he : profileExpTaylor ((11 / 10) * h) + 1 / 10 ^ 16 ≤ e) :
    Real.exp ((11 / 10 : ℝ) * (h : ℝ)) ≤ (e : ℝ) := by
  have hT := profile_exp_error ((11 / 10) * h) (by exact_mod_cast hh)
  have hR := (Rat.cast_le (K := ℝ)).mpr he
  simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_add, Rat.cast_pow] at hT hR
  linarith only [(abs_le.mp hT).2, hR]

private theorem cap_at (i : Fin 6) {h e : ℚ} {b r : ℝ} (hr : r ∈ Set.Icc 328 (1329 / 4))
    (hlog : 7 ≤ 2 * Real.log r) (hi : quarterShift663 i = h) (hh : h ≤ 7)
    (hex : |(11 / 10 : ℚ) * h| ≤ 11) (he : profileExpTaylor ((11 / 10) * h) + 1 / 10 ^ 16 ≤ e)
    (hb₁ :
      ((11 / 10 : ℝ) ^ 5 / 30 * 0.000002917949 * (e : ℝ)) *
          ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (11.611 - (h : ℝ)) ^ (5 - j) * momentBox j ≤
        b)
    (hb₂ :
      ((11 / 10 : ℝ) ^ 5 / 30 * 0.00000285 * (e : ℝ)) *
          ∑ j ∈ Finset.range 6, (Nat.choose 5 j : ℝ) * (11.6118 - (h : ℝ)) ^ (5 - j) * momentBox j ≤
        b) :
    quarterAuxReflectCap656 r (quarterShift663 i : ℝ) 103684 ≤ b := by
  rw [hi]
  have hh' := (by exact_mod_cast hh : (h : ℝ) ≤ 7).trans hlog
  have he' := shift_exp_upper h e hex he
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  by_cases hc : r ≤ 332
  · exact (cap_rectangle hr₀ hh' he' (cap_log_332 hr₀ hc) (cap_decay_328 hr.1)).trans hb₁
  · exact
      (cap_rectangle hr₀ hh' he' (cap_log_33225 hr₀ hr.2) (cap_decay_332 (le_of_not_ge hc))).trans
        hb₂

/-- The common prefix through 322 squared bounds the four shifted tails
throughout the section 137 radius interval. -/
theorem quarter_reflect_caps_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (1329 / 4))
    (hlog : 7 ≤ 2 * Real.log r) :
    let C := fun i : Fin 6 ↦ quarterAuxReflectCap656 r (quarterShift663 i : ℝ) 103684
    C 1 ≤ 0.002790 ∧ C 2 ≤ 0.013363 ∧ C 3 ≤ 0.059140 ∧ C 5 ≤ 0.851752 := by
  have h₁ := cap_at 1 hr hlog (h := 1 / 10) (e := 1.116279) (b := 0.002790)
  have h₂ := cap_at 2 hr hlog (h := 1.85) (e := 7.652253) (b := 0.013363)
  have h₃ := cap_at 3 hr hlog (h := 3.54) (e := 49.106923) (b := 0.059140)
  have h₅ := cap_at 5 hr hlog (h := 6.66) (e := 1519.292433) (b := 0.851752)
  refine ⟨h₁ ?_ ?_ ?_ ?_ ?_ ?_, h₂ ?_ ?_ ?_ ?_ ?_ ?_, h₃ ?_ ?_ ?_ ?_ ?_ ?_, h₅ ?_ ?_ ?_ ?_ ?_ ?_⟩
  all_goals
    first
    | decide +kernel
    |
      norm_num only [momentBox, Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific,
        Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero, Nat.choose,
        Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, Rat.cast_one]

/-- The four numerical caps bound the complete signed reflection charge
on every radius in the section 137 comparison. -/
theorem quarter_reflect_lower_box_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (1329 / 4))
    (hlog : 7 ≤ 2 * Real.log r) : (-0.003326 : ℝ) ≤ quarterReflectLower663 r 103684 := by
  obtain ⟨h₁, h₂, h₃, h₅⟩ := quarter_reflect_caps_663 hr hlog
  have hc₂ : quarterCoeff663 2 = -47978520 / 10 ^ 9 := by decide +kernel
  have hc₃ : quarterCoeff663 3 = -41881026 / 10 ^ 9 := by decide +kernel
  unfold quarterReflectLower663
  rw [hc₂, hc₃]
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_neg, Rat.cast_ofNat]
  linarith only [h₁, h₂, h₃, h₅]

/-- With the common prefix through 322 squared, the residual comparison
can charge a fixed amount for all six shifted reflections. -/
theorem quarter_shift_residual_box_663 (hRH : RiemannHypothesis) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hp : ∀ n ∈ Finset.Ioc 0 103684, ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) {r R l u M : ℝ}
    (hr : r ∈ Set.Icc 328 (1329 / 4)) (hR : r ≤ R) (hl : 0 ≤ l)
    (hv : 2 * Real.log r - 23 / 2 ∈ Set.Icc l u) (hM : r ^ (-(6 / 5) : ℝ) ≤ M)
    (hP : 0 ≤ thetaIntervalUpper663 l u) :
    -(11 / 10) ^ 5 / 30 * M * thetaIntervalUpper663 l u + 18.29172549 / R - 0.003326 ≤
      quarterAuxTheta663 r + quarterAuxNegPole663 / r +
        ∑ i, (quarterCoeff663 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hlog : 7 ≤ 2 * Real.log r := by linarith only [hl, hv.1]
  have h :=
    quarter_shift_residual_lower_663 hRH (by norm_num only) (by norm_num only) α hα hp hr.1 hR hl hv
      hM hP
  linarith only [h, quarter_reflect_lower_box_663 hr hlog]

private theorem theta_radius_box {r : ℝ} (hr : r ∈ Set.Icc 328 (1329 / 4)) :
    0.086 ≤ 2 * Real.log r - 23 / 2 ∧ quarterAuxConductorPoly663 (2 * Real.log r) ≤ 49404 := by
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1329 / 4) (j := 9) (n := 27) (lo := 5) (hi :=
        5.8059) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hhi
  have h₁ := hlo.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1)
  have h₂ := (Real.log_le_log hr₀ hr.2).trans hhi
  have hb : 2 * Real.log r - 23 / 2 ∈ Set.Icc 0.086 0.1118 :=
    ⟨by linarith only [h₁], by linarith only [h₂]⟩
  refine ⟨hb.1, (theta_poly_interval_663 (by norm_num only) hb).trans ?_⟩
  have h : thetaIntervalUpper663 0.086 0.1118 ≤ 49404 := by
    norm_num only [thetaIntervalUpper663, thetaCoeffUpper663, Fin.sum_univ_succ, Fin.sum_univ_zero,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.val_zero, Fin.val_succ, Rat.cast_ofScientific,
      Rat.cast_neg, ite_eq_left, ite_eq_right]
  exact h

private theorem right_decay_box : (663 / 2 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000945 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 109892) (p := 3) (d :=
        5) (lo := 0) (hi := 0.000945) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, neg_div] at h
  rw [show (-(6 / 5 : ℝ)) = ((2 : ℕ) : ℝ) * (-(3 / 5)) by norm_num only,
    Real.rpow_natCast_mul (by norm_num only : (0 : ℝ) ≤ 663 / 2)]
  refine
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 109892) (by norm_num only)
          (by norm_num only)).trans
      ?_
  norm_num only at h ⊢
  exact h

/-- On radii from 663/2 through 1329/4, the polynomial cap and the
decreasing power give a uniform lower bound for the conductor contribution. -/
theorem quarter_theta_lower_from663 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) (1329 / 4)) :
    -2.507 ≤ quarterAuxTheta663 r := by
  have h₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hb := theta_radius_box ⟨(by norm_num only : (328 : ℝ) ≤ 663 / 2).trans hr.1, hr.2⟩
  have hd :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
          (by norm_num only : (-(6 / 5) : ℝ) ≤ 0)).trans
      right_decay_box
  have hm :=
    (mul_le_mul_of_nonneg_left hb.2 (Real.rpow_nonneg h₀.le _)).trans
      (mul_le_mul_of_nonneg_right hd (by norm_num only))
  unfold quarterAuxTheta663
  nlinarith only [hm]

/-- Over the entire section 137 interval, the conductor contribution is
bounded by its certified right-endpoint estimate with an affine correction. -/
theorem quarter_theta_affine_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (663 / 2)) :
    -2.507 - 0.01 * (663 / 2 - r) ≤ quarterAuxTheta663 r := by
  have hd :=
    (theta_decay_affine (by linarith only [hr.1]) hr.2).trans (add_le_add right_decay_box le_rfl)
  have hR : r ∈ Set.Icc 328 (1329 / 4) := ⟨hr.1, hr.2.trans (by norm_num only)⟩
  have hm :=
    (mul_le_mul_of_nonneg_left (theta_radius_box hR).2
          (Real.rpow_nonneg (by linarith only [hr.1]) (-(6 / 5) : ℝ))).trans
      (mul_le_mul_of_nonneg_right hd (by norm_num only))
  have hs := sub_nonneg.mpr hr.2
  unfold quarterAuxTheta663
  nlinarith only [hm, hs]

/-- The linear deficit and the shifted conductor, pole and reflection terms
have a common lower bound on all radii of section 137. -/
theorem quarter_shift_comparison_lower_663 (hRH : RiemannHypothesis) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hp : ∀ n ∈ Finset.Ioc 0 103684, ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) :
    -13.054754 + 0.0219746789 * (663 / 2 - r) ≤
      -(3 / 4 - 0.71780481 + quarterAuxMix663 quarterConductorProfile663 + quarterAuxHalfCoeff663) *
          r +
        quarterAuxTheta663 r +
        quarterAuxNegPole663 / r +
        ∑ i, (quarterCoeff663 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hr₀ : 0 < r := by linarith only [hr.1]
  have hR : r ∈ Set.Icc 328 (1329 / 4) := ⟨hr.1, hr.2.trans (by norm_num only)⟩
  have hlog : 7 ≤ 2 * Real.log r := by linarith only [(theta_radius_box hR).1]
  have href :=
    (quarter_reflect_lower_box_663 hR hlog).trans
      (quarter_reflection_tail_663 hRH (by norm_num only) (by norm_num only) α hα hp hr₀ hlog)
  have hP :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 18.29172549) hr₀ hr.2).trans
      (div_le_div_of_nonneg_right quarter_aux_neg_pole_box_663.1 hr₀.le)
  linarith only [quarter_theta_affine_663 hr, quarter_aux_deficit_663 hr₀.le, hr.2, href, hP]

/-- The section 137 lower bound written directly in terms of the symmetric
conductor transform and the shifted kernel residues. -/
theorem quarter_shift_transform_lower_663 (hRH : RiemannHypothesis) (α : ℕ → ℝ)
    (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hp : ∀ n ∈ Finset.Ioc 0 103684, ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) {r : ℝ}
    (hr : r ∈ Set.Icc 328 (663 / 2)) :
    let x := fun i : Fin 6 ↦ r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ))
    (-13.054754 : ℝ) + 0.0219746789 * (663 / 2 - r) ≤
      -(3 / 4 - 0.71780481) * r -
          (4 * r) * quarterAuxMix663 (fun s ↦ quarterSymmetricProfile656 (Real.exp (s : ℝ))⁻¹) -
          3 *
            (∑ i,
              (quarterCoeff663 i : ℝ) *
                (quarterKernel656.function (1 / 2) * (x i : ℂ) ^ (1 / 2 : ℂ)).re) +
        (∑ i,
          (quarterCoeff663 i : ℝ) *
            (4 * r * (quarterKernel656.transform (x i)⁻¹).re -
              3 *
                (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) *
                    (x i : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re)) +
        ∑ i, (quarterCoeff663 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  intro x
  dsimp only [x]
  rw [quarter_aux_conductor_sum_663 rfl, quarter_aux_half_pole_sum_663 (by linarith only [hr.1]),
    quarter_aux_shift_signed_663 hr.1]
  linarith only [quarter_shift_comparison_lower_663 hRH α hα hp hr]

/-- The same moment bounds apply at the unshifted scale throughout the
section 137 radius range. -/
theorem quarter_main_reflect_box_663 {r : ℝ} (hr : r ∈ Set.Icc 328 (1329 / 4)) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.000242 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  refine (cap_rectangle hr₀ hh he' (cap_log_33225 hr₀ hr.2) (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

/-- An upper bound for the unshifted reflection through the first two K197 cells. -/
theorem k197_main_reflect_box {r : ℝ} (hr : r ∈ Set.Icc 328 336.9) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.000251 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 336.9) (j := 9) (n := 27) (lo := 5) (hi := 5.82)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 11.64 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

/-- An upper bound for the unshifted reflection through radius 342.9. -/
theorem k197_mid_main_reflect_box {r : ℝ} (hr : r ∈ Set.Icc 328 342.9) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.000255 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 342.9) (j := 9) (n := 27) (lo := 5) (hi := 5.838)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 11.676 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

/-- The main reflected kernel costs at most 0.00027 on radii 328 through 346.1. -/
theorem k197_main_reflect_to34610 {r : ℝ} (hr : r ∈ Set.Icc 328 346.1) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.00027 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 346.1) (j := 9) (n := 27) (lo := 5) (hi := 5.847)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 11.694 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

end PseudoPrime.PrimeTestBounds.MillerRabin
