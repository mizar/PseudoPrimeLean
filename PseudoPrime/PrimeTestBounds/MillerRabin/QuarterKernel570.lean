/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleMass
import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.Psi70Window
import PseudoPrime.Analysis.NumericalLogBounds
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Principal coefficient for the sixth-pole kernel through log 570 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The admissible sixth-pole kernel of section 31 has pole at -51/50 and shift 14/5. -/
noncomputable def quarterKernel570 : LLS.PaperStatements.MellinKernel :=
  LLS.PaperStatements.rationalPoleMellinKernel 3 (25 / 51) (7 / 5) (by norm_num only)
    (by norm_num only) (by norm_num only)

/-- The principal coefficient of the section 31 kernel exceeds 0.717289.
Evaluate its unit-cutoff moment and half-point value, then bound both exponentials. -/
theorem quarter_principal_delta_570 :
    717289 / 1000000 <
      4 * (∫ u : ℝ in (0 : ℝ)..1, (quarterKernel570.transform u).re / Real.sqrt u) -
        (quarterKernel570.function (1 / 2)).re := by
  rw [quarterKernel570, LLS.PaperStatements.rationalPole_half_value,
    LLS.PaperStatements.rationalPole_cutoff_moment _ _ _ _ (by norm_num only)]
  norm_num only [Nat.reduceMul, Nat.reduceSub, Nat.reduceAdd, Finset.sum_range_succ,
    Finset.sum_range_zero, Nat.choose_zero_right, Nat.choose_self, Nat.choose_one_right, Nat.choose,
    Nat.factorial, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (357 / 125 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  have hb :=
    Analysis.exp_le_taylor_add_two_next (x := (7 / 5 : ℝ)) (n := 20) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hi := one_div_le_one_div_of_le (Real.exp_pos _) ha
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  linarith only [hi, hb]

/-- The normalized boundary weight at the unit cutoff lies between 0.09104 and 0.09105. -/
theorem quarter_unit_weight_570 :
    9104 / 100000 < (quarterKernel570.transform 1).re ∧
      (quarterKernel570.transform 1).re < 9105 / 100000 := by
  rw [quarterKernel570, LLS.PaperStatements.rationalPole_transform _ _ _ _ zero_lt_one,
    Complex.ofReal_re]
  norm_num only [Analysis.rationalPoleProfile, Real.log_one, sub_zero, Nat.factorial, ite_true,
    and_self, zero_lt_one]
  rw [Real.exp_neg, ← one_div]
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (357 / 125 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 357 / 125) 20
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hl := one_div_le_one_div_of_le (Real.exp_pos _) ha
  have hh := one_div_le_one_div_of_le (by norm_num only) hb
  constructor <;> linarith only [hl, hh]

/-- At radii from 278 to 285 the normalized psi boundary exceeds -0.1191.
The one-third finite psi estimate applies on the whole square-radius interval. -/
theorem quarter_psi_boundary_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    -(1191 / 10000) <
      4 * (quarterKernel570.transform 1).re *
          (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) /
        r := by
  have hr : 0 < r := by linarith only [hl]
  have hp :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_third_window (x := r ^ 2)
      ((by norm_num only : (71539 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ hr.le hu 2).trans_lt (by norm_num only))
  rw [Real.sqrt_sq hr.le] at hp
  obtain ⟨hw, hW⟩ := quarter_unit_weight_570
  have hw0 : 0 ≤ (quarterKernel570.transform 1).re := by linarith only [hw]
  have hpsi := mul_le_mul_of_nonneg_left hp hw0
  have hlog := mul_le_mul hw.le Analysis.log_two_mul_pi_gt.le (by norm_num only) hw0
  apply (lt_div_iff₀ hr).mpr
  nlinarith only [hpsi, hlog, mul_lt_mul_of_pos_right hW hr, hu]

/-- The main term together with the psi boundary exceeds 0.717289 r - 0.1191
throughout the radius interval used for log 556 to 570. -/
theorem quarter_principal_boundary_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    717289 / 1000000 * r - 1191 / 10000 <
      r *
          (4 * (∫ u : ℝ in (0 : ℝ)..1, (quarterKernel570.transform u).re / Real.sqrt u) -
            (quarterKernel570.function (1 / 2)).re) +
        4 * (quarterKernel570.transform 1).re *
            (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) /
          r := by
  have hm := mul_lt_mul_of_pos_right quarter_principal_delta_570 (by linarith only [hl] : 0 < r)
  linarith only [hm, quarter_psi_boundary_570 hl hu]

private theorem fifth_profile_antitone :
    AntitoneOn (fun t : ℝ ↦ t ^ 5 * Real.exp (-t)) (Set.Ici 5) := by
  have hd (t : ℝ) :=
    ((hasDerivAt_pow 5 t).mul (Real.hasDerivAt_exp _ |>.comp t (hasDerivAt_id t).neg))
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact fun t _ ↦ (hd t).continuousAt.continuousWithinAt
  · exact fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht' : 5 ≤ t := interior_subset ht
    change deriv ((fun x : ℝ ↦ x ^ 5) * Real.exp ∘ (-id)) t ≤ 0
    rw [(hd t).deriv]
    change 5 * t ^ 4 * Real.exp (-t) + t ^ 5 * (Real.exp (-t) * -1) ≤ 0
    have h :=
      mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht')
        (mul_nonneg (by positivity : 0 ≤ t ^ 4) (Real.exp_pos (-t)).le)
    convert h using 1; ring

/-- At square cutoffs with radius from 278 through 285 the reflected unit weight
is between 0.0029 and 0.003. Monotonicity reduces both inequalities to rational endpoints. -/
theorem quarter_reflected_weight_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    29 / 10000 < (quarterKernel570.transform (1 / r ^ 2)).re ∧
      (quarterKernel570.transform (1 / r ^ 2)).re < 3 / 1000 := by
  have hr : 0 < r := by linarith only [hl]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 278) (j := 8) (n := 32) (lo := 56275 / 10000)
        (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 285) (j := 8) (n := 32) (lo := 5) (hi :=
        565249 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo hhi
  have hL := hlo.trans (Real.log_le_log (by norm_num only) hl)
  have hU := (Real.log_le_log hr hu).trans hhi
  let t := (14 / 5 + 2 * Real.log r) / (50 / 51)
  have htl : (14336 / 1000 : ℝ) ≤ t := by
    dsimp only [t]; linarith only [hL]
  have htu : t ≤ (143871 / 10000 : ℝ) := by
    dsimp only [t]; linarith only [hU]
  have h1 :=
    fifth_profile_antitone (show 5 ≤ (14336 / 1000 : ℝ) by norm_num only)
      (show 5 ≤ t by linarith only [htl]) htl
  have h2 :=
    fifth_profile_antitone (show 5 ≤ t by linarith only [htl])
      (show 5 ≤ (143871 / 10000 : ℝ) by norm_num only) htu
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (143871 / 10000 : ℝ)) (n := 48) (by norm_num only)
      (by norm_num only)
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 14336 / 1000) 45
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hA := one_div_le_one_div_of_le (Real.exp_pos _) ha
  have hB := one_div_le_one_div_of_le (by norm_num only) hb
  rw [one_div (Real.exp _), ← Real.exp_neg] at hA hB
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re]
  have he : Real.log (1 / r ^ 2) = -(2 * Real.log r) := by
    rw [one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  rw [Analysis.rationalPoleProfile,
    ite_eq_left
      ⟨one_div_pos.mpr (sq_pos_of_pos hr), by
        rw [he]; linarith only [hL]⟩,
    he]
  rw [show (2 * (7 / 5 : ℝ) - -(2 * Real.log r)) / (2 * (25 / 51)) = t by
      dsimp only [t]; ring]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat]
  change _ < t ^ 5 * Real.exp (-t) / 120 ∧ t ^ 5 * Real.exp (-t) / 120 < _
  constructor <;> linarith only [h1, h2, hA, hB]

/-- Including the reflected logarithmic boundary costs less than 0.135651 in total
relative to the certified linear main term at every radius from 278 to 285. -/
theorem quarter_main_reflected_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    717289 / 1000000 * r - 135651 / 1000000 <
      r *
            (4 * (∫ u : ℝ in (0 : ℝ)..1, (quarterKernel570.transform u).re / Real.sqrt u) -
              (quarterKernel570.function (1 / 2)).re) +
          4 * (quarterKernel570.transform 1).re *
              (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) /
            r -
        3 * Real.log (2 * Real.pi) * (quarterKernel570.transform (1 / r ^ 2)).re := by
  obtain ⟨hb, hB⟩ := quarter_reflected_weight_570 hl hu
  have h :=
    mul_le_mul Analysis.log_two_mul_pi_lt.le hB.le (by linarith only [hb]) (by norm_num only)
  linarith only [quarter_principal_boundary_570 hl hu, h]

/-- At radii from 278 to 285 the normalized psi boundary exceeds -0.1191.
The one-third finite psi estimate applies on the whole square-radius interval. -/
theorem quarter_psi_boundary_574 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 287) :
    -(1191 / 10000) <
      4 * (quarterKernel570.transform 1).re *
          (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) /
        r := by
  have hr : 0 < r := by linarith only [hl]
  have hp :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_third_window_82539 (x := r ^ 2)
      ((by norm_num only : (71539 : ℝ) ≤ 278 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ hr.le hu 2).trans_lt (by norm_num only))
  rw [Real.sqrt_sq hr.le] at hp
  obtain ⟨hw, hW⟩ := quarter_unit_weight_570
  have hw0 : 0 ≤ (quarterKernel570.transform 1).re := by linarith only [hw]
  have hpsi := mul_le_mul_of_nonneg_left hp hw0
  have hlog := mul_le_mul hw.le Analysis.log_two_mul_pi_gt.le (by norm_num only) hw0
  apply (lt_div_iff₀ hr).mpr
  nlinarith only [hpsi, hlog, mul_lt_mul_of_pos_right hW hr, hu]

/-- At square cutoffs with radius from 278 through 287 the reflected unit weight
is between 0.002873 and 0.003. Monotonicity reduces both inequalities to rational endpoints. -/
theorem quarter_reflected_weight_574 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 287) :
    2873 / 1000000 < (quarterKernel570.transform (1 / r ^ 2)).re ∧
      (quarterKernel570.transform (1 / r ^ 2)).re < 3 / 1000 := by
  have hr : 0 < r := by linarith only [hl]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 278) (j := 8) (n := 32) (lo := 56275 / 10000)
        (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 287) (j := 8) (n := 32) (lo := 5) (hi :=
        565950 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo hhi
  have hL := hlo.trans (Real.log_le_log (by norm_num only) hl)
  have hU := (Real.log_le_log hr hu).trans hhi
  let t := (14 / 5 + 2 * Real.log r) / (50 / 51)
  have htl : (14336 / 1000 : ℝ) ≤ t := by
    dsimp only [t]; linarith only [hL]
  have htu : t ≤ (1440138 / 100000 : ℝ) := by
    dsimp only [t]; linarith only [hU]
  have h1 :=
    fifth_profile_antitone (show 5 ≤ (14336 / 1000 : ℝ) by norm_num only)
      (show 5 ≤ t by linarith only [htl]) htl
  have h2 :=
    fifth_profile_antitone (show 5 ≤ t by linarith only [htl])
      (show 5 ≤ (1440138 / 100000 : ℝ) by norm_num only) htu
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (1440138 / 100000 : ℝ)) (n := 48) (by norm_num only)
      (by norm_num only)
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 14336 / 1000) 45
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hA := one_div_le_one_div_of_le (Real.exp_pos _) ha
  have hB := one_div_le_one_div_of_le (by norm_num only) hb
  rw [one_div (Real.exp _), ← Real.exp_neg] at hA hB
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re]
  have he : Real.log (1 / r ^ 2) = -(2 * Real.log r) := by
    rw [one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  rw [Analysis.rationalPoleProfile,
    ite_eq_left
      ⟨one_div_pos.mpr (sq_pos_of_pos hr), by
        rw [he]; linarith only [hL]⟩,
    he]
  rw [show (2 * (7 / 5 : ℝ) - -(2 * Real.log r)) / (2 * (25 / 51)) = t by
      dsimp only [t]; ring]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat]
  change _ < t ^ 5 * Real.exp (-t) / 120 ∧ t ^ 5 * Real.exp (-t) / 120 < _
  constructor <;> linarith only [h1, h2, hA, hB]

/-- Up to radius 288 the reflected kernel weight lies strictly between 0.002860 and 0.003.
Antitonicity reduces the two bounds to certified endpoint exponential estimates. -/
theorem quarter_reflected_weight_576 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 288) :
    2860 / 1000000 < (quarterKernel570.transform (1 / r ^ 2)).re ∧
      (quarterKernel570.transform (1 / r ^ 2)).re < 3 / 1000 := by
  have hr : 0 < r := by linarith only [hl]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 278) (j := 8) (n := 32) (lo := 56275 / 10000)
        (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 288) (j := 8) (n := 32) (lo := 5) (hi :=
        566300 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo hhi
  have hL := hlo.trans (Real.log_le_log (by norm_num only) hl)
  have hU := (Real.log_le_log hr hu).trans hhi
  let t := (14 / 5 + 2 * Real.log r) / (50 / 51)
  have htl : (14336 / 1000 : ℝ) ≤ t := by
    dsimp only [t]; linarith only [hL]
  have htu : t ≤ (1440852 / 100000 : ℝ) := by
    dsimp only [t]; linarith only [hU]
  have h1 :=
    fifth_profile_antitone (show 5 ≤ (14336 / 1000 : ℝ) by norm_num only)
      (show 5 ≤ t by linarith only [htl]) htl
  have h2 :=
    fifth_profile_antitone (show 5 ≤ t by linarith only [htl])
      (show 5 ≤ (1440852 / 100000 : ℝ) by norm_num only) htu
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (1440852 / 100000 : ℝ)) (n := 48) (by norm_num only)
      (by norm_num only)
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 14336 / 1000) 45
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hA := one_div_le_one_div_of_le (Real.exp_pos _) ha
  have hB := one_div_le_one_div_of_le (by norm_num only) hb
  rw [one_div (Real.exp _), ← Real.exp_neg] at hA hB
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re]
  have he : Real.log (1 / r ^ 2) = -(2 * Real.log r) := by
    rw [one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  rw [Analysis.rationalPoleProfile,
    ite_eq_left
      ⟨one_div_pos.mpr (sq_pos_of_pos hr), by
        rw [he]; linarith only [hL]⟩,
    he]
  rw [show (2 * (7 / 5 : ℝ) - -(2 * Real.log r)) / (2 * (25 / 51)) = t by
      dsimp only [t]; ring]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat]
  change _ < t ^ 5 * Real.exp (-t) / 120 ∧ t ^ 5 * Real.exp (-t) / 120 < _
  constructor <;> linarith only [h1, h2, hA, hB]

/-- From radius 278 to 292 the reflected weight lies between 0.00280 and 0.003. -/
theorem quarter_reflected_weight_584 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 292) :
    2800 / 1000000 < (quarterKernel570.transform (1 / r ^ 2)).re ∧
      (quarterKernel570.transform (1 / r ^ 2)).re < 3 / 1000 := by
  have hr : 0 < r := by linarith only [hl]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 278) (j := 8) (n := 32) (lo := 56275 / 10000)
        (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 32) (lo := 5) (hi :=
        567680 / 100000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo hhi
  have hL := hlo.trans (Real.log_le_log (by norm_num only) hl)
  have hU := (Real.log_le_log hr hu).trans hhi
  let t := (14 / 5 + 2 * Real.log r) / (50 / 51)
  have htl : (14336 / 1000 : ℝ) ≤ t := by
    dsimp only [t]; linarith only [hL]
  have htu : t ≤ (1443670 / 100000 : ℝ) := by
    dsimp only [t]; linarith only [hU]
  have h1 :=
    fifth_profile_antitone (show 5 ≤ (14336 / 1000 : ℝ) by norm_num only)
      (show 5 ≤ t by linarith only [htl]) htl
  have h2 :=
    fifth_profile_antitone (show 5 ≤ t by linarith only [htl])
      (show 5 ≤ (1443670 / 100000 : ℝ) by norm_num only) htu
  have ha :=
    Analysis.exp_le_taylor_add_two_next (x := (1443670 / 100000 : ℝ)) (n := 48) (by norm_num only)
      (by norm_num only)
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 14336 / 1000) 45
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ha hb
  have hA := one_div_le_one_div_of_le (Real.exp_pos _) ha
  have hB := one_div_le_one_div_of_le (by norm_num only) hb
  rw [one_div (Real.exp _), ← Real.exp_neg] at hA hB
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re]
  have he : Real.log (1 / r ^ 2) = -(2 * Real.log r) := by
    rw [one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  rw [Analysis.rationalPoleProfile,
    ite_eq_left
      ⟨one_div_pos.mpr (sq_pos_of_pos hr), by
        rw [he]; linarith only [hL]⟩,
    he]
  rw [show (2 * (7 / 5 : ℝ) - -(2 * Real.log r)) / (2 * (25 / 51)) = t by
      dsimp only [t]; ring]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat]
  change _ < t ^ 5 * Real.exp (-t) / 120 ∧ t ^ 5 * Real.exp (-t) / 120 < _
  constructor <;> linarith only [h1, h2, hA, hB]

/-- For radii at least 288, the decreasing fifth-power profile and a Taylor
lower bound for the exponential give a reflected weight below 0.002861. -/
theorem reflected_weight_upper_of_288 {r : ℝ} (hl : 288 ≤ r) :
    (quarterKernel570.transform (1 / r ^ 2)).re < 2861 / 1000000 := by
  have hr : 0 < r := by linarith only [hl]
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 288) (j := 8) (n := 32) (lo := 566295 / 100000)
        (hi := 6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlo
  have hL := hlo.trans (Real.log_le_log (by norm_num only) hl)
  let t := (14 / 5 + 2 * Real.log r) / (50 / 51)
  have htl : (144084 / 10000 : ℝ) ≤ t := by
    dsimp only [t]; linarith only [hL]
  have h1 :=
    fifth_profile_antitone (show 5 ≤ (144084 / 10000 : ℝ) by norm_num only)
      (show 5 ≤ t by linarith only [htl]) htl
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 144084 / 10000) 45
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hb
  have hB := one_div_le_one_div_of_le (by norm_num only) hb
  rw [one_div (Real.exp _), ← Real.exp_neg] at hB
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re]
  have he : Real.log (1 / r ^ 2) = -(2 * Real.log r) := by
    rw [one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  rw [Analysis.rationalPoleProfile,
    ite_eq_left
      ⟨one_div_pos.mpr (sq_pos_of_pos hr), by
        rw [he]; linarith only [hL]⟩,
    he]
  rw [show (2 * (7 / 5 : ℝ) - -(2 * Real.log r)) / (2 * (25 / 51)) = t by
      dsimp only [t]; ring]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat]
  change t ^ 5 * Real.exp (-t) / 120 < _
  linarith only [h1, hB]

end PseudoPrime.PrimeTestBounds.MillerRabin
