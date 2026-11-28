/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.Joint.PsiTenth574

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInnerError570
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.Analysis.NumericalLogBounds
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! # Main integrals for the section 31 principal comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem scale_weight {X t : ℝ} (hx : 0 < X) (ht : 0 < t) (hb : t ≤ X * Real.exp (14 / 5)) :
    quarterWeight570 X t =
      (1 / Real.sqrt X) * ((quarterKernel570.transform (t / X)).re / Real.sqrt (t / X)) := by
  have hp := div_pos ht hx
  have hlog := (Real.log_le_iff_le_exp hp).mpr ((div_le_iff₀ hx).mpr ((mul_comm _ X) ▸ hb))
  rw [quarterKernel570, LLS.PaperStatements.rationalPole_transform _ _ _ _ hp, Complex.ofReal_re,
    Analysis.rationalPoleProfile, ite_eq_left ⟨hp, by linarith only [hlog]⟩, Real.sqrt_div ht.le]
  norm_num only [quarterWeight570, Nat.reduceMul, Nat.reduceSub, Nat.factorial, Nat.cast_ofNat]
  field_simp [(Real.sqrt_pos.mpr hx).ne', (Real.sqrt_pos.mpr ht).ne']

/-- At its own positive cutoff, the weight is the unit transform divided
by the radius. This normalizes the lower Chebyshev boundary term. -/
theorem quarter_cutoff_weight_570 {X : ℝ} (hx : 0 < X) :
    quarterWeight570 X X = (quarterKernel570.transform 1).re / Real.sqrt X := by
  have hw := scale_weight hx hx (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)))
  rw [hw, div_self hx.ne', Real.sqrt_one, div_one]
  ring

/-- On a positive supported interval, rescaling the weight gives sqrt X times
the normalized Mellin weight integrated on the divided interval. -/
theorem quarter_scale_integral_570 {X a b : ℝ} (hx : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ X * Real.exp (14 / 5)) :
    (∫ t in a..b, quarterWeight570 X t) =
      Real.sqrt X * ∫ u in a / X..b / X, (quarterKernel570.transform u).re / Real.sqrt u := by
  let K := fun u ↦ (quarterKernel570.transform u).re / Real.sqrt u
  have he : (∫ t in a..b, quarterWeight570 X t) = ∫ t in a..b, (1 / Real.sqrt X) * K (t / X) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact scale_weight hx (ha.trans_le ht.1) (ht.2.trans hb)
  rw [he, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_div K hx.ne',
    smul_eq_mul]
  change _ = Real.sqrt X * ∫ u in a / X..b / X, K u
  rw [← mul_assoc]
  congr 1
  field_simp [(Real.sqrt_pos.mpr hx).ne']
  nlinarith only [Real.sq_sqrt hx.le]

/-- Any positive supported subinterval contributes at most the full Mellin mass
at one half, multiplied by the square root of the scale. -/
theorem quarter_integral_le_mass_570 {X a b : ℝ} (hx : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ X * Real.exp (14 / 5)) :
    (∫ t in a..b, quarterWeight570 X t) ≤ Real.sqrt X * (quarterKernel570.function (1 / 2)).re := by
  rw [quarter_scale_integral_570 hx ha hab hb]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg X)
  rw [intervalIntegral.integral_of_le (div_le_div_of_nonneg_right hab hx.le), ←
    LLS.PaperStatements.MellinKernel.integral_weight_Ioi_eq]
  apply
    MeasureTheory.setIntegral_mono_set
      (LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel570)
  · exact
      (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
        (fun u hu ↦ div_nonneg (quarterKernel570.mellin_nonneg u hu) (Real.sqrt_nonneg u))
  · exact MeasureTheory.ae_of_all _ (fun u hu ↦ (div_pos ha hx).trans hu.1)

/-- Below the unit endpoint the logarithmic derivative of the section 31 weight
is nonnegative whenever the scale is at least 278 squared. -/
theorem quarter_small_deriv_570 {X t : ℝ} (hx : 77284 ≤ X) (ht : 0 < t) (hu : t ≤ 1) :
    0 ≤ deriv (quarterWeight570 X) t := by
  have hx0 : 0 < X := by linarith only [hx]
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 77284) (j := 16) (n := 32) (lo := 56 / 5) (hi :=
        12) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hL := hlog.trans (Real.log_le_log (by norm_num only) hx)
  have hT := Real.log_nonpos ht.le hu
  have hv : 14 ≤ quarterCoord570 X t := by
    unfold quarterCoord570
    rw [Real.log_div ht.ne' hx0.ne']
    apply (le_div_iff₀ (by norm_num only)).mpr
    linarith only [hL, hT]
  apply (mul_nonneg_iff_of_pos_left ht).mp
  rw [quarter_log_deriv_570 hx0 ht]
  apply
    mul_nonneg
      (by
        unfold quarterFactor570; positivity)
  have hpos : 0 ≤ 13 / 25 * quarterCoord570 X t - 5 * (51 / 50) := by linarith only [hv]
  nlinarith only [mul_nonneg (by positivity : 0 ≤ quarterCoord570 X t ^ 4) hpos]

/-- For scales at least 278 squared, the weight increases up to one.
This bounds the omitted initial segment by its endpoint value. -/
theorem quarter_small_weight_mono_570 {X : ℝ} (hx : 77284 ≤ X) :
    MonotoneOn (quarterWeight570 X) (Set.Ioc 0 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ioc _ _)
  · intro t ht
    have ht0 := ht.1
    have hx0 : 0 < X := by linarith only [hx]
    apply ContinuousAt.continuousWithinAt
    unfold quarterWeight570
    fun_prop (disch := positivity)
  · intro t ht
    obtain ⟨ht0, ht1⟩ := interior_subset ht
    have hx0 : 0 < X := by linarith only [hx]
    apply DifferentiableAt.differentiableWithinAt
    have hs := (Real.hasDerivAt_sqrt (show t ≠ 0 from ne_of_gt ht0)).differentiableAt
    unfold quarterWeight570
    dsimp only
    fun_prop (disch := positivity)
  · intro t ht
    obtain ⟨ht0, ht1⟩ := interior_subset ht
    exact quarter_small_deriv_570 hx ht0 ht1

/-- At scales at least 278 squared, the missing normalized integral below 1/X,
after rescaling, is bounded by the physical weight at one. -/
theorem quarter_missing_mass_570 {X : ℝ} (hx : 77284 ≤ X) :
    Real.sqrt X * (∫ u in (0 : ℝ)..1 / X, (quarterKernel570.transform u).re / Real.sqrt u) ≤
      quarterWeight570 X 1 := by
  have hx0 : 0 < X := by linarith only [hx]
  have hs := Real.sqrt_pos.mpr hx0
  have hB : 1 ≤ X * Real.exp (14 / 5) := by
    have he := Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5)
    linarith only [hx, mul_le_mul_of_nonneg_left he hx0.le]
  let K := fun u ↦ (quarterKernel570.transform u).re / Real.sqrt u
  have hi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (one_div_pos.mpr hx0).le).mpr
      ((LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel570).mono_set
        (fun _ h ↦ h.1))
  have hm :
    (∫ u in (0 : ℝ)..1 / X, K u) ≤ ∫ _ in (0 : ℝ)..1 / X, Real.sqrt X * quarterWeight570 X 1 := by
    apply
      intervalIntegral.integral_mono_on_of_le_Ioo (one_div_pos.mpr hx0).le hi
        intervalIntegrable_const
    intro u hu
    have ht := mul_pos hu.1 hx0
    have hu1 := ((lt_div_iff₀ hx0).mp hu.2).le
    have hw := scale_weight hx0 ht (hu1.trans hB)
    rw [mul_div_cancel_right₀ _ hx0.ne'] at hw
    have hm := quarter_small_weight_mono_570 hx ⟨ht, hu1⟩ ⟨zero_lt_one, le_rfl⟩ hu1
    change _ = (1 / Real.sqrt X) * K u at hw
    rw [hw, one_div, inv_mul_eq_div] at hm
    exact (div_le_iff₀ hs).mp hm |>.trans_eq (mul_comm _ _)
  rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul] at hm
  have hc :
    Real.sqrt X * (1 / X * (Real.sqrt X * quarterWeight570 X 1)) = quarterWeight570 X 1 := by
    field_simp [hx0.ne']
    nlinarith only [congrArg (fun z : ℝ ↦ z * quarterWeight570 X 1) (Real.sq_sqrt hx0.le)]
  exact (mul_le_mul_of_nonneg_left hm hs.le).trans_eq hc

/-- On sections 31 and 62 radii the omitted principal mass is strictly below 0.003. -/
theorem quarter_missing_mass_lt_574 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 287) :
    r * (∫ u in (0 : ℝ)..1 / r ^ 2, (quarterKernel570.transform u).re / Real.sqrt u) <
      3 / 1000 := by
  have hr : 0 < r := by linarith only [hl]
  have hx : (77284 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (77284 : ℝ) = 278 ^ 2) ▸ pow_le_pow_left₀ (by norm_num only) hl 2
  have hm := quarter_missing_mass_570 hx
  rw [Real.sqrt_sq hr.le] at hm
  apply hm.trans_lt
  have he := Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5)
  have hb : 1 ≤ r ^ 2 * Real.exp (14 / 5) := by
    linarith only [hx, mul_le_mul_of_nonneg_left he (sq_nonneg r)]
  rw [scale_weight (sq_pos_of_pos hr) zero_lt_one hb, Real.sqrt_div zero_le_one, Real.sqrt_one,
    Real.sqrt_sq hr.le, div_div_eq_mul_div, div_one, one_div, ← mul_assoc]
  convert (quarter_reflected_weight_574 hl hu).2 using 1
  field_simp [hr.ne']

/-- The two physical principal integrals contribute more than 0.717289 times
the radius minus 0.012 on the sections 31 and 62 interval. -/
theorem quarter_integral_difference_574 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 287) :
    let X := r ^ 2
    717289 / 1000000 * r - 12 / 1000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
        ∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hx0 := zero_lt_one.trans_le hx
  have hb : X ≤ X * Real.exp (14 / 5) := by
    exact le_mul_of_one_le_right hx0.le (Real.one_le_exp (by norm_num only))
  let K := fun u ↦ (quarterKernel570.transform u).re / Real.sqrt u
  have hi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable K MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel570).mono_set
        (fun _ h ↦ ha.trans_lt h.1))
  have hq := (one_div_pos.mpr hx0).le
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hq)
      (hi hq ((div_le_one hx0).mpr hx))
  have hshort := quarter_scale_integral_570 hx0 zero_lt_one hx hb
  have hfull := quarter_integral_le_mass_570 hx0 zero_lt_one (hx.trans hb) le_rfl
  have hs : Real.sqrt X = r := Real.sqrt_sq hr.le
  rw [hs, div_self hx0.ne'] at hshort
  rw [hs] at hfull
  have hm := quarter_missing_mass_lt_574 hl hu
  have hd := mul_lt_mul_of_pos_right quarter_principal_delta_570 hr
  change _ = ∫ u in (0 : ℝ)..1, K u at hsplit
  change _ = r * ∫ u in 1 / X..1, K u at hshort
  change r * (∫ u in (0 : ℝ)..1 / X, K u) < _ at hm
  change _ < (4 * (∫ u in (0 : ℝ)..1, K u) - _) * r at hd
  nlinarith only [hshort, hfull, hm, hd, congrArg (fun z : ℝ ↦ r * z) hsplit]

/-- The principal integrals and the actual psi cutoff term together exceed
0.717289 times the radius minus 0.1311 for radii between 278 and 287. -/
theorem quarter_integral_boundary_574 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 287) :
    let X := r ^ 2
    717289 / 1000000 * r - 1311 / 10000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
          (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t) +
        4 * quarterWeight570 X X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 0 < X := sq_pos_of_pos hr
  have hb := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hw := scale_weight hx hx hb
  rw [div_self hx.ne', Real.sqrt_one, div_one, show Real.sqrt X = r from Real.sqrt_sq hr.le] at hw
  rw [hw]
  have hp := quarter_psi_boundary_574 hl hu
  change _ < 4 * _ * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) / r at hp
  have hi := quarter_integral_difference_574 hl hu
  change _ < 4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) - _ at hi
  simp only [div_eq_mul_inv] at hp
  rw [one_div]
  dsimp only [X] at hi hp ⊢
  linarith only [hp, hi]

/-- Under RH the principal difference exceeds 0.717289 r minus 0.21
on the entire radius interval used in sections 31 and 62. -/
theorem quarter_principal_lower_574 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 287)
    (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    717289 / 1000000 * r - 21 / 100 < 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X S
  have hr : 0 < r := by linarith only [hl]
  have hx : 0 < X := sq_pos_of_pos hr
  have hx1 : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hb := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hw := scale_weight hx zero_lt_one (hx1.trans hb)
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one, show Real.sqrt X = r from Real.sqrt_sq hr.le] at hw
  have he : quarterWeight570 X 1 = (quarterKernel570.transform (1 / X)).re := by
    rw [hw]
    field_simp [hr.ne']
  obtain ⟨hwlo, hwhi⟩ := quarter_reflected_weight_574 hl hu
  change _ < (quarterKernel570.transform (1 / X)).re at hwlo
  change (quarterKernel570.transform (1 / X)).re < _ at hwhi
  rw [← he] at hwlo hwhi
  have hw0 : 0 ≤ quarterWeight570 X 1 := by linarith only [hwlo]
  have hd := quarter_log_deriv_570 hx zero_lt_one
  rw [one_mul] at hd
  have hf : 0 ≤ quarterFactor570 X 1 := by
    unfold quarterFactor570; positivity
  have hpoly : quarterWeight570 X 1 = quarterFactor570 X 1 * quarterCoord570 X 1 ^ 5 := by
    unfold quarterWeight570 quarterFactor570 quarterCoord570
    ring
  have hdle : deriv (quarterWeight570 X) 1 ≤ 13 / 25 * quarterWeight570 X 1 := by
    rw [hd, hpoly]
    nlinarith only [mul_nonneg hf (by positivity : 0 ≤ quarterCoord570 X 1 ^ 4)]
  have hc := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hw0
  have hi := quarter_integral_boundary_574 hl hu
  have hp := quarter_principal_integrals_570 hl hRH
  dsimp only at hi hp
  dsimp only [X, S] at hc hdle hwhi ⊢
  linarith only [hi, hp, hc, hdle, hwhi]

/-- On section 31 radii the omitted principal mass is strictly below 0.003. -/
theorem quarter_missing_mass_lt_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    r * (∫ u in (0 : ℝ)..1 / r ^ 2, (quarterKernel570.transform u).re / Real.sqrt u) <
      3 / 1000 := by
  exact quarter_missing_mass_lt_574 hl (hu.trans (by norm_num only))

/-- The two physical principal integrals contribute more than 0.717289 times
the radius minus 0.012 on the section 31 interval. -/
theorem quarter_integral_difference_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    let X := r ^ 2
    717289 / 1000000 * r - 12 / 1000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
        ∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t := by
  exact quarter_integral_difference_574 hl (hu.trans (by norm_num only))

/-- The principal integrals and the actual psi cutoff term together exceed
0.717289 times the radius minus 0.1311 for radii between 278 and 285. -/
theorem quarter_integral_boundary_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    let X := r ^ 2
    717289 / 1000000 * r - 1311 / 10000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
          (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t) +
        4 * quarterWeight570 X X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) := by
  exact quarter_integral_boundary_574 hl (hu.trans (by norm_num only))

/-- Under RH the principal difference exceeds 0.717289 r minus 0.21
on the entire radius interval used in section 31. -/
theorem quarter_principal_lower_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285)
    (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    717289 / 1000000 * r - 21 / 100 < 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  exact quarter_principal_lower_574 hl (hu.trans (by norm_num only)) hRH

/-- On section 62 radii the one-tenth psi estimate bounds the principal
cutoff correction below by minus 0.037. -/
private theorem psi_boundary_tenth_574 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287) :
    -(37 / 1000) <
      4 * (quarterKernel570.transform 1).re *
          (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) /
        r := by
  have hr : 0 < r := by linarith only [hl]
  have hp :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_tenth_window_574 (x := r ^ 2)
      ((by norm_num only : (81219 : ℝ) ≤ 285 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ hr.le hu 2).trans_lt (by norm_num only))
  rw [Real.sqrt_sq hr.le] at hp
  obtain ⟨hw, hW⟩ := quarter_unit_weight_570
  have hw0 : 0 ≤ (quarterKernel570.transform 1).re := by linarith only [hw]
  have hpsi := mul_le_mul_of_nonneg_left hp hw0
  apply (lt_div_iff₀ hr).mpr
  nlinarith only [hpsi, mul_lt_mul_of_pos_right hW hr, hr,
    mul_nonneg hw0 (show 0 ≤ Real.log (2 * Real.pi) by linarith only [Analysis.log_two_mul_pi_gt])]

/-- The principal integrals and the actual psi cutoff term together exceed
0.717289 times the radius minus 0.049 for radii between 285 and 287. -/
theorem integral_boundary_tenth_574 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287) :
    let X := r ^ 2
    717289 / 1000000 * r - 49 / 1000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
          (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t) +
        4 * quarterWeight570 X X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 0 < X := sq_pos_of_pos hr
  have hb := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hw := scale_weight hx hx hb
  rw [div_self hx.ne', Real.sqrt_one, div_one, show Real.sqrt X = r from Real.sqrt_sq hr.le] at hw
  rw [hw]
  have hp := psi_boundary_tenth_574 hl hu
  change _ < 4 * _ * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) / r at hp
  have hi := quarter_integral_difference_574 (by linarith only [hl]) hu
  change _ < 4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) - _ at hi
  simp only [div_eq_mul_inv] at hp
  rw [one_div]
  dsimp only [X] at hi hp ⊢
  linarith only [hp, hi]

/-- Under RH the principal difference exceeds 0.717289 r minus 0.13
on the entire radius interval used in section 62. -/
theorem principal_lower_tenth_574 {r : ℝ} (hl : 285 ≤ r) (hu : r ≤ 287) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    717289 / 1000000 * r - 13 / 100 < 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X S
  have hr : 0 < r := by linarith only [hl]
  have hx : 0 < X := sq_pos_of_pos hr
  have hx1 : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hb := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hw := scale_weight hx zero_lt_one (hx1.trans hb)
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one, show Real.sqrt X = r from Real.sqrt_sq hr.le] at hw
  have he : quarterWeight570 X 1 = (quarterKernel570.transform (1 / X)).re := by
    rw [hw]
    field_simp [hr.ne']
  obtain ⟨hwlo, hwhi⟩ := quarter_reflected_weight_574 (by linarith only [hl]) hu
  change _ < (quarterKernel570.transform (1 / X)).re at hwlo
  change (quarterKernel570.transform (1 / X)).re < _ at hwhi
  rw [← he] at hwlo hwhi
  have hw0 : 0 ≤ quarterWeight570 X 1 := by linarith only [hwlo]
  have hd := quarter_log_deriv_570 hx zero_lt_one
  rw [one_mul] at hd
  have hf : 0 ≤ quarterFactor570 X 1 := by
    unfold quarterFactor570; positivity
  have hpoly : quarterWeight570 X 1 = quarterFactor570 X 1 * quarterCoord570 X 1 ^ 5 := by
    unfold quarterWeight570 quarterFactor570 quarterCoord570
    ring
  have hdle : deriv (quarterWeight570 X) 1 ≤ 13 / 25 * quarterWeight570 X 1 := by
    rw [hd, hpoly]
    nlinarith only [mul_nonneg hf (by positivity : 0 ≤ quarterCoord570 X 1 ^ 4)]
  have hc := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hw0
  have hi := integral_boundary_tenth_574 hl hu
  have hp := quarter_principal_integrals_570 (by linarith only [hl]) hRH
  dsimp only at hi hp
  dsimp only [X, S] at hc hdle hwhi ⊢
  linarith only [hi, hp, hc, hdle, hwhi]

/-- Throughout section 86 the actual principal cutoff boundary contributes
more than 0.002322, using the certified nonnegative psi error at the squared radius. -/
theorem psi_boundary_positive_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    2322 / 1000000 <
      4 * (quarterKernel570.transform 1).re *
          (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) /
        r := by
  have hr : 0 < r := by linarith only [hl]
  have hp :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_ge_self_window_576
      ((by norm_num only : (82369 : ℝ) ≤ 287 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ hr.le hu 2).trans_lt (by norm_num only))
  have hw := quarter_unit_weight_570.1
  have hlog := Analysis.log_two_mul_pi_gt
  have hprod :=
    mul_le_mul hw.le
      (show (1837 / 1000 : ℝ) ≤ Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi) by
        linarith only [hp, hlog])
      (by norm_num only) (by linarith only [hw])
  apply (lt_div_iff₀ hr).mpr
  linarith only [hprod, hu]

/-- On section 86 the omitted principal integral is less than 0.003. -/
theorem quarter_missing_mass_lt_576 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 288) :
    r * (∫ u in (0 : ℝ)..1 / r ^ 2, (quarterKernel570.transform u).re / Real.sqrt u) <
      3 / 1000 := by
  have hr : 0 < r := by linarith only [hl]
  have hx : (77284 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (77284 : ℝ) = 278 ^ 2) ▸ pow_le_pow_left₀ (by norm_num only) hl 2
  have hm := quarter_missing_mass_570 hx
  rw [Real.sqrt_sq hr.le] at hm
  apply hm.trans_lt
  have he := Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5)
  have hb : 1 ≤ r ^ 2 * Real.exp (14 / 5) := by
    linarith only [hx, mul_le_mul_of_nonneg_left he (sq_nonneg r)]
  rw [scale_weight (sq_pos_of_pos hr) zero_lt_one hb, Real.sqrt_div zero_le_one, Real.sqrt_one,
    Real.sqrt_sq hr.le, div_div_eq_mul_div, div_one, one_div, ← mul_assoc]
  convert (quarter_reflected_weight_576 hl hu).2 using 1
  field_simp [hr.ne']

/-- The principal integral difference exceeds 0.717289r minus 0.012 through radius 288. -/
theorem quarter_integral_difference_576 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 288) :
    let X := r ^ 2
    717289 / 1000000 * r - 12 / 1000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
        ∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hx0 := zero_lt_one.trans_le hx
  have hb : X ≤ X * Real.exp (14 / 5) := by
    exact le_mul_of_one_le_right hx0.le (Real.one_le_exp (by norm_num only))
  let K := fun u ↦ (quarterKernel570.transform u).re / Real.sqrt u
  have hi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable K MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel570).mono_set
        (fun _ h ↦ ha.trans_lt h.1))
  have hq := (one_div_pos.mpr hx0).le
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hq)
      (hi hq ((div_le_one hx0).mpr hx))
  have hshort := quarter_scale_integral_570 hx0 zero_lt_one hx hb
  have hfull := quarter_integral_le_mass_570 hx0 zero_lt_one (hx.trans hb) le_rfl
  have hs : Real.sqrt X = r := Real.sqrt_sq hr.le
  rw [hs, div_self hx0.ne'] at hshort
  rw [hs] at hfull
  have hm := quarter_missing_mass_lt_576 hl hu
  have hd := mul_lt_mul_of_pos_right quarter_principal_delta_570 hr
  change _ = ∫ u in (0 : ℝ)..1, K u at hsplit
  change _ = r * ∫ u in 1 / X..1, K u at hshort
  change r * (∫ u in (0 : ℝ)..1 / X, K u) < _ at hm
  change _ < (4 * (∫ u in (0 : ℝ)..1, K u) - _) * r at hd
  nlinarith only [hshort, hfull, hm, hd, congrArg (fun z : ℝ ↦ r * z) hsplit]

/-- The positive cutoff boundary improves the lower bound for the two principal integrals. -/
theorem integral_boundary_tenth_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    let X := r ^ 2
    717289 / 1000000 * r - 9678 / 1000000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
          (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t) +
        4 * quarterWeight570 X X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 0 < X := sq_pos_of_pos hr
  have hb := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hw := scale_weight hx hx hb
  rw [div_self hx.ne', Real.sqrt_one, div_one, show Real.sqrt X = r from Real.sqrt_sq hr.le] at hw
  rw [hw]
  have hp := psi_boundary_positive_576 hl hu
  change _ < 4 * _ * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) / r at hp
  have hi := quarter_integral_difference_576 (by linarith only [hl]) hu
  change _ < 4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) - _ at hi
  simp only [div_eq_mul_inv] at hp
  rw [one_div]
  dsimp only [X] at hi hp ⊢
  linarith only [hp, hi]

/-- Under RH the fourfold principal prefix minus the complete sum is strictly above
0.717289r minus 0.089 throughout the section 86 interval. -/
theorem principal_lower_tenth_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    717289 / 1000000 * r - 89 / 1000 < 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X S
  have hr : 0 < r := by linarith only [hl]
  have hx : 0 < X := sq_pos_of_pos hr
  have hx1 : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hb := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hw := scale_weight hx zero_lt_one (hx1.trans hb)
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one, show Real.sqrt X = r from Real.sqrt_sq hr.le] at hw
  have he : quarterWeight570 X 1 = (quarterKernel570.transform (1 / X)).re := by
    rw [hw]
    field_simp [hr.ne']
  obtain ⟨hwlo, hwhi⟩ := quarter_reflected_weight_576 (by linarith only [hl]) hu
  change _ < (quarterKernel570.transform (1 / X)).re at hwlo
  change (quarterKernel570.transform (1 / X)).re < _ at hwhi
  rw [← he] at hwlo hwhi
  have hw0 : 0 ≤ quarterWeight570 X 1 := by linarith only [hwlo]
  have hd := quarter_log_deriv_570 hx zero_lt_one
  rw [one_mul] at hd
  have hf : 0 ≤ quarterFactor570 X 1 := by
    unfold quarterFactor570; positivity
  have hpoly : quarterWeight570 X 1 = quarterFactor570 X 1 * quarterCoord570 X 1 ^ 5 := by
    unfold quarterWeight570 quarterFactor570 quarterCoord570
    ring
  have hdle : deriv (quarterWeight570 X) 1 ≤ 13 / 25 * quarterWeight570 X 1 := by
    rw [hd, hpoly]
    nlinarith only [mul_nonneg hf (by positivity : 0 ≤ quarterCoord570 X 1 ^ 4)]
  have hc := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hw0
  have hi := integral_boundary_tenth_576 hl hu
  have hp := quarter_principal_integrals_570 (by linarith only [hl]) hRH
  dsimp only at hi hp
  dsimp only [X, S] at hc hdle hwhi ⊢
  linarith only [hi, hp, hc, hdle, hwhi]

/-- The principal psi cutoff boundary on the second section 94 interval
is greater than -0.0415, including both squared-radius endpoints. -/
theorem psi_boundary_lower_584 {r : ℝ} (hl : 288 ≤ r) (hu : r ≤ 292) :
    -(415 / 10000) <
      4 * (quarterKernel570.transform 1).re *
          (Chebyshev.psi (r ^ 2) - r ^ 2 + Real.log (2 * Real.pi)) /
        r := by
  have hr : 0 < r := by linarith only [hl]
  have hp :=
    AnalyticNumberTheory.Cert.Chebyshev.Joint.psi_lower_window_584
      ((by norm_num only : (82369 : ℝ) ≤ 288 ^ 2).trans (pow_le_pow_left₀ (by norm_num only) hl 2))
      ((pow_le_pow_left₀ hr.le hu 2).trans_lt (by norm_num only))
  rw [Real.sqrt_sq hr.le] at hp
  obtain ⟨hw, hW⟩ := quarter_unit_weight_570
  have hψ :=
    mul_le_mul_of_nonneg_left hp (show 0 ≤ (quarterKernel570.transform 1).re by linarith only [hw])
  have hlog :=
    mul_le_mul hw.le Analysis.log_two_mul_pi_gt.le (by norm_num only) (by linarith only [hw])
  apply (lt_div_iff₀ hr).mpr
  linarith only [hψ, hlog, mul_lt_mul_of_pos_right hW hr, hu]

/-- The missing principal integral costs less than 0.003 up to radius 292. -/
theorem quarter_missing_mass_lt_584 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 292) :
    r * (∫ u in (0 : ℝ)..1 / r ^ 2, (quarterKernel570.transform u).re / Real.sqrt u) <
      3 / 1000 := by
  have hr : 0 < r := by linarith only [hl]
  have hx : (77284 : ℝ) ≤ r ^ 2 :=
    (by norm_num only : (77284 : ℝ) = 278 ^ 2) ▸ pow_le_pow_left₀ (by norm_num only) hl 2
  have hm := quarter_missing_mass_570 hx
  rw [Real.sqrt_sq hr.le] at hm
  apply hm.trans_lt
  have he := Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5)
  have hb : 1 ≤ r ^ 2 * Real.exp (14 / 5) := by
    linarith only [hx, mul_le_mul_of_nonneg_left he (sq_nonneg r)]
  rw [scale_weight (sq_pos_of_pos hr) zero_lt_one hb, Real.sqrt_div zero_le_one, Real.sqrt_one,
    Real.sqrt_sq hr.le, div_div_eq_mul_div, div_one, one_div, ← mul_assoc]
  convert (quarter_reflected_weight_584 hl hu).2 using 1
  field_simp [hr.ne']

/-- The principal integral difference exceeds 0.717289r minus 0.012 through radius 292. -/
theorem quarter_integral_difference_584 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 292) :
    let X := r ^ 2
    717289 / 1000000 * r - 12 / 1000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
        ∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hx0 := zero_lt_one.trans_le hx
  have hb : X ≤ X * Real.exp (14 / 5) := by
    exact le_mul_of_one_le_right hx0.le (Real.one_le_exp (by norm_num only))
  let K := fun u ↦ (quarterKernel570.transform u).re / Real.sqrt u
  have hi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable K MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel570).mono_set
        (fun _ h ↦ ha.trans_lt h.1))
  have hq := (one_div_pos.mpr hx0).le
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hq)
      (hi hq ((div_le_one hx0).mpr hx))
  have hshort := quarter_scale_integral_570 hx0 zero_lt_one hx hb
  have hfull := quarter_integral_le_mass_570 hx0 zero_lt_one (hx.trans hb) le_rfl
  have hs : Real.sqrt X = r := Real.sqrt_sq hr.le
  rw [hs, div_self hx0.ne'] at hshort
  rw [hs] at hfull
  have hm := quarter_missing_mass_lt_584 hl hu
  have hd := mul_lt_mul_of_pos_right quarter_principal_delta_570 hr
  change _ = ∫ u in (0 : ℝ)..1, K u at hsplit
  change _ = r * ∫ u in 1 / X..1, K u at hshort
  change r * (∫ u in (0 : ℝ)..1 / X, K u) < _ at hm
  change _ < (4 * (∫ u in (0 : ℝ)..1, K u) - _) * r at hd
  nlinarith only [hshort, hfull, hm, hd, congrArg (fun z : ℝ ↦ r * z) hsplit]

/-- The cutoff boundary and the two integrals contribute more than 0.717289r minus 0.0535. -/
theorem integral_boundary_tenth_584 {r : ℝ} (hl : 288 ≤ r) (hu : r ≤ 292) :
    let X := r ^ 2
    717289 / 1000000 * r - 535 / 10000 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) -
          (∫ t in (1 : ℝ)..X * Real.exp (14 / 5), quarterWeight570 X t) +
        4 * quarterWeight570 X X * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 0 < X := sq_pos_of_pos hr
  have hb := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hw := scale_weight hx hx hb
  rw [div_self hx.ne', Real.sqrt_one, div_one, show Real.sqrt X = r from Real.sqrt_sq hr.le] at hw
  rw [hw]
  have hp := psi_boundary_lower_584 hl hu
  change _ < 4 * _ * (Chebyshev.psi X - X + Real.log (2 * Real.pi)) / r at hp
  have hi := quarter_integral_difference_584 (by linarith only [hl]) hu
  change _ < 4 * (∫ t in (1 : ℝ)..X, quarterWeight570 X t) - _ at hi
  simp only [div_eq_mul_inv] at hp
  rw [one_div]
  dsimp only [X] at hi hp ⊢
  linarith only [hp, hi]

/-- Under RH the principal finite prefix comparison exceeds 0.717289r minus 0.133 on [288,292]. -/
theorem principal_lower_tenth_584 {r : ℝ} (hl : 288 ≤ r) (hu : r ≤ 292) (hRH : RiemannHypothesis) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel570.summand (1 : DirichletCharacter ℂ 1) X n).re
    717289 / 1000000 * r - 133 / 1000 < 4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X S
  have hr : 0 < r := by linarith only [hl]
  have hx : 0 < X := sq_pos_of_pos hr
  have hx1 : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hb := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only : (0 : ℝ) ≤ 14 / 5))
  have hw := scale_weight hx zero_lt_one (hx1.trans hb)
  rw [Real.sqrt_div zero_le_one, Real.sqrt_one, show Real.sqrt X = r from Real.sqrt_sq hr.le] at hw
  have he : quarterWeight570 X 1 = (quarterKernel570.transform (1 / X)).re := by
    rw [hw]
    field_simp [hr.ne']
  obtain ⟨hwlo, hwhi⟩ := quarter_reflected_weight_584 (by linarith only [hl]) hu
  change _ < (quarterKernel570.transform (1 / X)).re at hwlo
  change (quarterKernel570.transform (1 / X)).re < _ at hwhi
  rw [← he] at hwlo hwhi
  have hw0 : 0 ≤ quarterWeight570 X 1 := by linarith only [hwlo]
  have hd := quarter_log_deriv_570 hx zero_lt_one
  rw [one_mul] at hd
  have hf : 0 ≤ quarterFactor570 X 1 := by
    unfold quarterFactor570; positivity
  have hpoly : quarterWeight570 X 1 = quarterFactor570 X 1 * quarterCoord570 X 1 ^ 5 := by
    unfold quarterWeight570 quarterFactor570 quarterCoord570
    ring
  have hdle : deriv (quarterWeight570 X) 1 ≤ 13 / 25 * quarterWeight570 X 1 := by
    rw [hd, hpoly]
    nlinarith only [mul_nonneg hf (by positivity : 0 ≤ quarterCoord570 X 1 ^ 4)]
  have hc := mul_le_mul_of_nonneg_right Analysis.log_two_mul_pi_lt.le hw0
  have hi := integral_boundary_tenth_584 hl hu
  have hp := quarter_principal_integrals_570 (by linarith only [hl]) hRH
  dsimp only at hi hp
  dsimp only [X, S] at hc hdle hwhi ⊢
  linarith only [hi, hp, hc, hdle, hwhi]

end PseudoPrime.PrimeTestBounds.MillerRabin
