/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCorrection656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseRemainder656

/-! # Integrated principal weights for the section 132 kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem scale_weight {X t : ℝ} (hx : 0 < X) (ht : 0 < t) (hb : t ≤ X * Real.exp (21 / 8)) :
    quarterWeight656 X t =
      (1 / Real.sqrt X) * ((quarterKernel656.transform (t / X)).re / Real.sqrt (t / X)) := by
  have hp := div_pos ht hx
  have hlog := (Real.log_le_iff_le_exp hp).mpr ((div_le_iff₀ hx).mpr ((mul_comm _ X) ▸ hb))
  rw [quarter_transform_656 hp hlog, Real.sqrt_div ht.le]
  dsimp only [quarterWeight656]
  field_simp [(Real.sqrt_pos.mpr hx).ne', (Real.sqrt_pos.mpr ht).ne']

/-- On a positive supported interval, rescaling the weight gives sqrt X times
the normalized Mellin weight integrated on the divided interval. -/
private theorem quarter_scale_integral_656 {X a b : ℝ} (hx : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ X * Real.exp (21 / 8)) :
    (∫ t in a..b, quarterWeight656 X t) =
      Real.sqrt X * ∫ u in a / X..b / X, (quarterKernel656.transform u).re / Real.sqrt u := by
  let K := fun u ↦ (quarterKernel656.transform u).re / Real.sqrt u
  have he : (∫ t in a..b, quarterWeight656 X t) = ∫ t in a..b, (1 / Real.sqrt X) * K (t / X) := by
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
private theorem quarter_integral_le_mass_656 {X a b : ℝ} (hx : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (hb : b ≤ X * Real.exp (21 / 8)) :
    (∫ t in a..b, quarterWeight656 X t) ≤ Real.sqrt X * (quarterKernel656.function (1 / 2)).re := by
  rw [quarter_scale_integral_656 hx ha hab hb]
  apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg X)
  rw [intervalIntegral.integral_of_le (div_le_div_of_nonneg_right hab hx.le), ←
    LLS.PaperStatements.MellinKernel.integral_weight_Ioi_eq]
  apply
    MeasureTheory.setIntegral_mono_set
      (LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel656)
  · exact
      (MeasureTheory.ae_restrict_mem measurableSet_Ioi).mono
        (fun u hu ↦ div_nonneg (quarterKernel656.mellin_nonneg u hu) (Real.sqrt_nonneg u))
  · exact MeasureTheory.ae_of_all _ (fun u hu ↦ (div_pos ha hx).trans hu.1)

private theorem small_weight_decay {X t : ℝ} (hX : 0 < X) (ht : 0 < t) (hu : t ≤ 1)
    (hz : 14 ≤ 21 / 8 + Real.log X) :
    quarterWeight656 X t ≤ quarterWeight656 X 1 * t ^ (24 / 100 : ℝ) := by
  let z := 21 / 8 + Real.log X
  let y := -Real.log t
  have hz0 : 0 < z := by
    dsimp only [z]; linarith only [hz]
  have hy : 0 ≤ y := neg_nonneg.mpr (Real.log_nonpos ht.le hu)
  have hlog := Real.add_one_le_exp (y / z)
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ y / z + 1) hlog 5
  rw [← Real.exp_natCast_mul, Nat.cast_ofNat] at hp
  have h₁ : (z + y) ^ 5 ≤ z ^ 5 * Real.exp ((9 / 25) * y) := by
    have hb : 5 / z ≤ (9 / 25 : ℝ) :=
      (div_le_iff₀ hz0).mpr
        (by
          dsimp only [z]; linarith only [hz])
    have he : Real.exp (5 * (y / z)) ≤ Real.exp (9 / 25 * y) := by
      apply Real.exp_le_exp.mpr
      rw [show (5 : ℝ) * (y / z) = (5 / z) * y by ring]
      exact mul_le_mul_of_nonneg_right hb hy
    have h := mul_le_mul_of_nonneg_left (hp.trans he) (pow_nonneg hz0.le 5)
    calc
      _ = z ^ 5 * (y / z + 1) ^ 5 := by
        rw [← mul_pow]; congr 1; field_simp [hz0.ne']; ring
      _ ≤ _ := h
  have hlt : Real.log (t / X) = -y - Real.log X := by
    rw [Real.log_div ht.ne' hX.ne']
    dsimp only [y]; rw [neg_neg]
  have hlf : Real.log (1 / X) = -Real.log X := by rw [one_div, Real.log_inv]
  unfold quarterWeight656
  rw [hlt, hlf, Real.sqrt_one, div_one, one_mul, Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht,
    Real.rpow_def_of_pos ht]
  have hE :
    Real.exp (-((11 / 10) * (21 / 8 - (-y - Real.log X)))) =
      Real.exp (-(11 / 10) * z) * Real.exp (-(11 / 10) * y) := by
    rw [← Real.exp_add]
    congr 1
    dsimp only [z]
    ring
  have hZ : (11 / 10) * (21 / 8 - -Real.log X) = (11 / 10) * z := by
    dsimp only [z]; ring
  have hY : (11 / 10) * (21 / 8 - (-y - Real.log X)) = (11 / 10) * (z + y) := by
    dsimp only [z]; ring
  have hscale :
    (1 / Real.exp (Real.log t * (1 / 2))) * Real.exp (-(11 / 10) * y) * Real.exp ((9 / 25) * y) =
      Real.exp (Real.log t * (24 / 100)) := by
    rw [one_div, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add]
    congr 1
    dsimp only [y]
    ring
  dsimp only
  rw [hE, hZ, hY, mul_pow, mul_pow]
  have hh :=
    mul_le_mul_of_nonneg_left h₁
      (show
        0 ≤
          (1 / Real.exp (Real.log t * (1 / 2))) * ((11 / 10 : ℝ) ^ 5 / 120) *
            Real.exp (-(11 / 10) * z) *
            Real.exp (-(11 / 10) * y)
        by positivity)
  dsimp only [z] at hh hscale ⊢
  simp only [neg_mul] at hh hscale ⊢
  linear_combination
    hh +
      (((11 / 10 : ℝ) ^ 5 / 120) * Real.exp (-((11 / 10) * (21 / 8 + Real.log X))) *
          (21 / 8 + Real.log X) ^ 5) *
        hscale

/-- The omitted lower integral is at most 100/124 of the weight at one
when the logarithmic cutoff coordinate is at least fourteen. -/
theorem quarter_missing_mass_ratio_656 {X : ℝ} (hX : 1 ≤ X) (hz : 14 ≤ 21 / 8 + Real.log X) :
    Real.sqrt X * (∫ u in (0 : ℝ)..1 / X, (quarterKernel656.transform u).re / Real.sqrt u) ≤
      100 / 124 * quarterWeight656 X 1 := by
  have hx := zero_lt_one.trans_le hX
  let K := fun u : ℝ ↦ (quarterKernel656.transform u).re / Real.sqrt u
  let C := Real.sqrt X * quarterWeight656 X 1 * X ^ (24 / 100 : ℝ)
  have hi :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (one_div_pos.mpr hx).le).mpr
      ((LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel656).mono_set
        (fun _ h ↦ h.1))
  have hJ :
    IntervalIntegrable (fun u : ℝ ↦ C * u ^ (24 / 100 : ℝ)) MeasureTheory.volume 0 (1 / X) :=
    (Real.continuous_rpow_const (by norm_num only : (0 : ℝ) ≤ 24 / 100) |>.const_mul
        C) |>.intervalIntegrable
      _ _
  have h :=
    intervalIntegral.integral_mono_on_of_le_Ioo (one_div_pos.mpr hx).le hi hJ
      (by
        intro u hu
        have ht := mul_pos hu.1 hx
        have hu1 := ((lt_div_iff₀ hx).mp hu.2).le
        have hb : u * X ≤ X * Real.exp (21 / 8) :=
          hu1.trans (le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only)) |> hX.trans)
        have hw := scale_weight hx ht hb
        rw [mul_div_cancel_right₀ _ hx.ne'] at hw
        have hd := small_weight_decay hx ht hu1 hz
        rw [hw, Real.mul_rpow hu.1.le hx.le, one_div, inv_mul_eq_div] at hd
        change K u ≤ C * u ^ (24 / 100 : ℝ)
        unfold C K
        have hh := (div_le_iff₀ (Real.sqrt_pos.mpr hx)).mp hd
        exact hh.trans_eq (by ring))
  have hp : X ^ (24 / 100 : ℝ) * (1 / X) ^ (124 / 100 : ℝ) = 1 / X := by
    rw [one_div, Real.inv_rpow hx.le, ← div_eq_mul_inv, ← Real.rpow_sub hx]
    rw [show (24 / 100 - 124 / 100 : ℝ) = -1 by norm_num only, Real.rpow_neg hx.le, Real.rpow_one]
  have h' := mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg X)
  rw [intervalIntegral.integral_const_mul, integral_rpow (Or.inl (by norm_num only)),
    show (24 / 100 + 1 : ℝ) = 124 / 100 by norm_num only, Real.zero_rpow (by norm_num only),
    sub_zero] at h'
  change Real.sqrt X * (∫ u in (0 : ℝ)..1 / X, K u) ≤ _
  refine h'.trans_eq ?_
  unfold C
  have hs := Real.sq_sqrt hx.le
  calc
    _ =
        (Real.sqrt X) ^ 2 * quarterWeight656 X 1 *
            (X ^ (24 / 100 : ℝ) * (1 / X) ^ (124 / 100 : ℝ)) /
          (124 / 100) :=
      by ring
    _ = _ := by
      rw [hs, hp]; field_simp [hx.ne']

/-- The principal weight difference exceeds its full Mellin coefficient
minus the missing mass below the lower endpoint at one. -/
theorem quarter_integral_difference_656 {r : ℝ} (hl : 322 ≤ r) :
    let X := r ^ 2
    71780481 / 100000000 * r -
        4 * r * (∫ u in (0 : ℝ)..1 / X, (quarterKernel656.transform u).re / Real.sqrt u) <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight656 X t) -
        ∫ t in (1 : ℝ)..X * Real.exp (21 / 8), quarterWeight656 X t := by
  intro X
  have hr : 0 < r := by linarith only [hl]
  have hx : 1 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 1)]
  have hx0 := zero_lt_one.trans_le hx
  have hb : X ≤ X * Real.exp (21 / 8) := by
    exact le_mul_of_one_le_right hx0.le (Real.one_le_exp (by norm_num only))
  let K := fun u ↦ (quarterKernel656.transform u).re / Real.sqrt u
  have hi {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) : IntervalIntegrable K MeasureTheory.volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mpr
      ((LLS.PaperStatements.MellinKernel.integrableOn_weight_Ioi quarterKernel656).mono_set
        (fun _ h ↦ ha.trans_lt h.1))
  have hq := (one_div_pos.mpr hx0).le
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals (hi le_rfl hq)
      (hi hq ((div_le_one hx0).mpr hx))
  have hshort := quarter_scale_integral_656 hx0 zero_lt_one hx hb
  have hfull := quarter_integral_le_mass_656 hx0 zero_lt_one (hx.trans hb) le_rfl
  have hs : Real.sqrt X = r := Real.sqrt_sq hr.le
  rw [hs, div_self hx0.ne'] at hshort
  rw [hs] at hfull
  have hd := mul_lt_mul_of_pos_right quarter_principal_delta_656 hr
  change _ = ∫ u in (0 : ℝ)..1, K u at hsplit
  change _ = r * ∫ u in 1 / X..1, K u at hshort
  change _ < (4 * (∫ u in (0 : ℝ)..1, K u) - _) * r at hd
  nlinarith only [hshort, hfull, hd, congrArg (fun z : ℝ ↦ r * z) hsplit]

/-- On the two section 132 radius intervals, the principal weight integral
and its lower endpoint contribution exceed the scaled principal coefficient
minus 0.00032. The omitted mass is bounded by 100/124 of the endpoint weight. -/
theorem quarter_integral_endpoint_656 {r : ℝ} (hr : r ∈ Set.Icc 322 328) :
    let X := r ^ 2
    0.71780481 * r - 0.00032 <
      4 * (∫ t in (1 : ℝ)..X, quarterWeight656 X t) -
          (∫ t in (1 : ℝ)..X * Real.exp (21 / 8), quarterWeight656 X t) +
        3 * quarterWeight656 X 1 := by
  have h1 : 1 ≤ r := (by norm_num only : (1 : ℝ) ≤ 322).trans hr.1
  have hX := one_le_pow₀ h1 (n := 2)
  have hz : 14 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [log_322_bounds.1, Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hr.1]
  have hw := correction_weight hr
  have hp : 0 ≤ r := (by norm_num only : (0 : ℝ) ≤ 322).trans hr.1
  have hi := quarter_integral_difference_656 hr.1
  have hm := quarter_missing_mass_ratio_656 hX hz
  rw [Real.sqrt_sq hp] at hm
  dsimp only at hi ⊢
  linarith only [hi, hm, hw]

/-- Use the integrated mass lower bound and the signed cutoff bound in
the principal comparison. The trivial-zero action and the logarithmic
boundary at one are retained together for their later cancellation. -/
theorem quarter_principal_mass_lower_656 (hRH : RiemannHypothesis) {a b r : ℝ} (ha : 0 < a)
    (har : a ≤ r) (hrb : r ≤ b) (hr : r ∈ Set.Icc 322 328) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.71780481 * r - 0.00032 - 0.002594 - 4 * (9319732 / 100000000) * 70.4 / a +
          4 * (9319731 / 100000000) * (1837 / 1000) / b -
        (quarterAbelAction656 X AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries +
          3 * Real.log (2 * Real.pi) * quarterWeight656 X 1) ≤
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  intro X S
  have hmass := quarter_integral_endpoint_656 hr
  have h := quarter_principal_lower_656 hRH ha har hrb hr
  dsimp only [X, S] at hmass h ⊢
  linarith only [hmass, h]

end PseudoPrime.PrimeTestBounds.MillerRabin
