/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalWeights656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalLimit656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCorrection656
import PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTrivial

/-! # Trivial-zero contribution for the section 132 principal kernel -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shifted logarithmic coordinate vanishes at the upper support endpoint. -/
private noncomputable def shiftedCoord (X t : ℝ) : ℝ :=
  (11 / 10) * (21 / 8 - Real.log (t / X))

/-- Exponential and square-root factor multiplying the fifth power in the section 132 weight. -/
private noncomputable def weightFactor (X t : ℝ) : ℝ :=
  (1 / Real.sqrt t) * (Real.exp (-shiftedCoord X t) / 120)

private theorem coord_deriv {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    HasDerivAt (shiftedCoord X) (-(11 / 10) / t) t := by
  have hlog := ((hasDerivAt_id t).div_const X).log (div_pos ht hx).ne'
  apply (((hasDerivAt_const t (21 / 8 : ℝ)).sub hlog).const_mul (11 / 10 : ℝ)).congr_deriv
  simp only [id_eq]
  field_simp [hx.ne', ht.ne']
  ring

private theorem factor_deriv {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    HasDerivAt (weightFactor X) (weightFactor X t * (3 / 5) / t) t := by
  have h :=
    ((hasDerivAt_const t (1 : ℝ)).div (Real.hasDerivAt_sqrt ht.ne') (Real.sqrt_pos.mpr ht).ne').mul
      (((coord_deriv hx ht).neg.exp).div_const 120)
  apply h.congr_deriv
  simp only [Pi.neg_apply, Pi.div_apply, weightFactor]
  field_simp [ht.ne', (Real.sqrt_pos.mpr ht).ne']
  nlinarith only [Real.sq_sqrt ht.le]

/-- On positive inputs the logarithmic derivative is the exponential factor
times a polynomial of degrees four and five in the shifted coordinate. -/
private theorem log_deriv {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    let v := shiftedCoord X t
    t * deriv (quarterWeight656 X) t =
      weightFactor X t * ((3 / 5) * v ^ 5 - 5 * (11 / 10) * v ^ 4) := by
  intro v
  have he : quarterWeight656 X = fun u ↦ weightFactor X u * shiftedCoord X u ^ 5 := by
    funext u
    unfold quarterWeight656 weightFactor shiftedCoord
    ring
  rw [he,
    show deriv (fun u ↦ weightFactor X u * shiftedCoord X u ^ 5) t = _ from
      ((factor_deriv hx ht).mul ((coord_deriv hx ht).pow 5)).deriv]
  dsimp only [Pi.pow_apply, v]
  field_simp [ht.ne']
  ring

/-- The second Abel density has a cubic factor in the shifted coordinate.
The remaining quadratic controls every sign change on the positive support. -/
private theorem second_density {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    let v := shiftedCoord X t
    deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t =
      weightFactor X t / t * v ^ 3 *
        ((3 / 5) ^ 2 * v ^ 2 - 10 * (11 / 10) * (3 / 5) * v + 20 * (11 / 10) ^ 2) := by
  intro v
  let F := fun u ↦
    weightFactor X u * ((3 / 5) * shiftedCoord X u ^ 5 - (5 * (11 / 10)) * shiftedCoord X u ^ 4)
  have he : (fun u ↦ u * deriv (quarterWeight656 X) u) =ᶠ[nhds t] F :=
    Filter.eventually_of_mem (isOpen_Ioi.mem_nhds ht) (fun u hu ↦ log_deriv hx hu)
  have hv := coord_deriv hx ht
  have hf :=
    (factor_deriv hx ht).mul
      (((hv.pow 5).const_mul (3 / 5)).sub ((hv.pow 4).const_mul (5 * (11 / 10))))
  rw [he.deriv_eq, show deriv F t = _ from hf.deriv]
  dsimp only [Pi.sub_apply, Pi.pow_apply, v]
  field_simp [ht.ne']
  ring

/-- Between the arithmetic cutoff and the end of support, the second Abel density
is nonnegative. Here the shifted coordinate is between zero and 231/80. -/
private theorem outer_density_nonneg {X t : ℝ} (hx : 0 < X) (hl : X ≤ t)
    (hu : t ≤ X * Real.exp (21 / 8)) : 0 ≤ deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t := by
  have ht := hx.trans_le hl
  have hlog := Real.log_nonneg ((one_le_div hx).mpr hl)
  have hlog' :=
    (Real.log_le_iff_le_exp (div_pos ht hx)).mpr ((div_le_iff₀ hx).mpr ((mul_comm _ X) ▸ hu))
  have hv : 0 ≤ shiftedCoord X t := by
    unfold shiftedCoord
    norm_num only
    linarith only [hlog']
  have hu' : shiftedCoord X t ≤ 231 / 80 := by
    unfold shiftedCoord
    norm_num only
    linarith only [hlog]
  have hq :
    0 ≤
      (3 / 5 : ℝ) ^ 2 * shiftedCoord X t ^ 2 - 10 * (11 / 10) * (3 / 5) * shiftedCoord X t +
        20 * (11 / 10) ^ 2 := by
    nlinarith only [hu', sq_nonneg (shiftedCoord X t)]
  have hf : 0 ≤ weightFactor X t := by
    unfold weightFactor; positivity
  rw [second_density hx ht]
  exact mul_nonneg (mul_nonneg (div_nonneg hf ht.le) (pow_nonneg hv 3)) hq

/-- On positive inputs the exponential prefactor divided by the input is
its endpoint value times the power with exponent minus two fifths. -/
private theorem factor_div {X t : ℝ} (hx : 0 < X) (ht : 0 < t) :
    weightFactor X t / t = weightFactor X 1 * t ^ (-(2 / 5 : ℝ)) := by
  unfold weightFactor shiftedCoord
  rw [Real.sqrt_one, one_div_one, one_mul, Real.log_div ht.ne' hx.ne',
    show (1 / X : ℝ) = X⁻¹ from one_div X, Real.log_inv, sub_neg_eq_add, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos ht, Real.rpow_def_of_pos ht]
  have he :
    -((11 / 10) * (21 / 8 - (Real.log t - Real.log X))) =
      -((11 / 10) * (21 / 8 + Real.log X)) + Real.log t * (1 / 2) + Real.log t +
        Real.log t * -(2 / 5) := by
    ring
  rw [he, Real.exp_add, Real.exp_add, Real.exp_add, Real.exp_log ht]
  field_simp [ht.ne', Real.exp_ne_zero]

/-- On the inner support the second Abel density is at most 0.37 times
the physical weight at one. The shifted coordinate controls the sign
of the lower-degree terms. -/
private theorem inner_density_upper {X t : ℝ} (hx : 1 ≤ X) (hb : 14 ≤ shiftedCoord X 1) (ht : 1 ≤ t)
    (hcut : t ≤ X) :
    deriv (fun u ↦ u * deriv (quarterWeight656 X) u) t ≤ 0.37 * quarterWeight656 X 1 := by
  let v := shiftedCoord X t
  let b := shiftedCoord X 1
  let F := weightFactor X 1
  have hx0 := zero_lt_one.trans_le hx
  have ht0 := zero_lt_one.trans_le ht
  have hv0 : 0 ≤ v := by
    have hlog := Real.log_nonpos (div_nonneg ht0.le hx0.le) ((div_le_one hx0).2 hcut)
    dsimp only [v, shiftedCoord]
    norm_num only
    linarith only [hlog]
  have hvb : v ≤ b := by
    have hlog := Real.log_le_log (one_div_pos.mpr hx0) (div_le_div_of_nonneg_right ht hx0.le)
    dsimp only [v, b, shiftedCoord]
    norm_num only
    linarith only [hlog]
  have hb0 := hv0.trans hvb
  have hv5 := pow_le_pow_left₀ hv0 hvb 5
  have hpoly :
    v ^ 3 * ((3 / 5) ^ 2 * v ^ 2 - 10 * (11 / 10) * (3 / 5) * v + 20 * (11 / 10) ^ 2) ≤
      0.37 * b ^ 5 := by
    have h := pow_nonneg hv0 3
    rcases le_or_gt v 4 with hv | hv
    · have hv3 := pow_le_pow_left₀ hv0 hv 3
      have hb5 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 14) hb 5
      nlinarith only [hv5, hv3, hb5, mul_nonneg h hv0]
    · have hn : -10 * (11 / 10 : ℝ) * (3 / 5) * v + 20 * (11 / 10) ^ 2 ≤ 0 := by linarith only [hv]
      nlinarith only [hv5, pow_nonneg hb0 5, mul_nonpos_of_nonneg_of_nonpos h hn]
  have hp : t ^ (-(2 / 5 : ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos ht (by norm_num only)
  have hF : 0 ≤ F := by
    dsimp only [F, weightFactor]; positivity
  have hw : quarterWeight656 X 1 = F * b ^ 5 := by
    unfold F b quarterWeight656 weightFactor shiftedCoord
    ring
  rw [second_density hx0 ht0, factor_div hx0 ht0, hw]
  change F * t ^ (-(2 / 5 : ℝ)) * v ^ 3 * _ ≤ _
  rw [mul_assoc (F * _)]
  calc
    _ ≤ (F * t ^ (-(2 / 5 : ℝ))) * (0.37 * b ^ 5) :=
      mul_le_mul_of_nonneg_left hpoly (mul_nonneg hF (Real.rpow_nonneg ht0.le _))
    _ ≤ _ := by
      have h :=
        mul_le_mul_of_nonneg_right (mul_le_of_le_one_right hF hp)
          (show 0 ≤ 0.37 * b ^ 5 by positivity)
      linarith only [h]

/-- The logarithmic derivative at one costs at most 0.27 of the
endpoint weight when the shifted coordinate lies between fourteen and 16.05. -/
private theorem deriv_one_le {X : ℝ} (hx : 0 < X) (hb : 14 ≤ shiftedCoord X 1)
    (hu : shiftedCoord X 1 ≤ 16.05) :
    deriv (quarterWeight656 X) 1 ≤ 0.27 * quarterWeight656 X 1 := by
  let v := shiftedCoord X 1
  let F := weightFactor X 1
  have hv : 0 ≤ v := by linarith only [hb]
  have hF : 0 ≤ F := by
    dsimp only [F, weightFactor]; positivity
  have h := log_deriv hx (zero_lt_one : (0 : ℝ) < 1)
  rw [one_mul] at h
  have hw : quarterWeight656 X 1 = F * v ^ 5 := by
    unfold F v quarterWeight656 weightFactor shiftedCoord
    ring
  rw [h, hw]
  have hp : (3 / 5) * v ^ 5 - 5 * (11 / 10) * v ^ 4 ≤ 0.27 * v ^ 5 := by
    have he := mul_le_mul_of_nonneg_right hu (pow_nonneg hv 4)
    dsimp only [v]
    nlinarith only [he, pow_nonneg hv 4]
  linarith only [mul_le_mul_of_nonneg_left hp hF]

/-- The inverse-square majorant has integral at most one on the inner support. -/
private theorem inv_sq_integral {X : ℝ} (hX : 1 ≤ X) : (∫ t in (1 : ℝ)..X, t⁻¹ ^ 2) ≤ 1 := by
  have hp (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) X) : 0 < t := by
    rw [Set.uIcc_of_le hX] at ht
    exact zero_lt_one.trans_le ht.1
  have hc : ContinuousOn (fun t : ℝ ↦ t⁻¹ ^ 2) (Set.uIcc 1 X) := fun t ht ↦
    ((continuousAt_id.inv₀ (hp t ht).ne').pow 2).continuousWithinAt
  have hi := hc.intervalIntegrable (μ := MeasureTheory.volume)
  have hd (t : ℝ) (ht : t ∈ Set.uIcc (1 : ℝ) X) : HasDerivAt (fun x : ℝ ↦ -x⁻¹) (t⁻¹ ^ 2) t := by
    convert (hasDerivAt_inv (hp t ht).ne').neg using 1
    simp only [neg_neg, ← inv_pow]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi, inv_one]
  linarith only [inv_nonneg.mpr (zero_le_one.trans hX)]

/-- Using its explicit value at the arithmetic cutoff, the weight there
is nonnegative and at most two whenever the cutoff is at least one. -/
private theorem cutoff_weight_bound {X : ℝ} (hX : 1 ≤ X) :
    0 ≤ quarterWeight656 X X ∧ quarterWeight656 X X ≤ 2 := by
  have hx := zero_lt_one.trans_le hX
  have hs : 1 ≤ Real.sqrt X := by
    rw [← Real.sqrt_one]; exact Real.sqrt_le_sqrt hX
  have hsi := inv_le_one_of_one_le₀ hs
  have he := Real.exp_le_one_iff.mpr (by norm_num only : -(231 / 80 : ℝ) ≤ 0)
  have hf : (231 / 80 : ℝ) ^ 5 * Real.exp (-(231 / 80)) / 120 ≤ 2 := by
    have h := mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ (231 / 80) ^ 5)
    linarith only [h]
  have hp : 0 ≤ (231 / 80 : ℝ) ^ 5 * Real.exp (-(231 / 80)) / 120 := by positivity
  unfold quarterWeight656
  rw [div_self hx.ne', Real.log_one, sub_zero]
  dsimp only
  rw [show ((11 / 10) * (21 / 8) : ℝ) = 231 / 80 by norm_num only]
  change
    0 ≤ (1 / Real.sqrt X) * ((231 / 80) ^ 5 * Real.exp (-(231 / 80)) / 120) ∧
      (1 / Real.sqrt X) * ((231 / 80) ^ 5 * Real.exp (-(231 / 80)) / 120) ≤ 2
  rw [one_div]
  exact
    ⟨mul_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg X)) hp, (mul_le_of_le_one_left hp hsi).trans hf⟩

private theorem cutoff_deriv {X : ℝ} (hx : 0 < X) :
    X * deriv (quarterWeight656 X) X = -(137 / 105) * quarterWeight656 X X := by
  rw [log_deriv hx hx]
  dsimp only [quarterWeight656, weightFactor, shiftedCoord]
  rw [div_self hx.ne', Real.log_one, sub_zero]
  ring

/-- Bound the trivial-zero Abel action in terms of the actual weight at one. -/
private theorem trivial_upper_weight_of_deriv {r d : ℝ} (hl : 322 ≤ r)
    (hb : 14 ≤ shiftedCoord (r ^ 2) 1) (hd : 0 ≤ d)
    (hderiv : deriv (quarterWeight656 (r ^ 2)) 1 ≤ d * quarterWeight656 (r ^ 2) 1) :
    quarterAbelAction656 (r ^ 2) AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries ≤
      (0.4625 + 1.25 * d) * quarterWeight656 (r ^ 2) 1 + 0.000012 := by
  let X := r ^ 2
  let B := X * Real.exp (21 / 8)
  let W := quarterWeight656 X
  let P := fun t ↦ t * deriv W t
  let T := AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries
  have hx1000 : 1000 ≤ X := by
    dsimp only [X]; nlinarith only [hl, sq_nonneg (r - 322)]
  have hx1 : 1 ≤ X := (by norm_num only : (1 : ℝ) ≤ 1000).trans hx1000
  have hx := zero_lt_one.trans_le hx1
  have hXB : X ≤ B := le_mul_of_one_le_right hx.le (Real.one_le_exp (by norm_num only))
  have hQ : ContinuousOn (deriv P) (Set.Icc 1 B) := abel_deriv_continuous_656 hx
  have hT : ContinuousOn T (Set.Icc 1 B) :=
    AnalyticNumberTheory.RiemannZeta.trivial_cont_closed le_rfl
  have hI := hT.mul hQ
  have hI₁ :=
    (hI.mono (Set.Icc_subset_Icc_right hXB)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
      hx1
  have hI₂ :=
    (hI.mono (Set.Icc_subset_Icc_left hx1)).intervalIntegrable_of_Icc (μ := MeasureTheory.volume)
      hXB
  have hw : 0 ≤ W 1 := by
    change 0 ≤ quarterWeight656 X 1
    rw [weight_one_power_656 hx]
    have hlog := Real.log_nonneg hx1
    positivity
  have hD (t : ℝ) (ht : 1 ≤ t) : 0 ≤ T t ∧ T t ≤ (5 / 12 : ℝ) * t⁻¹ ^ 2 :=
    section99_trivial_envelope ht
  have hmajor : ContinuousOn (fun t : ℝ ↦ (0.37 * W 1 * (5 / 12)) * t⁻¹ ^ 2) (Set.Icc 1 X) := by
    intro t ht
    exact
      (continuousAt_const.mul
          ((continuousAt_id.inv₀ (zero_lt_one.trans_le ht.1).ne').pow 2)).continuousWithinAt
  have hi :=
    intervalIntegral.integral_mono_on hx1 hI₁ (hmajor.intervalIntegrable_of_Icc hx1)
      (fun t ht ↦ by
        have h₁ := mul_le_mul_of_nonneg_left (inner_density_upper hx1 hb ht.1 ht.2) (hD t ht.1).1
        have h₂ := mul_le_mul_of_nonneg_right (hD t ht.1).2 (show 0 ≤ 0.37 * W 1 by positivity)
        change T t * deriv P t ≤ _
        change T t * deriv P t ≤ T t * (0.37 * W 1) at h₁
        linarith only [h₁, h₂])
  rw [intervalIntegral.integral_const_mul] at hi
  have hin := hi.trans (mul_le_of_le_one_right (by positivity) (inv_sq_integral hx1))
  have hout : 0 ≤ ∫ t in X..B, T t * deriv P t := by
    apply intervalIntegral.integral_nonneg hXB
    intro t ht
    exact mul_nonneg (hD t (hx1.trans ht.1)).1 (outer_density_nonneg hx ht.1 ht.2)
  have h₁ : P 1 * T 1 ≤ d * W 1 * (5 / 12) := by
    have h := mul_le_mul_of_nonneg_right hderiv (hD 1 le_rfl).1
    have hj := (hD 1 le_rfl).2
    rw [inv_one, one_pow, mul_one] at hj
    exact
      (by simpa only [P, one_mul] using h : P 1 * T 1 ≤ d * W 1 * T 1).trans
        (mul_le_mul_of_nonneg_left hj (mul_nonneg hd hw))
  have hTX : T X ≤ (1 / 1000000 : ℝ) := by
    have h := (inv_le_inv₀ hx (by norm_num only : (0 : ℝ) < 1000)).2 hx1000
    have hh := pow_le_pow_left₀ (inv_nonneg.mpr hx.le) h 2
    linarith only [(hD X hx1).2, hh]
  have hpX : -P X * T X ≤ 3 / 1000000 := by
    have hW₂ := cutoff_weight_bound hx1
    dsimp only [P, W]
    rw [cutoff_deriv hx]
    have hh := mul_le_mul hW₂.2 hTX (hD X hx1).1 (by norm_num only : (0 : ℝ) ≤ 2)
    linarith only [hh]
  change 0 ≤ ∫ t in X..B, (T * deriv P) t at hout
  change
    4 * (∫ t in (1 : ℝ)..X, (T * deriv P) t) - (∫ t in (1 : ℝ)..B, (T * deriv P) t) -
          4 * P X * T X +
        3 * P 1 * T 1 ≤
      _
  rw [← intervalIntegral.integral_add_adjacent_intervals hI₁ hI₂]
  change _ ≤ (0.4625 + 1.25 * d) * W 1 + 0.000012
  nlinarith only [hin, hout, h₁, hpX, hw]

private theorem trivial_upper_weight {r : ℝ} (hl : 322 ≤ r) (hb : 14 ≤ shiftedCoord (r ^ 2) 1)
    (hbu : shiftedCoord (r ^ 2) 1 ≤ 16.05) :
    quarterAbelAction656 (r ^ 2) AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries ≤
      0.8 * quarterWeight656 (r ^ 2) 1 + 0.000012 := by
  have hr : 0 < r := (by norm_num only : (0 : ℝ) < 322).trans_le hl
  have he :=
    trivial_upper_weight_of_deriv hl hb (by norm_num only : (0 : ℝ) ≤ 0.27)
      (deriv_one_le (pow_pos hr 2) hb hbu)
  convert he using 1
  ring

/-- The trivial-zero action on the whole section 132 range is at most
four fifths of the weight at one plus the cutoff error. -/
theorem quarter_trivial_bound_656 {r : ℝ} (hr : r ∈ Set.Icc 322 328) :
    quarterAbelAction656 (r ^ 2) AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries ≤
      0.8 * quarterWeight656 (r ^ 2) 1 + 0.000012 := by
  have hpos : 0 < r := (by norm_num only : (0 : ℝ) < 322).trans_le hr.1
  have hL :=
    (Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo :=
        5774551543203 / 1000000000000) (hi := 6) (by decide +kernel)).1
  have hU :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5) (hi :=
        5793013610546 / 1000000000000) (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat] at hL hU
  have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hr.1
  have h' := Real.log_le_log hpos hr.2
  have hb : 14 ≤ shiftedCoord (r ^ 2) 1 := by
    unfold shiftedCoord
    rw [one_div, Real.log_inv, sub_neg_eq_add, Real.log_pow]
    linarith only [hL, h]
  have hbu : shiftedCoord (r ^ 2) 1 ≤ 16.05 := by
    unfold shiftedCoord
    rw [one_div, Real.log_inv, sub_neg_eq_add, Real.log_pow]
    linarith only [hU, h']
  exact trivial_upper_weight hr.1 hb hbu

/-- For radii at least 322 and shifted logarithmic coordinate at least
fourteen, the trivial-zero action is bounded using the weight at one. -/
theorem quarter_trivial_bound_656_from_coord {r : ℝ} (hr : 322 ≤ r)
    (hz : 14 ≤ (21 / 8 : ℝ) + Real.log (r ^ 2)) :
    quarterAbelAction656 (r ^ 2) AnalyticNumberTheory.RiemannZeta.riemannZetaLogTrivialZeroSeries ≤
      1.2125 * quarterWeight656 (r ^ 2) 1 + 0.000012 := by
  have hx : 0 < r ^ 2 := pow_pos ((by norm_num only : (0 : ℝ) < 322).trans_le hr) 2
  let v := shiftedCoord (r ^ 2) 1
  let F := weightFactor (r ^ 2) 1
  have hv : 14 ≤ v := by
    unfold v shiftedCoord
    rw [one_div, Real.log_inv, sub_neg_eq_add]
    linarith only [hz]
  have hF : 0 ≤ F := by
    dsimp only [F, weightFactor]
    positivity
  have hw : quarterWeight656 (r ^ 2) 1 = F * v ^ 5 := by
    unfold F v quarterWeight656 weightFactor shiftedCoord
    ring
  have hd : deriv (quarterWeight656 (r ^ 2)) 1 ≤ (3 / 5) * quarterWeight656 (r ^ 2) 1 := by
    have h := log_deriv hx (zero_lt_one : (0 : ℝ) < 1)
    rw [one_mul] at h
    rw [h, hw]
    change F * ((3 / 5) * v ^ 5 - 5 * (11 / 10) * v ^ 4) ≤ (3 / 5) * (F * v ^ 5)
    have hn := mul_nonneg hF (pow_nonneg ((by norm_num only : (0 : ℝ) ≤ 14).trans hv) 4)
    nlinarith only [hn]
  have he := trivial_upper_weight_of_deriv hr hv (by norm_num only : (0 : ℝ) ≤ 3 / 5) hd
  convert he using 1
  ring

/-- Retain the actual lower-end weight in the combined trivial-zero and
logarithmic boundary loss, so subsequent estimates can use its cancellation. -/
theorem quarter_principal_trivial_lower_656 (hRH : RiemannHypothesis) {a b r : ℝ} (ha : 0 < a)
    (har : a ≤ r) (hrb : r ≤ b) (hr : r ∈ Set.Icc 322 328) :
    let X := r ^ 2
    let S := fun n : ℕ ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) X n).re
    0.71780481 * r - 0.002926 - 4 * (9319732 / 100000000) * 70.4 / a +
          4 * (9319731 / 100000000) * (1837 / 1000) / b -
        (0.8 + 3 * Real.log (2 * Real.pi)) * quarterWeight656 X 1 ≤
      4 * (∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, S n) - (∑' n : ℕ, S n) := by
  have h := quarter_principal_mass_lower_656 hRH ha har hrb hr
  have ht := quarter_trivial_bound_656 hr
  dsimp only at h ⊢
  linarith only [h, ht]

end PseudoPrime.PrimeTestBounds.MillerRabin
