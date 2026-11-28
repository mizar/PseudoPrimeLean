/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThreeShift117
public import PseudoPrime.Analysis.ExponentialFixedPointBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseBoxes117
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedMoments
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedEuler

/-! # Euler weight and linear gain for the section 117 comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Coefficient of degree `k` after applying the shift `s` to the Euler polynomial. -/
noncomputable def shift117Coeff (s : ℝ) (k : ℕ) : ℝ :=
  let a : ℝ := 51 / 50
  let C (y : ℝ) :=
    if k = 0 then 3 / 8 + 3 * a / 8 * y + a ^ 2 / 8 * y ^ 2
    else if k = 1 then 3 * a / 8 + a ^ 2 / 4 * y else a ^ 2 / 8
  (Real.exp (-(a * s)) * C (5 + s) + Real.exp (a * s) * C (5 - s)) / 2

/-- Coefficient of degree `k` in the three-shift Euler polynomial. -/
noncomputable def coeff117 (k : ℕ) : ℝ :=
  ((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2) * shift117Coeff 0 k -
          (3.143 * 3.124) * shift117Coeff (1 / 50) k -
          (3.143 * 0.0374) * shift117Coeff (11 / 10) k +
        (3.124 * 0.0374) * shift117Coeff (27 / 25) k -
      3.143 * shift117Coeff (14 / 5) k +
    3.124 * shift117Coeff (141 / 50) k +
    0.0374 * shift117Coeff (39 / 10) k

private theorem shift117_exp_box {x l u : ℝ} (hx : 0 ≤ x) (hs : x / 33 ≤ 1 / 2)
    (hl : l ≤ ∑ k ∈ Finset.range 32, x ^ k / (k.factorial : ℝ))
    (hu :
      (∑ k ∈ Finset.range 32, x ^ k / (k.factorial : ℝ)) + (x ^ 32 / ((32 : ℕ).factorial : ℝ)) * 2 ≤
        u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u := by
  exact
    ⟨hl.trans (Real.sum_le_exp_of_nonneg hx _),
      (Analysis.exp_le_taylor_add_two_next (x := x) (n := 32) hx hs).trans hu⟩

private theorem shift117_inv_box {x l u : ℝ} (hl : 0 < l) (h : l ≤ Real.exp x ∧ Real.exp x ≤ u) :
    1 / u ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ 1 / l := by
  rw [Real.exp_neg, ← one_div]
  exact ⟨one_div_le_one_div_of_le (Real.exp_pos _) h.2, one_div_le_one_div_of_le hl h.1⟩

private theorem exp117_0 :
    1020609502188 / 10 ^ 12 ≤ Real.exp ((51 / 50) * (1 / 50)) ∧
      Real.exp ((51 / 50) * (1 / 50)) ≤ 1020609502191 / 10 ^ 12 := by
  exact
    shift117_exp_box (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])

private theorem exp117_1 :
    3070990045495 / 10 ^ 12 ≤ Real.exp ((51 / 50) * (11 / 10)) ∧
      Real.exp ((51 / 50) * (11 / 10)) ≤ 3070990045498 / 10 ^ 12 := by
  exact
    shift117_exp_box (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])

private theorem exp117_2 :
    3008976536967 / 10 ^ 12 ≤ Real.exp ((51 / 50) * (27 / 25)) ∧
      Real.exp ((51 / 50) * (27 / 25)) ≤ 3008976536970 / 10 ^ 12 := by
  exact
    shift117_exp_box (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])

private theorem exp117_3 :
    17391820334977 / 10 ^ 12 ≤ Real.exp ((51 / 50) * (14 / 5)) ∧
      Real.exp ((51 / 50) * (14 / 5)) ≤ 17391820334980 / 10 ^ 12 := by
  exact
    shift117_exp_box (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])

private theorem exp117_4 :
    17750257094255 / 10 ^ 12 ≤ Real.exp ((51 / 50) * (141 / 50)) ∧
      Real.exp ((51 / 50) * (141 / 50)) ≤ 17750257094258 / 10 ^ 12 := by
  exact
    shift117_exp_box (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])

private theorem exp117_5 :
    53410107121783 / 10 ^ 12 ≤ Real.exp ((51 / 50) * (39 / 10)) ∧
      Real.exp ((51 / 50) * (39 / 10)) ≤ 53410107121786 / 10 ^ 12 := by
  exact
    shift117_exp_box (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])

private theorem coeff117_box :
    coeff117 0 ∈ Set.Icc 1.12297004 1.12297010 ∧
      coeff117 1 ∈ Set.Icc 0.88991172 0.88991178 ∧ coeff117 2 ∈ Set.Icc 0.18022516 0.18022522 := by
  have h0 := exp117_0
  have j0 := shift117_inv_box (by norm_num only) h0
  have h1 := exp117_1
  have j1 := shift117_inv_box (by norm_num only) h1
  have h2 := exp117_2
  have j2 := shift117_inv_box (by norm_num only) h2
  have h3 := exp117_3
  have j3 := shift117_inv_box (by norm_num only) h3
  have h4 := exp117_4
  have j4 := shift117_inv_box (by norm_num only) h4
  have h5 := exp117_5
  have j5 := shift117_inv_box (by norm_num only) h5
  unfold coeff117 shift117Coeff
  norm_num only [Set.mem_Icc, ite_true, ite_false, mul_zero, neg_zero, Real.exp_zero, one_mul]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith only [h0.1, h0.2, j0.1, j0.2, h1.1, h1.2, j1.1, j1.2, h2.1, h2.2, j2.1, j2.2, h3.1,
      h3.2, j3.1, j3.2, h4.1, h4.2, j4.1, j4.2, h5.1, h5.2, j5.1, j5.2]

/-- The section 117 Euler weight is quadratic in the translated variable x-5. -/
private theorem three_shift_euler_poly_expand (x : ℝ) :
    threeShiftEulerPoly x = coeff117 0 + coeff117 1 * (x - 5) + coeff117 2 * (x - 5) ^ 2 := by
  unfold threeShiftEulerPoly weightedShiftPoly coeff117 shift117Coeff
  norm_num only [ite_true, ite_false, neg_mul]
  ring

/-- The three coefficients of the Euler weight in the basis 1, x-5, (x-5)^2
are positive, so the weight can be used with a common trace deficit. -/
theorem three_shift_euler_poly_pos {x : ℝ} (hx : 5 ≤ x) : 0 < threeShiftEulerPoly x := by
  obtain ⟨ha, hb, hc⟩ := coeff117_box
  rw [three_shift_euler_poly_expand]
  have h₁ := mul_nonneg (show 0 ≤ coeff117 1 by linarith only [hb.1]) (sub_nonneg.mpr hx)
  have h₂ := mul_nonneg (show 0 ≤ coeff117 2 by linarith only [hc.1]) (sq_nonneg (x - 5))
  linarith only [ha.1, h₁, h₂]

/-- At logarithmic prime power argument x, the slope polynomial is the
factor in the negative derivative of the section 117 Euler weight. -/
noncomputable def threeShiftEulerSlope (x : ℝ) : ℝ :=
  (38 / 25 * coeff117 0 - coeff117 1) + (38 / 25 * coeff117 1 - 2 * coeff117 2) * (x - 5) +
    (38 / 25 * coeff117 2) * (x - 5) ^ 2

/-- The slope polynomial is positive on the logarithmic Euler tail. -/
theorem three_shift_euler_slope_pos {x : ℝ} (hx : 5 ≤ x) : 0 < threeShiftEulerSlope x := by
  obtain ⟨ha, hb, hc⟩ := coeff117_box
  unfold threeShiftEulerSlope
  have h₁ :=
    mul_nonneg (show 0 ≤ 38 / 25 * coeff117 1 - 2 * coeff117 2 by linarith only [hb.1, hc.2])
      (sub_nonneg.mpr hx)
  have h₂ := mul_nonneg (show 0 ≤ 38 / 25 * coeff117 2 by linarith only [hc.1]) (sq_nonneg (x - 5))
  linarith only [ha.1, hb.2, h₁, h₂]

private theorem three_shift_poly_deriv (x : ℝ) :
    HasDerivAt threeShiftEulerPoly (coeff117 1 + 2 * coeff117 2 * (x - 5)) x := by
  have h := (hasDerivAt_id x).sub_const 5
  have H :=
    ((h.const_mul (coeff117 1)).const_add (coeff117 0)).add ((h.pow 2).const_mul (coeff117 2))
  rw [show
      threeShiftEulerPoly =
        (fun y : ℝ ↦ coeff117 0 + coeff117 1 * (y - 5) + coeff117 2 * (y - 5) ^ 2)
      from funext three_shift_euler_poly_expand]
  change
    HasDerivAt (fun y : ℝ ↦ coeff117 0 + coeff117 1 * (y - 5) + coeff117 2 * (y - 5) ^ 2) _ x at H
  convert H using 1
  norm_num only [id, Nat.cast_ofNat]
  ring

/-- The section 117 Euler density is the quadratic weight in log t multiplied
by t to the power -38/25, as used for partial summation over the prime powers. -/
noncomputable def threeShiftEulerDensity (t : ℝ) : ℝ :=
  Real.exp (-(38 / 25 : ℝ) * Real.log t) * threeShiftEulerPoly (Real.log t)

/-- Differentiating the section 117 Euler density at t > 0 yields the
logarithmic slope polynomial with a negative sign and a reciprocal factor. -/
theorem three_shift_density_deriv {t : ℝ} (ht : 0 < t) :
    deriv threeShiftEulerDensity t =
      -(Real.exp (-(38 / 25 : ℝ) * Real.log t) * threeShiftEulerSlope (Real.log t)) * t⁻¹ := by
  let x := Real.log t
  have he := ((hasDerivAt_id x).const_mul (-(38 / 25 : ℝ))).exp
  have h := (he.mul (three_shift_poly_deriv x)).comp t (Real.hasDerivAt_log ht.ne')
  change HasDerivAt threeShiftEulerDensity _ t at h
  rw [h.deriv, threeShiftEulerSlope, three_shift_euler_poly_expand x]
  dsimp only [id, x]
  ring

/-- The signed Abel slope is negative on the prime-power tail above exp 5. -/
theorem three_shift_density_deriv_neg {t : ℝ} (ht : 0 < t) (hl : 5 ≤ Real.log t) :
    deriv threeShiftEulerDensity t < 0 := by
  rw [three_shift_density_deriv ht]
  exact
    mul_neg_of_neg_of_pos
      (neg_neg_of_pos (mul_pos (Real.exp_pos _) (three_shift_euler_slope_pos hl))) (inv_pos.mpr ht)

/-- The normalized cosine conductor profile at a nonnegative shift. -/
noncomputable def threeShiftG (s : ℝ) : ℝ :=
  2 * Real.exp (-((51 / 50 : ℝ) * s)) * (3 / 8 + 3 * (51 / 50) / 8 * s + (51 / 50) ^ 2 / 8 * s ^ 2)

/-- The coefficient of r from the cosine conductor and shifted symmetric poles
in the section 117 comparison. -/
noncomputable def threeShiftGain : ℝ :=
  3.143 * threeShiftG (14 / 5) - 3.124 * threeShiftG (141 / 50) - 0.0374 * threeShiftG (39 / 10) -
        ((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2) * threeShiftG 0 +
      (3.143 * 3.124) * threeShiftG (1 / 50) +
      (3.143 * 0.0374) * threeShiftG (11 / 10) -
    (3.124 * 0.0374) * threeShiftG (27 / 25) -
    (3 * (51 / 50) ^ 5 / (38 / 25) ^ 6) *
      (3.143 - 3.124 * Real.exp (-(1 / 100)) - 0.0374 * Real.exp (-(11 / 20)))

/-- Rational Taylor intervals certify the section 117 linear gain. -/
theorem three_shift_gain_lower : 0.00120516 < threeShiftGain := by
  have k0 :=
    shift117_exp_box (x := 1 / 100) (l := 1010050167083 / 10 ^ 12) (u := 1010050167086 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have m0 := shift117_inv_box (by norm_num only) k0
  have k1 :=
    shift117_exp_box (x := 11 / 20) (l := 1733253017866 / 10 ^ 12) (u := 1733253017869 / 10 ^ 12)
      (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have m1 := shift117_inv_box (by norm_num only) k1
  have j0 := shift117_inv_box (by norm_num only) exp117_0
  have j1 := shift117_inv_box (by norm_num only) exp117_1
  have j2 := shift117_inv_box (by norm_num only) exp117_2
  have j3 := shift117_inv_box (by norm_num only) exp117_3
  have j4 := shift117_inv_box (by norm_num only) exp117_4
  have j5 := shift117_inv_box (by norm_num only) exp117_5
  unfold threeShiftGain threeShiftG
  norm_num only [mul_zero, neg_zero, Real.exp_zero, one_mul]
  linarith only [m0.1, m0.2, m1.1, m1.2, j0.1, j0.2, j1.1, j1.2, j2.1, j2.2, j3.1, j3.2, j4.1, j4.2,
    j5.1, j5.2]

private theorem three_shift_density_analytic {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ threeShiftEulerDensity t := by
  unfold threeShiftEulerDensity threeShiftEulerPoly weightedShiftPoly
  fun_prop (disch := exact ht.ne')

/-- On a positive finite interval, centered Abel summation expresses the
section 117 Euler sum by its main integral, endpoint errors, and derivative integral. -/
theorem three_shift_euler_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
            threeShiftEulerPoly (Real.log n)) -
        (∫ t : ℝ in a..b, threeShiftEulerDensity t) =
      (Chebyshev.psi b - b) * threeShiftEulerDensity b -
        (Chebyshev.psi a - a) * threeShiftEulerDensity a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv threeShiftEulerDensity t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := three_shift_density_analytic (ha.trans_le ht.1)
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt)
      (show ContinuousOn (deriv threeShiftEulerDensity) (Set.Icc a b) from fun t ht ↦
          (hd t ht).deriv.continuousAt.continuousWithinAt).integrableOn_Icc
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  rw [threeShiftEulerDensity, Real.rpow_def_of_pos hp, neg_mul, mul_comm (38 / 25 : ℝ),
    Real.exp_neg]
  ring

/-- The upper centered Abel boundary for the section 117 weight goes to zero
because its quadratic logarithmic moments decay against the unconditional psi bound. -/
theorem three_shift_euler_boundary_zero :
    Filter.Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - x) * threeShiftEulerDensity x) Filter.atTop
      (nhds 0) := by
  let E := fun x : ℝ ↦ (Chebyshev.psi x - x) / 4
  have hE : ∀ᶠ x : ℝ in Filter.atTop, ‖E x‖ ≤ 2 * x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 := zero_le_one.trans hx
    have hlog := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 4)
    have hu :=
      (Chebyshev.psi_le_const_mul_self hx0).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hlog] : Real.log 4 + 4 ≤ 7) hx0)
    rw [Real.norm_eq_abs, abs_le]
    dsimp only [E]
    constructor <;> linarith only [hu, Chebyshev.psi_nonneg (x := x), hx0]
  have hm (k : ℕ) :=
    AnalyticNumberTheory.RiemannZeta.moment_boundary_tendsto (by norm_num only : (1 : ℝ) < 38 / 25)
      k E hE
  let C := (coeff117 0) - 5 * (coeff117 1) + 25 * (coeff117 2)
  let L := (coeff117 1) - 10 * (coeff117 2)
  let Q := (coeff117 2)
  have hh :=
    ((((hm 0).const_mul (4 * C)).add ((hm 1).const_mul (4 * L))).add ((hm 2).const_mul (4 * Q)))
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, E, threeShiftEulerDensity, C, L,
    Q]
  rw [three_shift_euler_poly_expand]
  rw [Real.rpow_def_of_pos hx]
  rw [show Real.log x * -(38 / 25 : ℝ) = -(38 / 25 : ℝ) * Real.log x by ring]
  ring

/-- RH bounds the centered finite Abel error by its explicit square-root
envelope wherever the section 117 Euler density is decreasing. -/
theorem three_shift_euler_error_RH (hRH : RiemannHypothesis) {a b : ℝ} (ha : 101 ≤ a)
    (hla : 5 ≤ Real.log a) (hab : a ≤ b) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv threeShiftEulerDensity t| ≤
      ∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity t := by
  have hcont :
    ContinuousOn (fun t : ℝ ↦ Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity t)
      (Set.Icc a b) := by
    intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      ((Real.continuous_sqrt.continuousAt.mul
              (((Real.continuousAt_log hp.ne').pow 2).div_const 24)).mul
          (three_shift_density_analytic hp).deriv.continuousAt.neg).continuousWithinAt
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
  apply
    MeasureTheory.norm_integral_le_of_norm_le
      (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht' := ha.trans ht.1.le
  have hp : 0 < t := by linarith only [ht']
  have hl := hla.trans (Real.log_le_log (by linarith only [ha]) ht.1.le)
  have hn := (three_shift_density_deriv_neg hp hl).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hn]
  exact mul_le_mul_of_nonneg_right (psi_log_sq_of_RH hRH ht') (neg_nonneg.mpr hn)

/-- The section 117 Euler weights are absolutely summable by the three
von Mangoldt logarithmic moments at exponent 38/25. -/
theorem three_shift_euler_summable :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
          threeShiftEulerPoly (Real.log n)) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
      (by norm_num only)
  have h :=
    (((hm 0).mul_left ((coeff117 0) - 5 * (coeff117 1) + 25 * (coeff117 2))).add
          ((hm 1).mul_left ((coeff117 1) - 10 * (coeff117 2)))).add
      ((hm 2).mul_left (coeff117 2))
  apply h.congr
  intro n
  rw [three_shift_euler_poly_expand]
  ring

/-- Under RH, a limit M for the main integral and an eventual upper bound D
for the explicit slope integral bound the full section 117 Euler tail. -/
theorem three_shift_euler_tail_RH (hRH : RiemannHypothesis) {a M D : ℝ} (ha : 101 ≤ a)
    (hl : 5 ≤ Real.log a)
    (hm :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, threeShiftEulerDensity t) Filter.atTop (nhds M))
    (hd :
      ∀ᶠ b : ℝ in Filter.atTop,
        (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity t) ≤
          D) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * threeShiftEulerPoly (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      M + Real.sqrt a * (Real.log a ^ 2 / 24) * threeShiftEulerDensity a + D := by
  intro f
  have hf0 : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_div, zero_mul]
  have hs :=
    (AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix f hf0 three_shift_euler_summable a).comp
      (show Filter.Tendsto (fun b : ℝ ↦ ⌊b⌋₊) Filter.atTop Filter.atTop from
        tendsto_nat_floor_atTop)
  have h :=
    (((hm.add three_shift_euler_boundary_zero).sub_const
          ((Chebyshev.psi a - a) * threeShiftEulerDensity a)).sub
      hs)
  rw [add_zero] at h
  have he :=
    h.congr'
      (show
        ∀ᶠ b : ℝ in Filter.atTop,
          _ = ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv threeShiftEulerDensity t
        from by
        filter_upwards [Filter.eventually_ge_atTop a] with b hb
        have hab := three_shift_euler_abel (by linarith only [ha]) hb
        dsimp only [Function.comp_apply, f]
        linarith only [hab])
  have hb :=
    ge_of_tendsto he
      (show
        ∀ᶠ b : ℝ in Filter.atTop,
          -D ≤ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv threeShiftEulerDensity t
        from by
        filter_upwards [hd, Filter.eventually_ge_atTop a] with b hb hab
        exact (abs_le.mp ((three_shift_euler_error_RH hRH ha hl hab).trans hb)).1)
  have hw : 0 ≤ threeShiftEulerDensity a :=
    mul_nonneg (Real.exp_pos _).le (three_shift_euler_poly_pos hl).le
  have hp := mul_le_mul_of_nonneg_right (abs_le.mp (psi_log_sq_of_RH hRH ha)).1 hw
  linarith only [hb, hp]

/-- The three coefficients of the main Euler moment. -/
noncomputable def mainCoeff117 : Fin 3 → ℝ :=
  ![(coeff117 0) - 5 * (coeff117 1) + 25 * (coeff117 2), (coeff117 1) - 10 * (coeff117 2),
    (coeff117 2)]

/-- Closed main tail at a lower endpoint, using the three logarithmic moments
with decay exponent 13/25. -/
noncomputable def threeShiftEulerMain (a : ℝ) : ℝ :=
  ∑ j : Fin 3, mainCoeff117 j * eulerMomentValue570 (13 / 25) j.val a

/-- The integral between endpoints at least one equals the difference of their
closed main tails. Expand the weight and integrate its three monomials. -/
theorem three_shift_main_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, threeShiftEulerDensity t) =
      threeShiftEulerMain a - threeShiftEulerMain b := by
  unfold threeShiftEulerMain
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply euler570_polynomial_interval (k := 0) (by norm_num only) ha hab
  intro t ht
  have ht0 := zero_lt_one.trans_le (ha.trans ht.1)
  rw [Fin.sum_univ_three]
  simp only [mainCoeff117, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  unfold eulerMoment570 threeShiftEulerDensity
  rw [three_shift_euler_poly_expand]
  rw [show -(13 / 25 : ℝ) - 1 = -(38 / 25 : ℝ) by norm_num only, Real.rpow_def_of_pos ht0,
    mul_comm (Real.log t) (-(38 / 25 : ℝ))]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  ring

/-- The main integral tends to the closed tail at its lower endpoint. Each
upper endpoint moment vanishes since the decay exponent is positive. -/
theorem three_shift_main_limit {a : ℝ} (ha : 1 ≤ a) :
    Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, threeShiftEulerDensity t) Filter.atTop
      (nhds (threeShiftEulerMain a)) := by
  have h (k : ℕ) : Filter.Tendsto (eulerMomentValue570 (13 / 25) k) Filter.atTop (nhds 0) := by
    change
      Filter.Tendsto
        (fun t : ℝ ↦ t ^ (-(13 / 25 : ℝ)) * Analysis.logPowerTailPoly (13 / 25) k (Real.log t)) _ _
    simpa only [eulerMomentValue570, neg_mul, neg_neg, neg_zero] using
      (Analysis.log_power_tail_primitive_tendsto (by norm_num only : (0 : ℝ) < 13 / 25) k).neg
  have hz :=
    (((h 0).const_mul (mainCoeff117 0)).add ((h 1).const_mul (mainCoeff117 1))).add
      ((h 2).const_mul (mainCoeff117 2))
  simp only [mul_zero, add_zero] at hz
  have hz' : Filter.Tendsto threeShiftEulerMain Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t ↦ threeShiftEulerMain t) _ _
    simp only [threeShiftEulerMain, Fin.sum_univ_three]
    exact hz
  have hh := hz'.const_sub (threeShiftEulerMain a)
  rw [sub_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact (three_shift_main_interval ha hb).symm

/-- The three coefficients of the Euler error moment. -/
noncomputable def errorCoeff117 : Fin 3 → ℝ :=
  ![(38 / 25 * mainCoeff117 0 - mainCoeff117 1) / 24,
    (38 / 25 * mainCoeff117 1 - 2 * mainCoeff117 2) / 24, (38 / 25 * mainCoeff117 2) / 24]

/-- Closed tail for the square-root log-square error majorant. -/
noncomputable def threeShiftEulerError (a : ℝ) : ℝ :=
  ∑ j : Fin 3, errorCoeff117 j * eulerMomentValue570 (51 / 50) (2 + j.val) a

/-- The RH error envelope integrates exactly to the difference of three
endpoint moments of degrees two, three and four. -/
theorem three_shift_error_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity t) =
      threeShiftEulerError a - threeShiftEulerError b := by
  unfold threeShiftEulerError
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp := zero_lt_one.trans_le (ha.trans ht.1)
  let C := mainCoeff117 0
  let L := mainCoeff117 1
  let Q := mainCoeff117 2
  rw [three_shift_density_deriv hp, threeShiftEulerSlope, Fin.sum_univ_three]
  rw [mul_comm (-(38 / 25 : ℝ)), ← Real.rpow_def_of_pos hp]
  change
    _ =
      ((38 / 25 * C - L) / 24) * eulerMoment570 _ 2 t +
        ((38 / 25 * L - 2 * Q) / 24) * eulerMoment570 _ 3 t +
        ((38 / 25 * Q) / 24) * eulerMoment570 _ 4 t
  have hpow : t ^ (-(38 / 25 : ℝ)) * t⁻¹ = t ^ (-(38 / 25 : ℝ) - 1) := by
    rw [Real.rpow_sub hp, Real.rpow_one, div_eq_mul_inv (t ^ _) t]
  have hs : Real.sqrt t * t ^ (-(38 / 25 : ℝ) - 1) = t ^ (-(51 / 50 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  unfold eulerMoment570
  rw [← hs, ← hpow]
  unfold C L Q mainCoeff117
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- Under RH, the common Euler tail above a cutoff at least 101 is bounded
by its main tail, its lower boundary error, and three explicit error moments. -/
theorem three_shift_tail_closed {a : ℝ} (hRH : RiemannHypothesis) (ha : 101 ≤ a)
    (hl : 5 ≤ Real.log a) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * threeShiftEulerPoly (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      threeShiftEulerMain a + Real.sqrt a * (Real.log a ^ 2 / 24) * threeShiftEulerDensity a +
        threeShiftEulerError a := by
  have ha1 : 1 ≤ a := by linarith only [ha]
  have hm (k : ℕ) : Filter.Tendsto (eulerMomentValue570 (51 / 50) k) Filter.atTop (nhds 0) := by
    change
      Filter.Tendsto
        (fun t : ℝ ↦ t ^ (-(51 / 50 : ℝ)) * Analysis.logPowerTailPoly (51 / 50) k (Real.log t)) _ _
    simpa only [neg_mul, neg_neg, neg_zero] using
      (Analysis.log_power_tail_primitive_tendsto (by norm_num only : (0 : ℝ) < 51 / 50) k).neg
  have hz :=
    (((hm 2).const_mul (errorCoeff117 0)).add ((hm 3).const_mul (errorCoeff117 1))).add
      ((hm 4).const_mul (errorCoeff117 2))
  simp only [mul_zero, add_zero] at hz
  have he : Filter.Tendsto threeShiftEulerError Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t ↦ threeShiftEulerError t) _ _
    simp only [threeShiftEulerError, Fin.sum_univ_three]
    exact hz
  intro f
  apply le_of_forall_pos_le_add
  intro ε hε
  have hh :=
    three_shift_euler_tail_RH (D := threeShiftEulerError a + ε) hRH ha hl
      (three_shift_main_limit ha1)
      (by
        filter_upwards [he.eventually (lt_mem_nhds (neg_lt_zero.mpr hε)),
          Filter.eventually_ge_atTop a] with b hb hab
        rw [three_shift_error_interval ha1 hab]
        linarith only [hb])
  dsimp only at hh
  dsimp only [f]
  linarith only [hh]

/-- Under RH and the three-character trace floor, the cosine Euler contribution
for the section 117 coefficients is at least minus four times the explicit cap. -/
theorem three_shift_cosine_tail_lower {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 85264 ≤ X) (hl : 5 ≤ Real.log X) (hRH : RiemannHypothesis)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let S := twoShiftCosineTail a b c X
    (-4 : ℝ) *
        (threeShiftEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * threeShiftEulerDensity X +
          threeShiftEulerError X) ≤
      3.143 * S (14 / 5) + (-3.124) * S (141 / 50) + (-0.0374) * S (39 / 10) +
        (-((3.143 ^ 2 + 3.124 ^ 2 + 0.0374 ^ 2) / 2)) * S 0 +
        (3.143 * 3.124) * S (1 / 50) +
        (3.143 * 0.0374) * S (11 / 10) +
        (-(3.124 * 0.0374)) * S (27 / 25) := by
  intro S
  dsimp only [S]
  rw [three_shift_euler_eq a b c hX]
  let f := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * threeShiftEulerPoly (Real.log n)
  let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
  have hs : Summable f := three_shift_euler_summable
  have hp := hs.sum_add_tsum_compl (s := Finset.Icc 0 ⌊X⌋₊)
  change
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, f n) + (∑' n : { n : ℕ // n ∉ Finset.Icc 0 ⌊X⌋₊ }, f n.val) =
      ∑' n, f n at hp
  have hpred : (fun n : ℕ ↦ n ∉ Finset.Icc 0 ⌊X⌋₊) = (fun n : ℕ ↦ ⌊X⌋₊ < n) := by
    funext n
    simp only [Finset.mem_Icc, Nat.zero_le, true_and, not_le]
  rw [hpred, ← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)] at hp
  have hf0 : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_div, zero_mul]
  rw [hf0, add_zero] at hp
  have hcap := three_shift_tail_closed hRH (by linarith only [hX]) hl
  dsimp only at hcap
  change (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n ≤ _ at hcap
  have hsub := (hs.subtype (fun n ↦ ⌊X⌋₊ < n)).mul_left (4 : ℝ)
  have hb (n : { n : ℕ // ⌊X⌋₊ < n }) :
    0 ≤ D n.val * f n.val ∧ D n.val * f n.val ≤ 4 * f n.val := by
    have hn := Nat.lt_of_floor_lt n.property
    have hlog := hl.trans (Real.log_le_log (by linarith only [hX]) hn.le)
    have hf : 0 ≤ f n.val :=
      mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (three_shift_euler_poly_pos hlog).le
    have hD : 0 ≤ D n.val := by
      dsimp only [D]
      linarith only [(Complex.re_le_norm _).trans (a.norm_le_one n.val),
        (Complex.re_le_norm _).trans (b.norm_le_one n.val),
        (Complex.re_le_norm _).trans (c.norm_le_one n.val)]
    have hu : D n.val ≤ 4 := by
      dsimp only [D]; linarith only [ht n.val]
    exact ⟨mul_nonneg hD hf, mul_le_mul_of_nonneg_right hu hf⟩
  have hD :=
    hsub.of_norm_bounded
      (fun n ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hb n).1]
        exact (hb n).2)
  have hsum := hD.tsum_le_tsum (fun n ↦ (hb n).2) hsub
  rw [tsum_mul_left] at hsum
  change _ ≤ -(∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val)
  linarith only [hp, hcap, hsum]

/-- In the logarithmic radius coordinate the main Euler tail has derivative
minus twice its polynomial density. -/
theorem three_shift_main_log_deriv (t : ℝ) :
    HasDerivAt (fun x : ℝ ↦ threeShiftEulerMain (Real.exp (2 * x)))
      (-2 * Real.exp (-(13 / 25) * (2 * t)) * threeShiftEulerPoly (2 * t)) t := by
  have hp : 0 < Real.exp (2 * t) := Real.exp_pos _
  have hm (k : ℕ) :
    HasDerivAt (fun x : ℝ ↦ eulerMomentValue570 (13 / 25) k (Real.exp (2 * x)))
      (-2 * Real.exp (-(13 / 25) * (2 * t)) * (2 * t) ^ k) t := by
    have h₁ :=
      (Analysis.log_power_tail_primitive_deriv (by norm_num only : (0 : ℝ) < 13 / 25) hp k).neg
    have h₂ := ((hasDerivAt_id t).const_mul (2 : ℝ)).exp
    have h := h₁.comp t h₂
    convert h using 1
    · funext x
      simp only [eulerMomentValue570, Function.comp_apply, Pi.neg_apply, id_eq, neg_mul, neg_neg]
    · have hpow :
        Real.exp (2 * t) ^ (-(13 / 25 : ℝ) - 1) * Real.exp (2 * t) =
          Real.exp (-(13 / 25) * (2 * t)) := by
        nth_rw 2 [← Real.rpow_one (Real.exp (2 * t))]
        rw [← Real.rpow_add hp, sub_add_cancel, Real.rpow_def_of_pos hp, Real.log_exp, mul_comm]
      simp only [id_eq, Real.log_exp, mul_one]
      linear_combination (norm := ring) (2 * (2 * t) ^ k) * hpow
  have h :=
    (((hm 0).const_mul (mainCoeff117 0)).add ((hm 1).const_mul (mainCoeff117 1))).add
      ((hm 2).const_mul (mainCoeff117 2))
  convert h using 1
  · funext x
    simp only [threeShiftEulerMain, Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two,
      Pi.add_apply]
  · rw [three_shift_euler_poly_expand]
    simp only [mainCoeff117, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, pow_zero, pow_one]
    ring

/-- The Euler polynomial exceeds fourteen at log cutoff 11.4 and above.
This controls the derivative contributed by the main tail. -/
theorem three_shift_euler_poly_gt14 {x : ℝ} (hx : 11.4 ≤ x) : 14 < threeShiftEulerPoly x := by
  obtain ⟨ha, hb, hc⟩ := coeff117_box
  have hy : 6.4 ≤ x - 5 := by linarith only [hx]
  have h₁ := mul_le_mul hb.1 hy (by norm_num only) (by linarith only [hb.1])
  have h₂ :=
    mul_le_mul hc.1 (pow_le_pow_left₀ (by norm_num only) hy 2) (by norm_num only)
      (by linarith only [hc.1])
  rw [three_shift_euler_poly_expand]
  linarith only [ha.1, h₁, h₂]

private theorem three_shift_poly_log_slope {x : ℝ} (hx : 10 ≤ x) :
    x * (coeff117 1 + 2 * coeff117 2 * (x - 5)) ≤ 4 * threeShiftEulerPoly x := by
  obtain ⟨ha, hb, hc⟩ := coeff117_box
  have hb0 : 0 ≤ coeff117 1 := by linarith only [hb.1]
  have hc0 : 0 ≤ coeff117 2 := by linarith only [hc.1]
  have hy : 0 ≤ x - 5 := by linarith only [hx]
  have hd : x ≤ 2 * (x - 5) := by linarith only [hx]
  have h :=
    mul_le_mul_of_nonneg_right hd
      (add_nonneg hb0 (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) hc0) hy))
  rw [three_shift_euler_poly_expand]
  nlinarith only [h, ha.1, mul_nonneg hb0 hy]

private theorem three_shift_boundary_log_eq (x : ℝ) :
    Real.sqrt (Real.exp x) * (Real.log (Real.exp x) ^ 2 / 24) *
        threeShiftEulerDensity (Real.exp x) =
      Real.exp (-(51 / 50) * x) * (x ^ 2 / 24) * threeShiftEulerPoly x := by
  rw [threeShiftEulerDensity, Real.log_exp, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos (Real.exp_pos x), Real.log_exp]
  have h : Real.exp (x * (1 / 2)) * Real.exp (-(38 / 25) * x) = Real.exp (-(51 / 50) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  linear_combination (norm := ring) (x ^ 2 / 24 * threeShiftEulerPoly x) * h

/-- The forward RH boundary envelope decreases above logarithmic cutoff ten. -/
theorem three_shift_boundary_antitone :
    AntitoneOn
      (fun x : ℝ ↦
        Real.sqrt (Real.exp x) * (Real.log (Real.exp x) ^ 2 / 24) *
          threeShiftEulerDensity (Real.exp x))
      (Set.Ici 10) := by
  simp only [three_shift_boundary_log_eq]
  have hd (x : ℝ) :=
    (((hasDerivAt_id x).const_mul (-(51 / 50 : ℝ))).exp.mul
          (((hasDerivAt_id x).pow 2).div_const 24)).mul
      (three_shift_poly_deriv x)
  apply
    antitoneOn_of_deriv_nonpos (convex_Ici _) (fun x _ ↦ (hd x).continuousAt.continuousWithinAt)
      (fun x _ ↦ (hd x).differentiableAt.differentiableWithinAt)
  intro x hx
  have hx' : 10 ≤ x := interior_subset hx
  rw [(hd x).deriv]
  norm_num only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one, Pi.pow_apply, Pi.mul_apply]
  have hs :=
    mul_le_mul_of_nonneg_left (three_shift_poly_log_slope hx') (show 0 ≤ x by linarith only [hx'])
  have hp := (three_shift_euler_poly_pos (show 5 ≤ x by linarith only [hx'])).le
  have h :=
    mul_nonpos_of_nonpos_of_nonneg (show 6 - (51 / 50 : ℝ) * x ≤ 0 by linarith only [hx'])
      (mul_nonneg (show 0 ≤ x by linarith only [hx']) hp)
  have hh := mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos (-(51 / 50) * x)).le h
  have hss := mul_le_mul_of_nonneg_left hs (Real.exp_pos (-(51 / 50) * x)).le
  linear_combination hh / 24 + hss / 24

/-- The main Euler contribution in logarithmic coordinates. -/
noncomputable def phaseEulerMainPoly117 (x : ℝ) : ℝ :=
  ∑ k : Fin 3, mainCoeff117 k * Analysis.logPowerTailPoly (13 / 25) k.val x

/-- The boundary and integrated slope contributions in logarithmic coordinates. -/
noncomputable def phaseEulerErrorPoly117 (x : ℝ) : ℝ :=
  x ^ 2 / 24 * threeShiftEulerPoly x +
    ∑ k : Fin 3, errorCoeff117 k * Analysis.logPowerTailPoly (51 / 50) (2 + k.val) x

/-- The forward Euler cap splits into two scaled logarithmic polynomials. -/
theorem phase_euler_log117 {t : ℝ} (ht : 0 < t) :
    threeShiftEulerMain t + Real.sqrt t * (Real.log t ^ 2 / 24) * threeShiftEulerDensity t +
        threeShiftEulerError t =
      Real.exp (-(13 / 25) * Real.log t) * phaseEulerMainPoly117 (Real.log t) +
        Real.exp (-(51 / 50) * Real.log t) * phaseEulerErrorPoly117 (Real.log t) := by
  unfold threeShiftEulerMain threeShiftEulerDensity threeShiftEulerError phaseEulerMainPoly117
    phaseEulerErrorPoly117
  simp_rw [forward_moment_scale ht, Finset.mul_sum]
  rw [show
      Real.sqrt t * (Real.log t ^ 2 / 24) *
          (Real.exp (-(38 / 25 : ℝ) * Real.log t) * threeShiftEulerPoly (Real.log t)) =
        (Real.sqrt t * Real.exp (-(38 / 25 : ℝ) * Real.log t)) *
          (Real.log t ^ 2 / 24 * threeShiftEulerPoly (Real.log t))
      by ring,
    forward_boundary_scale ht]
  simp only [mul_add, Fin.sum_univ_three]
  ring

private theorem moment_mul_upper117 {d l x h a A : ℝ} (hd : 0 < d) (hl : 0 ≤ l)
    (hx : x ∈ Set.Icc l h) (ha : a ≤ A) (k : ℕ) :
    a * Analysis.logPowerTailPoly d k x ≤
      A * Analysis.logPowerTailPoly d k (if 0 ≤ A then h else l) := by
  have h0 := Analysis.log_power_tail_poly_nonneg hd (hl.trans hx.1) k
  apply (mul_le_mul_of_nonneg_right ha h0).trans
  split_ifs with hA
  · exact mul_le_mul_of_nonneg_left (Analysis.log_power_tail_poly_mono hd (hl.trans hx.1) hx.2 k) hA
  · exact
      mul_le_mul_of_nonpos_left (Analysis.log_power_tail_poly_mono hd hl hx.1 k) (le_of_not_ge hA)

/-- Bound the main Euler polynomial using the signs of its three coefficients
and rational endpoints of the logarithmic argument. -/
theorem phase_euler_main_box117 {l x h : ℝ} (hl : 0 ≤ l) (hx : x ∈ Set.Icc l h) :
    phaseEulerMainPoly117 x ≤
      1.1790424 * Analysis.logPowerTailPoly (13 / 25) 0 h -
          0.91233941 * Analysis.logPowerTailPoly (13 / 25) 1 l +
        0.18022562 * Analysis.logPowerTailPoly (13 / 25) 2 h := by
  obtain ⟨hc, he, hq⟩ := coeff117_box
  have h0 : mainCoeff117 0 ≤ 1.1790424 := by
    change (coeff117 0) - 5 * (coeff117 1) + 25 * (coeff117 2) ≤ _
    linarith only [hc.2, he.1, hq.2]
  have h1 : mainCoeff117 1 ≤ -0.91233941 := by
    change (coeff117 1) - 10 * (coeff117 2) ≤ _
    linarith only [he.2, hq.1]
  have h2 : mainCoeff117 2 ≤ 0.18022562 := by
    change (coeff117 2) ≤ _
    linarith only [hq.2]
  have H0 := moment_mul_upper117 (by norm_num only : 0 < (13 / 25 : ℝ)) hl hx h0 0
  have H1 := moment_mul_upper117 (by norm_num only : 0 < (13 / 25 : ℝ)) hl hx h1 1
  have H2 := moment_mul_upper117 (by norm_num only : 0 < (13 / 25 : ℝ)) hl hx h2 2
  unfold phaseEulerMainPoly117
  norm_num only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, ite_eq_left,
    ite_eq_right, show (0 : ℝ) ≤ 1.1790424 by norm_num only,
    show ¬(0 : ℝ) ≤ -0.91233941 by norm_num only,
    show (0 : ℝ) ≤ 0.18022562 by norm_num only] at H0 H1 H2 ⊢
  linarith only [H0, H1, H2]

/-- Bound the forward error polynomial by evaluating its boundary factor and
the three signed moments at the appropriate rational endpoints. -/
theorem phase_euler_error_box117 {l x h : ℝ} (hl : 5 ≤ l) (hx : x ∈ Set.Icc l h) :
    phaseEulerErrorPoly117 x ≤
      h ^ 2 / 24 * (1.12297010 + 0.88991178 * (h - 5) + 0.18022522 * (h - 5) ^ 2) +
            0.11268722 * Analysis.logPowerTailPoly (51 / 50) 2 h -
          0.07279988 * Analysis.logPowerTailPoly (51 / 50) 3 l +
        0.01141467 * Analysis.logPowerTailPoly (51 / 50) 4 h := by
  obtain ⟨hc, he, hq⟩ := coeff117_box
  have h0 : errorCoeff117 0 ≤ 0.11268722 := by
    change
      (38 / 25 * ((coeff117 0) - 5 * (coeff117 1) + 25 * (coeff117 2)) -
            ((coeff117 1) - 10 * (coeff117 2))) /
          24 ≤
        _
    linarith only [hc.2, he.1, hq.2]
  have h1 : errorCoeff117 1 ≤ -0.07279988 := by
    change (38 / 25 * ((coeff117 1) - 10 * (coeff117 2)) - 2 * (coeff117 2)) / 24 ≤ _
    linarith only [he.2, hq.1]
  have h2 : errorCoeff117 2 ≤ 0.01141467 := by
    change (38 / 25 * (coeff117 2)) / 24 ≤ _
    linarith only [hq.2]
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hx0 := hl0.trans hx.1
  have hxh : 0 ≤ x - 5 := sub_nonneg.mpr (hl.trans hx.1)
  have hshift : x - 5 ≤ h - 5 := sub_le_sub_right hx.2 _
  have hP :
    threeShiftEulerPoly x ≤ 1.12297010 + 0.88991178 * (h - 5) + 0.18022522 * (h - 5) ^ 2 := by
    rw [three_shift_euler_poly_expand]
    have h₁ := mul_le_mul he.2 hshift hxh (by norm_num only)
    have h₂ := mul_le_mul hq.2 (pow_le_pow_left₀ hxh hshift 2) (sq_nonneg _) (by norm_num only)
    linarith only [hc.2, h₁, h₂]
  have hboundary :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx.2 2)
      (three_shift_euler_poly_pos (hl.trans hx.1)).le
  have hboundary' := mul_le_mul_of_nonneg_left hP (sq_nonneg h)
  have H0 := moment_mul_upper117 (by norm_num only : 0 < (51 / 50 : ℝ)) hl0 hx h0 2
  have H1 := moment_mul_upper117 (by norm_num only : 0 < (51 / 50 : ℝ)) hl0 hx h1 3
  have H2 := moment_mul_upper117 (by norm_num only : 0 < (51 / 50 : ℝ)) hl0 hx h2 4
  unfold phaseEulerErrorPoly117
  norm_num only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd,
    ite_eq_left, ite_eq_right, show (0 : ℝ) ≤ 0.11268722 by norm_num only,
    show ¬(0 : ℝ) ≤ -0.07279988 by norm_num only,
    show (0 : ℝ) ≤ 0.01141467 by norm_num only] at H0 H1 H2 ⊢
  linarith only [H0, H1, H2, hboundary, hboundary']

private theorem euler_cost_box117 {X m e M E : ℝ} (hX : 0 < X)
    (hm : Real.exp (-(13 / 25) * Real.log X) ≤ m) (he : Real.exp (-(51 / 50) * Real.log X) ≤ e)
    (hM : phaseEulerMainPoly117 (Real.log X) ≤ M) (hE : phaseEulerErrorPoly117 (Real.log X) ≤ E)
    (hM0 : 0 ≤ M) (hE0 : 0 ≤ E) :
    threeShiftEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * threeShiftEulerDensity X +
        threeShiftEulerError X ≤
      m * M + e * E := by
  rw [phase_euler_log117 hX]
  exact
    add_le_add
      ((mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right hm hM0))
      ((mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right he hE0))

/-- The forward Euler cap at radius 314 is bounded by this rational endpoint value. -/
theorem section117_euler_cost_314 :
    let X := (314 : ℝ) ^ 2
    threeShiftEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * threeShiftEulerDensity X +
        threeShiftEulerError X ≤
      10930554 / 10 ^ 8 := by
  dsimp only
  have hl : Real.log ((314 : ℝ) ^ 2) = 2 * Real.log (314) := by rw [Real.log_pow, Nat.cast_ofNat]
  have hx := section117_log_box_314
  obtain ⟨hm, he, _, _⟩ := section117_exp_box_314
  rw [← hl] at hx hm he
  have hM := phase_euler_main_box117 (by norm_num only) hx
  have hE := phase_euler_error_box117 (by norm_num only) hx
  refine
      (euler_cost_box117 (M := 42437041 / 10 ^ 6) (E := 238482143 / 10 ^ 6) (by norm_num only) hm.2
            he.2 (hM.trans ?_) (hE.trans ?_) (by norm_num only) (by norm_num only)).trans
        ?_ <;>
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      Nat.reduceAdd]

/-- The forward Euler cap at radius 314.45 is bounded by this rational endpoint value. -/
theorem section117_euler_cost_314_45 :
    let X := (6289 / 20 : ℝ) ^ 2
    threeShiftEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * threeShiftEulerDensity X +
        threeShiftEulerError X ≤
      10919682 / 10 ^ 8 := by
  dsimp only
  have hl : Real.log ((6289 / 20 : ℝ) ^ 2) = 2 * Real.log (6289 / 20) := by
    rw [Real.log_pow, Nat.cast_ofNat]
  have hx := section117_log_box_314_45
  obtain ⟨hm, he, _, _⟩ := section117_exp_box_314_45
  rw [← hl] at hx hm he
  have hM := phase_euler_main_box117 (by norm_num only) hx
  have hE := phase_euler_error_box117 (by norm_num only) hx
  refine
      (euler_cost_box117 (M := 42458666 / 10 ^ 6) (E := 238738919 / 10 ^ 6) (by norm_num only) hm.2
            he.2 (hM.trans ?_) (hE.trans ?_) (by norm_num only) (by norm_num only)).trans
        ?_ <;>
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      Nat.reduceAdd]

/-- The forward Euler cap at radius 315 is bounded by this rational endpoint value. -/
theorem section117_euler_cost_315 :
    let X := (315 : ℝ) ^ 2
    threeShiftEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * threeShiftEulerDensity X +
        threeShiftEulerError X ≤
      10906428 / 10 ^ 8 := by
  dsimp only
  have hl : Real.log ((315 : ℝ) ^ 2) = 2 * Real.log (315) := by rw [Real.log_pow, Nat.cast_ofNat]
  have hx := section117_log_box_315
  obtain ⟨hm, he, _, _⟩ := section117_exp_box_315
  rw [← hl] at hx hm he
  have hM := phase_euler_main_box117 (by norm_num only) hx
  have hE := phase_euler_error_box117 (by norm_num only) hx
  refine
      (euler_cost_box117 (M := 42485063 / 10 ^ 6) (E := 239052539 / 10 ^ 6) (by norm_num only) hm.2
            he.2 (hM.trans ?_) (hE.trans ?_) (by norm_num only) (by norm_num only)).trans
        ?_ <;>
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      Nat.reduceAdd]

end PseudoPrime.PrimeTestBounds.MillerRabin
