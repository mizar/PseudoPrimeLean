/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosine644
import PseudoPrime.Analysis.ExponentialFixedPointBounds
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerTail644
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevBoundary43
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerError570
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWeightedMoments
import all PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Paired Euler polynomial for the three-frequency comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The paired exponential-quadratic profile at shift s with the common
exponential decay removed. It is quadratic in the logarithmic argument. -/
noncomputable def weightedShiftPoly644 (s x : ℝ) : ℝ :=
  let a : ℝ := 107 / 100
  let q := fun z : ℝ ↦ 3 / 8 + 3 * a / 8 * z + a ^ 2 / 8 * z ^ 2
  (Real.exp (-a * s) * q (x + s) + Real.exp (a * s) * q (x - s)) / 2

/-- The negative of the signed combination of all six shifted pairs and
the diagonal pair. This is the section 122 Euler polynomial P. -/
noncomputable def threeShiftEulerPoly644 (x : ℝ) : ℝ :=
  ((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2) * weightedShiftPoly644 0 x -
          (1.54 * 1.508) * weightedShiftPoly644 (1 / 50) x -
          (1.54 * 0.0917) * weightedShiftPoly644 (11 / 10) x +
        (1.508 * 0.0917) * weightedShiftPoly644 (27 / 25) x -
      1.54 * weightedShiftPoly644 (2687 / 1000) x +
    1.508 * weightedShiftPoly644 (2707 / 1000) x +
    0.0917 * weightedShiftPoly644 (3787 / 1000) x

private noncomputable def shift644Coeff (s : ℝ) (k : ℕ) : ℝ :=
  let a : ℝ := 107 / 100
  let C (y : ℝ) :=
    if k = 0 then 3 / 8 + 3 * a / 8 * y + a ^ 2 / 8 * y ^ 2
    else if k = 1 then 3 * a / 8 + a ^ 2 / 4 * y else a ^ 2 / 8
  (Real.exp (-(a * s)) * C (5 + s) + Real.exp (a * s) * C (5 - s)) / 2

private noncomputable def coeff644 (k : ℕ) : ℝ :=
  ((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2) * shift644Coeff 0 k -
          (1.54 * 1.508) * shift644Coeff (1 / 50) k -
          (1.54 * 0.0917) * shift644Coeff (11 / 10) k +
        (1.508 * 0.0917) * shift644Coeff (27 / 25) k -
      1.54 * shift644Coeff (2687 / 1000) k +
    1.508 * shift644Coeff (2707 / 1000) k +
    0.0917 * shift644Coeff (3787 / 1000) k

private theorem shift122_exp_box {x l u : ℝ} (hx : 0 ≤ x) (hs : x / 33 ≤ 1 / 2)
    (hl : l ≤ ∑ k ∈ Finset.range 32, x ^ k / (k.factorial : ℝ))
    (hu :
      (∑ k ∈ Finset.range 32, x ^ k / (k.factorial : ℝ)) + (x ^ 32 / ((32 : ℕ).factorial : ℝ)) * 2 ≤
        u) :
    l ≤ Real.exp x ∧ Real.exp x ≤ u := by
  exact
    ⟨hl.trans (Real.sum_le_exp_of_nonneg hx _),
      (Analysis.exp_le_taylor_add_two_next (x := x) (n := 32) hx hs).trans hu⟩

private theorem shift122_inv_box {x l u : ℝ} (hl : 0 < l) (h : l ≤ Real.exp x ∧ Real.exp x ≤ u) :
    1 / u ≤ Real.exp (-x) ∧ Real.exp (-x) ≤ 1 / l := by
  rw [Real.exp_neg, ← one_div]
  exact ⟨one_div_le_one_div_of_le (Real.exp_pos _) h.2, one_div_le_one_div_of_le hl h.1⟩

private theorem coeff644_box :
    coeff644 0 ∈ Set.Icc 2.535445 2.535446 ∧
      coeff644 1 ∈ Set.Icc 1.893980 1.893981 ∧ coeff644 2 ∈ Set.Icc 0.377293 0.377294 := by
  have h0 :=
    shift122_exp_box (x := (107 / 100) * (1 / 50)) (l := 1021630622165 / 10 ^ 12) (u :=
      1021630622168 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j0 := shift122_inv_box (by norm_num only) h0
  have h1 :=
    shift122_exp_box (x := (107 / 100) * (11 / 10)) (l := 3244625710330 / 10 ^ 12) (u :=
      3244625710333 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j1 := shift122_inv_box (by norm_num only) h1
  have h2 :=
    shift122_exp_box (x := (107 / 100) * (27 / 25)) (l := 3175928403015 / 10 ^ 12) (u :=
      3175928403018 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j2 := shift122_inv_box (by norm_num only) h2
  have h3 :=
    shift122_exp_box (x := (107 / 100) * (2687 / 1000)) (l := 17727019481421 / 10 ^ 12) (u :=
      17727019481424 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j3 := shift122_inv_box (by norm_num only) h3
  have h4 :=
    shift122_exp_box (x := (107 / 100) * (2707 / 1000)) (l := 18110465941968 / 10 ^ 12) (u :=
      18110465941971 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j4 := shift122_inv_box (by norm_num only) h4
  have h5 :=
    shift122_exp_box (x := (107 / 100) * (3787 / 1000)) (l := 57517543176965 / 10 ^ 12) (u :=
      57517543176968 / 10 ^ 12) (by norm_num only) (by norm_num only)
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
      (by
        norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
          Nat.cast_one, Nat.cast_zero])
  have j5 := shift122_inv_box (by norm_num only) h5
  unfold coeff644 shift644Coeff
  norm_num only [Set.mem_Icc, ite_true, ite_false, mul_zero, neg_zero, Real.exp_zero, one_mul]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
    linarith only [h0.1, h0.2, j0.1, j0.2, h1.1, h1.2, j1.1, j1.2, h2.1, h2.2, j2.1, j2.2, h3.1,
      h3.2, j3.1, j3.2, h4.1, h4.2, j4.1, j4.2, h5.1, h5.2, j5.1, j5.2]

/-- The section 644 Euler weight is quadratic in the translated variable x-5. -/
private theorem three_shift_euler_poly_expand644 (x : ℝ) :
    threeShiftEulerPoly644 x = coeff644 0 + coeff644 1 * (x - 5) + coeff644 2 * (x - 5) ^ 2 := by
  unfold threeShiftEulerPoly644 weightedShiftPoly644 coeff644 shift644Coeff
  norm_num only [ite_true, ite_false, neg_mul]
  ring

/-- The three coefficients of the Euler weight in the basis 1, x-5, (x-5)^2
are positive, so the weight can be used with a common trace deficit. -/
theorem three_shift_euler_poly_pos644 {x : ℝ} (hx : 5 ≤ x) : 0 < threeShiftEulerPoly644 x := by
  obtain ⟨ha, hb, hc⟩ := coeff644_box
  rw [three_shift_euler_poly_expand644]
  have h₁ := mul_nonneg (show 0 ≤ coeff644 1 by linarith only [hb.1]) (sub_nonneg.mpr hx)
  have h₂ := mul_nonneg (show 0 ≤ coeff644 2 by linarith only [hc.1]) (sq_nonneg (x - 5))
  linarith only [ha.1, h₁, h₂]

/-- At logarithmic prime power argument x, the slope polynomial is the
factor in the negative derivative of the section 644 Euler weight. -/
noncomputable def threeShiftEulerSlope644 (x : ℝ) : ℝ :=
  (157 / 100 * coeff644 0 - coeff644 1) + (157 / 100 * coeff644 1 - 2 * coeff644 2) * (x - 5) +
    (157 / 100 * coeff644 2) * (x - 5) ^ 2

/-- The slope polynomial is positive on the logarithmic Euler tail. -/
theorem three_shift_euler_slope_pos644 {x : ℝ} (hx : 5 ≤ x) : 0 < threeShiftEulerSlope644 x := by
  obtain ⟨ha, hb, hc⟩ := coeff644_box
  unfold threeShiftEulerSlope644
  have h₁ :=
    mul_nonneg (show 0 ≤ 157 / 100 * coeff644 1 - 2 * coeff644 2 by linarith only [hb.1, hc.2])
      (sub_nonneg.mpr hx)
  have h₂ :=
    mul_nonneg (show 0 ≤ 157 / 100 * coeff644 2 by linarith only [hc.1]) (sq_nonneg (x - 5))
  linarith only [ha.1, hb.2, h₁, h₂]

private theorem three_shift_poly_deriv644 (x : ℝ) :
    HasDerivAt threeShiftEulerPoly644 (coeff644 1 + 2 * coeff644 2 * (x - 5)) x := by
  have h := (hasDerivAt_id x).sub_const 5
  have H :=
    ((h.const_mul (coeff644 1)).const_add (coeff644 0)).add ((h.pow 2).const_mul (coeff644 2))
  rw [show
      threeShiftEulerPoly644 =
        (fun y : ℝ ↦ coeff644 0 + coeff644 1 * (y - 5) + coeff644 2 * (y - 5) ^ 2)
      from funext three_shift_euler_poly_expand644]
  change
    HasDerivAt (fun y : ℝ ↦ coeff644 0 + coeff644 1 * (y - 5) + coeff644 2 * (y - 5) ^ 2) _ x at H
  convert H using 1
  norm_num only [id, Nat.cast_ofNat]
  ring

/-- The section 644 Euler density is the quadratic weight in log t multiplied
by t to the power -157/100, as used for partial summation over the prime powers. -/
noncomputable def threeShiftEulerDensity644 (t : ℝ) : ℝ :=
  Real.exp (-(157 / 100 : ℝ) * Real.log t) * threeShiftEulerPoly644 (Real.log t)

/-- Differentiating the section 644 Euler density at t > 0 yields the
logarithmic slope polynomial with a negative sign and a reciprocal factor. -/
theorem three_shift_density_deriv644 {t : ℝ} (ht : 0 < t) :
    deriv threeShiftEulerDensity644 t =
      -(Real.exp (-(157 / 100 : ℝ) * Real.log t) * threeShiftEulerSlope644 (Real.log t)) * t⁻¹ := by
  let x := Real.log t
  have he := ((hasDerivAt_id x).const_mul (-(157 / 100 : ℝ))).exp
  have h := (he.mul (three_shift_poly_deriv644 x)).comp t (Real.hasDerivAt_log ht.ne')
  change HasDerivAt threeShiftEulerDensity644 _ t at h
  rw [h.deriv, threeShiftEulerSlope644, three_shift_euler_poly_expand644 x]
  dsimp only [id, x]
  ring

/-- The signed Abel slope is negative on the prime-power tail above exp 5. -/
theorem three_shift_density_deriv_neg644 {t : ℝ} (ht : 0 < t) (hl : 5 ≤ Real.log t) :
    deriv threeShiftEulerDensity644 t < 0 := by
  rw [three_shift_density_deriv644 ht]
  exact
    mul_neg_of_neg_of_pos
      (neg_neg_of_pos (mul_pos (Real.exp_pos _) (three_shift_euler_slope_pos644 hl)))
      (inv_pos.mpr ht)

/-- The forward and reflected inverse transforms at shift `s` combine
to the shifted quadratic times the common exponential when `log k ≥ s`. -/
theorem quarter_paired_profile_644 {k s : ℝ} (hk : 0 < k) (hs : 0 ≤ s) (hsk : s ≤ Real.log k) :
    (quarterSymmetricMellin644.transform (k * Real.exp (-s))).re +
        (quarterSymmetricMellin644.transform (k⁻¹ * Real.exp (-s))).re =
      Real.exp (-(107 / 100) * Real.log k) * weightedShiftPoly644 s (Real.log k) := by
  rw [quarter_symmetric_transform_644 (mul_pos hk (Real.exp_pos _)),
    quarter_symmetric_transform_644 (mul_pos (inv_pos.mpr hk) (Real.exp_pos _))]
  simp only [Complex.ofReal_re, Real.log_mul hk.ne' (Real.exp_ne_zero _),
    Real.log_mul (inv_pos.mpr hk).ne' (Real.exp_ne_zero _), Real.log_exp, Real.log_inv]
  rw [abs_of_nonneg (by linarith only [hsk] : 0 ≤ Real.log k + -s),
    abs_of_nonpos (by linarith only [hs, hsk] : -Real.log k + -s ≤ 0)]
  unfold weightedShiftPoly644
  rw [show -(107 / 100 : ℝ) * (Real.log k + -s) = -(107 / 100) * Real.log k + (107 / 100) * s by
      ring,
    show -(107 / 100 : ℝ) * -(-Real.log k + -s) = -(107 / 100) * Real.log k + -(107 / 100) * s by
      ring,
    Real.exp_add, Real.exp_add]
  ring

/-- Above logarithmic argument five, the signed seven-term profile
combination equals the negative auxiliary Euler polynomial times the
common decay. All cross terms are included. -/
theorem quarter_cosine_euler_poly_644 {k : ℝ} (hk : 0 < k) (hl : 5 ≤ Real.log k) :
    let D := fun s : ℝ ↦
      (quarterSymmetricMellin644.transform (k * Real.exp (-s))).re +
        (quarterSymmetricMellin644.transform (k⁻¹ * Real.exp (-s))).re
    1.54 * D (2687 / 1000) - 1.508 * D (2707 / 1000) - 0.0917 * D (3787 / 1000) -
            ((1.54 ^ 2 + 1.508 ^ 2 + 0.0917 ^ 2) / 2) * D 0 +
          1.54 * 1.508 * D (1 / 50) +
          1.54 * 0.0917 * D (11 / 10) -
        1.508 * 0.0917 * D (27 / 25) =
      -(Real.exp (-(107 / 100) * Real.log k) * threeShiftEulerPoly644 (Real.log k)) := by
  intro D
  have hp {s : ℝ} (hs : 0 ≤ s) (hu : s ≤ 5) :
    D s = Real.exp (-(107 / 100) * Real.log k) * weightedShiftPoly644 s (Real.log k) :=
    quarter_paired_profile_644 hk hs (hu.trans hl)
  rw [hp (s := 2687 / 1000) (by norm_num only) (by norm_num only),
    hp (s := 2707 / 1000) (by norm_num only) (by norm_num only),
    hp (s := 3787 / 1000) (by norm_num only) (by norm_num only),
    hp (s := 0) (by norm_num only) (by norm_num only),
    hp (s := 1 / 50) (by norm_num only) (by norm_num only),
    hp (s := 11 / 10) (by norm_num only) (by norm_num only),
    hp (s := 27 / 25) (by norm_num only) (by norm_num only)]
  unfold threeShiftEulerPoly644
  ring

private theorem three_shift_density_analytic644 {t : ℝ} (ht : 0 < t) :
    AnalyticAt ℝ threeShiftEulerDensity644 t := by
  unfold threeShiftEulerDensity644 threeShiftEulerPoly644 weightedShiftPoly644
  fun_prop (disch := exact ht.ne')

/-- On a positive finite interval, centered Abel summation expresses the
section 122 Euler sum by its main integral, endpoint errors, and derivative integral. -/
theorem three_shift_euler_abel644 {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (157 / 100 : ℝ) *
            threeShiftEulerPoly644 (Real.log n)) -
        (∫ t : ℝ in a..b, threeShiftEulerDensity644 t) =
      (Chebyshev.psi b - b) * threeShiftEulerDensity644 b -
        (Chebyshev.psi a - a) * threeShiftEulerDensity644 a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv threeShiftEulerDensity644 t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := three_shift_density_analytic644 (ha.trans_le ht.1)
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt)
      (show ContinuousOn (deriv threeShiftEulerDensity644) (Set.Icc a b) from fun t ht ↦
          (hd t ht).deriv.continuousAt.continuousWithinAt).integrableOn_Icc
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  rw [threeShiftEulerDensity644, Real.rpow_def_of_pos hp, neg_mul, mul_comm (157 / 100 : ℝ),
    Real.exp_neg]
  ring

/-- The section 122 Euler weights are absolutely summable by the three
von Mangoldt logarithmic moments at exponent 157/100. -/
theorem three_shift_euler_summable644 :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (157 / 100 : ℝ) *
          threeShiftEulerPoly644 (Real.log n)) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 157 / 100)
      (by norm_num only)
  have h :=
    (((hm 0).mul_left ((coeff644 0) - 5 * (coeff644 1) + 25 * (coeff644 2))).add
          ((hm 1).mul_left ((coeff644 1) - 10 * (coeff644 2)))).add
      ((hm 2).mul_left (coeff644 2))
  apply h.congr
  intro n
  rw [three_shift_euler_poly_expand644]
  ring

/-- The upper centered Abel boundary for the section 122 weight goes to zero
because its quadratic logarithmic moments decay against the unconditional psi bound. -/
theorem three_shift_euler_boundary_zero644 :
    Filter.Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - x) * threeShiftEulerDensity644 x) Filter.atTop
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
    AnalyticNumberTheory.RiemannZeta.moment_boundary_tendsto
      (by norm_num only : (1 : ℝ) < 157 / 100) k E hE
  let C := (coeff644 0) - 5 * (coeff644 1) + 25 * (coeff644 2)
  let L := (coeff644 1) - 10 * (coeff644 2)
  let Q := (coeff644 2)
  have hh :=
    ((((hm 0).const_mul (4 * C)).add ((hm 1).const_mul (4 * L))).add ((hm 2).const_mul (4 * Q)))
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, E, threeShiftEulerDensity644, C,
    L, Q]
  rw [three_shift_euler_poly_expand644]
  rw [Real.rpow_def_of_pos hx]
  rw [show Real.log x * -(157 / 100 : ℝ) = -(157 / 100 : ℝ) * Real.log x by ring]
  ring

private noncomputable def mainCoeff644 : Fin 3 → ℝ :=
  ![(coeff644 0) - 5 * (coeff644 1) + 25 * (coeff644 2), (coeff644 1) - 10 * (coeff644 2),
    (coeff644 2)]

/-- Closed main tail at a lower endpoint, using the three logarithmic moments
with decay exponent 57/100. -/
noncomputable def threeShiftEulerMain644 (a : ℝ) : ℝ :=
  ∑ j : Fin 3, mainCoeff644 j * eulerMomentValue570 (57 / 100) j.val a

/-- The integral between endpoints at least one equals the difference of their
closed main tails. Expand the weight and integrate its three monomials. -/
theorem three_shift_main_interval644 {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, threeShiftEulerDensity644 t) =
      threeShiftEulerMain644 a - threeShiftEulerMain644 b := by
  unfold threeShiftEulerMain644
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply euler570_polynomial_interval (k := 0) (by norm_num only) ha hab
  intro t ht
  have ht0 := zero_lt_one.trans_le (ha.trans ht.1)
  rw [Fin.sum_univ_three]
  simp only [mainCoeff644, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]
  unfold eulerMoment570 threeShiftEulerDensity644
  rw [three_shift_euler_poly_expand644]
  rw [show -(57 / 100 : ℝ) - 1 = -(157 / 100 : ℝ) by norm_num only, Real.rpow_def_of_pos ht0,
    mul_comm (Real.log t) (-(157 / 100 : ℝ))]
  norm_num only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one]
  ring

/-- The main integral tends to the closed tail at its lower endpoint. Each
upper endpoint moment vanishes since the decay exponent is positive. -/
theorem three_shift_main_limit644 {a : ℝ} (ha : 1 ≤ a) :
    Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, threeShiftEulerDensity644 t) Filter.atTop
      (nhds (threeShiftEulerMain644 a)) := by
  have h (k : ℕ) : Filter.Tendsto (eulerMomentValue570 (57 / 100) k) Filter.atTop (nhds 0) := by
    change
      Filter.Tendsto
        (fun t : ℝ ↦ t ^ (-(57 / 100 : ℝ)) * Analysis.logPowerTailPoly (57 / 100) k (Real.log t)) _
        _
    simpa only [eulerMomentValue570, neg_mul, neg_neg, neg_zero] using
      (Analysis.log_power_tail_primitive_tendsto (by norm_num only : (0 : ℝ) < 57 / 100) k).neg
  have hz :=
    (((h 0).const_mul (mainCoeff644 0)).add ((h 1).const_mul (mainCoeff644 1))).add
      ((h 2).const_mul (mainCoeff644 2))
  simp only [mul_zero, add_zero] at hz
  have hz' : Filter.Tendsto threeShiftEulerMain644 Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t ↦ threeShiftEulerMain644 t) _ _
    simp only [threeShiftEulerMain644, Fin.sum_univ_three]
    exact hz
  have hh := hz'.const_sub (threeShiftEulerMain644 a)
  rw [sub_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact (three_shift_main_interval644 ha hb).symm

private noncomputable def errorCoeff117 : Fin 3 → ℝ :=
  ![(157 / 100 * mainCoeff644 0 - mainCoeff644 1) / 24,
    (157 / 100 * mainCoeff644 1 - 2 * mainCoeff644 2) / 24, (157 / 100 * mainCoeff644 2) / 24]

/-- RH bounds the centered finite Abel error by its explicit square-root
envelope wherever the section 122 Euler density is decreasing. -/
theorem three_shift_euler_error_RH_644 (hRH : RiemannHypothesis) {a b : ℝ} (ha : 101 ≤ a)
    (hla : 5 ≤ Real.log a) (hab : a ≤ b) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv threeShiftEulerDensity644 t| ≤
      ∫ t : ℝ in a..b,
        Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity644 t := by
  have hcont :
    ContinuousOn
      (fun t : ℝ ↦ Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity644 t)
      (Set.Icc a b) := by
    intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      ((Real.continuous_sqrt.continuousAt.mul
              (((Real.continuousAt_log hp.ne').pow 2).div_const 24)).mul
          (three_shift_density_analytic644 hp).deriv.continuousAt.neg).continuousWithinAt
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
  apply
    MeasureTheory.norm_integral_le_of_norm_le
      (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht' := ha.trans ht.1.le
  have hp : 0 < t := by linarith only [ht']
  have hl := hla.trans (Real.log_le_log (by linarith only [ha]) ht.1.le)
  have hn := (three_shift_density_deriv_neg644 hp hl).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hn]
  exact mul_le_mul_of_nonneg_right (psi_log_sq_of_RH hRH ht') (neg_nonneg.mpr hn)

/-- Under RH, a limit M for the main integral and an eventual upper bound D
for the explicit slope integral bound the full section 122 Euler tail. -/
theorem three_shift_euler_tail_RH_644 (hRH : RiemannHypothesis) {a M D : ℝ} (ha : 101 ≤ a)
    (hl : 5 ≤ Real.log a)
    (hm :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, threeShiftEulerDensity644 t) Filter.atTop
        (nhds M))
    (hd :
      ∀ᶠ b : ℝ in Filter.atTop,
        (∫ t : ℝ in a..b,
            Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity644 t) ≤
          D) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (157 / 100 : ℝ) *
        threeShiftEulerPoly644 (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      M + Real.sqrt a * (Real.log a ^ 2 / 24) * threeShiftEulerDensity644 a + D := by
  intro f
  have hf0 : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_div, zero_mul]
  have hs :=
    (AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix f hf0 three_shift_euler_summable644 a).comp
      (show Filter.Tendsto (fun b : ℝ ↦ ⌊b⌋₊) Filter.atTop Filter.atTop from
        tendsto_nat_floor_atTop)
  have h :=
    (((hm.add three_shift_euler_boundary_zero644).sub_const
          ((Chebyshev.psi a - a) * threeShiftEulerDensity644 a)).sub
      hs)
  rw [add_zero] at h
  have he :=
    h.congr'
      (show
        ∀ᶠ b : ℝ in Filter.atTop,
          _ = ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv threeShiftEulerDensity644 t
        from by
        filter_upwards [Filter.eventually_ge_atTop a] with b hb
        have hab := three_shift_euler_abel644 (by linarith only [ha]) hb
        dsimp only [Function.comp_apply, f]
        linarith only [hab])
  have hb :=
    ge_of_tendsto he
      (show
        ∀ᶠ b : ℝ in Filter.atTop,
          -D ≤ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv threeShiftEulerDensity644 t
        from by
        filter_upwards [hd, Filter.eventually_ge_atTop a] with b hb hab
        exact (abs_le.mp ((three_shift_euler_error_RH_644 hRH ha hl hab).trans hb)).1)
  have hw : 0 ≤ threeShiftEulerDensity644 a :=
    mul_nonneg (Real.exp_pos _).le (three_shift_euler_poly_pos644 hl).le
  have hp := mul_le_mul_of_nonneg_right (abs_le.mp (psi_log_sq_of_RH hRH ha)).1 hw
  linarith only [hb, hp]

private noncomputable def errorCoeff644 : Fin 3 → ℝ :=
  ![(157 / 100 * mainCoeff644 0 - mainCoeff644 1) / 24,
    (157 / 100 * mainCoeff644 1 - 2 * mainCoeff644 2) / 24, (157 / 100 * mainCoeff644 2) / 24]

/-- Closed tail for the square-root log-square error majorant. -/
noncomputable def threeShiftEulerError_644 (a : ℝ) : ℝ :=
  ∑ j : Fin 3, errorCoeff644 j * eulerMomentValue570 (107 / 100) (2 + j.val) a

/-- The RH error envelope integrates exactly to the difference of three
endpoint moments of degrees two, three and four. -/
theorem three_shift_error_interval_644 {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv threeShiftEulerDensity644 t) =
      threeShiftEulerError_644 a - threeShiftEulerError_644 b := by
  unfold threeShiftEulerError_644
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp := zero_lt_one.trans_le (ha.trans ht.1)
  let C := mainCoeff644 0
  let L := mainCoeff644 1
  let Q := mainCoeff644 2
  rw [three_shift_density_deriv644 hp, threeShiftEulerSlope644, Fin.sum_univ_three]
  rw [mul_comm (-(157 / 100 : ℝ)), ← Real.rpow_def_of_pos hp]
  change
    _ =
      ((157 / 100 * C - L) / 24) * eulerMoment570 _ 2 t +
        ((157 / 100 * L - 2 * Q) / 24) * eulerMoment570 _ 3 t +
        ((157 / 100 * Q) / 24) * eulerMoment570 _ 4 t
  have hpow : t ^ (-(157 / 100 : ℝ)) * t⁻¹ = t ^ (-(157 / 100 : ℝ) - 1) := by
    rw [Real.rpow_sub hp, Real.rpow_one, div_eq_mul_inv (t ^ _) t]
  have hs : Real.sqrt t * t ^ (-(157 / 100 : ℝ) - 1) = t ^ (-(107 / 100 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  unfold eulerMoment570
  rw [← hs, ← hpow]
  unfold C L Q mainCoeff644
  norm_num only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons]
  ring

/-- Under RH, the common Euler tail above a cutoff at least 101 is bounded
by its main tail, its lower boundary error, and three explicit error moments. -/
theorem three_shift_tail_closed_644 {a : ℝ} (hRH : RiemannHypothesis) (ha : 101 ≤ a)
    (hl : 5 ≤ Real.log a) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (157 / 100 : ℝ) *
        threeShiftEulerPoly644 (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      threeShiftEulerMain644 a + Real.sqrt a * (Real.log a ^ 2 / 24) * threeShiftEulerDensity644 a +
        threeShiftEulerError_644 a := by
  have ha1 : 1 ≤ a := by linarith only [ha]
  have hm (k : ℕ) : Filter.Tendsto (eulerMomentValue570 (107 / 100) k) Filter.atTop (nhds 0) := by
    change
      Filter.Tendsto
        (fun t : ℝ ↦ t ^ (-(107 / 100 : ℝ)) * Analysis.logPowerTailPoly (107 / 100) k (Real.log t))
        _ _
    simpa only [neg_mul, neg_neg, neg_zero] using
      (Analysis.log_power_tail_primitive_tendsto (by norm_num only : (0 : ℝ) < 107 / 100) k).neg
  have hz :=
    (((hm 2).const_mul (errorCoeff644 0)).add ((hm 3).const_mul (errorCoeff644 1))).add
      ((hm 4).const_mul (errorCoeff644 2))
  simp only [mul_zero, add_zero] at hz
  have he : Filter.Tendsto threeShiftEulerError_644 Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t ↦ threeShiftEulerError_644 t) _ _
    simp only [threeShiftEulerError_644, Fin.sum_univ_three]
    exact hz
  intro f
  apply le_of_forall_pos_le_add
  intro ε hε
  have hh :=
    three_shift_euler_tail_RH_644 (D := threeShiftEulerError_644 a + ε) hRH ha hl
      (three_shift_main_limit644 ha1)
      (by
        filter_upwards [he.eventually (lt_mem_nhds (neg_lt_zero.mpr hε)),
          Filter.eventually_ge_atTop a] with b hb hab
        rw [three_shift_error_interval_644 ha1 hab]
        linarith only [hb])
  dsimp only at hh
  dsimp only [f]
  linarith only [hh]

/-- The explicit main, boundary and error terms for the section 122
auxiliary Euler tail above a positive cutoff `X`. -/
noncomputable def quarterAuxEulerCap644 (X : ℝ) : ℝ :=
  threeShiftEulerMain644 X + Real.sqrt X * (Real.log X ^ 2 / 24) * threeShiftEulerDensity644 X +
    threeShiftEulerError_644 X

private theorem aux_euler_lower_of_cap {X B : ℝ} (hX : 101 ≤ X) (hl : 5 ≤ Real.log X) (τ : ℕ → ℝ)
    (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3)
    (hcap :
      let f := fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (157 / 100 : ℝ) *
          threeShiftEulerPoly644 (Real.log n)
      (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n ≤ B) :
    -4 * B ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n },
          (3 - τ n.val) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (157 / 100 : ℝ) *
              threeShiftEulerPoly644 (Real.log n.val))) := by
  let f := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (157 / 100 : ℝ) *
      threeShiftEulerPoly644 (Real.log n)
  let D := fun n : ℕ ↦ 3 - τ n
  have hs : Summable f := three_shift_euler_summable644
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
  change (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n ≤ _ at hcap
  have hsub := (hs.subtype (fun n ↦ ⌊X⌋₊ < n)).mul_left (4 : ℝ)
  have hb (n : { n : ℕ // ⌊X⌋₊ < n }) :
    0 ≤ D n.val * f n.val ∧ D n.val * f n.val ≤ 4 * f n.val := by
    have hn := Nat.lt_of_floor_lt n.property
    have hlog := hl.trans (Real.log_le_log (by linarith only [hX]) hn.le)
    have hf : 0 ≤ f n.val :=
      mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (three_shift_euler_poly_pos644 hlog).le
    have hD : 0 ≤ D n.val := sub_nonneg.mpr (ht n.val).2
    have hu : D n.val ≤ 4 := by
      dsimp only [D]; linarith only [(ht n.val).1]
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

private theorem aux_boundary_scale {t : ℝ} (ht : 0 < t) :
    Real.sqrt t * Real.exp (-(157 / 100 : ℝ) * Real.log t) =
      Real.exp (-(107 / 100 : ℝ) * Real.log t) := by
  rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos ht, ← Real.exp_add]
  congr 1
  ring

/-- The main Euler contribution in logarithmic coordinates. -/
private noncomputable def phaseEulerMainPoly644 (x : ℝ) : ℝ :=
  ∑ k : Fin 3, mainCoeff644 k * Analysis.logPowerTailPoly (57 / 100) k.val x

/-- The boundary and integrated slope contributions in logarithmic coordinates. -/
private noncomputable def phaseEulerErrorPoly644 (x : ℝ) : ℝ :=
  x ^ 2 / 24 * threeShiftEulerPoly644 x +
    ∑ k : Fin 3, errorCoeff644 k * Analysis.logPowerTailPoly (107 / 100) (2 + k.val) x

/-- The forward Euler cap splits into two scaled logarithmic polynomials. -/
private theorem phase_euler_log644 {t : ℝ} (ht : 0 < t) :
    threeShiftEulerMain644 t + Real.sqrt t * (Real.log t ^ 2 / 24) * threeShiftEulerDensity644 t +
        threeShiftEulerError_644 t =
      Real.exp (-(57 / 100) * Real.log t) * phaseEulerMainPoly644 (Real.log t) +
        Real.exp (-(107 / 100) * Real.log t) * phaseEulerErrorPoly644 (Real.log t) := by
  unfold threeShiftEulerMain644 threeShiftEulerDensity644 threeShiftEulerError_644
    phaseEulerMainPoly644 phaseEulerErrorPoly644
  simp_rw [forward_moment_scale ht, Finset.mul_sum]
  rw [show
      Real.sqrt t * (Real.log t ^ 2 / 24) *
          (Real.exp (-(157 / 100 : ℝ) * Real.log t) * threeShiftEulerPoly644 (Real.log t)) =
        (Real.sqrt t * Real.exp (-(157 / 100 : ℝ) * Real.log t)) *
          (Real.log t ^ 2 / 24 * threeShiftEulerPoly644 (Real.log t))
      by ring,
    aux_boundary_scale ht]
  simp only [mul_add, Fin.sum_univ_three]
  ring

private theorem moment_mul_upper644 {d l x h a A : ℝ} (hd : 0 < d) (hl : 0 ≤ l)
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
private theorem phase_euler_main_box644 {l x h : ℝ} (hl : 0 ≤ l) (hx : x ∈ Set.Icc l h) :
    phaseEulerMainPoly644 x ≤
      2.497896 * Analysis.logPowerTailPoly (57 / 100) 0 h -
          1.878949 * Analysis.logPowerTailPoly (57 / 100) 1 l +
        0.377294 * Analysis.logPowerTailPoly (57 / 100) 2 h := by
  obtain ⟨hc, he, hq⟩ := coeff644_box
  have h0 : mainCoeff644 0 ≤ 2.497896 := by
    change (coeff644 0) - 5 * (coeff644 1) + 25 * (coeff644 2) ≤ _
    linarith only [hc.2, he.1, hq.2]
  have h1 : mainCoeff644 1 ≤ -1.878949 := by
    change (coeff644 1) - 10 * (coeff644 2) ≤ _
    linarith only [he.2, hq.1]
  have h2 : mainCoeff644 2 ≤ 0.377294 := by
    change (coeff644 2) ≤ _
    linarith only [hq.2]
  have H0 := moment_mul_upper644 (by norm_num only : 0 < (57 / 100 : ℝ)) hl hx h0 0
  have H1 := moment_mul_upper644 (by norm_num only : 0 < (57 / 100 : ℝ)) hl hx h1 1
  have H2 := moment_mul_upper644 (by norm_num only : 0 < (57 / 100 : ℝ)) hl hx h2 2
  unfold phaseEulerMainPoly644
  norm_num only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, ite_eq_left,
    ite_eq_right, show (0 : ℝ) ≤ 2.497896 by norm_num only,
    show ¬(0 : ℝ) ≤ -1.878949 by norm_num only,
    show (0 : ℝ) ≤ 0.377294 by norm_num only] at H0 H1 H2 ⊢
  linarith only [H0, H1, H2]

/-- Bound the forward error polynomial by evaluating its boundary factor and
the three signed moments at the appropriate rational endpoints. -/
private theorem phase_euler_error_box644 {l x h : ℝ} (hl : 5 ≤ l) (hx : x ∈ Set.Icc l h) :
    phaseEulerErrorPoly644 x ≤
      h ^ 2 / 24 * (2.535446 + 1.893981 * (h - 5) + 0.377294 * (h - 5) ^ 2) +
            0.24169404 * Analysis.logPowerTailPoly (107 / 100) 2 h -
          0.15435566 * Analysis.logPowerTailPoly (107 / 100) 3 l +
        0.02468132 * Analysis.logPowerTailPoly (107 / 100) 4 h := by
  obtain ⟨hc, he, hq⟩ := coeff644_box
  have h0 : errorCoeff644 0 ≤ 0.24169404 := by
    change
      (157 / 100 * ((coeff644 0) - 5 * (coeff644 1) + 25 * (coeff644 2)) -
            ((coeff644 1) - 10 * (coeff644 2))) /
          24 ≤
        _
    linarith only [hc.2, he.1, hq.2]
  have h1 : errorCoeff644 1 ≤ -0.15435566 := by
    change (157 / 100 * ((coeff644 1) - 10 * (coeff644 2)) - 2 * (coeff644 2)) / 24 ≤ _
    linarith only [he.2, hq.1]
  have h2 : errorCoeff644 2 ≤ 0.02468132 := by
    change (157 / 100 * (coeff644 2)) / 24 ≤ _
    linarith only [hq.2]
  have hl0 : 0 ≤ l := by linarith only [hl]
  have hx0 := hl0.trans hx.1
  have hxh : 0 ≤ x - 5 := sub_nonneg.mpr (hl.trans hx.1)
  have hshift : x - 5 ≤ h - 5 := sub_le_sub_right hx.2 _
  have hP : threeShiftEulerPoly644 x ≤ 2.535446 + 1.893981 * (h - 5) + 0.377294 * (h - 5) ^ 2 := by
    rw [three_shift_euler_poly_expand644]
    have h₁ := mul_le_mul he.2 hshift hxh (by norm_num only)
    have h₂ := mul_le_mul hq.2 (pow_le_pow_left₀ hxh hshift 2) (sq_nonneg _) (by norm_num only)
    linarith only [hc.2, h₁, h₂]
  have hboundary :=
    mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hx0 hx.2 2)
      (three_shift_euler_poly_pos644 (hl.trans hx.1)).le
  have hboundary' := mul_le_mul_of_nonneg_left hP (sq_nonneg h)
  have H0 := moment_mul_upper644 (by norm_num only : 0 < (107 / 100 : ℝ)) hl0 hx h0 2
  have H1 := moment_mul_upper644 (by norm_num only : 0 < (107 / 100 : ℝ)) hl0 hx h1 3
  have H2 := moment_mul_upper644 (by norm_num only : 0 < (107 / 100 : ℝ)) hl0 hx h2 4
  unfold phaseEulerErrorPoly644
  norm_num only [Fin.sum_univ_three, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.reduceAdd,
    ite_eq_left, ite_eq_right, show (0 : ℝ) ≤ 0.24169404 by norm_num only,
    show ¬(0 : ℝ) ≤ -0.15435566 by norm_num only,
    show (0 : ℝ) ≤ 0.02468132 by norm_num only] at H0 H1 H2 ⊢
  linarith only [H0, H1, H2, hboundary, hboundary']

private theorem euler_cost_box644 {X m e M E : ℝ} (hX : 0 < X)
    (hm : Real.exp (-(57 / 100) * Real.log X) ≤ m) (he : Real.exp (-(107 / 100) * Real.log X) ≤ e)
    (hM : phaseEulerMainPoly644 (Real.log X) ≤ M) (hE : phaseEulerErrorPoly644 (Real.log X) ≤ E)
    (hM0 : 0 ≤ M) (hE0 : 0 ≤ E) : quarterAuxEulerCap644 X ≤ m * M + e * E := by
  unfold quarterAuxEulerCap644
  rw [phase_euler_log644 hX]
  exact
    add_le_add
      ((mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right hm hM0))
      ((mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le).trans (mul_le_mul_of_nonneg_right he hE0))

/-- The auxiliary Euler cap at the first section 122 cutoff is at most
0.114155. The logarithm and the two powers use rational certificates. -/
theorem quarter_aux_euler_cap_316 : quarterAuxEulerCap644 99856 ≤ 0.114155 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 99856) (j := 16) (n := 48) (lo :=
      1151148440 / 100000000) (hi := 1151148445 / 100000000) (by decide +kernel)
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 57) (d :=
        100) (lo := 0) (hi := 141369826767 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 99856) (p := 107) (d :=
        100) (lo := 0) (hi := 4473728697 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hm he
  rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < 99856), mul_comm (Real.log 99856)] at hm he
  have hM := phase_euler_main_box644 (by norm_num only) hl
  have hE := phase_euler_error_box644 (by norm_num only) hl
  refine
      (euler_cost_box644 (M := 79.17670) (E := 496.79760) (by norm_num only) hm he (hM.trans ?_)
            (hE.trans ?_) (by norm_num only) (by norm_num only)).trans
        ?_ <;>
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      Nat.reduceAdd]

private theorem aux_euler_above {a X B : ℝ} (ha : 101 ≤ a) (hlog : 5 ≤ Real.log a) (hX : a ≤ X)
    (hB : quarterAuxEulerCap644 a ≤ B) (hRH : RiemannHypothesis) (τ : ℕ → ℝ)
    (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3) :
    -4 * B ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n },
          (3 - τ n.val) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (157 / 100 : ℝ) *
              threeShiftEulerPoly644 (Real.log n.val))) := by
  let f := fun n : ℕ ↦
    ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (157 / 100 : ℝ) *
      threeShiftEulerPoly644 (Real.log n)
  have hcap := three_shift_tail_closed_644 hRH ha hlog
  change (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤ quarterAuxEulerCap644 a at hcap
  have hprefix : ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact
        Finset.mem_Ioc.mpr
          ⟨(Finset.mem_Ioc.mp hn).1, (Finset.mem_Ioc.mp hn).2.trans (Nat.floor_mono hX)⟩
    · intro n hn hnot
      have hlt : ⌊a⌋₊ < n :=
        lt_of_not_ge (fun h ↦ hnot (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, h⟩))
      have hle := (Nat.lt_of_floor_lt hlt).le
      have hl := hlog.trans (Real.log_le_log (by linarith only [ha]) hle)
      exact
        mul_nonneg
          (div_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (three_shift_euler_poly_pos644 hl).le
  have h :=
    aux_euler_lower_of_cap (B := B) (ha.trans hX)
      (hlog.trans (Real.log_le_log (by linarith only [ha]) hX)) τ ht
      (show (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n ≤ _ by linarith only [hcap, hprefix, hB])
  linarith only [h]

/-- The auxiliary Euler cap at the section 122 row endpoint is at most
0.113024. The logarithm and the two powers use rational certificates. -/
theorem quarter_aux_euler_cap_320 : quarterAuxEulerCap644 (102400) ≤ 0.113024 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := (102400)) (j := 16) (n := 48) (lo :=
      1153664197 / 100000000) (hi := 1153664202 / 100000000) (by decide +kernel)
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (102400)) (p := 57)
        (d := 100) (lo := 0) (hi := 139357075793 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (102400)) (p := 107)
        (d := 100) (lo := 0) (hi := 43549086186 / 10000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hm he
  rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < (102400)),
    mul_comm (Real.log (102400))] at hm he
  have hM := phase_euler_main_box644 (by norm_num only) hl
  have hE := phase_euler_error_box644 (by norm_num only) hl
  refine
      (euler_cost_box644 (M := 79.53600) (E := 501.50482) (by norm_num only) hm he (hM.trans ?_)
            (hE.trans ?_) (by norm_num only) (by norm_num only)).trans
        ?_ <;>
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      Nat.reduceAdd]

/-- The auxiliary Euler cap at the section 122 row endpoint is at most
0.112536. The logarithm and the two powers use rational certificates. -/
theorem quarter_aux_euler_cap_32175 : quarterAuxEulerCap644 (1656369 / 16) ≤ 0.112536 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := (1656369 / 16)) (j := 16) (n := 48) (lo :=
      1154754967 / 100000000) (hi := 1154754972 / 100000000) (by decide +kernel)
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (1656369 / 16)) (p :=
        57) (d := 100) (lo := 0) (hi := 138493326450 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (1656369 / 16)) (p :=
        107) (d := 100) (lo := 0) (hi := 43043768905 / 10000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hm he
  rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < (1656369 / 16)),
    mul_comm (Real.log (1656369 / 16))] at hm he
  have hM := phase_euler_main_box644 (by norm_num only) hl
  have hE := phase_euler_error_box644 (by norm_num only) hl
  refine
      (euler_cost_box644 (M := 79.69205) (E := 503.55614) (by norm_num only) hm he (hM.trans ?_)
            (hE.trans ?_) (by norm_num only) (by norm_num only)).trans
        ?_ <;>
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      Nat.reduceAdd]

/-- The auxiliary Euler cap at the section 122 row endpoint is at most
0.112522. The logarithm and the two powers use rational certificates. -/
theorem quarter_aux_euler_cap_3218 : quarterAuxEulerCap644 (2588881 / 25) ≤ 0.112522 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := (2588881 / 25)) (j := 16) (n := 48) (lo :=
      1154786044 / 100000000) (hi := 1154786049 / 100000000) (by decide +kernel)
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (2588881 / 25)) (p :=
        57) (d := 100) (lo := 0) (hi := 138468795581 / 100000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := (2588881 / 25)) (p :=
        107) (d := 100) (lo := 0) (hi := 43029457919 / 10000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hl hm he
  rw [Real.rpow_def_of_pos (by norm_num only : (0 : ℝ) < (2588881 / 25)),
    mul_comm (Real.log (2588881 / 25))] at hm he
  have hM := phase_euler_main_box644 (by norm_num only) hl
  have hE := phase_euler_error_box644 (by norm_num only) hl
  refine
      (euler_cost_box644 (M := 79.69649) (E := 503.61468) (by norm_num only) hm he (hM.trans ?_)
            (hE.trans ?_) (by norm_num only) (by norm_num only)).trans
        ?_ <;>
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one,
      Nat.reduceAdd]

/-- The signed Euler correction above the section 122 radius-316 cutoff
is at least minus four times the certified endpoint cap under RH. -/
theorem quarter_aux_euler_lower_316 {X : ℝ} (hX : (99856 : ℝ) ≤ X) (hRH : RiemannHypothesis)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3) :
    -0.456620 ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n },
          (3 - τ n.val) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (157 / 100 : ℝ) *
              threeShiftEulerPoly644 (Real.log n.val))) := by
  have hlog : (5 : ℝ) ≤ Real.log (99856) :=
    (Analysis.rationalLogIntervalCheck_sound (N := (99856)) (j := 16) (n := 20) (lo := 5) (hi := 12)
        (by decide +kernel)).1
  have h := aux_euler_above (by norm_num only) hlog hX quarter_aux_euler_cap_316 hRH τ ht
  linarith only [h]

/-- The signed Euler correction above the section 122 radius-320 cutoff
is at least minus four times the certified endpoint cap under RH. -/
theorem quarter_aux_euler_lower_320 {X : ℝ} (hX : (102400 : ℝ) ≤ X) (hRH : RiemannHypothesis)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3) :
    -0.452096 ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n },
          (3 - τ n.val) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (157 / 100 : ℝ) *
              threeShiftEulerPoly644 (Real.log n.val))) := by
  have hlog : (5 : ℝ) ≤ Real.log (102400) :=
    (Analysis.rationalLogIntervalCheck_sound (N := (102400)) (j := 16) (n := 20) (lo := 5) (hi :=
        12) (by decide +kernel)).1
  have h := aux_euler_above (by norm_num only) hlog hX quarter_aux_euler_cap_320 hRH τ ht
  linarith only [h]

/-- The signed Euler correction above the section 122 radius-32175 cutoff
is at least minus four times the certified endpoint cap under RH. -/
theorem quarter_aux_euler_lower_32175 {X : ℝ} (hX : (1656369 / 16 : ℝ) ≤ X)
    (hRH : RiemannHypothesis) (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3) :
    -0.450144 ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n },
          (3 - τ n.val) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (157 / 100 : ℝ) *
              threeShiftEulerPoly644 (Real.log n.val))) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1656369 / 16) (j := 16) (n := 20) (lo := 5)
        (hi := 12) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have h := aux_euler_above (by norm_num only) hlog hX quarter_aux_euler_cap_32175 hRH τ ht
  linarith only [h]

/-- The signed Euler correction above the section 122 radius-3218 cutoff
is at least minus four times the certified endpoint cap under RH. -/
theorem quarter_aux_euler_lower_3218 {X : ℝ} (hX : (2588881 / 25 : ℝ) ≤ X) (hRH : RiemannHypothesis)
    (τ : ℕ → ℝ) (ht : ∀ n, -1 ≤ τ n ∧ τ n ≤ 3) :
    -0.450088 ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n },
          (3 - τ n.val) *
            (ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (157 / 100 : ℝ) *
              threeShiftEulerPoly644 (Real.log n.val))) := by
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 2588881 / 25) (j := 16) (n := 20) (lo := 5)
        (hi := 12) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have h := aux_euler_above (by norm_num only) hlog hX quarter_aux_euler_cap_3218 hRH τ ht
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
