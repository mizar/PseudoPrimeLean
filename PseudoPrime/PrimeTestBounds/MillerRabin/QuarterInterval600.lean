/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectedTriple570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerBoundary570
import all PseudoPrime.Analysis.LogTaylorBounds
import all PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import Mathlib.Analysis.Calculus.MeanValue

/-! # Section 99 comparison on the independent quarter-square interval [584,600] -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The conductor contribution 4rR(r) in (99.12), with the factor r
absorbed in the exponent 1 - 2a = -26/25. -/
noncomputable def section99Conductor (r : ℝ) : ℝ :=
  (4 * (51 / 50) ^ 5 * Real.exp (-(51 / 50) * (14 / 5)) / 120) *
    (r ^ (-(26 / 25) : ℝ) * (14 / 5 + 2 * Real.log r) ^ 5)

theorem quarter_conductor_box {r z y : ℝ} (hr : 1 ≤ r) (hz : Real.log r ≤ z)
    (hy : r ^ (-(26 / 25) : ℝ) ≤ y) :
    section99Conductor r ≤
      (4 * (51 / 50) ^ 5 * (57498294069 / 1000000000000) / 120) * (y * (14 / 5 + 2 * z) ^ 5) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 357 / 125) 26
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h
  have hi := one_div_le_one_div_of_le (by norm_num only) h
  rw [one_div (Real.exp _), ← Real.exp_neg] at hi
  have he : Real.exp (-(51 / 50 : ℝ) * (14 / 5)) ≤ 57498294069 / 1000000000000 := by
    rw [show -(51 / 50 : ℝ) * (14 / 5) = -(357 / 125) by norm_num only]
    linarith only [hi]
  have hl := Real.log_nonneg hr
  have hp := Real.rpow_nonneg (zero_le_one.trans hr) (-(26 / 25) : ℝ)
  have _hy := hp.trans hy
  unfold section99Conductor
  gcongr

/-- Certified conductor upper bound at radius 292 for the section 99 Euler endpoint. -/
theorem section99_conductor_292 : section99Conductor 292 ≤ 32798714 / 10000000 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 5) (hi :=
        5676753806 / 1000000000) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 292) (p := 26) (d := 25)
        (lo := 0) (hi := 2728989311 / 1000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat, neg_div] at hl hp
  apply (quarter_conductor_box (by norm_num only : (1 : ℝ) ≤ 292) hl hp).trans
  norm_num only

/-- Certified conductor upper bound at radius 299 for the section 99 Euler endpoint. -/
theorem section99_conductor_299 : section99Conductor 299 ≤ 32539728 / 10000000 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 299) (j := 8) (n := 24) (lo := 5) (hi :=
        5700443577 / 1000000000) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 299) (p := 26) (d := 25)
        (lo := 0) (hi := 2662575701 / 1000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat, neg_div] at hl hp
  apply (quarter_conductor_box (by norm_num only : (1 : ℝ) ≤ 299) hl hp).trans
  norm_num only

/-- Certified conductor upper bound at radius 300 for the section 99 Euler endpoint. -/
theorem section99_conductor_300 : section99Conductor 300 ≤ 32503245 / 10000000 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 24) (lo := 5) (hi :=
        5703782478 / 1000000000) (by decide +kernel)).2
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 300) (p := 26) (d := 25)
        (lo := 0) (hi := 2653346054 / 1000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat, neg_div] at hl hp
  apply (quarter_conductor_box (by norm_num only : (1 : ℝ) ≤ 300) hl hp).trans
  norm_num only

theorem quarter_tail_box {x z m e b : ℝ} (hx : 1 ≤ x) (hz : Real.log x ≤ z)
    (hm : x ^ (-(13 / 25) : ℝ) ≤ m) (he : x ^ (-(51 / 50) : ℝ) ≤ e)
    (hb : x ^ (-(38 / 25) : ℝ) ≤ b) :
    positiveTail570 x ≤
      3 / 8 * (m * Analysis.logPowerTailPoly (13 / 25) 0 z) +
        153 / 400 * (m * Analysis.logPowerTailPoly (13 / 25) 1 z) +
        2601 / 20000 * (m * Analysis.logPowerTailPoly (13 / 25) 2 z) +
        4 / 5 * Real.sqrt x * (b * (3 / 8 + 153 / 400 * z + 2601 / 20000 * z ^ 2)) +
        (3 / 20 * (e * Analysis.logPowerTailPoly (51 / 50) 0 z) +
          3213 / 12500 * (e * Analysis.logPowerTailPoly (51 / 50) 1 z) +
          49419 / 312500 * (e * Analysis.logPowerTailPoly (51 / 50) 2 z)) +
        33605 / 100000000 := by
  have hlog := Real.log_nonneg hx
  have hb0 := (Real.rpow_nonneg (zero_le_one.trans hx) _).trans hb
  have hD : eulerDensity570 x ≤ b * (3 / 8 + 153 / 400 * z + 2601 / 20000 * z ^ 2) := by
    unfold eulerDensity570
    gcongr
  unfold positiveTail570 eulerMainTail570 eulerLowError570
  gcongr
  all_goals
    first
    | exact eulerHighError_million_le
    |
      exact
        mul_le_mul hm (Analysis.log_power_tail_poly_mono (by norm_num only) hlog hz _)
          (Analysis.log_power_tail_poly_nonneg (by norm_num only) hlog _)
          ((Real.rpow_nonneg (zero_le_one.trans hx) _).trans hm)
    |
      exact
        mul_le_mul he (Analysis.log_power_tail_poly_mono (by norm_num only) hlog hz _)
          (Analysis.log_power_tail_poly_nonneg (by norm_num only) hlog _)
          ((Real.rpow_nonneg (zero_le_one.trans hx) _).trans he)

/-- The full section 99 Euler envelope at radius 292 satisfies its endpoint budget. -/
theorem section99_euler_292 : section99Conductor 292 + 4 * positiveTail570 (292 ^ 2) ≤ 3.88866 := by
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 85264) (j := 16) (n := 40) (lo := 11) (hi :=
        1135350762 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 85264) (p := 13) (d :=
        25) (lo := 0) (hi := 2728989310247 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 85264) (p := 51) (d :=
        50) (lo := 0) (hi := 9345853803 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 85264) (p := 38) (d :=
        25) (lo := 0) (hi := 32006349 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have ht := quarter_tail_box (by norm_num only : (1 : ℝ) ≤ 85264) hz hm he hb
  rw [show (85264 : ℝ) = 292 ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at ht
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at ht
  linarith only [section99_conductor_292, ht]

/-- The full section 99 Euler envelope at radius 299 satisfies its endpoint budget. -/
theorem section99_euler_299 : section99Conductor 299 + 4 * positiveTail570 (299 ^ 2) ≤ 3.85168 := by
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 89401) (j := 16) (n := 40) (lo := 11) (hi :=
        1140088716 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 89401) (p := 13) (d :=
        25) (lo := 0) (hi := 2662575700266 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 89401) (p := 51) (d :=
        50) (lo := 0) (hi := 8904935453 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 89401) (p := 38) (d :=
        25) (lo := 0) (hi := 29782393 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have ht := quarter_tail_box (by norm_num only : (1 : ℝ) ≤ 89401) hz hm he hb
  rw [show (89401 : ℝ) = 299 ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at ht
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at ht
  linarith only [section99_conductor_299, ht]

/-- The full section 99 Euler envelope at radius 300 satisfies its endpoint budget. -/
theorem section99_euler_300 : section99Conductor 300 + 4 * positiveTail570 (300 ^ 2) ≤ 3.84649 := by
  have hz :=
    (Analysis.rationalLogIntervalCheck_sound (N := 90000) (j := 16) (n := 40) (lo := 11) (hi :=
        1140756496 / 100000000) (by decide +kernel)).2
  have hm :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 90000) (p := 13) (d :=
        25) (lo := 0) (hi := 2653346053846 / 1000000000000000) (by decide +kernel)).2
  have he :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 90000) (p := 51) (d :=
        50) (lo := 0) (hi := 8844486847 / 1000000000000000) (by decide +kernel)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 90000) (p := 38) (d :=
        25) (lo := 0) (hi := 29481623 / 1000000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat, neg_div] at hz hm he hb
  have ht := quarter_tail_box (by norm_num only : (1 : ℝ) ≤ 90000) hz hm he hb
  rw [show (90000 : ℝ) = 300 ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)] at ht
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd] at ht
  linarith only [section99_conductor_300, ht]

/-- At square cutoff and radius at least one, the conductor term in the contour formula
is exactly the closed conductor contribution in (99.12). -/
private theorem section99_conductor_profile {r : ℝ} (hr : 1 ≤ r) :
    4 * r * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (r ^ 2)⁻¹ = section99Conductor r := by
  have hp := zero_lt_one.trans_le hr
  have hs := sq_pos_of_pos hp
  rw [quarter_profile_below_one (inv_pos.mpr hs) ((inv_le_one₀ hs).mpr (one_le_pow₀ hr)),
    Real.log_inv, Real.log_pow, Nat.cast_ofNat, Real.inv_rpow hs.le, ← Real.rpow_neg hs.le, ←
    Real.rpow_natCast_mul hp.le]
  have he : r * r ^ ((2 : ℕ) * (-(51 / 50) : ℝ)) = r ^ (-(26 / 25) : ℝ) := by
    rw [mul_comm, ← Real.rpow_add_one hp.ne']
    norm_num only
  unfold section99Conductor
  linear_combination
    (4 * (51 / 50) ^ 5 * Real.exp (-(51 / 50) * (14 / 5)) / 120 * (14 / 5 + 2 * Real.log r) ^ 5) *
      he

/-- The logarithmic slope of the conductor term factors into a positive
weight and an affine function of the shifted logarithm. -/
theorem section99_conductor_deriv {r : ℝ} (hr : 0 < r) :
    let C : ℝ := 4 * (51 / 50) ^ 5 * Real.exp (-(51 / 50) * (14 / 5)) / 120
    let v := 14 / 5 + 2 * Real.log r
    HasDerivAt section99Conductor (C * r ^ (-(26 / 25) : ℝ) * v ^ 4 * (10 - (26 / 25) * v) / r)
      r := by
  intro C v
  have h :=
    ((Real.hasDerivAt_rpow_const (p := -(26 / 25 : ℝ)) (Or.inl hr.ne')).mul
          ((((Real.hasDerivAt_log hr.ne').const_mul 2).const_add (14 / 5)).pow 5)).const_mul
      C
  apply h.congr_deriv
  rw [Real.rpow_sub_one hr.ne']
  dsimp only [v, Pi.pow_apply]
  field_simp [hr.ne']
  ring

/-- On the section 99 radius interval the conductor decreases and satisfies
the lower logarithmic slope required of the total Euler remainder. -/
theorem section99_conductor_slope {r : ℝ} (hr : 292 ≤ r) :
    -(2.04 * section99Conductor r) ≤ r * deriv section99Conductor r ∧
      deriv section99Conductor r ≤ 0 := by
  have hp : 0 < r := by linarith only [hr]
  have he := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 4
  have hl : 4 ≤ Real.log r := by
    apply (Real.le_log_iff_exp_le hp).mpr
    rw [show (4 : ℝ) = (4 : ℕ) * (1 : ℝ) by norm_num only, Real.exp_natCast_mul]
    linarith only [he, hr]
  let v := 14 / 5 + 2 * Real.log r
  let C : ℝ := 4 * (51 / 50) ^ 5 * Real.exp (-(51 / 50) * (14 / 5)) / 120
  have hW : 0 ≤ C * r ^ (-(26 / 25) : ℝ) * v ^ 4 := by
    dsimp only [C]; positivity
  have hv : 10.8 ≤ v := by
    dsimp only [v]; linarith only [hl]
  rw [(section99_conductor_deriv hp).deriv]
  change
    -(2.04 * (C * (r ^ (-(26 / 25) : ℝ) * v ^ 5))) ≤
        r * (C * r ^ (-(26 / 25) : ℝ) * v ^ 4 * (10 - 26 / 25 * v) / r) ∧
      _
  rw [← mul_div_assoc, mul_div_cancel_left₀ _ hp.ne']
  constructor
  · nlinarith only [mul_nonneg hW (show 0 ≤ 10 + v by linarith only [hv])]
  · exact
      div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hW (by linarith only [hl]))
        hp.le

/-- The two rational rows of section 99 give a positive comparison gap
through radius 300 when the Euler remainder obeys its endpoint slope envelope.
The bound on E is a hypothesis to be supplied by the analytic estimates. -/
theorem section99_gap_positive {r E : ℝ} (hu : r ≤ 300)
    (hE :
      E ≤
        if r ≤ 299 then 3.85168 + (2.04 * 3.88866 / 292) * (299 - r)
        else 3.84649 + (2.04 * 3.85168 / 299) * (300 - r)) :
    let C : ℝ :=
      if r ≤ 299 then
        -0.13 + 0.02549 + 0.09184 + 3 * 0.03434 + 1.113 * 0.002720 + 0.002237 + 0.01154 + 0.02169
      else
        -0.125 + 0.02537 + 0.09239 + 3 * 0.03424 + 1.113 * 0.002708 + 0.002229 + 0.01232 + 0.02179
    0 < -0.0312773 * r + 13.4154 - 0.29136 - 0.0273 - E + C := by
  intro C
  by_cases hr : r ≤ 299
  · simp only [C, ite_eq_left hr] at hE ⊢
    linarith only [hr, hE]
  · simp only [C, ite_eq_right hr] at hE ⊢
    linarith only [hu, hE]

/-- The logarithmic slope inequality in (99.12) bounds E at any interior
radius by its right endpoint plus a linear correction from the left endpoint. -/
theorem euler_row_envelope {E : ℝ → ℝ} {a b r M U c : ℝ} (hc : 0 ≤ c) (ha : 0 < a)
    (hr : r ∈ Set.Icc a b) (hM : 0 ≤ M) (hu : E b ≤ U) (hm : E a ≤ M)
    (hmono : AntitoneOn E (Set.Icc a b)) (hd : ∀ t ∈ Set.Icc a b, DifferentiableAt ℝ E t)
    (hs : ∀ t ∈ Set.Icc a b, -(c * E t) ≤ t * deriv E t) : E r ≤ U + (c * M / a) * (b - r) := by
  have hab := hr.1.trans hr.2
  have hder (t : ℝ) (ht : t ∈ interior (Set.Icc a b)) : -(c * M / a) ≤ deriv E t := by
    have ht' : t ∈ Set.Icc a b := interior_subset ht
    have hval := (hmono (Set.left_mem_Icc.mpr hab) ht' ht'.1).trans hm
    have hpos : 0 ≤ c * M / a := div_nonneg (mul_nonneg hc hM) ha.le
    have hmul := mul_le_mul_of_nonneg_right ht'.1 hpos
    have he : a * (c * M / a) = c * M := by field_simp [ha.ne']
    rw [he] at hmul
    apply le_of_mul_le_mul_left (a := t) _ (ha.trans_le ht'.1)
    linarith only [hmul, mul_le_mul_of_nonneg_left hval hc, hs t ht']
  have h :=
    (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      (fun t ht ↦ (hd t ht).continuousAt.continuousWithinAt)
      (fun t ht ↦ (hd t (interior_subset ht)).differentiableWithinAt) hder r hr b
      (Set.right_mem_Icc.mpr hab) hr.2
  linarith only [h, hu]

/-- Endpoint certificates at 292, 299 and 300 suffice for both affine
Euler envelopes when E is decreasing and obeys its logarithmic slope bound. -/
theorem section99_euler_envelope {E : ℝ → ℝ} {r : ℝ} (hr : r ∈ Set.Icc 292 300)
    (hmono : AntitoneOn E (Set.Icc 292 300)) (hd : ∀ t ∈ Set.Icc 292 300, DifferentiableAt ℝ E t)
    (hs : ∀ t ∈ Set.Icc 292 300, -(2.04 * E t) ≤ t * deriv E t) (h292 : E 292 ≤ 3.88866)
    (h299 : E 299 ≤ 3.85168) (h300 : E 300 ≤ 3.84649) :
    E r ≤
      if r ≤ 299 then 3.85168 + (2.04 * 3.88866 / 292) * (299 - r)
      else 3.84649 + (2.04 * 3.85168 / 299) * (300 - r) := by
  by_cases h : r ≤ 299
  · rw [ite_eq_left h]
    have hi : Set.Icc (292 : ℝ) 299 ⊆ Set.Icc 292 300 := Set.Icc_subset_Icc_right (by norm_num only)
    exact
      euler_row_envelope (c := 2.04) (by norm_num only) (by norm_num only) ⟨hr.1, h⟩
        (by norm_num only) h299 h292 (hmono.mono hi) (fun t ht ↦ hd t (hi ht))
        (fun t ht ↦ hs t (hi ht))
  · rw [ite_eq_right h]
    have hi : Set.Icc (299 : ℝ) 300 ⊆ Set.Icc 292 300 := Set.Icc_subset_Icc_left (by norm_num only)
    exact
      euler_row_envelope (c := 2.04) (by norm_num only) (by norm_num only) ⟨le_of_not_ge h, hr.2⟩
        (by norm_num only) h300 h299 (hmono.mono hi) (fun t ht ↦ hd t (hi ht))
        (fun t ht ↦ hs t (hi ht))

/-- With the section 99 endpoint and slope bounds, the comparison is positive
on the full closed radius interval, including the common endpoint 299. -/
theorem section99_gap_of_endpoints {E : ℝ → ℝ} {r : ℝ} (hr : r ∈ Set.Icc 292 300)
    (hmono : AntitoneOn E (Set.Icc 292 300)) (hd : ∀ t ∈ Set.Icc 292 300, DifferentiableAt ℝ E t)
    (hs : ∀ t ∈ Set.Icc 292 300, -(2.04 * E t) ≤ t * deriv E t) (h292 : E 292 ≤ 3.88866)
    (h299 : E 299 ≤ 3.85168) (h300 : E 300 ≤ 3.84649) :
    let C : ℝ :=
      if r ≤ 299 then
        -0.13 + 0.02549 + 0.09184 + 3 * 0.03434 + 1.113 * 0.002720 + 0.002237 + 0.01154 + 0.02169
      else
        -0.125 + 0.02537 + 0.09239 + 3 * 0.03424 + 1.113 * 0.002708 + 0.002229 + 0.01232 + 0.02179
    0 < -0.0312773 * r + 13.4154 - 0.29136 - 0.0273 - E r + C := by
  exact section99_gap_positive hr.2 (section99_euler_envelope hr hmono hd hs h292 h299 h300)

/-- For a cutoff X above A in the finite psi range, bound its unsigned Euler tail
by the Abel envelope at A. Taking A = X retains the radius in section 99. -/
theorem unshifted_tail_upper {A X : ℝ} (hAX : A ≤ X) (ha : 2701 ≤ A) (hbnd : A ≤ 1000000)
    (hRH : RiemannHypothesis) :
    (∑' k : { n : ℕ // ⌊X⌋₊ < n },
        ArithmeticFunction.vonMangoldt k.val * quarterEulerWeight570 k.val) ≤
      positiveTail570 A := by
  let s := Finset.Ioc 0 ⌊A⌋₊
  let w := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * quarterEulerWeight570 n
  let e := fun k : { n : ℕ // ⌊X⌋₊ < n } ↦
    (⟨k.val, fun h ↦
        (not_lt_of_ge (Finset.mem_Ioc.mp h).2) ((Nat.floor_mono hAX).trans_lt k.property)⟩ :
      { n : ℕ // n ∉ s })
  have hi : Function.Injective e := fun _ _ h ↦
    Subtype.ext (congrArg (fun k : { n : ℕ // n ∉ s } ↦ k.val) h)
  have ht : (∑' k : { n : ℕ // ⌊X⌋₊ < n }, w k.val) ≤ ∑' k : { n : ℕ // n ∉ s }, w k.val :=
    Summable.tsum_le_tsum_of_inj e hi
      (fun k _ ↦
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
          (quarter_euler_weight_nonneg_570_all k.val))
      (fun _ ↦ le_rfl) (quarter_euler_weight_summable_570.subtype _)
      (quarter_euler_weight_summable_570.subtype _)
  have hs := quarter_euler_weight_summable_570.sum_add_tsum_subtype_compl s
  have hb := positive_tail_upper_570 hRH ha hbnd
  change (∑' n, w n) - (∑ n ∈ s, w n) ≤ positiveTail570 A at hb
  change (∑ n ∈ s, w n) + (∑' k : { n : ℕ // n ∉ s }, w k.val) = ∑' n, w n at hs
  exact ht.trans ((le_of_eq (eq_sub_of_add_eq' hs)).trans hb)

/-- At radii from 292 to 300 the conductor and unsigned Euler tail at the square cutoff
are bounded by the variable-radius envelope of (99.12). -/
theorem section99_euler_upper {r : ℝ} (hl : 292 ≤ r) (hu : r ≤ 300) (hRH : RiemannHypothesis) :
    4 * r * Analysis.rationalPoleProfile 3 (25 / 51) (7 / 5) (r ^ 2)⁻¹ +
        4 *
          (∑' k : { n : ℕ // ⌊r ^ 2⌋₊ < n },
            ArithmeticFunction.vonMangoldt k.val * quarterEulerWeight570 k.val) ≤
      section99Conductor r + 4 * positiveTail570 (r ^ 2) := by
  have hb : 2701 ≤ r ^ 2 := by nlinarith only [hl, sq_nonneg (r - 292)]
  have hh := pow_le_pow_left₀ (by linarith only [hl] : 0 ≤ r) hu 2
  have ht := unshifted_tail_upper (le_refl (r ^ 2)) hb (by linarith only [hh]) hRH
  rw [section99_conductor_profile (by linarith only [hl])]
  exact add_le_add_right (mul_le_mul_of_nonneg_left ht (by norm_num only : (0 : ℝ) ≤ 4)) _

/-- For positive x the square-root boundary is a positive combination of moments of
degrees one and two. The constant coefficient cancels after expanding the tail polynomials. -/
theorem section99_boundary_moments {x : ℝ} (hx : 0 < x) :
    Real.sqrt x * eulerDensity570 x =
      2601 / 20000 * eulerMomentValue570 (51 / 50) 1 x +
        132651 / 1000000 * eulerMomentValue570 (51 / 50) 2 x := by
  unfold eulerDensity570 eulerMomentValue570
  rw [Real.sqrt_eq_rpow, ← mul_assoc, ← Real.rpow_add hx]
  norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one, Nat.cast_zero,
    Nat.reduceAdd, show (1 / 2 : ℝ) + -(38 / 25) = -(51 / 50) by norm_num only]
  ring

/-- At square cutoff, a positive log moment of decay d has nonpositive derivative,
and its logarithmic slope is at least minus 2d times the moment. -/
theorem section99_moment_slope {d r : ℝ} (hd : 0 < d) (hr : 1 ≤ r) (k : ℕ) :
    ∃ v : ℝ,
      HasDerivAt (fun t : ℝ ↦ eulerMomentValue570 d k (t ^ 2)) v r ∧
        -(2 * d * eulerMomentValue570 d k (r ^ 2)) ≤ r * v ∧ v ≤ 0 := by
  let x := r ^ 2
  have hpos := zero_lt_one.trans_le hr
  have hx : 0 < x := sq_pos_of_pos hpos
  have hz : 0 ≤ Real.log x := Real.log_nonneg (one_le_pow₀ hr)
  have h := (Analysis.log_power_tail_primitive_deriv hd hx k).neg
  have hm : HasDerivAt (eulerMomentValue570 d k) (-(Real.log x ^ k * x ^ (-d - 1))) x := by
    convert h using 1
    funext t
    simp only [Pi.neg_apply, neg_mul, neg_neg, eulerMomentValue570]
  have hs : HasDerivAt (fun t : ℝ ↦ t ^ 2) (2 * r) r := by
    simpa only [Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one] using (hasDerivAt_pow 2 r)
  refine ⟨_, hm.comp (h := fun t : ℝ ↦ t ^ 2) r hs, ?_, ?_⟩
  · have hp : Real.log x ^ k ≤ d * Analysis.logPowerTailPoly d k (Real.log x) := by
      cases k with
      | zero =>
        simp only [pow_zero, Analysis.logPowerTailPoly, one_div, mul_inv_cancel₀ hd.ne', le_refl]
      | succ
        j =>
        rw [Analysis.logPowerTailPoly, mul_add, ← mul_div_assoc, mul_div_cancel_left₀ _ hd.ne']
        exact
          le_add_of_nonneg_right
            (mul_nonneg hd.le
              (mul_nonneg (div_nonneg (Nat.cast_nonneg _) hd.le)
                (Analysis.log_power_tail_poly_nonneg hd hz j)))
    change -(2 * d * (x ^ (-d) * _)) ≤ _
    rw [Real.rpow_sub_one hx.ne']
    dsimp only [x] at *
    field_simp [hpos.ne']
    linarith only [hp]
  · exact
      mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg (pow_nonneg hz _) (Real.rpow_nonneg hx.le _)))
        (mul_nonneg (by norm_num only) hpos.le)

private theorem section99_tail_slope {r : ℝ} (hr : 1 ≤ r) :
    ∃ v : ℝ,
      HasDerivAt (fun x : ℝ ↦ positiveTail570 (x ^ 2)) v r ∧
        -(2.04 * positiveTail570 (r ^ 2)) ≤ r * v ∧ v ≤ 0 := by
  have hp := zero_lt_one.trans_le hr
  have hm {d : ℝ} (hd : 0 < d) (k : ℕ) : 0 ≤ eulerMomentValue570 d k (r ^ 2) :=
    mul_nonneg (Real.rpow_nonneg (sq_nonneg _) _)
      (Analysis.log_power_tail_poly_nonneg hd (Real.log_nonneg (one_le_pow₀ hr)) k)
  have hh : 0 ≤ eulerHighError570 1000000 := by
    have h (k : ℕ) : 0 ≤ eulerMomentValue570 (51 / 50) k 1000000 :=
      mul_nonneg (Real.rpow_nonneg (by norm_num only) _)
        (Analysis.log_power_tail_poly_nonneg (by norm_num only) (Real.log_nonneg (by norm_num only))
          k)
    unfold eulerHighError570
    linarith only [h 2, h 3, h 4]
  obtain ⟨a0, ha0, la0, ua0⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 13 / 25) hr 0
  obtain ⟨a1, ha1, la1, ua1⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 13 / 25) hr 1
  obtain ⟨a2, ha2, la2, ua2⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 13 / 25) hr 2
  obtain ⟨b0, hb0, lb0, ub0⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 51 / 50) hr 0
  obtain ⟨b1, hb1, lb1, ub1⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 51 / 50) hr 1
  obtain ⟨b2, hb2, lb2, ub2⟩ := section99_moment_slope (by norm_num only : (0 : ℝ) < 51 / 50) hr 2
  have hmain :=
    (((ha0.const_mul (3 / 8)).add (ha1.const_mul (153 / 400))).add (ha2.const_mul (2601 / 20000)))
  have hlow :=
    (((hb0.const_mul (3 / 20)).add (hb1.const_mul (3213 / 12500))).add
      (hb2.const_mul (49419 / 312500)))
  have hbd :=
    ((hb1.const_mul (2601 / 20000)).add (hb2.const_mul (132651 / 1000000))) |>.const_mul (4 / 5)
  have hsum := (((hmain.add hbd).add hlow).add_const (eulerHighError570 1000000))
  refine ⟨_, hsum.congr_of_eventuallyEq ?_, ?_, ?_⟩
  · filter_upwards [lt_mem_nhds hp] with x hx
    unfold positiveTail570 eulerMainTail570 eulerLowError570
    rw [mul_assoc, section99_boundary_moments (sq_pos_of_pos hx)]
    rfl
  · unfold positiveTail570 eulerMainTail570 eulerLowError570
    rw [mul_assoc (4 / 5), section99_boundary_moments (sq_pos_of_pos hp)]
    linarith only [la0, la1, la2, lb0, lb1, lb2, hh, hm (by norm_num only : (0 : ℝ) < 13 / 25) 0,
      hm (by norm_num only : (0 : ℝ) < 13 / 25) 1, hm (by norm_num only : (0 : ℝ) < 13 / 25) 2]
  · linarith only [ua0, ua1, ua2, ub0, ub1, ub2]

/-- The full Euler envelope is differentiable and antitone above radius 292. -/
theorem quarter_euler_deriv_nonpos {r : ℝ} (hr : 292 ≤ r) :
    DifferentiableAt ℝ (fun x : ℝ ↦ section99Conductor x + 4 * positiveTail570 (x ^ 2)) r ∧
      deriv (fun x : ℝ ↦ section99Conductor x + 4 * positiveTail570 (x ^ 2)) r ≤ 0 := by
  obtain ⟨d, hd, _, hu⟩ := section99_tail_slope (by linarith only [hr] : 1 ≤ r)
  have hc := (section99_conductor_deriv (by linarith only [hr])).differentiableAt.hasDerivAt
  have h := hc.add (hd.const_mul 4)
  exact ⟨h.differentiableAt, h.deriv ▸ by linarith only [(section99_conductor_slope hr).2, hu]⟩

/-- With the sharper conductor exponent, the scaled derivative improves
the usual Euler-envelope bound by the full conductor contribution. -/
theorem quarter_euler_slope_sharp {r : ℝ} (hr : 292 ≤ r) :
    -(2.04 * (section99Conductor r + 4 * positiveTail570 (r ^ 2))) + section99Conductor r ≤
      r * deriv (fun x : ℝ ↦ section99Conductor x + 4 * positiveTail570 (x ^ 2)) r := by
  have hp : 0 < r := by linarith only [hr]
  obtain ⟨d, hd, hlo, _⟩ := section99_tail_slope (by linarith only [hr] : 1 ≤ r)
  have hc := (section99_conductor_deriv hp).differentiableAt.hasDerivAt
  have h :
    HasDerivAt (fun x : ℝ ↦ section99Conductor x + 4 * positiveTail570 (x ^ 2))
      (deriv section99Conductor r + 4 * d) r :=
    hc.add (hd.const_mul 4)
  have hcond : -(26 / 25) * section99Conductor r ≤ r * deriv section99Conductor r := by
    rw [(section99_conductor_deriv hp).deriv]
    unfold section99Conductor
    rw [show ∀ x : ℝ, r * (x / r) = x from fun x ↦ by field_simp [hp.ne']]
    have h₀ :
      0 ≤
        4 * (51 / 50) ^ 5 * Real.exp (-(51 / 50) * (14 / 5)) / 120 * r ^ (-(26 / 25) : ℝ) *
          (14 / 5 + 2 * Real.log r) ^ 4 := by
      positivity
    nlinarith only [h₀]
  rw [h.deriv]
  linarith only [hcond, hlo]

/-- On a closed radius interval starting at 292 or later, two certified endpoint values
give an affine upper bound for the conductor and the full Euler tail. -/
theorem quarter_euler_row {a b r M U : ℝ} (ha : 292 ≤ a) (hr : r ∈ Set.Icc a b) (hM : 0 ≤ M)
    (hm : section99Conductor a + 4 * positiveTail570 (a ^ 2) ≤ M)
    (hu : section99Conductor b + 4 * positiveTail570 (b ^ 2) ≤ U) :
    section99Conductor r + 4 * positiveTail570 (r ^ 2) ≤ U + (2.04 * M / a) * (b - r) := by
  let E := fun x : ℝ ↦ section99Conductor x + 4 * positiveTail570 (x ^ 2)
  have hd (t : ℝ) (hi : t ∈ Set.Icc a b) :
    DifferentiableAt ℝ E t ∧ -(2.04 * E t) ≤ t * deriv E t ∧ deriv E t ≤ 0 := by
    obtain ⟨d, h, hlo, hhi⟩ :=
      section99_tail_slope ((by norm_num only : (1 : ℝ) ≤ 292).trans (ha.trans hi.1))
    have hp : 0 < t := lt_of_lt_of_le (by norm_num only) (ha.trans hi.1)
    have hc := (section99_conductor_deriv hp).differentiableAt.hasDerivAt
    have he : HasDerivAt E (deriv section99Conductor t + 4 * d) t := hc.add (h.const_mul 4)
    have hs := section99_conductor_slope (ha.trans hi.1)
    refine ⟨he.differentiableAt, ?_, ?_⟩ <;> rw [he.deriv]
    · dsimp only [E]
      linarith only [hs.1, hlo]
    · linarith only [hs.2, hhi]
  apply
    euler_row_envelope (E := E) (c := 2.04) (by norm_num only)
      (lt_of_lt_of_le (by norm_num only) ha) hr hM hu hm _ (fun t ht ↦ (hd t ht).1)
      (fun t ht ↦ (hd t ht).2.1)
  apply antitoneOn_of_deriv_nonpos (convex_Icc _ _)
  · exact fun t hi ↦ (hd t hi).1.continuousAt.continuousWithinAt
  · exact fun t hi ↦ (hd t (interior_subset hi)).1.differentiableWithinAt
  · exact fun t hi ↦ (hd t (interior_subset hi)).2.2

/-- The two endpoint rows of section 99 bound its Euler envelope at every radius. -/
theorem section99_full_envelope {r : ℝ} (hr : r ∈ Set.Icc 292 300) :
    section99Conductor r + 4 * positiveTail570 (r ^ 2) ≤
      if r ≤ 299 then 3.85168 + (2.04 * 3.88866 / 292) * (299 - r)
      else 3.84649 + (2.04 * 3.85168 / 299) * (300 - r) := by
  by_cases h : r ≤ 299
  · rw [ite_eq_left h]
    exact
      quarter_euler_row (le_refl _) ⟨hr.1, h⟩ (by norm_num only) section99_euler_292
        section99_euler_299
  · rw [ite_eq_right h]
    exact
      quarter_euler_row (by norm_num only) ⟨le_of_not_ge h, hr.2⟩ (by norm_num only)
        section99_euler_299 section99_euler_300

/-- The two section 99 comparisons are positive with the actual conductor
and closed positive Euler-tail envelope on the full radius interval. -/
theorem section99_closed_gap {r : ℝ} (hr : r ∈ Set.Icc 292 300) :
    let C : ℝ :=
      if r ≤ 299 then
        -0.13 + 0.02549 + 0.09184 + 3 * 0.03434 + 1.113 * 0.002720 + 0.002237 + 0.01154 + 0.02169
      else
        -0.125 + 0.02537 + 0.09239 + 3 * 0.03424 + 1.113 * 0.002708 + 0.002229 + 0.01232 + 0.02179
    0 <
      -0.0312773 * r + 13.4154 - 0.29136 - 0.0273 -
          (section99Conductor r + 4 * positiveTail570 (r ^ 2)) +
        C := by
  exact section99_gap_positive hr.2 (section99_full_envelope hr)

/-- With the full first Gamma convolution, the two section 99 scalar
comparisons close using the signed boundary coefficient -1.517. The low
and upper rows use respectively the boundary caps 0.00281 and 0.002721. -/
theorem section99_full_gamma_gap {r : ℝ} (hr : r ∈ Set.Icc 292 300) :
    let C : ℝ :=
      if r ≤ 299 then
        -0.13 + 0.02549 + 0.09239 + 3 * 0.03434 - 1.517 * 0.00281 + 0.002237 + 0.01154 + 0.02169
      else -0.125 + 0.02537 + 0.09239 + 3 * 0.0364 - 1.517 * 0.002721 + 0.002229 + 0.01232 + 0.02179
    0 <
      -0.0312773 * r + 13.4154 - 0.29136 - 0.0273 -
          (section99Conductor r + 4 * positiveTail570 (r ^ 2)) +
        C := by
  have hE := section99_full_envelope hr
  dsimp only
  split_ifs with h
  · rw [ite_eq_left h] at hE
    linarith only [h, hE]
  · rw [ite_eq_right h] at hE
    linarith only [hr.2, hE]

end PseudoPrime.PrimeTestBounds.MillerRabin
