/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterTriangleAbel

/-! # Euler weights on the prime window at logarithmic cutoff 576 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Across the section 86 prime window the sixth-pole Euler weight dominates the
shifted triangle divided by the square root, with a common radius-dependent coefficient. -/
theorem prime_window_euler_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) {p : ℕ} (hp : r ^ 2 ≤ p)
    (hw : Real.log p - 2 * Real.log r ≤ 5) :
    (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) *
        (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p) ≤
      quarterEulerWeight570 p := by
  have hr : 0 < r := by linarith only [hl]
  have hpos := (sq_pos_of_pos hr).trans_le hp
  have hlog := Real.log_le_log (sq_pos_of_pos hr) hp
  rw [Real.log_pow, Nat.cast_ofNat] at hlog
  have h288 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 288) (j := 8) (n := 24) (lo := 5) (hi := 17 / 3)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h288
  have ht :=
    window_weight_lower_576 (v := 2 * Real.log r) (x := Real.log p - 2 * Real.log r)
      (mul_nonneg (by norm_num only) (Real.log_nonneg (by linarith only [hl])))
      (sub_nonneg.mpr hlog) (by linarith only [hw, Real.log_le_log hr hu, h288])
  rw [show 2 * Real.log r + (Real.log p - 2 * Real.log r) = Real.log p by ring] at ht
  have hs :=
    mul_le_mul_of_nonneg_right ht (show 0 ≤ r ^ (-(51 / 25 : ℝ)) / Real.sqrt p by positivity)
  have he :
    Real.exp (-(51 / 50) * (Real.log p - 2 * Real.log r)) * (r ^ (-(51 / 25 : ℝ)) / Real.sqrt p) =
      ((p : ℝ) ^ (38 / 25 : ℝ))⁻¹ := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hr, Real.rpow_def_of_pos hpos,
      Real.rpow_def_of_pos hpos, ← Real.exp_sub, ← Real.exp_neg, ← Real.exp_add]
    congr 1
    ring
  rw [show quarterEulerWeight570 p = eulerLogPoly (Real.log p) / (p : ℝ) ^ (38 / 25 : ℝ) by
      unfold quarterEulerWeight570 eulerLogPoly; ring]
  convert hs using 1
  · ring
  · rw [mul_right_comm _ (eulerLogPoly _) _, he]
    ring

/-- Summing the pointwise comparison with nonnegative logarithmic weights bounds
the triangle mass of any finite subset of the window by its Euler contribution. -/
theorem sum_window_euler_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) (s : Finset ℕ)
    (hp : ∀ p ∈ s, r ^ 2 ≤ (p : ℝ)) (hw : ∀ p ∈ s, Real.log p - 2 * Real.log r ≤ 5) :
    (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) *
        ∑ p ∈ s,
          Real.log p * (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p) ≤
      ∑ p ∈ s, Real.log p * quarterEulerWeight570 p := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro p h
  rw [mul_left_comm]
  exact
    mul_le_mul_of_nonneg_left (prime_window_euler_576 hl hu (hp p h) (hw p h))
      (Real.log_natCast_nonneg p)

/-- On radii from 287 to 288, a triangle mass of 1.46 times the radius yields
a fourfold Euler contribution strictly above 0.02238. -/
theorem window_factor_gt_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    1119 / 50000 <
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) := by
  have hr : 0 < r := by linarith only [hl]
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 287) (j := 8) (n := 24) (lo := 113 / 20) (hi :=
        6) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hv : 113 / 10 ≤ 2 * Real.log r := by
    linarith only [h, Real.log_le_log (by norm_num only : (0 : ℝ) < 287) hl]
  have hq : eulerLogPoly (113 / 10) ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly
    gcongr
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 288) (p := 26) (d := 25)
        (lo := 27684 / 10000000) (hi := 1) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hb
  have ha : 27684 / 10000000 ≤ r ^ (-(26 / 25 : ℝ)) := by
    apply le_trans _ (Real.rpow_le_rpow_of_nonpos hr hu (by norm_num only))
    linarith only [hb]
  have hm :=
    mul_le_mul hq ha (by norm_num only)
      (by
        unfold eulerLogPoly; positivity)
  have he : r ^ (-(51 / 25 : ℝ)) * r = r ^ (-(26 / 25 : ℝ)) := by
    calc
      _ = r ^ (-(51 / 25 : ℝ)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hr]; norm_num only
  unfold eulerLogPoly at hm
  rw [show
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) =
        (4 * (13 / 200) * (73 / 50)) * (eulerLogPoly (2 * Real.log r) * (r ^ (-(51 / 25 : ℝ)) * r))
      by ring,
    he]
  unfold eulerLogPoly
  linarith only [hm]

/-- A finite window with triangle mass at least 1.46 times the radius saves more
than 0.02238 in the fourfold Euler sum on section 86. -/
theorem window_euler_saving_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) (s : Finset ℕ)
    (hp : ∀ p ∈ s, r ^ 2 ≤ (p : ℝ)) (hw : ∀ p ∈ s, Real.log p - 2 * Real.log r ≤ 5)
    (hm :
      73 / 50 * r ≤
        ∑ p ∈ s,
          Real.log p * (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p)) :
    1119 / 50000 < 4 * ∑ p ∈ s, Real.log p * quarterEulerWeight570 p := by
  have hr : 0 < r := by linarith only [hl]
  have hlog := Real.log_nonneg (show 1 ≤ r by linarith only [hl])
  have hq : 0 ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly; positivity
  have ha :=
    mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ)) by positivity)
  have hb := ha.trans (sum_window_euler_576 hl hu s hp hw)
  linarith only [window_factor_gt_576 hl hu, hb]

/-- On the section 86 interval the explicit psi error of the wide triangle
is below one sixteenth of the radius, by the upper logarithm at 300. -/
theorem triangle_psi_error_300 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) :
    41 / 120 * (Real.log r) ^ 2 + 739 / 720 * Real.log r + 10631 / 11520 < r / 16 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 24) (lo := 5) (hi :=
        571 / 100) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hv := (Real.log_le_log (show 0 < r by linarith only [hl]) hu).trans h
  have hs := pow_le_pow_left₀ (Real.log_nonneg (show 1 ≤ r by linarith only [hl])) hv 2
  linarith only [hl, hv, hs]

/-- On the section 86 interval the explicit psi error of the wide triangle
is below one sixteenth of the radius, by the upper logarithm at 300. -/
theorem triangle_psi_error_313 {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 313) :
    41 / 120 * (Real.log r) ^ 2 + 739 / 720 * Real.log r + 10631 / 11520 < r / 16 := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 24) (lo := 5) (hi := 23 / 4)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hv := (Real.log_le_log (show 0 < r by linarith only [hl]) hu).trans h
  have hs := pow_le_pow_left₀ (Real.log_nonneg (show 1 ≤ r by linarith only [hl])) hv 2
  linarith only [hl, hv, hs]

/-- Restrict the estimate through radius 300 to section 86. -/
theorem triangle_psi_error_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    41 / 120 * (Real.log r) ^ 2 + 739 / 720 * Real.log r + 10631 / 11520 < r / 16 := by
  exact triangle_psi_error_300 hl (hu.trans (by norm_num only))

/-- The total triangle mass, three character estimates and the prime-power loss
in section 76 imply its linear lower bound for the identity prime mass. -/
theorem triangle_prime_lower_576 {r W I D J B : ℝ} (hl : 287 ≤ r) (hw : 3943 / 400 * r ≤ W)
    (hi : W - 4 * r + 3 * D - 3 * J ≤ 4 * I) (hd : 28 / 5 ≤ D) (hj : J ≤ 1 / 250) (hb : B ≤ 5) :
    73 / 50 * r < I - B := by linarith only [hl, hw, hi, hd, hj, hb]

/-- The logarithmic triangle on the interval from zero to five has main mass
strictly above 248/25 after removing the radius factor. -/
theorem triangle_main_mass_576 :
    248 / 25 < ∫ x in (0 : ℝ)..5, Real.exp (x / 2) * shiftedTriangle (5 / 2) x := by
  let f (x : ℝ) := Real.exp (x / 2) * shiftedTriangle (5 / 2) x
  have hc : Continuous f := by
    unfold f shiftedTriangle; fun_prop
  have he (x : ℝ) : HasDerivAt (fun t : ℝ => Real.exp (t / 2)) (Real.exp (x / 2) / 2) x := by
    convert (((hasDerivAt_id x).div_const 2).exp) using 1 <;>
      simp only [id_eq, div_eq_mul_inv, one_mul]
  have ha :
    ∫ x in (0 : ℝ)..(5 / 2), f x =
      (4 / 5) * (5 / 2 - 2) * Real.exp ((5 / 2) / 2) - (4 / 5) * (0 - 2) * Real.exp (0 / 2) := by
    apply
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ =>
        (4 / 5) * (t - 2) * Real.exp (t / 2)) _ (hc.intervalIntegrable _ _)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num only)] at hx
    have ht := (((hasDerivAt_id x).sub_const 2).const_mul (4 / 5)).mul (he x)
    convert ht using 1
    · rfl
    · unfold f shiftedTriangle
      rw [abs_of_nonpos (sub_nonpos.mpr hx.2), max_eq_right (by linarith only [hx.1])]
      simp only [id_eq]
      ring
  have hb :
    ∫ x in (5 / 2 : ℝ)..5, f x =
      (4 / 5) * (7 - 5) * Real.exp (5 / 2) - (4 / 5) * (7 - 5 / 2) * Real.exp ((5 / 2) / 2) := by
    apply
      intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t : ℝ =>
        (4 / 5) * (7 - t) * Real.exp (t / 2)) _ (hc.intervalIntegrable _ _)
    intro x hx
    rw [Set.uIcc_of_le (by norm_num only)] at hx
    have ht := (((hasDerivAt_id x).const_sub 7).const_mul (4 / 5)).mul (he x)
    convert ht using 1
    · rfl
    · unfold f shiftedTriangle
      rw [abs_of_nonneg (sub_nonneg.mpr hx.1), max_eq_right (by linarith only [hx.2])]
      simp only [id_eq]
      ring
  change _ < ∫ x in (0 : ℝ)..5, f x
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (b := (5 / 2 : ℝ)) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _),
    ha, hb]
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 4) 9
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  rw [show (5 / 2 : ℝ) / 2 = 5 / 4 by ring, show (5 / 2 : ℝ) = 5 / 4 + 5 / 4 by ring, Real.exp_add,
    zero_div, Real.exp_zero]
  nlinarith only [ht, sq_nonneg (Real.exp (5 / 4) - 349 / 100)]

/-- Integrating a squared logarithmic coordinate against an affine density gives
the endpoint difference used on each of the three triangle segments. -/
private theorem affine_triangle_integral (t a b l u : ℝ) :
    ∫ x in l..u, (t + x) ^ 2 * (a + b * x) =
      ((a - b * t) / 3 * (t + u) ^ 3 + b / 4 * (t + u) ^ 4) -
        ((a - b * t) / 3 * (t + l) ^ 3 + b / 4 * (t + l) ^ 4) := by
  apply
    intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun x =>
      (a - b * t) / 3 * (t + x) ^ 3 + b / 4 * (t + x) ^ 4)
  · intro x _
    have h := (hasDerivAt_id x).const_add t
    convert ((h.pow 3).const_mul ((a - b * t) / 3)).add ((h.pow 4).const_mul (b / 4)) using 1
    · rfl
    · simp only [id_eq, Nat.cast_ofNat]
      ring
  · exact (by fun_prop : Continuous (fun x : ℝ => (t + x) ^ 2 * (a + b * x))).intervalIntegrable _ _

/-- The three signed polynomial pieces of the triangle variation give exactly
the section 76 psi error polynomial after division by 24. -/
theorem triangle_variation_integral_576 (v : ℝ) :
    ((∫ x in (0 : ℝ)..2, (2 * v + x) ^ 2 * (2 / 5 + -(1 / 5) * x)) +
          (∫ x in (2 : ℝ)..(5 / 2), (2 * v + x) ^ 2 * (-(2 / 5) + 1 / 5 * x)) +
          (∫ x in (5 / 2 : ℝ)..5, (2 * v + x) ^ 2 * (7 / 5 + -(1 / 5) * x))) /
        24 =
      41 / 120 * v ^ 2 + 739 / 720 * v + 10631 / 11520 := by
  rw [affine_triangle_integral, affine_triangle_integral, affine_triangle_integral]
  ring

/-- The explicit variation polynomial bounds the error over the translated triangle window. -/
theorem triangle_abs_variation_of_bound {r : ℝ}
    (hbound : 41 / 120 * (Real.log r) ^ 2 + 739 / 720 * Real.log r + 10631 / 11520 < r / 16) :
    ((∫ x in (0 : ℝ)..(5 / 2), (2 * Real.log r + x) ^ 2 * |2 / 5 - x / 5|) +
          (∫ x in (5 / 2 : ℝ)..5, (2 * Real.log r + x) ^ 2 * |x / 5 - 7 / 5|)) /
        24 <
      r / 16 := by
  let f (x : ℝ) := (2 * Real.log r + x) ^ 2 * |2 / 5 - x / 5|
  have hc : Continuous f := by
    unfold f; fun_prop
  change ((∫ x in (0 : ℝ)..(5 / 2), f x) + _) / 24 < _
  rw [←
    intervalIntegral.integral_add_adjacent_intervals (b := (2 : ℝ)) (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  apply lt_of_eq_of_lt _ hbound
  rw [← triangle_variation_integral_576]
  congr 2
  · congr 1
    · apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num only)] at hx
      unfold f
      rw [abs_of_nonneg (by linarith only [hx.2])]
      ring
    · apply intervalIntegral.integral_congr
      intro x hx
      rw [Set.uIcc_of_le (by norm_num only)] at hx
      unfold f
      rw [abs_of_nonpos (by linarith only [hx.1])]
      ring
  · apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by norm_num only)] at hx
    dsimp only
    rw [abs_of_nonpos (show x / 5 - 7 / 5 ≤ 0 by linarith only [hx.2])]
    ring

/-- The absolute variation of the two differentiable branches, weighted by the
squared logarithm, costs less than one sixteenth of the radius for radii from 287 to 313. -/
theorem triangle_abs_variation_313 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 313) :
    ((∫ x in (0 : ℝ)..(5 / 2), (2 * Real.log r + x) ^ 2 * |2 / 5 - x / 5|) +
          (∫ x in (5 / 2 : ℝ)..5, (2 * Real.log r + x) ^ 2 * |x / 5 - 7 / 5|)) /
        24 <
      r / 16 := by
  exact
    triangle_abs_variation_of_bound
      (if h : r ≤ 300 then triangle_psi_error_300 hl h
      else triangle_psi_error_313 (le_of_not_ge h) hu)

/-- The absolute variation of the two differentiable branches, weighted by the
squared logarithm, costs less than one sixteenth of the radius for radii from 287 to 300. -/
theorem triangle_abs_variation_300 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) :
    ((∫ x in (0 : ℝ)..(5 / 2), (2 * Real.log r + x) ^ 2 * |2 / 5 - x / 5|) +
          (∫ x in (5 / 2 : ℝ)..5, (2 * Real.log r + x) ^ 2 * |x / 5 - 7 / 5|)) /
        24 <
      r / 16 := by
  exact triangle_abs_variation_313 hl (hu.trans (by norm_num only))

/-- Restrict the estimate through radius 300 to section 86. -/
theorem triangle_abs_variation_576 {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    ((∫ x in (0 : ℝ)..(5 / 2), (2 * Real.log r + x) ^ 2 * |2 / 5 - x / 5|) +
          (∫ x in (5 / 2 : ℝ)..5, (2 * Real.log r + x) ^ 2 * |x / 5 - 7 / 5|)) /
        24 <
      r / 16 := by
  exact triangle_abs_variation_300 hl (hu.trans (by norm_num only))

/-- On a logarithmic subinterval above 101, monotone substitution turns the
centered Abel error into an integral bounded by the affine variation density. -/
theorem triangle_branch_integral_error (hRH : RiemannHypothesis) (a b v l u : ℝ) (hlu : l ≤ u)
    (hl : 101 ≤ Real.exp (v + l)) :
    |∫ t in Real.exp (v + l)..Real.exp (v + u),
          deriv (triangleLogBranch a b) t * (Chebyshev.psi t - t)| ≤
      (∫ x in l..u, (v + x) ^ 2 * |b - (a + b * (v + x)) / 2|) / 24 := by
  let g (t : ℝ) := deriv (triangleLogBranch a b) t * (Chebyshev.psi t - t)
  let f (x : ℝ) := Real.exp (v + x)
  have hd (x : ℝ) : HasDerivAt f (f x) x := by
    simpa only [f, id_eq, mul_one] using ((hasDerivAt_id x).const_add v).exp
  have hs :=
    intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg (a := l) (b := u) (g := g) (f := f)
      (f' := f)
      (by
        unfold f; fun_prop)
      (fun x _ => hd x) (fun x _ => (Real.exp_pos _).le)
  change |∫ t in f l..f u, g t| ≤ _
  rw [← hs, ← intervalIntegral.integral_div]
  rw [← Real.norm_eq_abs]
  apply intervalIntegral.norm_integral_le_of_norm_le hlu
  · apply Filter.Eventually.of_forall
    intro x hx
    change |g (f x) * f x| ≤ _
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact
      triangle_branch_psi_error hRH a b (v + x)
        (hl.trans (Real.exp_le_exp.mpr (add_le_add le_rfl hx.1.le)))
  · exact
      (by fun_prop :
            Continuous
              (fun x : ℝ => (v + x) ^ 2 * |b - (a + b * (v + x)) / 2| / 24)).intervalIntegrable
        _ _

/-- The explicit variation polynomial bounds the error over the translated triangle window. -/
theorem triangle_joined_error_of_bound (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r)
    (hbound : 41 / 120 * (Real.log r) ^ 2 + 739 / 720 * Real.log r + 10631 / 11520 < r / 16) :
    let v := 2 * Real.log r
    let E := fun a b l u : ℝ =>
      ∫ t in Real.exp (v + l)..Real.exp (v + u),
        deriv (triangleLogBranch a b) t * (Chebyshev.psi t - t)
    |E (-(2 * v / 5)) (2 / 5) 0 (5 / 2)| + |E (2 + 2 * v / 5) (-(2 / 5)) (5 / 2) 5| < r / 16 := by
  intro v E
  have hr : 0 < r := by linarith only [hl]
  have he : Real.exp v = r ^ 2 := by
    dsimp only [v]
    rw [two_mul, Real.exp_add, Real.exp_log hr, sq]
  have h0 : 101 ≤ Real.exp (v + 0) := by
    rw [add_zero, he]
    nlinarith only [hl, sq_nonneg (r - 287)]
  have hm := h0.trans (Real.exp_le_exp.mpr (show v + 0 ≤ v + 5 / 2 by linarith only))
  have ha :=
    triangle_branch_integral_error hRH (-(2 * v / 5)) (2 / 5) v 0 (5 / 2) (by norm_num only) h0
  have hb :=
    triangle_branch_integral_error hRH (2 + 2 * v / 5) (-(2 / 5)) v (5 / 2) 5 (by norm_num only) hm
  simp_rw [show ∀ x : ℝ, 2 / 5 - (-(2 * v / 5) + 2 / 5 * (v + x)) / 2 = 2 / 5 - x / 5 from fun x =>
      by ring] at ha
  simp_rw [show ∀ x : ℝ, -(2 / 5) - (2 + 2 * v / 5 + -(2 / 5) * (v + x)) / 2 = x / 5 - 7 / 5 from
      fun x => by ring] at hb
  exact
    (add_le_add ha hb).trans_lt
      (by
        rw [← add_div]
        exact triangle_abs_variation_of_bound hbound)

/-- Under RH the sum of the two absolute centered Abel errors over the
actual triangle window is less than r/16 for radii from 287 to 313. -/
theorem triangle_joined_error_313 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 313) :
    let v := 2 * Real.log r
    let E := fun a b l u : ℝ =>
      ∫ t in Real.exp (v + l)..Real.exp (v + u),
        deriv (triangleLogBranch a b) t * (Chebyshev.psi t - t)
    |E (-(2 * v / 5)) (2 / 5) 0 (5 / 2)| + |E (2 + 2 * v / 5) (-(2 / 5)) (5 / 2) 5| < r / 16 := by
  exact
    triangle_joined_error_of_bound hRH hl
      (if h : r ≤ 300 then triangle_psi_error_300 hl h
      else triangle_psi_error_313 (le_of_not_ge h) hu)

/-- Under RH the sum of the two absolute centered Abel errors over the
actual triangle window is less than r/16 for radii from 287 to 300. -/
theorem triangle_joined_error_300 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 300) :
    let v := 2 * Real.log r
    let E := fun a b l u : ℝ =>
      ∫ t in Real.exp (v + l)..Real.exp (v + u),
        deriv (triangleLogBranch a b) t * (Chebyshev.psi t - t)
    |E (-(2 * v / 5)) (2 / 5) 0 (5 / 2)| + |E (2 + 2 * v / 5) (-(2 / 5)) (5 / 2) 5| < r / 16 := by
  exact triangle_joined_error_313 hRH hl (hu.trans (by norm_num only))

/-- Restrict the estimate through radius 300 to section 86. -/
theorem triangle_joined_error_576 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r) (hu : r ≤ 288) :
    let v := 2 * Real.log r
    let E := fun a b l u : ℝ =>
      ∫ t in Real.exp (v + l)..Real.exp (v + u),
        deriv (triangleLogBranch a b) t * (Chebyshev.psi t - t)
    |E (-(2 * v / 5)) (2 / 5) 0 (5 / 2)| + |E (2 + 2 * v / 5) (-(2 / 5)) (5 / 2) 5| < r / 16 := by
  exact triangle_joined_error_300 hRH hl (hu.trans (by norm_num only))

/-- On a positive interval the centered psi integral is the difference of
the full Abel integral and its main term. Monotonicity makes psi integrable. -/
private theorem triangle_centered_eq (a b : ℝ) {l u : ℝ} (hl : 0 < l) (hu : l ≤ u) :
    (∫ t in l..u, deriv (triangleLogBranch a b) t * (Chebyshev.psi t - t)) =
      (∫ t in l..u, deriv (triangleLogBranch a b) t * Chebyshev.psi t) -
        ∫ t in l..u, deriv (triangleLogBranch a b) t * t := by
  have hp (x : ℝ) (hx : x ∈ Set.uIcc l u) : 0 < x :=
    hl.trans_le ((Set.uIcc_of_le hu ▸ hx : x ∈ Set.Icc l u).1)
  have hc : ContinuousOn (deriv (triangleLogBranch a b)) (Set.uIcc l u) := by
    apply ContinuousOn.congr _ (fun x hx => triangle_branch_deriv a b (hp x hx))
    apply ContinuousOn.div
    · have hlog := Real.continuousOn_log.mono (fun x hx => (hp x hx).ne')
      exact
        continuousOn_const.sub ((continuousOn_const.add (continuousOn_const.mul hlog)).div_const 2)
    · exact continuousOn_id.mul Real.continuous_sqrt.continuousOn
    · exact fun x hx => (mul_pos (hp x hx) (Real.sqrt_pos.mpr (hp x hx))).ne'
  simp_rw [mul_sub]
  exact
    intervalIntegral.integral_sub (Chebyshev.psi_mono.intervalIntegrable.continuousOn_mul hc)
      ((continuous_id.intervalIntegrable l u).continuousOn_mul hc)

/-- The explicit variation polynomial bounds the error over the translated triangle window. -/
theorem triangle_mangoldt_lower_of_bound (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r)
    (hbound : 41 / 120 * (Real.log r) ^ 2 + 739 / 720 * Real.log r + 10631 / 11520 < r / 16) :
    let v := 2 * Real.log r
    let l := Real.exp v
    let m := Real.exp (v + 5 / 2)
    let u := Real.exp (v + 5)
    let f := triangleLogBranch (-(2 * v / 5)) (2 / 5)
    let g := triangleLogBranch (2 + 2 * v / 5) (-(2 / 5))
    3943 / 400 * r <
      (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊m⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ Finset.Ioc ⌊m⌋₊ ⌊u⌋₊, g n * ArithmeticFunction.vonMangoldt n) := by
  intro v l m u f g
  have hr : 0 < r := by linarith only [hl]
  have hmain := triangle_joined_main hr
  have herr := triangle_joined_error_of_bound hRH hl hbound
  dsimp only at hmain herr
  rw [add_zero] at hmain herr
  have hab := triangle_joined_abel v
  change _ < _ + _
  rw [hab]
  have hA :=
    triangle_centered_eq (-(2 * v / 5)) (2 / 5) (Real.exp_pos v)
      (Real.exp_le_exp.mpr (show v ≤ v + 5 / 2 by linarith only))
  have hB :=
    triangle_centered_eq (2 + 2 * v / 5) (-(2 / 5)) (Real.exp_pos (v + 5 / 2))
      (Real.exp_le_exp.mpr (show v + 5 / 2 ≤ v + 5 by linarith only))
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 5 / 4) 9
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  have hcoef : 248 / 25 < (8 / 5) * (Real.exp (5 / 4) - 1) ^ 2 := by
    nlinarith only [ht, sq_nonneg (Real.exp (5 / 4) - 349 / 100)]
  have hsum := (add_le_add (le_abs_self _) (le_abs_self _)).trans_lt herr
  dsimp only [v] at hA hB ⊢
  linarith only [hsum, hA, hB, hmain, mul_lt_mul_of_pos_right hcoef hr]

/-- Under RH the two halves of the wide-window Mangoldt sum have total mass
strictly above 3943r/400 for radii from 287 to 313. -/
theorem triangle_mangoldt_lower_313 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r)
    (hu : r ≤ 313) :
    let v := 2 * Real.log r
    let l := Real.exp v
    let m := Real.exp (v + 5 / 2)
    let u := Real.exp (v + 5)
    let f := triangleLogBranch (-(2 * v / 5)) (2 / 5)
    let g := triangleLogBranch (2 + 2 * v / 5) (-(2 / 5))
    3943 / 400 * r <
      (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊m⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ Finset.Ioc ⌊m⌋₊ ⌊u⌋₊, g n * ArithmeticFunction.vonMangoldt n) := by
  exact
    triangle_mangoldt_lower_of_bound hRH hl
      (if h : r ≤ 300 then triangle_psi_error_300 hl h
      else triangle_psi_error_313 (le_of_not_ge h) hu)

/-- Under RH the two halves of the wide-window Mangoldt sum have total mass
strictly above 3943r/400 for radii from 287 to 300. -/
theorem triangle_mangoldt_lower_300 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r)
    (hu : r ≤ 300) :
    let v := 2 * Real.log r
    let l := Real.exp v
    let m := Real.exp (v + 5 / 2)
    let u := Real.exp (v + 5)
    let f := triangleLogBranch (-(2 * v / 5)) (2 / 5)
    let g := triangleLogBranch (2 + 2 * v / 5) (-(2 / 5))
    3943 / 400 * r <
      (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊m⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ Finset.Ioc ⌊m⌋₊ ⌊u⌋₊, g n * ArithmeticFunction.vonMangoldt n) := by
  exact triangle_mangoldt_lower_313 hRH hl (hu.trans (by norm_num only))

/-- Restrict the estimate through radius 300 to section 86. -/
theorem triangle_mangoldt_lower_576 (hRH : RiemannHypothesis) {r : ℝ} (hl : 287 ≤ r)
    (hu : r ≤ 288) :
    let v := 2 * Real.log r
    let l := Real.exp v
    let m := Real.exp (v + 5 / 2)
    let u := Real.exp (v + 5)
    let f := triangleLogBranch (-(2 * v / 5)) (2 / 5)
    let g := triangleLogBranch (2 + 2 * v / 5) (-(2 / 5))
    3943 / 400 * r <
      (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊m⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ Finset.Ioc ⌊m⌋₊ ⌊u⌋₊, g n * ArithmeticFunction.vonMangoldt n) := by
  exact triangle_mangoldt_lower_300 hRH hl (hu.trans (by norm_num only))

/-- Under RH the two halves of the translated Mangoldt sum have total mass strictly above
3943r/400 for radii from 313 to 316. Use the certified logarithm bound at radius 316. -/
theorem triangle_mangoldt_lower_316 (hRH : RiemannHypothesis) {r : ℝ} (hl : 313 ≤ r)
    (hu : r ≤ 316) :
    let v := 2 * Real.log r
    let l := Real.exp v
    let m := Real.exp (v + 5 / 2)
    let u := Real.exp (v + 5)
    let f := triangleLogBranch (-(2 * v / 5)) (2 / 5)
    let g := triangleLogBranch (2 + 2 * v / 5) (-(2 / 5))
    3943 / 400 * r <
      (∑ n ∈ Finset.Ioc ⌊l⌋₊ ⌊m⌋₊, f n * ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ Finset.Ioc ⌊m⌋₊ ⌊u⌋₊, g n * ArithmeticFunction.vonMangoldt n) := by
  apply triangle_mangoldt_lower_of_bound hRH (show 287 ≤ r by linarith only [hl])
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 316) (j := 8) (n := 24) (lo := 5) (hi :=
        144 / 25) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  have hv := (Real.log_le_log (show 0 < r by linarith only [hl]) hu).trans h
  have hs := pow_le_pow_left₀ (Real.log_nonneg (show 1 ≤ r by linarith only [hl])) hv 2
  linarith only [hl, hv, hs]

end PseudoPrime.PrimeTestBounds.MillerRabin
