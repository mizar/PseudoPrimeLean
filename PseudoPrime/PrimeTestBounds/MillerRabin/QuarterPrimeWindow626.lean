/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterWindow576
import PseudoPrime.Analysis.ExponentialFixedPointBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Euler weight transfer through logarithm 626 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Through logarithmic argument 827/50, the polynomial grows at least as fast as
exp(10v/91) relative to its initial value. Differentiate the exponentially damped polynomial. -/
theorem euler_poly_growth_wide {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (hu : v + x ≤ 827 / 50) :
    eulerLogPoly v * Real.exp (x * (10 / 91)) ≤ eulerLogPoly (v + x) := by
  let f := fun t : ℝ ↦ eulerLogPoly t * Real.exp (-t * (10 / 91))
  have hd (t : ℝ) :
    HasDerivAt f
      (((153 / 50 + 2 * (2601 / 2500) * t) / 8 - eulerLogPoly t * (10 / 91)) *
        Real.exp (-t * (10 / 91)))
      t := by
    dsimp only [f, eulerLogPoly]
    have h1 :=
      (((hasDerivAt_const t (3 : ℝ)).add ((hasDerivAt_id t).const_mul (153 / 50))).add
            ((hasDerivAt_pow 2 t).const_mul (2601 / 2500))).div_const
        8
    have h2 := (((hasDerivAt_id t).neg.mul_const (10 / 91)).exp)
    convert h1.mul h2 using 1 <;>
      first
      | (funext u; rfl)
      | (simp only [Pi.neg_apply, Pi.add_apply, id_eq]; ring)
  have hm : MonotoneOn f (Set.Icc 0 (827 / 50)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t _ ↦ (hd t).continuousAt.continuousWithinAt
    · exact fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      apply mul_nonneg _ (Real.exp_pos _).le
      obtain ⟨ht0, ht1⟩ := (interior_subset ht : t ∈ Set.Icc (0 : ℝ) (827 / 50))
      unfold eulerLogPoly
      nlinarith only [mul_nonneg ht0 (sub_nonneg.mpr ht1), ht0]
  have h :=
    hm (show v ∈ Set.Icc (0 : ℝ) (827 / 50) from ⟨hv, by linarith only [hx, hu]⟩)
      (show v + x ∈ Set.Icc (0 : ℝ) (827 / 50) from ⟨add_nonneg hv hx, hu⟩)
      (le_add_of_nonneg_right hx)
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos ((v + x) * (10 / 91))).le
  dsimp only [f] at h'
  rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add,
    show -v * (10 / 91) + (v + x) * (10 / 91) = x * (10 / 91) by ring,
    show -(v + x) * (10 / 91) + (v + x) * (10 / 91) = 0 by ring, Real.exp_zero, mul_one] at h'
  exact h'

/-- On the finite logarithmic window in section 107, the Euler polynomial and
exponential dominate the triangular prime weight with coefficient 13/200.
The growth of the polynomial reduces the effective decay rate to 409/450. -/
theorem window_weight_lower_wide {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (hu : v + x ≤ 827 / 50) :
    13 / 200 * eulerLogPoly v * shiftedTriangle (5 / 2) x ≤
      Real.exp (-(51 / 50) * x) * eulerLogPoly (v + x) := by
  have h :=
    exp_triangle_lower (by norm_num only : (0 : ℝ) < 4141 / 4550)
      (by norm_num only : (0 : ℝ) < 5 / 2) x
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (3231 / 910 : ℝ)) (n := 20) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at he
  have hk :
    (13 / 200 : ℝ) ≤ 4141 / 4550 * (5 / 2) * Real.exp (1 - 2 * (4141 / 4550) * (5 / 2)) := by
    rw [show (1 - 2 * (4141 / 4550) * (5 / 2) : ℝ) = -(3231 / 910) by norm_num only, Real.exp_neg, ←
      div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    linarith only [he]
  have hg := (mul_le_mul_of_nonneg_right hk (le_max_left 0 _)).trans h
  have hp : 0 ≤ eulerLogPoly v := by
    unfold eulerLogPoly; positivity
  have h1 := mul_le_mul_of_nonneg_left hg hp
  have h2 :=
    mul_le_mul_of_nonneg_left (euler_poly_growth_wide hv hx hu) (Real.exp_pos (-(51 / 50) * x)).le
  have heq :
    Real.exp (-(51 / 50) * x) * Real.exp (x * (10 / 91)) = Real.exp (-(4141 / 4550) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold shiftedTriangle
  linarith only [h1, h2, congrArg (fun z : ℝ ↦ eulerLogPoly v * z) heq]

/-- Restrict polynomial growth to logarithmic arguments at most 33/2. -/
theorem euler_poly_growth_626 {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (hu : v + x ≤ 33 / 2) :
    eulerLogPoly v * Real.exp (x * (10 / 91)) ≤ eulerLogPoly (v + x) := by
  exact euler_poly_growth_wide hv hx (hu.trans (by norm_num only))

/-- Restrict the triangular Euler weight comparison to arguments at most 33/2. -/
theorem window_weight_lower_626 {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (hu : v + x ≤ 33 / 2) :
    13 / 200 * eulerLogPoly v * shiftedTriangle (5 / 2) x ≤
      Real.exp (-(51 / 50) * x) * eulerLogPoly (v + x) := by
  exact window_weight_lower_wide hv hx (hu.trans (by norm_num only))

/-- Across the radius interval [300, 316] the sixth-pole Euler weight dominates the
shifted triangle divided by the square root, with a common radius-dependent coefficient. -/
theorem prime_window_euler_316 {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 316) {p : ℕ} (hp : r ^ 2 ≤ p)
    (hw : Real.log p - 2 * Real.log r ≤ 5) :
    (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) *
        (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p) ≤
      quarterEulerWeight570 p := by
  have hr : 0 < r := by linarith only [hl]
  have hpos := (sq_pos_of_pos hr).trans_le hp
  have hlog := Real.log_le_log (sq_pos_of_pos hr) hp
  rw [Real.log_pow, Nat.cast_ofNat] at hlog
  have h316 :=
    (Analysis.rationalLogIntervalCheck_sound (N := 316) (j := 8) (n := 24) (lo := 5) (hi :=
        144 / 25) (by decide +kernel)).2
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h316
  have ht :=
    window_weight_lower_wide (v := 2 * Real.log r) (x := Real.log p - 2 * Real.log r)
      (mul_nonneg (by norm_num only) (Real.log_nonneg (by linarith only [hl])))
      (sub_nonneg.mpr hlog) (by linarith only [hw, Real.log_le_log hr hu, h316])
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

/-- Across the section 107 prime window the sixth-pole Euler weight dominates the
shifted triangle divided by the square root, with a common radius-dependent coefficient. -/
theorem prime_window_euler_626 {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 313) {p : ℕ} (hp : r ^ 2 ≤ p)
    (hw : Real.log p - 2 * Real.log r ≤ 5) :
    (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) *
        (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p) ≤
      quarterEulerWeight570 p := by
  exact prime_window_euler_316 hl (hu.trans (by norm_num only)) hp hw

/-- Summing the pointwise comparison with nonnegative logarithmic weights bounds
the triangle mass of any finite subset of the window by its Euler contribution. -/
theorem sum_window_euler_316 {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 316) (s : Finset ℕ)
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
    mul_le_mul_of_nonneg_left (prime_window_euler_316 hl hu (hp p h) (hw p h))
      (Real.log_natCast_nonneg p)

/-- Summing the pointwise comparison with nonnegative logarithmic weights bounds
the triangle mass of any finite subset of the window by its Euler contribution. -/
theorem sum_window_euler_626 {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 313) (s : Finset ℕ)
    (hp : ∀ p ∈ s, r ^ 2 ≤ (p : ℝ)) (hw : ∀ p ∈ s, Real.log p - 2 * Real.log r ≤ 5) :
    (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) *
        ∑ p ∈ s,
          Real.log p * (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p) ≤
      ∑ p ∈ s, Real.log p * quarterEulerWeight570 p := by
  exact sum_window_euler_316 hl (hu.trans (by norm_num only)) s hp hw

/-- The fourfold window coefficient is bounded below by freezing the
logarithmic polynomial at a left endpoint and the power at a right endpoint. -/
private theorem window_factor_endpoint_626 {r V P : ℝ} (hr : 0 < r) (hV : 0 ≤ V)
    (hv : V ≤ 2 * Real.log r) (hP : 0 ≤ P) (hp : P ≤ r ^ (-(26 / 25 : ℝ))) :
    4 * (13 / 200 : ℝ) * (73 / 50) * (eulerLogPoly V * P) ≤
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) := by
  have hq : eulerLogPoly V ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly
    have hsq := pow_le_pow_left₀ hV hv 2
    linarith only [hv, hsq]
  have hn : 0 ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly
    have h := hV.trans hv
    positivity
  have hm := mul_le_mul hq hp hP hn
  have he : r ^ (-(51 / 25 : ℝ)) * r = r ^ (-(26 / 25 : ℝ)) := by
    calc
      _ = r ^ (-(51 / 25 : ℝ)) * r ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by
        rw [← Real.rpow_add hr]; norm_num only
  rw [show
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) =
        (4 * (13 / 200) * (73 / 50)) * (eulerLogPoly (2 * Real.log r) * (r ^ (-(51 / 25 : ℝ)) * r))
      by ring,
    he]
  exact mul_le_mul_of_nonneg_left hm (by norm_num only)

/-- Freeze the logarithmic polynomial at radius 300 and the negative power at radius 313
to bound the fourfold saving coefficient throughout the interval. -/
private theorem window_factor_gt_626 {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 313) :
    0.02085 <
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) := by
  have hr : 0 < r := by linarith only [hl]
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 300) (j := 8) (n := 24) (lo := 57 / 10) (hi := 6)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hv : (57 / 5 : ℝ) ≤ 2 * Real.log r := by
    linarith only [hlog, Real.log_le_log (by norm_num only) hl]
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 313) (p := 26) (d := 25)
        (lo := 25388 / 10000000) (hi := 1) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact
    (by norm_num only [eulerLogPoly] :
          (0.02085 : ℝ) <
            4 * (13 / 200) * (73 / 50) * (eulerLogPoly (57 / 5) * (25388 / 10000000))).trans_le
      (window_factor_endpoint_626 hr (by norm_num only) hv (by norm_num only)
        (by
          apply le_trans _ (Real.rpow_le_rpow_of_nonpos hr hu (by norm_num only))
          linarith only [hb]))

/-- A window with triangle mass at least 1.46 times the radius saves more than
0.02085 for radii between 300 and 313. -/
theorem window_euler_saving_626 {r : ℝ} (hl : 300 ≤ r) (hu : r ≤ 313) (s : Finset ℕ)
    (hp : ∀ p ∈ s, r ^ 2 ≤ (p : ℝ)) (hw : ∀ p ∈ s, Real.log p - 2 * Real.log r ≤ 5)
    (hm :
      73 / 50 * r ≤
        ∑ p ∈ s,
          Real.log p * (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p)) :
    0.02085 < 4 * ∑ p ∈ s, Real.log p * quarterEulerWeight570 p := by
  have hlog := Real.log_nonneg (show 1 ≤ r by linarith only [hl])
  have hq : 0 ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly; positivity
  have ha :=
    mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ)) by positivity)
  have hb := ha.trans (sum_window_euler_626 hl hu s hp hw)
  linarith only [window_factor_gt_626 hl hu, hb]

/-- Freeze the logarithmic polynomial at radius 313 and the negative power at radius 316
to bound the fourfold saving coefficient throughout the interval. -/
private theorem window_factor_gt_316 {r : ℝ} (hl : 313 ≤ r) (hu : r ≤ 316) :
    0.02085 <
      4 * (13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ))) * (73 / 50 * r) := by
  have hr : 0 < r := by linarith only [hl]
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 313) (j := 8) (n := 24) (lo := 1149 / 200) (hi :=
        6) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hlog
  have hv : (1149 / 100 : ℝ) ≤ 2 * Real.log r := by
    linarith only [hlog, Real.log_le_log (by norm_num only) hl]
  have hb :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 316) (p := 26) (d := 25)
        (lo := 25137 / 10000000) (hi := 1) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  exact
    (by norm_num only [eulerLogPoly] :
          (0.02085 : ℝ) <
            4 * (13 / 200) * (73 / 50) * (eulerLogPoly (1149 / 100) * (25137 / 10000000))).trans_le
      (window_factor_endpoint_626 hr (by norm_num only) hv (by norm_num only)
        (by
          apply le_trans _ (Real.rpow_le_rpow_of_nonpos hr hu (by norm_num only))
          linarith only [hb]))

/-- A window with triangle mass at least 1.46 times the radius saves more than
0.02085 for radii between 313 and 316. -/
theorem window_euler_saving_316 {r : ℝ} (hl : 313 ≤ r) (hu : r ≤ 316) (s : Finset ℕ)
    (hp : ∀ p ∈ s, r ^ 2 ≤ (p : ℝ)) (hw : ∀ p ∈ s, Real.log p - 2 * Real.log r ≤ 5)
    (hm :
      73 / 50 * r ≤
        ∑ p ∈ s,
          Real.log p * (shiftedTriangle (5 / 2) (Real.log p - 2 * Real.log r) / Real.sqrt p)) :
    0.02085 < 4 * ∑ p ∈ s, Real.log p * quarterEulerWeight570 p := by
  have hlog := Real.log_nonneg (show 1 ≤ r by linarith only [hl])
  have hq : 0 ≤ eulerLogPoly (2 * Real.log r) := by
    unfold eulerLogPoly; positivity
  have ha :=
    mul_le_mul_of_nonneg_left hm
      (show 0 ≤ 13 / 200 * eulerLogPoly (2 * Real.log r) * r ^ (-(51 / 25 : ℝ)) by positivity)
  have hb := ha.trans (sum_window_euler_316 (show 300 ≤ r by linarith only [hl]) hu s hp hw)
  linarith only [window_factor_gt_316 hl hu, hb]

end PseudoPrime.PrimeTestBounds.MillerRabin
