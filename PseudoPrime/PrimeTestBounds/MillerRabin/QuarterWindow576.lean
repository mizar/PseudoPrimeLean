/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterIdentity576

/-! # Triangular window bounds for the section 86 Euler weight -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The section 76 triangular weight of half-width H, shifted to the interval from zero to 2H. -/
noncomputable def shiftedTriangle (H x : ℝ) : ℝ :=
  max 0 (1 - |x - H| / H)

/-- A supporting line to the exponential bounds the shifted triangle at every real x.
The coefficient is aH exp(1 - 2aH) for positive a and H. -/
theorem exp_triangle_lower {a H : ℝ} (ha : 0 < a) (hH : 0 < H) (x : ℝ) :
    a * H * Real.exp (1 - 2 * a * H) * shiftedTriangle H x ≤ Real.exp (-a * x) := by
  have h := Real.add_one_le_exp (a * (2 * H - x) - 1)
  have he := mul_le_mul_of_nonneg_left h (Real.exp_pos (1 - 2 * a * H)).le
  rw [← Real.exp_add, show 1 - 2 * a * H + (a * (2 * H - x) - 1) = -a * x by ring] at he
  unfold shiftedTriangle
  rcases le_total (1 - |x - H| / H) 0 with hn | hp
  · rw [max_eq_left hn, mul_zero]
    exact (Real.exp_pos _).le
  rw [max_eq_right hp, mul_assoc a H, mul_assoc]
  have hlin : H * (1 - |x - H| / H) ≤ 2 * H - x := by
    field_simp [hH.ne']
    nlinarith only [le_abs_self (x - H), mul_le_mul_of_nonneg_right (le_abs_self (x - H)) hH.le]
  have hb := mul_le_mul_of_nonneg_left hlin (mul_pos ha (Real.exp_pos (1 - 2 * a * H))).le
  linarith only [hb, he]

/-- The quadratic polynomial in the section 31 Euler weight at logarithmic argument v. -/
noncomputable def eulerLogPoly (v : ℝ) : ℝ :=
  (3 + 153 / 50 * v + 2601 / 2500 * v ^ 2) / 8

/-- Through logarithmic argument 329/20, the polynomial grows at least as fast as
exp(v/9) relative to its initial value. Differentiate the exponentially damped polynomial. -/
theorem euler_poly_growth_600 {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (hu : v + x ≤ 329 / 20) :
    eulerLogPoly v * Real.exp (x / 9) ≤ eulerLogPoly (v + x) := by
  let f := fun t : ℝ ↦ eulerLogPoly t * Real.exp (-t / 9)
  have hd (t : ℝ) :
    HasDerivAt f (((153 / 50 + 2 * (2601 / 2500) * t) / 8 - eulerLogPoly t / 9) * Real.exp (-t / 9))
      t := by
    dsimp only [f, eulerLogPoly]
    have h1 :=
      (((hasDerivAt_const t (3 : ℝ)).add ((hasDerivAt_id t).const_mul (153 / 50))).add
            ((hasDerivAt_pow 2 t).const_mul (2601 / 2500))).div_const
        8
    have h2 := (((hasDerivAt_id t).neg.div_const 9).exp)
    convert h1.mul h2 using 1 <;>
      first
      | (funext u; rfl)
      | (simp only [Pi.neg_apply, Pi.add_apply, id_eq]; ring)
  have hm : MonotoneOn f (Set.Icc 0 (329 / 20)) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
    · exact fun t _ ↦ (hd t).continuousAt.continuousWithinAt
    · exact fun t _ ↦ (hd t).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [(hd t).deriv]
      apply mul_nonneg _ (Real.exp_pos _).le
      obtain ⟨ht0, ht1⟩ := (interior_subset ht : t ∈ Set.Icc (0 : ℝ) (329 / 20))
      unfold eulerLogPoly
      nlinarith only [mul_nonneg ht0 (sub_nonneg.mpr ht1), ht0]
  have h :=
    hm (show v ∈ Set.Icc (0 : ℝ) (329 / 20) from ⟨hv, by linarith only [hx, hu]⟩)
      (show v + x ∈ Set.Icc (0 : ℝ) (329 / 20) from ⟨add_nonneg hv hx, hu⟩)
      (le_add_of_nonneg_right hx)
  have h' := mul_le_mul_of_nonneg_right h (Real.exp_pos ((v + x) / 9)).le
  dsimp only [f] at h'
  rw [mul_assoc, ← Real.exp_add, mul_assoc, ← Real.exp_add,
    show -v / 9 + (v + x) / 9 = x / 9 by ring, show -(v + x) / 9 + (v + x) / 9 = 0 by ring,
    Real.exp_zero, mul_one] at h'
  exact h'

/-- On the finite logarithmic window in section 99, the Euler polynomial and
exponential dominate the triangular prime weight with coefficient 13/200.
The growth of the polynomial reduces the effective decay rate to 409/450. -/
theorem window_weight_lower_600 {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (hu : v + x ≤ 329 / 20) :
    13 / 200 * eulerLogPoly v * shiftedTriangle (5 / 2) x ≤
      Real.exp (-(51 / 50) * x) * eulerLogPoly (v + x) := by
  have h :=
    exp_triangle_lower (by norm_num only : (0 : ℝ) < 409 / 450) (by norm_num only : (0 : ℝ) < 5 / 2)
      x
  have he :=
    Analysis.exp_le_taylor_add_two_next (x := (319 / 90 : ℝ)) (n := 20) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at he
  have hk : (13 / 200 : ℝ) ≤ 409 / 450 * (5 / 2) * Real.exp (1 - 2 * (409 / 450) * (5 / 2)) := by
    rw [show (1 - 2 * (409 / 450) * (5 / 2) : ℝ) = -(319 / 90) by norm_num only, Real.exp_neg, ←
      div_eq_mul_inv]
    apply (le_div_iff₀ (Real.exp_pos _)).mpr
    linarith only [he]
  have hg := (mul_le_mul_of_nonneg_right hk (le_max_left 0 _)).trans h
  have hp : 0 ≤ eulerLogPoly v := by
    unfold eulerLogPoly; positivity
  have h1 := mul_le_mul_of_nonneg_left hg hp
  have h2 :=
    mul_le_mul_of_nonneg_left (euler_poly_growth_600 hv hx hu) (Real.exp_pos (-(51 / 50) * x)).le
  have heq : Real.exp (-(51 / 50) * x) * Real.exp (x / 9) = Real.exp (-(409 / 450) * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold shiftedTriangle
  linarith only [h1, h2, congrArg (fun z : ℝ ↦ eulerLogPoly v * z) heq]

/-- Restrict the exponential growth comparison to the section 86 window. -/
theorem euler_poly_growth {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (hu : v + x ≤ 49 / 3) :
    eulerLogPoly v * Real.exp (x / 9) ≤ eulerLogPoly (v + x) := by
  exact euler_poly_growth_600 hv hx (hu.trans (by norm_num only))

/-- Restrict the triangular Euler comparison to the section 86 window. -/
theorem window_weight_lower_576 {v x : ℝ} (hv : 0 ≤ v) (hx : 0 ≤ x) (hu : v + x ≤ 49 / 3) :
    13 / 200 * eulerLogPoly v * shiftedTriangle (5 / 2) x ≤
      Real.exp (-(51 / 50) * x) * eulerLogPoly (v + x) := by
  exact window_weight_lower_600 hv hx (hu.trans (by norm_num only))

end PseudoPrime.PrimeTestBounds.MillerRabin
