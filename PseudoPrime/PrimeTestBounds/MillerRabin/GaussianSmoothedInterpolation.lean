/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogWeightedDifferences
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! # Endpoint interpolation for the smoothed Chebyshev error -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The smoothed Chebyshev error in the logarithmic coordinate. -/
@[expose]
noncomputable def gaussianLogError (s : ℝ) : ℝ :=
  AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (Real.exp s) - Real.exp s +
    Real.log (2 * Real.pi) * s

private theorem smoothed_log_convex :
    ConvexOn ℝ Set.univ
      (fun s ↦ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum (Real.exp s)) := by
  apply convexOn_of_slope_mono_adjacent convex_univ
  intro a t b _ _ hat htb
  have ha :=
    (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_difference_bounds (Real.exp_pos a)
        (Real.exp_le_exp.mpr hat.le)).2
  have hb :=
    (AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum_difference_bounds (Real.exp_pos t)
        (Real.exp_le_exp.mpr htb.le)).1
  rw [← Real.exp_sub, Real.log_exp] at ha hb
  exact
    ((div_le_iff₀ (sub_pos.mpr hat)).mpr (by linarith only [ha])).trans
      ((le_div_iff₀ (sub_pos.mpr htb)).mpr hb)

private theorem exp_corrected_convex {a b M : ℝ} (hM : Real.exp b ≤ M) :
    ConvexOn ℝ (Set.Icc a b) (fun s ↦ M / 2 * s ^ 2 - Real.exp s) := by
  have hd (s : ℝ) : HasDerivAt (fun t : ℝ ↦ M / 2 * t ^ 2 - Real.exp t) (M * s - Real.exp s) s := by
    convert (((hasDerivAt_id s).pow 2).const_mul (M / 2)).sub (Real.hasDerivAt_exp s) using 1
    · funext t
      simp only [Pi.sub_apply, Pi.pow_apply, id_eq]
    · simp only [id_eq, Nat.cast_ofNat, Nat.reduceSub, pow_one, mul_one]
      ring
  apply
    convexOn_of_hasDerivWithinAt2_nonneg (f' := fun s ↦ M * s - Real.exp s) (f'' := fun s ↦
      M - Real.exp s) (convex_Icc a b) (by fun_prop)
  · exact fun s _ ↦ (hd s).hasDerivWithinAt
  · exact fun s _ ↦
      (((hasDerivAt_id s).const_mul M).sub (Real.hasDerivAt_exp s)).hasDerivWithinAt.congr_deriv
        (by simp only [mul_one])
  · intro s hs
    exact sub_nonneg.mpr ((Real.exp_le_exp.mpr (interior_subset hs).2).trans hM)

/-- Two logarithmic endpoint bounds control the smoothed error between
them, with a quadratic allowance from the exponential curvature. -/
theorem gaussian_log_error_upper {a b s M C : ℝ} (hs : s ∈ Set.Icc a b) (hM : Real.exp b ≤ M)
    (ha : gaussianLogError a ≤ C) (hb : gaussianLogError b ≤ C) :
    gaussianLogError s ≤ C + M * (b - a) ^ 2 / 8 := by
  have hM₀ := (Real.exp_pos b).le.trans hM
  have hab := hs.1.trans hs.2
  rcases hab.eq_or_lt with he | hlt
  · have h := le_antisymm (hs.2.trans_eq he.symm) hs.1
    rw [h, he, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0), mul_zero, zero_div, add_zero]
    exact hb
  let u := (b - s) / (b - a)
  let v := (s - a) / (b - a)
  have hden := sub_pos.mpr hlt
  have hu : 0 ≤ u := div_nonneg (sub_nonneg.mpr hs.2) hden.le
  have hv : 0 ≤ v := div_nonneg (sub_nonneg.mpr hs.1) hden.le
  have huv : u + v = 1 := by
    dsimp only [u, v]; field_simp [hden.ne']; ring
  have huv' : u * a + v * b = s := by
    dsimp only [u, v]; field_simp [hden.ne']; ring
  have hconv :=
    (smoothed_log_convex.subset (Set.subset_univ _) (convex_Icc a b)).add
      (exp_corrected_convex (a := a) hM)
  have h := hconv.2 (Set.left_mem_Icc.mpr hab) (Set.right_mem_Icc.mpr hab) hu hv huv
  simp only [smul_eq_mul, Pi.add_apply, huv'] at h
  unfold gaussianLogError at ha hb ⊢
  have hCa := mul_le_mul_of_nonneg_left ha hu
  have hCb := mul_le_mul_of_nonneg_left hb hv
  have hq : u * a ^ 2 + v * b ^ 2 - s ^ 2 = (s - a) * (b - s) := by
    dsimp only [u, v]
    field_simp [hden.ne']
    ring
  have hq' : (s - a) * (b - s) ≤ (b - a) ^ 2 / 4 := by nlinarith only [sq_nonneg (2 * s - a - b)]
  nlinarith only [h, hCa, hCb, mul_le_mul_of_nonneg_left hq' (by linarith only [hM₀] : 0 ≤ M / 2),
    congrArg (fun w : ℝ ↦ M / 2 * w) hq, congrArg (fun w : ℝ ↦ C * w) huv,
    congrArg (fun w : ℝ ↦ Real.log (2 * Real.pi) * w) huv']

/-- Physical endpoints give the same interpolation bound using a rational
width allowance. This permits endpoint certificates at integer cutoffs. -/
theorem gaussian_error_log_cell {a b t C : ℝ} (ha : 0 < a) (ht : t ∈ Set.Icc a b)
    (hl : gaussianLogError (Real.log a) ≤ C) (hr : gaussianLogError (Real.log b) ≤ C) :
    gaussianLogError (Real.log t) ≤ C + b * ((b - a) / a) ^ 2 / 8 := by
  have ht₀ := ha.trans_le ht.1
  have hb := ht₀.trans_le ht.2
  have hlog :=
    gaussian_log_error_upper ⟨Real.log_le_log ha ht.1, Real.log_le_log ht₀ ht.2⟩
      (le_of_eq (Real.exp_log hb)) hl hr
  have hd := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne', ← div_self ha.ne', ← sub_div] at hd
  have hsq := pow_le_pow_left₀ (sub_nonneg.mpr (Real.log_le_log ha (ht.1.trans ht.2))) hd 2
  exact
    hlog.trans
      (add_le_add (le_refl C)
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hb.le)
          (by norm_num only : (0 : ℝ) ≤ 8)))

end PseudoPrime.PrimeTestBounds.MillerRabin
