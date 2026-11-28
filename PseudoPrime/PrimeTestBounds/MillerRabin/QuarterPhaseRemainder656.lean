/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseScalar656
import PseudoPrime.Analysis.LogTaylorBounds

/-! # Scalar remainder budget for section 132 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The polynomial multiplying the exponentially decaying part of the
section 132 remainder, in the shifted logarithmic coordinate. -/
private noncomputable def remPoly (z : ℝ) : ℝ :=
  789 / 700 * z ^ 5 - 47 / 7 * z ^ 4 + 125 / 21 * z ^ 3

/-- Differentiating the decaying polynomial leaves a polynomial with
nonpositive coefficients after translating the origin to fourteen. -/
private theorem rem_deriv_nonpos {z : ℝ} (hz : 14 ≤ z) :
    5 * (789 / 700) * z ^ 4 - 4 * (47 / 7) * z ^ 3 + 3 * (125 / 21) * z ^ 2 - 11 / 10 * remPoly z ≤
      0 := by
  let y := z - 14
  have hy : 0 ≤ y := sub_nonneg.mpr hz
  have he : z = y + 14 := by
    dsimp only [y]; ring
  rw [he, remPoly]
  have h2 := pow_nonneg hy 2
  have h3 := pow_nonneg hy 3
  have h4 := pow_nonneg hy 4
  have h5 := pow_nonneg hy 5
  linarith only [hy, h2, h3, h4, h5]

/-- Exponential decay dominates the section 132 remainder polynomial
once the shifted logarithm is at least fourteen. -/
private theorem rem_profile_antitone :
    AntitoneOn (fun z : ℝ ↦ Real.exp (-(11 / 10) * z) * remPoly z) (Set.Ici 14) := by
  let f := fun z : ℝ ↦ Real.exp (-(11 / 10) * z) * remPoly z
  have hd (z : ℝ) :
    HasDerivAt f
      (Real.exp (-(11 / 10) * z) *
        (5 * (789 / 700) * z ^ 4 - 4 * (47 / 7) * z ^ 3 + 3 * (125 / 21) * z ^ 2 -
          11 / 10 * remPoly z))
      z := by
    have he := ((hasDerivAt_id z).const_mul (-(11 / 10 : ℝ))).exp
    have hp :=
      (((hasDerivAt_pow 5 z).const_mul (789 / 700 : ℝ)).sub
            ((hasDerivAt_pow 4 z).const_mul (47 / 7 : ℝ))).add
        ((hasDerivAt_pow 3 z).const_mul (125 / 21 : ℝ))
    apply (show HasDerivAt f _ z from he.mul hp).congr_deriv
    simp only [remPoly, id_eq, Nat.cast_ofNat]
    ring
  apply
    antitoneOn_of_deriv_nonpos (convex_Ici _) (fun z _ ↦ (hd z).continuousAt.continuousWithinAt)
      (fun z _ ↦ (hd z).differentiableAt.differentiableWithinAt)
  intro z hz
  rw [(hd z).deriv]
  exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le (rem_deriv_nonpos (interior_subset hz))

/-- The scalar remainder allowance from the section 132 comparison.
The first term incorporates the shifted kernel normalization and the
second term is the inverse-fifth-power correction in the radius. -/
noncomputable def quarterPhaseRem656 (r : ℝ) : ℝ :=
  let z := 21 / 8 + 2 * Real.log r
  let C := (11 / 10 : ℝ) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120
  3 * (11 / 10 : ℝ) ^ 5 / 120 * (Real.exp (-(11 / 10) * z) * remPoly z) +
    5 / 3 * C * (21 / 8) ^ 4 * (5 - (3 / 5) * (21 / 8)) / r ^ 5

private theorem log_322_bounds :
    (5774551543203 / 1000000000000 : ℝ) ≤ Real.log 322 ∧
      Real.log 322 ≤ 5774551547707 / 1000000000000 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 322) (j := 9) (n := 27) (lo :=
      5774551543203 / 1000000000000) (hi := 5774551547707 / 1000000000000) (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- The remainder allowance decreases from the left end of the section
132 radius range. -/
theorem quarter_phase_rem_antitone_656 : AntitoneOn quarterPhaseRem656 (Set.Ici 322) := by
  intro l hl r hr hlr
  have hl0 := (by norm_num only : (0 : ℝ) < 322).trans_le hl
  have hlog := Real.log_le_log hl0 hlr
  have hb : 14 ≤ 21 / 8 + 2 * Real.log l := by
    linarith only [log_322_bounds.1, Real.log_le_log (by norm_num only : (0 : ℝ) < 322) hl]
  have hb' : 14 ≤ 21 / 8 + 2 * Real.log r := by linarith only [hb, hlog]
  have hm :=
    rem_profile_antitone hb hb'
      (show 21 / 8 + 2 * Real.log l ≤ 21 / 8 + 2 * Real.log r by linarith only [hlog])
  unfold quarterPhaseRem656
  dsimp only
  exact
    add_le_add (mul_le_mul_of_nonneg_left hm (by norm_num only))
      (div_le_div_of_nonneg_left (by positivity) (pow_pos hl0 5) (pow_le_pow_left₀ hl0.le hlr 5))

/-- A rational Taylor estimate for the exponential at the left endpoint
gives a bound for the exponentially decaying remainder term. -/
private theorem rem_exp_322 {z : ℝ} (hz : 14.174103 ≤ z) :
    Real.exp (-(11 / 10) * z) ≤ 169314 / 1000000000000 := by
  have hx : (-(11 / 10 : ℝ)) * z ≤ -(11 / 10 * 14.174103) := by linarith only [hz]
  apply (Real.exp_le_exp.mpr hx).trans
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 11 / 10 * 14.174103) 46
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h
  linarith only [h]

/-- The scalar allowance at any radius from 322 to 328 fits within the
remainder budget subtracted from the finite zero sum. -/
theorem quarter_phase_rem_le_656 {r : ℝ} (hr : 322 ≤ r) :
    quarterPhaseRem656 r ≤ 2665 / 1000000 := by
  apply (quarter_phase_rem_antitone_656 (Set.mem_Ici.mpr le_rfl) hr hr).trans
  let z : ℝ := 21 / 8 + 2 * Real.log 322
  have hlo : 14.174103 ≤ z := by
    dsimp only [z]; linarith only [log_322_bounds.1]
  have hhi : z ≤ 14.1741032 := by
    dsimp only [z]; linarith only [log_322_bounds.2]
  have hp5 := pow_le_pow_left₀ (by linarith only [hlo] : 0 ≤ z) hhi 5
  have hp4 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 14.174103) hlo 4
  have hp3 := pow_le_pow_left₀ (by linarith only [hlo] : 0 ≤ z) hhi 3
  have hp : remPoly z ≤ 390835 := by
    unfold remPoly; linarith only [hp5, hp4, hp3]
  have hm :=
    mul_le_mul hp (rem_exp_322 hlo) (Real.exp_pos _).le (by norm_num only : (0 : ℝ) ≤ 390835)
  let C := (11 / 10 : ℝ) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120
  have hC : C ≤ 0.000748 := by
    dsimp only [C]
    linarith only [quarter_phase_normalization_656.2]
  change
    3 * (11 / 10 : ℝ) ^ 5 / 120 * (Real.exp (-(11 / 10) * z) * remPoly z) +
        5 / 3 * C * (21 / 8) ^ 4 * (5 - (3 / 5) * (21 / 8)) / (322 : ℝ) ^ 5 ≤
      _
  rw [mul_comm (Real.exp _) (remPoly z)]
  linarith only [hm, hC]

end PseudoPrime.PrimeTestBounds.MillerRabin
