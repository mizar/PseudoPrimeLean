/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerBoundary570

/-! # Uniform numerical gap for the section 31 contour comparison -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Exponential times a fifth power of the shifted log in the conductor term. -/
private noncomputable def profile (r : ℝ) : ℝ :=
  Real.exp (-(13 / 25 : ℝ) * (14 / 5 + 2 * Real.log r)) * (14 / 5 + 2 * Real.log r) ^ 5

/-- On radii at least 278 the shifted-log profile decreases because the negative
exponential derivative dominates the fifth-power derivative. -/
private theorem profile_anti {a r : ℝ} (ha : 278 ≤ a) (hl : a ≤ r) : profile r ≤ profile a := by
  have hz0 : (14 : ℝ) ≤ 14 / 5 + 2 * Real.log 278 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound (N := 278) (j := 8) (n := 16) (lo := 56 / 10) (hi :=
          6) (by decide +kernel)).1
    norm_num only [Rat.cast_ofNat, Rat.cast_div, Nat.cast_ofNat] at h
    linarith only [h]
  have hap : 0 < a := by linarith only [ha]
  have hbase := Real.log_le_log (by norm_num only : (0 : ℝ) < 278) ha
  have hz : (14 : ℝ) ≤ 14 / 5 + 2 * Real.log a := by linarith only [hz0, hbase]
  have hf : AntitoneOn (fun z : ℝ ↦ Real.exp (-(13 / 25 : ℝ) * z) * z ^ 5) (Set.Ici 14) := by
    have hd (z : ℝ) :=
      (((hasDerivAt_id z).const_mul (-(13 / 25 : ℝ))).exp).mul ((hasDerivAt_id z).pow 5)
    apply antitoneOn_of_deriv_nonpos (convex_Ici _)
    · exact fun z _ ↦ (hd z).continuousAt.continuousWithinAt
    · exact fun z _ ↦ (hd z).differentiableAt.differentiableWithinAt
    · intro z h
      have hz' : 14 ≤ z := interior_subset h
      change deriv ((fun t : ℝ ↦ Real.exp (-(13 / 25 : ℝ) * id t)) * (id : ℝ → ℝ) ^ 5) z ≤ 0
      rw [(hd z).deriv]
      simp only [id_eq, mul_one, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub]
      have hw : 0 ≤ Real.exp (-(13 / 25 : ℝ) * z) * z ^ 4 := by positivity
      have hn : 5 - 13 / 25 * z ≤ 0 := by linarith only [hz']
      linear_combination mul_nonpos_of_nonneg_of_nonpos hw hn
  have hlog := Real.log_le_log hap hl
  have hh : 14 / 5 + 2 * Real.log a ≤ 14 / 5 + 2 * Real.log r := by linarith only [hlog]
  exact hf hz (hz.trans hh) hh

/-- After multiplying the reflected unit weight by the radius, the explicit kernel yields
the shifted-log profile with a positive constant factor. -/
private theorem profile_identity {r : ℝ} (hl : 278 ≤ r) :
    r * (quarterKernel570.transform (1 / r ^ 2)).re =
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(7 / 5 : ℝ))) * profile r := by
  have hr : 0 < r := by linarith only [hl]
  have hL := Real.log_nonneg (show 1 ≤ r by linarith only [hl])
  rw [quarterKernel570,
    LLS.PaperStatements.rationalPole_transform _ _ _ _ (one_div_pos.mpr (sq_pos_of_pos hr)),
    Complex.ofReal_re]
  have he : Real.log (1 / r ^ 2) = -(2 * Real.log r) := by
    rw [one_div, Real.log_inv, Real.log_pow, Nat.cast_ofNat]
  rw [Analysis.rationalPoleProfile,
    ite_eq_left
      ⟨one_div_pos.mpr (sq_pos_of_pos hr), by
        rw [he]; linarith only [hL]⟩,
    he]
  norm_num only [Nat.factorial, Nat.reduceMul, Nat.reduceSub, Nat.cast_ofNat]
  unfold profile
  generalize hx : Real.log r = x
  nth_rw 1 [← Real.exp_log hr, hx]
  have h :
    Real.exp x * Real.exp (-((14 / 5 - -(2 * x)) / (50 / 51))) =
      Real.exp (-(7 / 5)) * Real.exp (-(13 / 25) * (14 / 5 + 2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  linear_combination (((14 / 5 - -(2 * x)) / (50 / 51)) ^ 5 / 120) * h

/-- Above radius 278 the reflected conductor contribution is bounded by its value
at any smaller radius in the same range. -/
theorem conductor_radius_antitone {a r : ℝ} (ha : 278 ≤ a) (hl : a ≤ r) :
    r * (quarterKernel570.transform (1 / r ^ 2)).re ≤
      a * (quarterKernel570.transform (1 / a ^ 2)).re := by
  rw [profile_identity (ha.trans hl), profile_identity ha]
  exact mul_le_mul_of_nonneg_left (profile_anti ha hl) (by positivity)

/-- Multiplying the unit reflected weight by the radius costs less than 0.834 above 278.
Use the decreasing profile and the existing upper bound at radius 278. -/
theorem conductor_radius_upper_570 {r : ℝ} (hl : 278 ≤ r) :
    r * (quarterKernel570.transform (1 / r ^ 2)).re < 834 / 1000 := by
  have he := conductor_radius_antitone (le_refl 278) hl
  have ht := (quarter_reflected_weight_570 (le_refl 278) (by norm_num only)).2
  linarith only [he, ht]

/-- Throughout the section 31 interval, the numerical lower expression in (31.8.2)
exceeds 0.003. Uniform tail and conductor estimates suffice without differentiating the gap. -/
theorem radius_gap_570 {r : ℝ} (hl : 278 ≤ r) (hu : r ≤ 285) :
    let R := (quarterKernel570.transform (1 / r ^ 2)).re
    let E := 4 * (r * R) + 4 * positiveTail570 (r ^ 2)
    3 / 1000 <
      -(32711 / 1000000) * r + 13386 / 1000 - 29136 / 100000 - E + 916 / 10000 +
        3 * (3575 / 100000) +
        (1113 / 1000) * R +
        234 / 100000 := by
  dsimp only
  have hc := conductor_radius_upper_570 hl
  have ht := radius_tail_numeric hl hu
  have hr := (quarter_reflected_weight_570 hl hu).1
  linarith only [hc, ht, hr, hu]

/-- From radius 288 onward the conductor term is less than 0.824. Evaluate
the monotone radius-weight product at 288 using the explicit kernel estimate. -/
theorem conductor_radius_upper_of_288 {r : ℝ} (hl : 288 ≤ r) :
    r * (quarterKernel570.transform (1 / r ^ 2)).re < 824 / 1000 := by
  have hm := conductor_radius_antitone (by norm_num only : (278 : ℝ) ≤ 288) hl
  have hw := reflected_weight_upper_of_288 (le_refl (288 : ℝ))
  linarith only [hm, hw]

end PseudoPrime.PrimeTestBounds.MillerRabin
