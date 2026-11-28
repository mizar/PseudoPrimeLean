/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseMonotone117

/-! # Left-endpoint bounds for the section 117 phase remainder -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The shifted conductor term expressed in the logarithmic cutoff. -/
noncomputable def phaseTheta117 (x : ℝ) : ℝ :=
  ((51 / 50 : ℝ) ^ 5 / 30) *
    (3.143 * phaseConductorMonomial117 0 x -
      3.124 * Real.exp ((51 / 50) * (1 / 50)) * phaseConductorMonomial117 (1 / 50) x -
      0.0374 * Real.exp ((51 / 50) * (11 / 10)) * phaseConductorMonomial117 (11 / 10) x)

private theorem phase_theta_box117 {l x u m T : ℝ} (hl : 11 / 10 ≤ l) (hx : x ∈ Set.Icc l u)
    (he : Real.exp (-(13 / 25) * x) ≤ m) (hT : 0 ≤ T)
    (hb :
      3.124 * 1.0206095022 * (u - 1 / 50) ^ 5 + 0.0374 * 3.070990047 * (u - 11 / 10) ^ 5 -
          3.143 * l ^ 5 ≤
        T) :
    -(51 / 50 : ℝ) ^ 5 / 30 * (m * T) ≤ phaseTheta117 x := by
  have h₁ :=
    Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (1 / 50)) (n := 24) (by norm_num only)
      (by norm_num only)
  have h₂ :=
    Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (11 / 10)) (n := 24)
      (by norm_num only) (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h₁ h₂
  have hA : Real.exp ((51 / 50 : ℝ) * (1 / 50)) ≤ 1.0206095022 := by linarith only [h₁]
  have hB : Real.exp ((51 / 50 : ℝ) * (11 / 10)) ≤ 3.070990047 := by linarith only [h₂]
  have hp₀ := pow_le_pow_left₀ (show 0 ≤ l by linarith only [hl]) hx.1 5
  have hn : 0 ≤ x - 1 / 50 := by linarith only [hl, hx.1]
  have hf : 0 ≤ x - 11 / 10 := by linarith only [hl, hx.1]
  have hp₁ :=
    mul_le_mul hA (pow_le_pow_left₀ hn (sub_le_sub_right hx.2 _) 5) (pow_nonneg hn _)
      (by norm_num only)
  have hp₂ :=
    mul_le_mul hB (pow_le_pow_left₀ hf (sub_le_sub_right hx.2 _) 5) (pow_nonneg hf _)
      (by norm_num only)
  have h :=
    (mul_le_mul_of_nonneg_left
          (show
            3.124 * Real.exp ((51 / 50) * (1 / 50)) * (x - 1 / 50) ^ 5 +
                  0.0374 * Real.exp ((51 / 50) * (11 / 10)) * (x - 11 / 10) ^ 5 -
                3.143 * x ^ 5 ≤
              T
            by linarith only [hp₀, hp₁, hp₂, hb])
          (Real.exp_pos (-(13 / 25) * x)).le).trans
      (mul_le_mul_of_nonneg_right he hT)
  unfold phaseTheta117 phaseConductorMonomial117
  rw [sub_zero]
  linear_combination ((51 / 50 : ℝ) ^ 5 / 30) * h

/-- The shifted conductor at radius 314 has a certified lower bound. -/
theorem section117_theta_314 : -1632922230 / 10 ^ 9 ≤ phaseTheta117 (2 * Real.log (314)) := by
  obtain ⟨he, _, _, _⟩ := section117_exp_box_314
  apply
    le_trans _
      (phase_theta_box117 (T := 1753447354 / 10 ^ 5) (by norm_num only) section117_log_box_314 he.2
        (by norm_num only) (by norm_num only))
  norm_num only

/-- The shifted conductor at radius 314.45 has a certified lower bound. -/
theorem section117_theta_314_45 :
    -1632823287 / 10 ^ 9 ≤ phaseTheta117 (2 * Real.log (6289 / 20)) := by
  obtain ⟨he, _, _, _⟩ := section117_exp_box_314_45
  apply
    le_trans _
      (phase_theta_box117 (T := 1755954442 / 10 ^ 5) (by norm_num only) section117_log_box_314_45
        he.2 (by norm_num only) (by norm_num only))
  norm_num only

/-- The shifted conductor at radius 315 has a certified lower bound. -/
theorem section117_theta_315 : -1632701618 / 10 ^ 9 ≤ phaseTheta117 (2 * Real.log (315)) := by
  obtain ⟨he, _, _, _⟩ := section117_exp_box_315
  apply
    le_trans _
      (phase_theta_box117 (T := 1759017639 / 10 ^ 5) (by norm_num only) section117_log_box_315 he.2
        (by norm_num only) (by norm_num only))
  norm_num only

private theorem section117_forward_at_radius {r : ℝ} (hr : 0 < r) :
    let X := r ^ 2
    threeShiftForward117 (2 * Real.log r) =
      phaseTheta117 (2 * Real.log r) + phaseRecip117 * Real.exp (-(2 * Real.log r) / 2) -
        4 *
          (threeShiftEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * threeShiftEulerDensity X +
            threeShiftEulerError X) := by
  have h : Real.exp (2 * Real.log r) = r ^ 2 := by rw [two_mul, Real.exp_add, Real.exp_log hr, sq]
  unfold threeShiftForward117 phaseTheta117
  dsimp only
  rw [h]
  ring

/-- The finite phase remainder at radius 314 exceeds 0.007541. -/
theorem section117_remainder_314 : 0.007541 < threeShiftRemainder117 (314) := by
  have hr : 0 < (314 : ℝ) := by norm_num only
  rw [three_shift_remainder_forward_eq hr, section117_forward_at_radius hr]
  have hE := section117_euler_cost_314
  dsimp only at hE
  linarith only [phase_pole_lower117, phase_recip_at_radius117 hr, section117_theta_314, hE,
    section117_ref_cost_314]

/-- The finite phase remainder at radius 314.45 exceeds 0.008023. -/
theorem section117_remainder_314_45 : 0.008023 < threeShiftRemainder117 (6289 / 20) := by
  have hr : 0 < (6289 / 20 : ℝ) := by norm_num only
  rw [three_shift_remainder_forward_eq hr, section117_forward_at_radius hr]
  have hE := section117_euler_cost_314_45
  dsimp only at hE
  linarith only [phase_pole_lower117, phase_recip_at_radius117 hr, section117_theta_314_45, hE,
    section117_ref_cost_314_45]

/-- The finite phase remainder at radius 315 exceeds 0.008611. -/
theorem section117_remainder_315 : 0.008611 < threeShiftRemainder117 (315) := by
  have hr : 0 < (315 : ℝ) := by norm_num only
  rw [three_shift_remainder_forward_eq hr, section117_forward_at_radius hr]
  have hE := section117_euler_cost_315
  dsimp only at hE
  linarith only [phase_pole_lower117, phase_recip_at_radius117 hr, section117_theta_315, hE,
    section117_ref_cost_315]

/-- The certified left endpoints bound the remainder over all three section 117 rows. -/
theorem section117_remainder_lower {r : ℝ} (hr : r ∈ Set.Icc 314 316) :
    (if r ≤ 6289 / 20 then 0.007541 else if r ≤ 315 then 0.008023 else 0.008611) <
      threeShiftRemainder117 r := by
  by_cases h : r ≤ 6289 / 20
  · rw [ite_eq_left h]
    exact
      section117_remainder_314.trans_le
        (section117_remainder_mono (by norm_num only [Set.mem_Icc, and_self]) hr hr.1)
  rw [ite_eq_right h]
  by_cases h' : r ≤ 315
  · rw [ite_eq_left h']
    exact
      section117_remainder_314_45.trans_le
        (section117_remainder_mono (by norm_num only [Set.mem_Icc, and_self]) hr (le_of_not_ge h))
  rw [ite_eq_right h']
  exact
    section117_remainder_315.trans_le
      (section117_remainder_mono (by norm_num only [Set.mem_Icc, and_self]) hr (le_of_not_ge h'))

end PseudoPrime.PrimeTestBounds.MillerRabin
