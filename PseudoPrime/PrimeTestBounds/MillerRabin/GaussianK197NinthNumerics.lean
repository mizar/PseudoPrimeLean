/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Shift
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Shift
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ConductorTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663

/-! # K197 conductor bounds from radius 335.6 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem radius_log_3356 : Real.log (1678 / 5 : ℝ) ∈ Set.Icc 5.81591 5.81593 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 1678 / 5) (j := 9) (n := 27) (lo := 5.81591)
      (hi := 5.81593) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_3356 : (1678 / 5 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000931138 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 1678 / 5) (p := 6) (d :=
        5) (lo := 0) (hi := 0.000931138) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

private theorem theta_from3356 {r : ℝ} (hr : (1678 / 5 : ℝ) ≤ r) :
    (-2.94 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (1678 / 5) := by linarith only [radius_log_3356.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.13186)
      (show 2 * Real.log (1678 / 5) - 23 / 2 ≤ 0.13186 by linarith only [radius_log_3356.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_3356 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 335.6 for all larger radii. -/
theorem quarter_main_conductor_from3356 {r : ℝ} (hr : (1678 / 5 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.64042 := by
  have hb :=
    main_conductor_box (r := 1678 / 5) (u := 1678 / 5) (z := 11.63186) (C := 1.64042)
      (by norm_num only) le_rfl (by linarith only [radius_log_3356.2]) radius_power_3356
      (by norm_num only) (by norm_num only)
  have hl : (1678 / 5 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

private theorem shift_from3356 {r s : ℝ} (hr : r ∈ Set.Icc (1678 / 5) 336.9) (hs : 1 ≤ s) :
    (-2.8785 : ℝ) ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 1678 / 5).trans_le hr.1
  have hθ : (-2.94 : ℝ) ≤ gaussianTheta197 r / s :=
    (le_div_iff₀ (zero_lt_one.trans_le hs)).mpr
      ((by linarith only [hs] : (-2.94 : ℝ) * s ≤ -2.94).trans (theta_from3356 hr.1))
  have hn : (0.0615 : ℝ) ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr (by linarith only [hr.2, gaussian_neg_pole_lower_197])
  linarith only [hθ, hn]

/-- For the ninth K197 cell the three shifted forward terms and the
positive half-point contribution have a lower bound of -2.878559. -/
theorem gaussian_shift_forward_from3356 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r s : ℝ}
    (hr : r ∈ Set.Icc (1678 / 5) 336.9) (hs : 1 ≤ s)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r / s)
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    (-2.878559 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have hwide : r ∈ Set.Icc 332.15 336.9 :=
    ⟨(by norm_num only : (332.15 : ℝ) ≤ 1678 / 5).trans hr.1, hr.2⟩
  have h := shift_forward_lower ha hb hc hRH hwide hL ht hpa hpb hpc (shift_from3356 hr hs)
  linarith only [h]

private theorem radius_log_33588 : Real.log (8397 / 25 : ℝ) ∈ Set.Icc 5.81675 5.81676 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 8397 / 25) (j := 9) (n := 27) (lo := 5.81675)
      (hi := 5.81676) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at h ⊢
  exact h

private theorem radius_power_33588 : (8397 / 25 : ℝ) ^ (-(6 / 5) : ℝ) ≤ 0.000930207 := by
  have h :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8397 / 25) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000930207) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat,
    neg_div] at h ⊢
  exact h

private theorem theta_from33588 {r : ℝ} (hr : (8397 / 25 : ℝ) ≤ r) :
    (-2.93822 : ℝ) ≤ gaussianTheta197 r := by
  have hlog : (23 / 2 : ℝ) ≤ 2 * Real.log (8397 / 25) := by linarith only [radius_log_33588.1]
  have hP :=
    conductor_poly_mono (sub_nonneg.mpr hlog) (by norm_num only : (0 : ℝ) ≤ 0.13352)
      (show 2 * Real.log (8397 / 25) - 23 / 2 ≤ 0.13352 by linarith only [radius_log_33588.2])
  have hprod :=
    (mul_le_mul_of_nonneg_left hP (Real.rpow_nonneg (by norm_num only) _)).trans
      (mul_le_mul_of_nonneg_right radius_power_33588 (by norm_num only [gaussianConductorPoly197]))
  apply gaussian_theta_endpoint_197 (by norm_num only) hr hlog
  rw [mul_assoc]
  exact
    (mul_le_mul_of_nonneg_left hprod (by norm_num only : (0 : ℝ) ≤ (11 / 10) ^ 5 / 30)).trans
      (by norm_num only [gaussianConductorPoly197])

/-- The principal inverse-scale conductor is bounded by its certified
value at radius 335.88 for all larger radii. -/
theorem quarter_main_conductor_from33588 {r : ℝ} (hr : (8397 / 25 : ℝ) ≤ r) :
    4 * r * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.63974 := by
  have hb :=
    main_conductor_box (r := 8397 / 25) (u := 8397 / 25) (z := 11.63352) (C := 1.63974)
      (by norm_num only) le_rfl (by linarith only [radius_log_33588.2]) radius_power_33588
      (by norm_num only) (by norm_num only)
  have hl : (8397 / 25 : ℝ) ∈ Set.Ici 328 := by norm_num only [Set.mem_Ici]
  have he := main_conductor_antitone hl (hl.trans hr) hr
  exact he.trans (by simpa only [sub_self, mul_zero, add_zero] using hb)

/-- For the tenth K197 scale, the conductor and half-point charge is
bounded using the left radius and the exact Gaussian multiplier. -/
theorem gaussian_shift_cell10_cost {r : ℝ} (hr : r ∈ Set.Icc (8397 / 25) 336.02) :
    (-2.87421 : ℝ) ≤
      gaussianTheta197 r / (1000790836787 / 1000000000000) + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 8397 / 25).trans_le hr.1
  have hθ : (-2.93591 : ℝ) ≤ gaussianTheta197 r / (1000790836787 / 1000000000000) :=
    (le_div_iff₀ (by norm_num only)).mpr
      ((by norm_num only : (-2.93591 : ℝ) * (1000790836787 / 1000000000000) ≤ -2.93822).trans
        (theta_from33588 hr.1))
  have hn : (0.0617 : ℝ) ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr (by linarith only [hr.2, gaussian_neg_pole_lower_197])
  linarith only [hθ, hn]

/-- For the tenth K197 cell the three shifted forward terms and the
positive half-point contribution have a lower bound of -2.874269. -/
theorem gaussian_shift_forward_cell10 {p q k : ℕ} [NeZero p] [NeZero q] [NeZero k]
    {a : DirichletCharacter ℂ p} {b : DirichletCharacter ℂ q} {c : DirichletCharacter ℂ k}
    (ha : a.IsPrimitive ∧ a ≠ 1 ∧ a⁻¹ = a ∧ a.Even) (hb : b.IsPrimitive ∧ b ≠ 1 ∧ b⁻¹ = b ∧ b.Even)
    (hc : c.IsPrimitive ∧ c ≠ 1 ∧ c⁻¹ = c ∧ c.Even) (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc (8397 / 25) 336.02)
    (hL : Real.log p + Real.log q + Real.log k = 4 * r / (1000790836787 / 1000000000000))
    (ht : ∀ n : ℕ, (a n).re + (b n).re + (c n).re ∈ Set.Icc (-1) 3)
    (hpa : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → a l = 1)
    (hpb : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → b l = 1)
    (hpc : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ r ^ 2 → c l = 1) :
    (-2.874269 : ℝ) ≤
      (gaussianShiftedForward197 a r + gaussianShiftedForward197 b r +
          gaussianShiftedForward197 c r) +
        gaussianHalfCoeff197 * r := by
  have hwide : r ∈ Set.Icc 332.15 336.9 :=
    ⟨(by norm_num only : (332.15 : ℝ) ≤ 8397 / 25).trans hr.1, hr.2.trans (by norm_num only)⟩
  have h := shift_forward_lower ha hb hc hRH hwide hL ht hpa hpb hpc (gaussian_shift_cell10_cost hr)
  linarith only [h]

end PseudoPrime.PrimeTestBounds.MillerRabin
