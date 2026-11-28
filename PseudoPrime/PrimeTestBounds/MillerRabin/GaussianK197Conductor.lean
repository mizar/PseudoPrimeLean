/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ReflectionEarly
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import PseudoPrime.Analysis.LogTaylorBounds
import PseudoPrime.AnalyticNumberTheory.Arithmetic.TruncatedEulerCertificates3

/-! # Conductor and half-point terms of the K197 shifts -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The conductor contribution after combining the six K197 shifts. -/
@[expose]
noncomputable def gaussianTheta197 (r : ℝ) : ℝ :=
  -(11 / 10) ^ 5 / 30 * r ^ (-(6 / 5) : ℝ) * gaussianJoint197 (2 * Real.log r)

/-- The inverse transforms of the shared principal kernel combine into
the K197 conductor polynomial at scale `r`. -/
theorem gaussian_theta_sum_197 {r : ℝ} (hr : 328 ≤ r) :
    (∑ i,
        (gaussianCoeff197 i : ℝ) *
          (4 * r *
            (quarterKernel656.transform (r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)))⁻¹).re)) =
      gaussianTheta197 r := by
  have hr₀ : 0 < r := by linarith only [hr]
  have he (i : Fin 6) := conductor_profile hr i
  have hf (i : Fin 6) := aux_conductor_factor hr₀ (quarterShift663 i : ℝ)
  dsimp only at he hf
  unfold gaussianTheta197 gaussianJoint197
  simp only [he, hf, mul_assoc, mul_left_comm (gaussianCoeff197 _ : ℝ), ← Finset.mul_sum]
  ring

/-- The negative half-point coefficient before division by the radius. -/
@[expose]
noncomputable def gaussianNegPole197 : ℝ :=
  -(3 * (11 / 10) ^ 5 / (3 / 5) ^ 6) *
    ∑ i, (gaussianCoeff197 i : ℝ) * Real.exp ((quarterShift663 i : ℝ) / 2)

/-- The six negative half-point terms sum to the signed K197 residue over
the physical radius. -/
theorem gaussian_neg_pole_sum_197 {r : ℝ} (hr : 0 < r) :
    -3 *
        (∑ i,
          (gaussianCoeff197 i : ℝ) *
            (quarterKernel656.function ((-1 / 2 : ℝ) : ℂ) *
                ((r ^ 2 * Real.exp (-(quarterFreq663 i : ℝ)) : ℝ) : ℂ) ^ ((-1 / 2 : ℝ) : ℂ)).re) =
      gaussianNegPole197 / r := by
  have h (i : Fin 6) := quarter_shifted_neg_pole_656 hr (quarterShift663 i : ℝ)
  have hs (i : Fin 6) : 21 / 8 + (quarterShift663 i : ℝ) = quarterFreq663 i := by
    simp only [quarterShift663, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat]
    ring
  unfold gaussianNegPole197
  simp only [← hs, h, mul_left_comm (gaussianCoeff197 _ : ℝ), ← Finset.mul_sum]
  ring

private def negPoleApprox : ℚ :=
  -(3 * (11 / 10) ^ 5 / (3 / 5) ^ 6) *
    ∑ i, gaussianCoeff197 i * profileExpTaylor (quarterShift663 i / 2)

/-- A rational Taylor certificate bounds the K197 negative half-point coefficient. -/
theorem gaussian_neg_pole_lower_197 : (20.74 : ℝ) ≤ gaussianNegPole197 := by
  let c : ℝ := -(3 * (11 / 10) ^ 5 / (3 / 5) ^ 6)
  have hshift : ∀ i : Fin 6, |quarterShift663 i / 2| ≤ 11 := by decide +kernel
  have hcoeff : ∀ i : Fin 6, |gaussianCoeff197 i| ≤ 1 := by decide +kernel
  have he (i : Fin 6) :
    |(gaussianCoeff197 i : ℝ) * Real.exp ((quarterShift663 i : ℝ) / 2) -
          (gaussianCoeff197 i : ℝ) * (profileExpTaylor (quarterShift663 i / 2) : ℝ)| ≤
      1 / 10 ^ 16 := by
    have h := profile_exp_error (quarterShift663 i / 2) (by exact_mod_cast hshift i)
    norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
    rw [← mul_sub, abs_mul]
    refine
      (mul_le_mul (by exact_mod_cast hcoeff i : |(gaussianCoeff197 i : ℝ)| ≤ 1) h (abs_nonneg _)
            (by norm_num only)).trans
        ?_
    norm_num only
  have hs := (abs_le.mp (sum_six_error _ _ he)).2
  have h := mul_le_mul_of_nonpos_left hs (by norm_num only [c] : c ≤ 0)
  have hb : (20.7419 : ℚ) ≤ negPoleApprox := by decide +kernel
  have hcast := (Rat.cast_le (K := ℝ)).mpr hb
  norm_num only [negPoleApprox, Rat.cast_neg, Rat.cast_mul, Rat.cast_div, Rat.cast_pow,
    Rat.cast_ofNat, Rat.cast_ofScientific, Rat.cast_sum] at hcast
  unfold gaussianNegPole197
  dsimp only [c] at h
  linarith only [h, hcast]

/-- Given interval bounds for the logarithm and decay, bound the
conductor contribution by a single rational polynomial evaluation. -/
theorem gaussian_theta_lower_197 {r M : ℝ} {l u : ℚ} (hr : 0 < r) (hl : 0 ≤ l)
    (hlog : 2 * Real.log r - 23 / 2 ∈ Set.Icc (l : ℝ) (u : ℝ)) (hM : r ^ (-(6 / 5) : ℝ) ≤ M)
    (hP : 0 ≤ (jointShiftUpper197 l u 0 : ℝ)) :
    -(11 / 10) ^ 5 / 30 * M * (jointShiftUpper197 l u 0 : ℝ) ≤ gaussianTheta197 r := by
  have h :=
    (mul_le_mul_of_nonneg_left (gaussian_joint_base_upper_197 hl hlog)
          (Real.rpow_nonneg hr.le (-(6 / 5) : ℝ))).trans
      (mul_le_mul_of_nonneg_right hM hP)
  unfold gaussianTheta197
  nlinarith only [h]

/-- The conductor term costs at most 2.970 in the first physical radius
range, using outward logarithm and power bounds. -/
theorem gaussian_theta_early_lower_197 {r : ℝ} (hr : r ∈ Set.Icc 332.15 334) :
    (-2.970 : ℝ) ≤ gaussianTheta197 r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 6643 / 20) (j := 9) (n := 27) (lo := 5.80555)
        (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 334) (j := 9) (n := 27) (lo := 5) (hi := 5.81115)
        (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hhi
  have hrl : (6643 / 20 : ℝ) ≤ r := by linarith only [hr.1]
  have hll := hlo.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 6643 / 20) hrl)
  have hlu := (Real.log_le_log hp hr.2).trans hhi
  have hlog : 2 * Real.log r - 23 / 2 ∈ Set.Icc (↑(0.111 : ℚ) : ℝ) (↑(0.123 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_ofScientific, Set.mem_Icc]
    exact ⟨by linarith only [hll], by linarith only [hlu]⟩
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 6643 / 20) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000943) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hpow
  have hM : r ^ (-(6 / 5) : ℝ) ≤ 0.000943 :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 6643 / 20) hrl
          (by norm_num only : (-(6 / 5) : ℝ) ≤ 0)).trans
      (by
        norm_num only; exact hpow)
  have hcert :
    (0 : ℚ) ≤ jointShiftUpper197 0.111 0.123 0 ∧
      (11 / 10) ^ 5 / 30 * 0.000943 * jointShiftUpper197 0.111 0.123 0 ≤ 2.970 := by
    decide +kernel
  have hP := (Rat.cast_nonneg (K := ℝ)).mpr hcert.1
  have hh := (Rat.cast_le (K := ℝ)).mpr hcert.2
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofScientific] at hh
  exact
    (by linarith only [hh] :
          (-2.970 : ℝ) ≤
            -(11 / 10) ^ 5 / 30 * 0.000943 * (jointShiftUpper197 0.111 0.123 0 : ℝ)).trans
      (gaussian_theta_lower_197 hp (by norm_num only) hlog hM hP)

/-- The early K197 conductor and pole charge stays below 2.908 at any
admissible scale at least one. -/
theorem gaussian_shift_early_lower_197 {r s : ℝ} (hr : r ∈ Set.Icc 332.15 334) (hs : 1 ≤ s) :
    (-2.908 : ℝ) ≤ gaussianTheta197 r / s + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1
  have hθ : (-2.970 : ℝ) ≤ gaussianTheta197 r / s :=
    (le_div_iff₀ (zero_lt_one.trans_le hs)).mpr
      ((by linarith only [hs] : (-2.970 : ℝ) * s ≤ -2.970).trans
        (gaussian_theta_early_lower_197 hr))
  have hn : (0.062 : ℝ) ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr (by linarith only [hr.2, gaussian_neg_pole_lower_197])
  linarith only [hθ, hn]

/-- Combine the early conductor, pole, and joint reflection bounds in
the sign needed by the K197 three-character comparison. -/
theorem gaussian_aux_early_lower_197 (hRH : RiemannHypothesis) {r s : ℝ}
    (hr : r ∈ Set.Icc 332.15 334) (hs : 1 ≤ s) (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-2.90805 : ℝ) ≤
      gaussianTheta197 r / s + gaussianNegPole197 / r +
        ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  linarith only [gaussian_shift_early_lower_197 hr hs,
    gaussian_joint_early_lower_197 hRH ⟨hr.1, hr.2.trans (by norm_num only)⟩ α hα hprefix]

/-- The first K197 radius interval gives a sharper conductor bound
by enclosing the common polynomial and decay at its exact endpoints. -/
theorem gaussian_theta_first_lower_197 {r : ℝ} (hr : r ∈ Set.Icc 332.249 332.5) :
    (-2.958 : ℝ) ≤ gaussianTheta197 r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 332.249).trans_le hr.1
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 332249 / 1000) (j := 9) (n := 27) (lo := 5.80588)
        (hi := 6) (by decide +kernel)).1
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 665 / 2) (j := 9) (n := 27) (lo := 5) (hi :=
        5.80665) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hlo hhi
  have hrl : (332249 / 1000 : ℝ) ≤ r := by linarith only [hr.1]
  have hll := hlo.trans (Real.log_le_log (by norm_num only : (0 : ℝ) < 332249 / 1000) hrl)
  have hru : r ≤ (665 / 2 : ℝ) := by linarith only [hr.2]
  have hlu := (Real.log_le_log hp hru).trans hhi
  have hlog : 2 * Real.log r - 23 / 2 ∈ Set.Icc (↑(0.11176 : ℚ) : ℝ) (↑(0.11330 : ℚ) : ℝ) := by
    norm_num only [Rat.cast_ofScientific, Set.mem_Icc]
    exact ⟨by linarith only [hll], by linarith only [hlu]⟩
  have hpow :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 332249 / 1000) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000942419) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hpow
  have hM : r ^ (-(6 / 5) : ℝ) ≤ 0.000942419 :=
    (Real.rpow_le_rpow_of_nonpos (by norm_num only : (0 : ℝ) < 332249 / 1000) hrl
          (by norm_num only : (-(6 / 5) : ℝ) ≤ 0)).trans
      (by
        norm_num only; exact hpow)
  have hcert :
    (0 : ℚ) ≤ jointShiftUpper197 0.11176 0.11330 0 ∧
      (11 / 10) ^ 5 / 30 * 0.000942419 * jointShiftUpper197 0.11176 0.11330 0 ≤ 2.958 := by
    decide +kernel
  have hP := (Rat.cast_nonneg (K := ℝ)).mpr hcert.1
  have hh := (Rat.cast_le (K := ℝ)).mpr hcert.2
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
    Rat.cast_ofScientific] at hh
  exact
    (by linarith only [hh] :
          (-2.958 : ℝ) ≤
            -(11 / 10) ^ 5 / 30 * 0.000942419 * (jointShiftUpper197 0.11176 0.11330 0 : ℝ)).trans
      (gaussian_theta_lower_197 hp (by norm_num only) hlog hM hP)

/-- Combine the conductor and pole on the first K197 cell using its
fixed Gaussian scale. -/
theorem gaussian_shift_first_lower_197 {r : ℝ} (hr : r ∈ Set.Icc 332.249 332.5) :
    (-2.895 : ℝ) ≤ gaussianTheta197 r / (500186760939 / 500000000000) + gaussianNegPole197 / r := by
  have hp : 0 < r := (by norm_num only : (0 : ℝ) < 332.249).trans_le hr.1
  have hθ : (-2.957 : ℝ) ≤ gaussianTheta197 r / (500186760939 / 500000000000) :=
    (le_div_iff₀ (by norm_num only)).mpr
      ((by norm_num only : (-2.957 : ℝ) * (500186760939 / 500000000000) ≤ -2.958).trans
        (gaussian_theta_first_lower_197 hr))
  have hn : (0.062 : ℝ) ≤ gaussianNegPole197 / r :=
    (le_div_iff₀ hp).mpr (by linarith only [hr.2, gaussian_neg_pole_lower_197])
  linarith only [hθ, hn]

end PseudoPrime.PrimeTestBounds.MillerRabin
