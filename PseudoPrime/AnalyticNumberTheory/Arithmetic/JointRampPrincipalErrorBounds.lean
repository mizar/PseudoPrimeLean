/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.JointRampPrincipalVariation
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ExponentialRampErrorBounds

/-! # Joint ramp-principal errors with common signed densities -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For a real error function f and principal cutoff y, define twice the complete ramp
variation minus the principal exponential variation. This combines the shared arithmetic error
before applying absolute values and retains the signed endpoint jumps. -/
noncomputable def jointRampPrincipalFunctional (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  2 * exponentialRampVariationFunctional f -
    ∫ u in (0 : ℝ)..y, f u * Analysis.exponentialRampVariationLeft u

/-- For y at least the right ramp endpoint and f continuous on the full interval, the joint
functional equals one left density, the combined middle density, a negative tail and twice the
paired endpoint jumps. Split the principal integral at both ramp endpoints and use linearity.
This is the exact cancellation identity behind the common error estimate. -/
theorem jointRampPrincipalFunctional_eq {f : ℝ → ℝ} {y : ℝ} (hy : (99 / 40 : ℝ) ≤ y)
    (hf : ContinuousOn f (Set.Icc 0 y)) :
    jointRampPrincipalFunctional f y =
      (∫ u in (0 : ℝ)..(247 / 100), f u * Analysis.exponentialRampVariationLeft u) +
            (∫ u in (247 / 100 : ℝ)..(99 / 40),
              f u *
                (2 * Analysis.exponentialRampVariationMiddle u -
                  Analysis.exponentialRampVariationLeft u)) -
          (∫ u in (99 / 40 : ℝ)..y, f u * Analysis.exponentialRampVariationLeft u) +
        2 * (-(f (247 / 100) * Analysis.rampLeftJump) + f (99 / 40) * Analysis.rampRightJump) := by
  have hL : Continuous Analysis.exponentialRampVariationLeft :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hi (Q : ℝ → ℝ) (hQ : Continuous Q) {u v : ℝ} (hu : 0 ≤ u) (hv : v ≤ y) (huv : u ≤ v) :
    IntervalIntegrable (fun t ↦ f t * Q t) MeasureTheory.volume u v := by
    have hfc : ContinuousOn f (Set.uIcc u v) := by
      rw [Set.uIcc_of_le huv]
      exact hf.mono (Set.Icc_subset_Icc hu hv)
    exact (hfc.mul hQ.continuousOn).intervalIntegrable
  have h0a :=
    hi _ hL (u := 0) (v := 247 / 100) (le_refl _) (show (247 / 100 : ℝ) ≤ y by linarith only [hy])
      (by norm_num only)
  have hab := hi _ hL (u := 247 / 100) (v := 99 / 40) (by norm_num only) hy (by norm_num only)
  have h0b := hi _ hL (u := 0) (v := 99 / 40) (le_refl _) hy (by norm_num only)
  have hby := hi _ hL (u := 99 / 40) (v := y) (by norm_num only) (le_refl _) hy
  have hM :=
    hi _ Analysis.ramp_middle_density_continuous (u := 247 / 100) (v := 99 / 40) (by norm_num only)
      hy (by norm_num only)
  have h1 := intervalIntegral.integral_add_adjacent_intervals h0a hab
  have h2 := intervalIntegral.integral_add_adjacent_intervals h0b hby
  have hJ :
    (∫ u in (247 / 100 : ℝ)..(99 / 40),
        f u *
          (2 * Analysis.exponentialRampVariationMiddle u -
            Analysis.exponentialRampVariationLeft u)) =
      2 * (∫ u in (247 / 100 : ℝ)..(99 / 40), f u * Analysis.exponentialRampVariationMiddle u) -
        (∫ u in (247 / 100 : ℝ)..(99 / 40), f u * Analysis.exponentialRampVariationLeft u) := by
    have he (u : ℝ) :
      f u *
          (2 * Analysis.exponentialRampVariationMiddle u -
            Analysis.exponentialRampVariationLeft u) =
        2 * (f u * Analysis.exponentialRampVariationMiddle u) -
          f u * Analysis.exponentialRampVariationLeft u := by
      ring
    simp only [he]
    rw [intervalIntegral.integral_sub (hM.const_mul 2) hab, intervalIntegral.integral_const_mul]
  rw [hJ]
  dsimp only [jointRampPrincipalFunctional, exponentialRampVariationFunctional,
    Analysis.exponentialRampVariationLeft, Analysis.exponentialRampVariationMiddle,
    Analysis.rampLeftJump, Analysis.rampRightJump] at *
  linarith only [h1, h2]

/-- For an interval-continuous error f, assume a compact bound M, ramp increment bound D and
nonnegative affine tail envelope A+B*u. The joint functional has the displayed uniform bound.
Apply the exact cancellation identity, the compact density masses, paired jumps and affine tail
integral. This controls the common ramp-principal error at every cutoff beyond the ramp. -/
theorem jointRampPrincipalFunctional_abs_le {f : ℝ → ℝ} {y M D A B : ℝ} (hy : (99 / 40 : ℝ) ≤ y)
    (hf : ContinuousOn f (Set.Icc 0 y)) (hM : ∀ u ∈ Set.Icc 0 (99 / 40 : ℝ), |f u| ≤ M)
    (hD : |f (99 / 40) - f (247 / 100)| ≤ D) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hTail : ∀ u ∈ Set.Icc (99 / 40 : ℝ) y, |f u| ≤ A + B * u) :
    |jointRampPrincipalFunctional f y| ≤
      (17 / 10 : ℝ) * M + 84 * D + (21 / 100 : ℝ) * A + (13 / 16 : ℝ) * B := by
  have hM0 : 0 ≤ M := (abs_nonneg (f 0)).trans (hM 0 ⟨le_refl _, by norm_num only⟩)
  have hL : Continuous Analysis.exponentialRampVariationLeft :=
    (continuous_id.sub continuous_const).mul (Real.continuous_exp.comp continuous_id.neg)
  have hfc {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hv : v ≤ y) : ContinuousOn f (Set.uIcc u v) := by
    rw [Set.uIcc_of_le huv]
    exact hf.mono (Set.Icc_subset_Icc hu hv)
  have h1 :=
    Analysis.abs_integral_mul_le_of_continuousOn (by norm_num only : (0 : ℝ) ≤ 247 / 100)
      (hfc (u := 0) (v := 247 / 100) (le_refl _) (by norm_num only)
        (show (247 / 100 : ℝ) ≤ y by linarith only [hy]))
      hL.continuousOn (fun u hu ↦ hM u ⟨hu.1, by linarith only [hu.2]⟩)
  have h2 :=
    Analysis.abs_integral_mul_le_of_continuousOn (by norm_num only : (247 / 100 : ℝ) ≤ 99 / 40)
      (hfc (u := 247 / 100) (v := 99 / 40) (by norm_num only) (by norm_num only) hy)
      Analysis.ramp_joint_middle_density_continuous.continuousOn
      (fun u hu ↦ hM u ⟨by linarith only [hu.1], hu.2⟩)
  have hm1 := mul_le_mul_of_nonneg_left Analysis.ramp_left_abs_integral_le_three_quarters hM0
  have hm2 := mul_le_mul_of_nonneg_left Analysis.ramp_joint_middle_abs_integral_le hM0
  have hj :=
    Analysis.ramp_paired_jumps_abs_le (hM (247 / 100) ⟨by norm_num only, by norm_num only⟩) hD
  have hn :=
    intervalIntegral.norm_integral_le_integral_norm (f := fun u ↦
      f u * Analysis.exponentialRampVariationLeft u) (μ := MeasureTheory.volume) hy
  simp only [Real.norm_eq_abs] at hn
  have ht :=
    intervalIntegral.integral_mono_on (μ := MeasureTheory.volume) hy
      (((hfc (u := 99 / 40) (v := y) (by norm_num only) hy (le_refl _)).mul
          hL.continuousOn).abs.intervalIntegrable)
      ((((continuous_const.add (continuous_const.mul continuous_id)).mul
                (continuous_id.sub continuous_const)).mul
            (Real.continuous_exp.comp continuous_id.neg)).intervalIntegrable
        (99 / 40 : ℝ) y)
      (fun u hu ↦
        show |f u * Analysis.exponentialRampVariationLeft u| ≤ (A + B * u) * (u - 1) * Real.exp (-u)
          from by
          have hQ : 0 ≤ Analysis.exponentialRampVariationLeft u :=
            mul_nonneg (by linarith only [hu.1]) (Real.exp_pos _).le
          rw [abs_mul, abs_of_nonneg hQ]
          exact
            (mul_le_mul_of_nonneg_right (hTail u hu) hQ).trans_eq
              (by
                dsimp only [Analysis.exponentialRampVariationLeft]
                ring))
  have htail := hn.trans (ht.trans (Analysis.integral_affine_exponential_tail_le hA hB hy))
  let I1 := ∫ u in (0 : ℝ)..(247 / 100), f u * Analysis.exponentialRampVariationLeft u
  let I2 :=
    ∫ u in (247 / 100 : ℝ)..(99 / 40),
      f u *
        (2 * Analysis.exponentialRampVariationMiddle u - Analysis.exponentialRampVariationLeft u)
  let It := ∫ u in (99 / 40 : ℝ)..y, f u * Analysis.exponentialRampVariationLeft u
  let J := -(f (247 / 100) * Analysis.rampLeftJump) + f (99 / 40) * Analysis.rampRightJump
  have ha := abs_add_le I1 I2
  have hb := abs_sub (I1 + I2) It
  have hc := abs_add_le (I1 + I2 - It) (2 * J)
  rw [abs_mul, abs_of_pos (by norm_num only : (0 : ℝ) < 2)] at hc
  rw [jointRampPrincipalFunctional_eq hy hf]
  change |I1 + I2 - It + 2 * J| ≤ _
  nlinarith only [h1, h2, hm1, hm2, hj, htail, ha, hb, hc]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
