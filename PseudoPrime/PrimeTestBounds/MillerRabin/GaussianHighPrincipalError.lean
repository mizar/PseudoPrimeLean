/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighPrincipalCenter
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianLogZetaRemainder
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # Spectral decomposition of the centered Gaussian principal error -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The centered Abel functional pairs the discrepancy with the differentiated weight
on each side of one and includes the shared boundary term. -/
@[expose]
public noncomputable def principalErrorFunctional (Q g : ℝ → ℝ) (edge X y : ℝ) : ℝ :=
  3 * (∫ u in (0 : ℝ)..1, g (X * u) * Q u) - (∫ u in (1 : ℝ)..y, g (X * u) * Q u) - 4 * edge * g X

/-- Linearity of the centered functional applies when all weighted summands are integrable.
A vanishing constant contribution removes the constant from the error split. -/
private theorem principal_error_split_aux {Q E Z G : ℝ → ℝ} {edge X y C : ℝ}
    (hE : ∀ x, E x = Z x + G x - C)
    (hcancel : 3 * (∫ u in (0 : ℝ)..1, Q u) - (∫ u in (1 : ℝ)..y, Q u) - 4 * edge = 0)
    (hQ₁ : IntervalIntegrable Q MeasureTheory.volume 0 1)
    (hQ₂ : IntervalIntegrable Q MeasureTheory.volume 1 y)
    (hZ₁ : IntervalIntegrable (fun u ↦ Z (X * u) * Q u) MeasureTheory.volume 0 1)
    (hZ₂ : IntervalIntegrable (fun u ↦ Z (X * u) * Q u) MeasureTheory.volume 1 y)
    (hG₁ : IntervalIntegrable (fun u ↦ G (X * u) * Q u) MeasureTheory.volume 0 1)
    (hG₂ : IntervalIntegrable (fun u ↦ G (X * u) * Q u) MeasureTheory.volume 1 y) :
    principalErrorFunctional Q E edge X y =
      principalErrorFunctional Q Z edge X y + principalErrorFunctional Q G edge X y := by
  unfold principalErrorFunctional
  simp only [hE, sub_mul, add_mul]
  rw [intervalIntegral.integral_sub (hZ₁.add hG₁) (hQ₁.const_mul C),
    intervalIntegral.integral_sub (hZ₂.add hG₂) (hQ₂.const_mul C),
    intervalIntegral.integral_add hZ₁ hG₁, intervalIntegral.integral_add hZ₂ hG₂,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  linear_combination -C * hcancel

/-- For a reflected power-log profile vanishing to second order at zero, the
centered principal error separates into the zero sum and the decaying remainder. -/
public theorem reflected_principal_error_split (B : Polynomial ℝ) (hRH : RiemannHypothesis)
    {d b X : ℝ} (hd : 0 < d) (hb : 0 < b) (hX : 0 < X) (hB : B.eval 0 = 0)
    (hB' : B.derivative.eval 0 = 0) :
    let W := fun u : ℝ ↦ u ^ d * B.eval (b - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    principalErrorFunctional (deriv F) gaussianLogZetaError (F 1) X (Real.exp b) =
      principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp b) +
        principalErrorFunctional (deriv F) gaussianLogZetaRemainder (F 1) X (Real.exp b) := by
  intro W F
  have hle := Real.one_le_exp hb.le
  have hQ := reflected_principal_integrable B hd hb
  have hZ := gaussian_log_zero_scaled_continuous hRH hX (Real.exp b)
  have hG := gaussian_log_remainder_continuous hRH hX (Real.exp b)
  have h₁ : Set.uIcc (0 : ℝ) 1 ⊆ Set.Icc 0 (Real.exp b) := by
    rw [Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl hle
  have h₂ : Set.uIcc (1 : ℝ) (Real.exp b) ⊆ Set.Icc 0 (Real.exp b) := by
    rw [Set.uIcc_of_le hle]
    exact Set.Icc_subset_Icc zero_le_one le_rfl
  exact
    principal_error_split_aux gaussian_log_error_split (reflected_principal_cancel B hd hb hB hB')
      hQ.1 hQ.2 (hQ.1.continuousOn_mul (hZ.mono h₁)) (hQ.2.continuousOn_mul (hZ.mono h₂))
      (hQ.1.continuousOn_mul (hG.mono h₁)) (hQ.2.continuousOn_mul (hG.mono h₂))

/-- Specialize the reflected principal error split to either high Gaussian kernel. -/
public theorem high_principal_error_split (K : HighGaussianKernel) (hRH : RiemannHypothesis) {X : ℝ}
    (hX : 0 < X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    principalErrorFunctional (deriv F) gaussianLogZetaError (F 1) X (Real.exp 5) =
      principalErrorFunctional (deriv F) gaussianLogZetaZeroSum (F 1) X (Real.exp 5) +
        principalErrorFunctional (deriv F) gaussianLogZetaRemainder (F 1) X (Real.exp 5) :=
  reflected_principal_error_split K.realProfile hRH (sub_pos.mpr (high_gaussian_pole_gt K))
    (by norm_num only) hX (high_real_profile_at_zero K).1 (high_real_profile_at_zero K).2

/-- Below the reciprocal cutoff, the remainder costs the constant small-argument envelope. -/
private theorem principal_rem_low {Q : ℝ → ℝ} {X c : ℝ} (hRH : RiemannHypothesis) (hX : 0 < X)
    (hc : 0 ≤ c) (hcut : X * c ≤ 1) (hQ : IntervalIntegrable Q MeasureTheory.volume 0 c) :
    |∫ u in (0 : ℝ)..c, gaussianLogZetaRemainder (X * u) * Q u| ≤
      (17 / 10 : ℝ) * ∫ u in (0 : ℝ)..c, |Q u| := by
  rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.norm_integral_le_of_norm_le hc ?_ (hQ.abs.const_mul _)
  filter_upwards with u hu
  rw [Real.norm_eq_abs, abs_mul]
  exact
    mul_le_mul_of_nonneg_right
      (gaussian_log_remainder_small hRH (mul_pos hX hu.1)
          ((mul_le_mul_of_nonneg_left hu.2 hX.le).trans hcut)).le
      (abs_nonneg _)

/-- Above the reciprocal cutoff, the remainder is dominated by an inverse-square moment. -/
public theorem principal_rem_high {Q : ℝ → ℝ} {X a b : ℝ} (hX : 0 < X) (ha : 0 < a) (hab : a ≤ b)
    (hcut : 1 ≤ X * a) (hQ : IntervalIntegrable Q MeasureTheory.volume a b) :
    |∫ u in a..b, gaussianLogZetaRemainder (X * u) * Q u| ≤
      (5 / 12 : ℝ) * X⁻¹ ^ 2 * ∫ u in a..b, u⁻¹ ^ 2 * |Q u| := by
  have hi : ContinuousOn (fun u : ℝ ↦ u⁻¹ ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have hId : ContinuousOn (fun u : ℝ ↦ u) (Set.Icc a b) := continuousOn_id
    exact (hId.inv₀ (fun _ hu ↦ (ha.trans_le hu.1).ne')).pow 2
  rw [← Real.norm_eq_abs, ← intervalIntegral.integral_const_mul]
  refine
    intervalIntegral.norm_integral_le_of_norm_le hab ?_ ((hQ.abs.continuousOn_mul hi).const_mul _)
  filter_upwards with u hu
  rw [Real.norm_eq_abs, abs_mul]
  refine
    (mul_le_mul_of_nonneg_right
          (gaussian_log_remainder_large (hcut.trans (mul_le_mul_of_nonneg_left hu.1.le hX.le)))
          (abs_nonneg _)).trans_eq
      ?_
  rw [mul_inv, mul_pow]
  ring

/-- Before the substitutions of H27, the centered remainder is bounded by
two absolute moments split at the reciprocal cutoff and one boundary charge. -/
public theorem principal_remainder_moments (Q : ℝ → ℝ) (hRH : RiemannHypothesis) {X y edge : ℝ}
    (hX : 1 ≤ X) (hy : 1 ≤ y) (hQ₁ : IntervalIntegrable Q MeasureTheory.volume 0 1)
    (hQ₂ : IntervalIntegrable Q MeasureTheory.volume 1 y) :
    |principalErrorFunctional Q gaussianLogZetaRemainder edge X y| ≤
      51 / 10 * (∫ u in (0 : ℝ)..X⁻¹, |Q u|) + 5 / 4 * X⁻¹ ^ 2 * (∫ u in X⁻¹..y, u⁻¹ ^ 2 * |Q u|) +
        5 / 3 * |edge| * X⁻¹ ^ 2 := by
  have hX₀ := zero_lt_one.trans_le hX
  let c := X⁻¹
  have hc₀ : 0 < c := inv_pos.mpr hX₀
  have hc₁ : c ≤ 1 := (inv_le_one₀ hX₀).mpr hX
  have hXc : X * c = 1 := mul_inv_cancel₀ hX₀.ne'
  have hsub₀ : Set.uIcc 0 c ⊆ Set.uIcc 0 (1 : ℝ) := by
    rw [Set.uIcc_of_le hc₀.le, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc le_rfl hc₁
  have hsub₁ : Set.uIcc c 1 ⊆ Set.uIcc 0 (1 : ℝ) := by
    rw [Set.uIcc_of_le hc₁, Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc hc₀.le le_rfl
  have hQc₀ := hQ₁.mono_set hsub₀
  have hQc₁ := hQ₁.mono_set hsub₁
  have hGl :
    IntervalIntegrable (fun u ↦ gaussianLogZetaRemainder (X * u) * Q u) MeasureTheory.volume 0 1 :=
    hQ₁.continuousOn_mul
      (by
        rw [Set.uIcc_of_le zero_le_one]
        exact gaussian_log_remainder_continuous hRH hX₀ 1)
  have hsplit :=
    intervalIntegral.integral_add_adjacent_intervals (hGl.mono_set hsub₀) (hGl.mono_set hsub₁)
  have hlo := abs_le.mp (principal_rem_low hRH hX₀ hc₀.le hXc.le hQc₀)
  have hhi := abs_le.mp (principal_rem_high hX₀ hc₀ hc₁ hXc.ge hQc₁)
  have htop := abs_le.mp (principal_rem_high hX₀ zero_lt_one hy (by rwa [mul_one]) hQ₂)
  have hInv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    ContinuousOn (fun u : ℝ ↦ u⁻¹ ^ 2) (Set.uIcc a b) := by
    rw [Set.uIcc_of_le hab]
    have hId : ContinuousOn (fun u : ℝ ↦ u) (Set.Icc a b) := continuousOn_id
    exact (hId.inv₀ (fun _ hu ↦ (ha.trans_le hu.1).ne')).pow 2
  have hAdd :=
    intervalIntegral.integral_add_adjacent_intervals (hQc₁.abs.continuousOn_mul (hInv hc₀ hc₁))
      (hQ₂.abs.continuousOn_mul (hInv zero_lt_one hy))
  have hnon : 0 ≤ (5 / 12 : ℝ) * X⁻¹ ^ 2 * (∫ u in (1 : ℝ)..y, u⁻¹ ^ 2 * |Q u|) :=
    mul_nonneg (mul_nonneg (by norm_num only) (sq_nonneg _))
      (intervalIntegral.integral_nonneg hy (fun _ _ ↦ mul_nonneg (sq_nonneg _) (abs_nonneg _)))
  have hedge : |4 * edge * gaussianLogZetaRemainder X| ≤ 5 / 3 * |edge| * X⁻¹ ^ 2 := by
    rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 4)]
    refine
      (mul_le_mul_of_nonneg_left (gaussian_log_remainder_large hX)
            (mul_nonneg (by norm_num only) (abs_nonneg _))).trans_eq
        ?_
    ring
  have hAdd' := congrArg (fun v : ℝ ↦ (5 / 12 : ℝ) * X⁻¹ ^ 2 * v) hAdd
  rw [principalErrorFunctional, ← hsplit]
  change
    _ ≤
      51 / 10 * (∫ u in (0 : ℝ)..c, |Q u|) + 5 / 4 * X⁻¹ ^ 2 * (∫ u in c..y, u⁻¹ ^ 2 * |Q u|) +
        5 / 3 * |edge| * X⁻¹ ^ 2
  exact
    abs_le.mpr
      ⟨by linarith only [hlo.1, hhi.1, htop.2, (abs_le.mp hedge).2, hAdd', hnon], by
        linarith only [hlo.2, hhi.2, htop.1, (abs_le.mp hedge).1, hAdd', hnon]⟩

/-- The error made by keeping only the zero sum in the high-kernel principal functional
is bounded by the two absolute moments and the single boundary charge. -/
public theorem high_principal_error_remainder (K : HighGaussianKernel) (hRH : RiemannHypothesis)
    {X : ℝ} (hX : 1 ≤ X) :
    let d := (K.pole : ℝ) - 1 / 2
    let W := fun u : ℝ ↦ u ^ d * K.realProfile.eval (5 - Real.log u)
    let F := fun u : ℝ ↦ u * deriv W u
    let Q := deriv F
    |principalErrorFunctional Q gaussianLogZetaError (F 1) X (Real.exp 5) -
          principalErrorFunctional Q gaussianLogZetaZeroSum (F 1) X (Real.exp 5)| ≤
      51 / 10 * (∫ u in (0 : ℝ)..X⁻¹, |Q u|) +
        5 / 4 * X⁻¹ ^ 2 * (∫ u in X⁻¹..Real.exp 5, u⁻¹ ^ 2 * |Q u|) +
        5 / 3 * |F 1| * X⁻¹ ^ 2 := by
  intro d W F Q
  have h := high_principal_error_split K hRH (zero_lt_one.trans_le hX)
  change principalErrorFunctional Q gaussianLogZetaError (F 1) X (Real.exp 5) = _ at h
  rw [h, add_sub_cancel_left]
  have hb : (0 : ℝ) < 5 := by norm_num only
  have hi := reflected_principal_integrable K.realProfile (sub_pos.mpr (high_gaussian_pole_gt K)) hb
  exact principal_remainder_moments Q hRH hX (Real.one_le_exp_iff.mpr hb.le) hi.1 hi.2

end PseudoPrime.PrimeTestBounds.MillerRabin
