/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerApproximationBounds
public import Mathlib.Analysis.Real.Pi.Bounds

/-! # An explicit positive logarithmic moment for the Gamma half line -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a positive real variable.
Claim: log(u)^2<=64*(u^(1/4)+u^(-1/4)).
Proof: apply the two signed logarithm bounds at exponent 1/8 and square by sign.
Role: dominate logarithmic moments by integrable Gamma densities. -/
theorem log_sq_le_rpow_pair {u : ℝ} (hu : 0 < u) :
    (Real.log u) ^ 2 ≤ 64 * (u ^ (1 / 4 : ℝ) + u ^ (-1 / 4 : ℝ)) := by
  have hp := Real.log_le_rpow_div hu.le (by norm_num only : (0 : ℝ) < 1 / 8)
  have hn := Real.neg_rpow_div_le_log hu.le (by norm_num only : (0 : ℝ) < 1 / 8)
  have he (a : ℝ) : (u ^ a) ^ 2 = u ^ (2 * a) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hu.le]
    congr 1
    ring
  have hp0 := Real.rpow_nonneg hu.le (1 / 8 : ℝ)
  have hn0 := Real.rpow_nonneg hu.le (-1 / 8 : ℝ)
  by_cases hl : 0 ≤ Real.log u
  · have hs := mul_self_le_mul_self hl hp
    norm_num only at hs
    have heP := he (1 / 8)
    norm_num only at heP
    nlinarith only [hs, heP, Real.rpow_nonneg hu.le (-1 / 4 : ℝ)]
  · have hz : 0 ≤ -Real.log u := neg_nonneg.mpr (le_of_not_ge hl)
    have hneg : -Real.log u ≤ u ^ (-1 / 8 : ℝ) / (1 / 8) := by linarith only [hn]
    have hs := mul_self_le_mul_self hz hneg
    norm_num only at hs
    have heN := he (-1 / 8)
    norm_num only at heN
    nlinarith only [hs, heN, Real.rpow_nonneg hu.le (1 / 4 : ℝ)]

/-- Input: a real integration variable. Output: exp(-u)*u^(-1/2).
Role: retain the positive Mellin density of the Gamma half line. -/
noncomputable def gammaHalfDensity (u : ℝ) : ℝ :=
  Real.exp (-u) * u ^ (-1 / 2 : ℝ)

/-- Input: a positive scale and integration variable.
Output: a combination of Gamma densities dominating the log-square moment.
Role: prove integrability and a quantitative moment bound using elementary powers. -/
noncomputable def gammaLogSquareEnvelope (x u : ℝ) : ℝ :=
  128 * (Real.exp (-u) * u ^ (-1 / 4 : ℝ) + Real.exp (-u) * u ^ (-3 / 4 : ℝ)) +
    2 * (Real.log x) ^ 2 * gammaHalfDensity u

/-- Input: a nonnegative variable. Claim: the half-line Gamma density is nonnegative.
Proof: exponential and real powers are nonnegative.
Role: preserve moment and integral inequalities. -/
theorem gammaHalfDensity_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ gammaHalfDensity u := by
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hu _)

/-- Input: positive scale and integration variable.
Claim: the logarithmic second-moment density is bounded by the explicit Gamma envelope.
Proof: expand log(u*x), bound the square, and combine real powers.
Role: dominate the phase moment without discarding its integral structure. -/
theorem gammaHalf_logSquare_le_envelope {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    gammaHalfDensity u * (Real.log (u * x)) ^ 2 ≤ gammaLogSquareEnvelope x u := by
  have hw := gammaHalfDensity_nonneg hu.le
  have hsq : (Real.log (u * x)) ^ 2 ≤ 2 * (Real.log u) ^ 2 + 2 * (Real.log x) ^ 2 := by
    rw [Real.log_mul hu.ne' hx.ne']
    nlinarith only [sq_nonneg (Real.log u - Real.log x)]
  have hp : u ^ (-1 / 2 : ℝ) * u ^ (1 / 4 : ℝ) = u ^ (-1 / 4 : ℝ) := by
    rw [← Real.rpow_add hu]
    congr 1
    norm_num only
  have hn : u ^ (-1 / 2 : ℝ) * u ^ (-1 / 4 : ℝ) = u ^ (-3 / 4 : ℝ) := by
    rw [← Real.rpow_add hu]
    congr 1
    norm_num only
  have h :=
    (mul_le_mul_of_nonneg_left hsq hw).trans
      (mul_le_mul_of_nonneg_left
        (add_le_add
          (mul_le_mul_of_nonneg_left (log_sq_le_rpow_pair hu) (by norm_num only : (0 : ℝ) ≤ 2))
          (le_refl (2 * (Real.log x) ^ 2)))
        hw)
  have he :
    gammaHalfDensity u * (2 * (64 * (u ^ (1 / 4 : ℝ) + u ^ (-1 / 4 : ℝ))) + 2 * (Real.log x) ^ 2) =
      gammaLogSquareEnvelope x u := by
    dsimp only [gammaHalfDensity, gammaLogSquareEnvelope]
    calc
      _ =
          128 *
              (Real.exp (-u) * (u ^ (-1 / 2 : ℝ) * u ^ (1 / 4 : ℝ)) +
                Real.exp (-u) * (u ^ (-1 / 2 : ℝ) * u ^ (-1 / 4 : ℝ))) +
            2 * (Real.log x) ^ 2 * (Real.exp (-u) * u ^ (-1 / 2 : ℝ)) :=
        by ring
      _ = _ := by rw [hp, hn]
  exact he ▸ h

/-- Input: a real power exponent greater than -1.
Claim: exp(-u)*u^a is integrable on the positive halfline.
Proof: specialize Gamma integral convergence at a+1.
Role: support all positive-density moment envelopes. -/
theorem integrable_gammaPower {a : ℝ} (ha : -1 < a) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.exp (-u) * u ^ a) (Set.Ioi 0) := by
  have h := Real.GammaIntegral_convergent (s := a + 1) (by linarith only [ha])
  simpa only [add_sub_cancel_right] using h

/-- Input: a real power exponent greater than -1.
Claim: the density integral equals Gamma(a+1).
Proof: specialize the defining Gamma integral.
Role: evaluate the dominating moment explicitly. -/
theorem integral_gammaPower {a : ℝ} (ha : -1 < a) :
    (∫ u : ℝ in Set.Ioi 0, Real.exp (-u) * u ^ a) = Real.Gamma (a + 1) := by
  have h := Real.Gamma_eq_integral (s := a + 1) (by linarith only [ha])
  simpa only [add_sub_cancel_right] using h.symm

/-- Input: any scale. Claim: the log-square envelope is integrable on the positive halfline.
Proof: combine three convergent Gamma densities.
Role: justify the majorized logarithmic moment. -/
theorem integrable_gammaLogSquareEnvelope (x : ℝ) :
    MeasureTheory.IntegrableOn (gammaLogSquareEnvelope x) (Set.Ioi 0) := by
  exact
    ((integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 4)).add
            (integrable_gammaPower (by norm_num only : (-1 : ℝ) < -3 / 4))).const_mul
        128 |>.add
      ((integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 2)).const_mul
        (2 * (Real.log x) ^ 2))

/-- Input: a positive scale.
Claim: the actual Gamma log-square density is integrable on the positive halfline.
Proof: apply measurable domination by the explicit envelope.
Role: supply the genuine moment hypothesis for integrated concavity. -/
theorem integrable_gammaHalf_logSquare {x : ℝ} (hx : 0 < x) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ gammaHalfDensity u * (Real.log (u * x)) ^ 2)
      (Set.Ioi 0) := by
  have hm : Measurable (fun u : ℝ ↦ gammaHalfDensity u * (Real.log (u * x)) ^ 2) :=
    ((Real.measurable_exp.comp measurable_neg).mul (measurable_id.pow_const (-1 / 2 : ℝ))).mul
      ((Real.measurable_log.comp (measurable_id.mul_const x)).pow_const (2 : ℕ))
  apply (integrable_gammaLogSquareEnvelope x).mono' hm.aestronglyMeasurable
  exact
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun u hu ↦ by
        rw [Real.norm_eq_abs,
          abs_of_nonneg (mul_nonneg (gammaHalfDensity_nonneg hu.le) (sq_nonneg _))]
        exact gammaHalf_logSquare_le_envelope hx hu)

/-- Claim: Gamma(1/4)<=4.
Proof: log convexity bounds Gamma(5/4) by one; use the Gamma recurrence.
Role: certify the small-exponent moment with rational constants. -/
theorem Gamma_quarter_le_four : Real.Gamma (1 / 4) ≤ (4 : ℝ) := by
  have h :=
    Real.convexOn_log_Gamma.2 (show (1 : ℝ) ∈ Set.Ioi 0 by norm_num only [Set.mem_Ioi])
      (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num only [Set.mem_Ioi]) (by norm_num only : (0 : ℝ) ≤ 3 / 4)
      (by norm_num only : (0 : ℝ) ≤ 1 / 4) (by norm_num only : (3 / 4 : ℝ) + 1 / 4 = 1)
  norm_num only [smul_eq_mul, Function.comp_apply, Real.Gamma_one, Real.Gamma_two, Real.log_one,
    mul_zero, add_zero] at h
  have hg : 0 < Real.Gamma (5 / 4) := Real.Gamma_pos_of_pos (by norm_num only)
  have hle := (Real.log_le_iff_le_exp hg).mp h
  rw [Real.exp_zero] at hle
  have he := Real.Gamma_add_one (s := (1 / 4 : ℝ)) (by norm_num only)
  norm_num only at he
  nlinarith only [hle, he]

/-- Claim: Gamma(3/4)<=2.
Proof: compare with Gamma(1/2)=sqrt(pi) using monotonicity on (0,1].
Role: bound the other shifted moment. -/
theorem Gamma_three_quarters_le_two : Real.Gamma (3 / 4) ≤ (2 : ℝ) := by
  have h :=
    Real.Gamma_strictAntiOn_Ioc.antitoneOn
      (show (1 / 2 : ℝ) ∈ Set.Ioc 0 1 by norm_num only [Set.mem_Ioc, and_self])
      (show (3 / 4 : ℝ) ∈ Set.Ioc 0 1 by norm_num only [Set.mem_Ioc, and_self])
      (by norm_num only : (1 / 2 : ℝ) ≤ 3 / 4)
  rw [Real.Gamma_one_half_eq] at h
  exact h.trans (Real.sqrt_le_iff.mpr ⟨by norm_num only, by linarith only [Real.pi_lt_four]⟩)

/-- Input: any scale. Claim: the envelope integral equals the displayed Gamma combination.
Proof: integrate the three densities and retain the logarithmic scale factor.
Role: convert integrability into an explicit analytic cost. -/
theorem integral_gammaLogSquareEnvelope (x : ℝ) :
    (∫ u : ℝ in Set.Ioi 0, gammaLogSquareEnvelope x u) =
      128 * (Real.Gamma (3 / 4) + Real.Gamma (1 / 4)) +
        2 * (Real.log x) ^ 2 * Real.Gamma (1 / 2) := by
  have hp := integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 4)
  have hn := integrable_gammaPower (by norm_num only : (-1 : ℝ) < -3 / 4)
  have hh := integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 2)
  change
    (∫ u : ℝ in Set.Ioi 0,
        128 * (Real.exp (-u) * u ^ (-1 / 4 : ℝ) + Real.exp (-u) * u ^ (-3 / 4 : ℝ)) +
          2 * (Real.log x) ^ 2 * (Real.exp (-u) * u ^ (-1 / 2 : ℝ))) =
      _
  have h128 :
    MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ 128 * (Real.exp (-u) * u ^ (-1 / 4 : ℝ) + Real.exp (-u) * u ^ (-3 / 4 : ℝ)))
      (Set.Ioi 0) :=
    (hp.add hn).const_mul 128
  rw [MeasureTheory.integral_add h128 (hh.const_mul (2 * (Real.log x) ^ 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hp hn, integral_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 4),
    integral_gammaPower (by norm_num only : (-1 : ℝ) < -3 / 4),
    integral_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 2)]
  norm_num only

/-- Input: a positive scale.
Claim: the actual log-square moment is at most 768+4*log(x)^2.
Proof: integrate the envelope and apply the rational Gamma bounds.
Role: quantify the phase interpolation cost. -/
theorem gammaHalf_logSquareMoment_le {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ in Set.Ioi 0, gammaHalfDensity u * (Real.log (u * x)) ^ 2) ≤
      768 + 4 * (Real.log x) ^ 2 := by
  have h :=
    MeasureTheory.setIntegral_mono_on (integrable_gammaHalf_logSquare hx)
      (integrable_gammaLogSquareEnvelope x) measurableSet_Ioi
      (fun u hu ↦ gammaHalf_logSquare_le_envelope hx hu)
  rw [integral_gammaLogSquareEnvelope, Real.Gamma_one_half_eq] at h
  have hh : Real.sqrt Real.pi ≤ (2 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by linarith only [Real.pi_lt_four]⟩
  have hm :=
    mul_le_mul_of_nonneg_left hh
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (sq_nonneg (Real.log x)))
  linarith only [h, hm, Gamma_quarter_le_four, Gamma_three_quarters_le_two]

/-- Input: a positive scale with |log(x)|<=8.
Claim: the actual log-square moment is at most 1024.
Proof: specialize the scale-sensitive bound and square the logarithm bound.
Role: give a fixed error coefficient for finite-scale phase certification. -/
theorem gammaHalf_logSquareMoment_le_1024 {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8) :
    (∫ u : ℝ in Set.Ioi 0, gammaHalfDensity u * (Real.log (u * x)) ^ 2) ≤ 1024 := by
  have h := gammaHalf_logSquareMoment_le hx
  have hs := mul_self_le_mul_self (abs_nonneg (Real.log x)) hlog
  rw [← pow_two, sq_abs] at hs
  nlinarith only [h, hs]

end PseudoPrime.Analysis
