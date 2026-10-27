/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLogSquareMoment
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-! # Sharper positive logarithmic moments for the Gamma phase -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: any real number. Claim: cosh(z) is at least 1+z^2/2+z^4/24.
Proof: retain the first three nonnegative terms of the convergent cosh series.
Role: derive a uniform logarithmic-square envelope with a smaller coefficient. -/
theorem cosh_ge_quartic (z : ℝ) : 1 + z ^ 2 / 2 + z ^ 4 / 24 ≤ Real.cosh z := by
  have hn (n : ℕ) : 0 ≤ z ^ (2 * n) / ((2 * n).factorial : ℝ) := by
    apply div_nonneg _ (Nat.cast_nonneg _)
    rw [pow_mul]
    exact pow_nonneg (sq_nonneg z) n
  have h := Summable.sum_le_tsum (Finset.range 3) (fun n _ ↦ hn n) (Real.hasSum_cosh z).summable
  rw [(Real.hasSum_cosh z).tsum_eq] at h
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, Nat.factorial] at h
  nlinarith only [h]

/-- Input: a positive real u. Claim: log(u)^2<=9*(u^(1/4)+u^(-1/4)).
Proof: apply the quartic cosh bound to log(u)/4 and complete a polynomial square.
Role: sharpen Gamma logarithmic moment domination independently of any finite scale. -/
theorem log_sq_le_nine_rpow_pair {u : ℝ} (hu : 0 < u) :
    (Real.log u) ^ 2 ≤ 9 * (u ^ (1 / 4 : ℝ) + u ^ (-1 / 4 : ℝ)) := by
  have h := cosh_ge_quartic (Real.log u / 4)
  rw [Real.cosh_eq] at h
  have hs := sq_nonneg ((Real.log u / 4) ^ 2 - 14 / 3)
  have he :
    u ^ (1 / 4 : ℝ) + u ^ (-1 / 4 : ℝ) =
      Real.exp (Real.log u / 4) + Real.exp (-(Real.log u / 4)) := by
    rw [Real.rpow_def_of_pos hu, Real.rpow_def_of_pos hu]
    congr 1 <;> congr 1 <;> ring
  rw [he]
  nlinarith only [h, hs]

/-- Input: a scale and integration variable. Output: the Gamma power envelope with coefficient18.
Definition: use the improved logarithmic-square bound and the square-of-sum inequality.
Role: dominate the actual phase moment by explicitly integrable positive densities. -/
noncomputable def sharpGammaLogSquareEnvelope (x u : ℝ) : ℝ :=
  18 * (Real.exp (-u) * u ^ (-1 / 4 : ℝ) + Real.exp (-u) * u ^ (-3 / 4 : ℝ)) +
    2 * (Real.log x) ^ 2 * gammaHalfDensity u

/-- Input: positive scale and integration variable.
Claim: the Gamma logarithmic-square density is below the sharper explicit envelope.
Proof: expand the product logarithm and apply the coefficient-nine power bound.
Role: retain positive integrands in the moment comparison. -/
theorem gammaHalf_logSquare_le_sharp_envelope {x u : ℝ} (hx : 0 < x) (hu : 0 < u) :
    gammaHalfDensity u * (Real.log (u * x)) ^ 2 ≤ sharpGammaLogSquareEnvelope x u := by
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
          (mul_le_mul_of_nonneg_left (log_sq_le_nine_rpow_pair hu) (by norm_num only : (0 : ℝ) ≤ 2))
          (le_refl (2 * (Real.log x) ^ 2)))
        hw)
  have he :
    gammaHalfDensity u * (2 * (9 * (u ^ (1 / 4 : ℝ) + u ^ (-1 / 4 : ℝ))) + 2 * (Real.log x) ^ 2) =
      sharpGammaLogSquareEnvelope x u := by
    dsimp only [gammaHalfDensity, sharpGammaLogSquareEnvelope]
    calc
      _ =
          18 *
              (Real.exp (-u) * (u ^ (-1 / 2 : ℝ) * u ^ (1 / 4 : ℝ)) +
                Real.exp (-u) * (u ^ (-1 / 2 : ℝ) * u ^ (-1 / 4 : ℝ))) +
            2 * (Real.log x) ^ 2 * (Real.exp (-u) * u ^ (-1 / 2 : ℝ)) :=
        by ring
      _ = _ := by rw [hp, hn]
  exact he ▸ h

/-- Input: any real scale. Claim: the sharper envelope is integrable over the positive half-line.
Proof: combine integrability of the three Gamma powers.
Role: justify comparison with the actual logarithmic moment. -/
theorem integrable_sharpGammaLogSquareEnvelope (x : ℝ) :
    MeasureTheory.IntegrableOn (sharpGammaLogSquareEnvelope x) (Set.Ioi 0) := by
  exact
    ((integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 4)).add
            (integrable_gammaPower (by norm_num only : (-1 : ℝ) < -3 / 4))).const_mul
        18 |>.add
      ((integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 2)).const_mul
        (2 * (Real.log x) ^ 2))

/-- Input: any real scale. Claim: the envelope integral is the stated sum of three Gamma values.
Proof: integrate the Gamma powers term by term using established absolute convergence.
Role: evaluate the sharper interpolation cost. -/
theorem integral_sharpGammaLogSquareEnvelope (x : ℝ) :
    (∫ u : ℝ in Set.Ioi 0, sharpGammaLogSquareEnvelope x u) =
      18 * (Real.Gamma (3 / 4) + Real.Gamma (1 / 4)) +
        2 * (Real.log x) ^ 2 * Real.Gamma (1 / 2) := by
  have hp := integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 4)
  have hn := integrable_gammaPower (by norm_num only : (-1 : ℝ) < -3 / 4)
  have hh := integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 2)
  change
    (∫ u : ℝ in Set.Ioi 0,
        18 * (Real.exp (-u) * u ^ (-1 / 4 : ℝ) + Real.exp (-u) * u ^ (-3 / 4 : ℝ)) +
          2 * (Real.log x) ^ 2 * (Real.exp (-u) * u ^ (-1 / 2 : ℝ))) =
      _
  have h18 :
    MeasureTheory.IntegrableOn
      (fun u : ℝ ↦ 18 * (Real.exp (-u) * u ^ (-1 / 4 : ℝ) + Real.exp (-u) * u ^ (-3 / 4 : ℝ)))
      (Set.Ioi 0) :=
    (hp.add hn).const_mul 18
  rw [MeasureTheory.integral_add h18 (hh.const_mul (2 * (Real.log x) ^ 2)),
    MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_add hp hn, integral_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 4),
    integral_gammaPower (by norm_num only : (-1 : ℝ) < -3 / 4),
    integral_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 2)]
  norm_num only

/-- Input: a positive scale. Claim: the actual moment is at most 108+4*log(x)^2.
Proof: integrate the coefficient18 envelope and use the existing rational Gamma bounds.
Role: expose a scale-sensitive quantitative moment bound. -/
theorem sharpGammaHalf_logSquareMoment_le {x : ℝ} (hx : 0 < x) :
    (∫ u : ℝ in Set.Ioi 0, gammaHalfDensity u * (Real.log (u * x)) ^ 2) ≤
      108 + 4 * (Real.log x) ^ 2 := by
  have h :=
    MeasureTheory.setIntegral_mono_on (integrable_gammaHalf_logSquare hx)
      (integrable_sharpGammaLogSquareEnvelope x) measurableSet_Ioi
      (fun u hu ↦ gammaHalf_logSquare_le_sharp_envelope hx hu)
  rw [integral_sharpGammaLogSquareEnvelope, Real.Gamma_one_half_eq] at h
  have hh : Real.sqrt Real.pi ≤ (2 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num only, by linarith only [Real.pi_lt_four]⟩
  have hm :=
    mul_le_mul_of_nonneg_left hh
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (sq_nonneg (Real.log x)))
  linarith only [h, hm, Gamma_quarter_le_four, Gamma_three_quarters_le_two]

/-- Input: a positive scale with |log x|<=8.
Claim: its actual second logarithmic moment is at most364.
Proof: specialize the scale-sensitive moment inequality.
Role: reduce the number of ordinate intervals needed in spectral certification. -/
theorem sharpGammaHalf_logSquareMoment_le_364 {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8) :
    (∫ u : ℝ in Set.Ioi 0, gammaHalfDensity u * (Real.log (u * x)) ^ 2) ≤ 364 := by
  have h := sharpGammaHalf_logSquareMoment_le hx
  have hs := mul_self_le_mul_self (abs_nonneg (Real.log x)) hlog
  rw [← pow_two, sq_abs] at hs
  nlinarith only [h, hs]

end PseudoPrime.Analysis
