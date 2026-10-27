/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaLogSquareMoment
public import PseudoPrime.Analysis.CosineMomentInterpolation

/-! # Actual Gamma phase interpolation from a positive logarithmic moment -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: positive real bases and any real exponent and ordinate.
Claim: the real-exponent complex power and imaginary phase combine into one exponential.
Proof: split the complex power and combine positive real bases.
Role: identify the exact positive Mellin phase integrand. -/
theorem realPower_cpow_mul_phase {a x : ℝ} (ha : 0 < a) (hx : 0 < x) (σ t : ℝ) :
    (a : ℂ) ^ ((σ : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t) =
      (a ^ σ : ℝ) * Complex.exp (Complex.I * (((t * Real.log (a * x) : ℝ)) : ℂ)) := by
  rw [Complex.cpow_add _ _ (Complex.ofReal_ne_zero.mpr ha.ne'), ← Complex.ofReal_cpow ha.le,
    mul_assoc, ← Complex.mul_cpow_ofReal_nonneg ha.le hx.le, ← Complex.ofReal_mul,
    Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr (mul_pos ha hx).ne'), ←
    Complex.ofReal_log (mul_pos ha hx).le, Complex.ofReal_mul]
  congr 2
  ring

/-- Input: positive scale and integration variable, and any real ordinate.
Claim: the real Gamma phase integrand equals the positive half-line density times cosine.
Proof: normalize the real power and imaginary phase, then take the real part.
Role: retain the common positive density in the spectral comparison. -/
theorem gammaHalf_phase_integrand_re {x u : ℝ} (hx : 0 < x) (hu : 0 < u) (t : ℝ) :
    (((Real.exp (-u) : ℝ) : ℂ) * (u : ℂ) ^ (((1 / 2 : ℂ) + Complex.I * t) - 1) *
          (x : ℂ) ^ (Complex.I * t)).re =
      gammaHalfDensity u * Real.cos (t * Real.log (u * x)) := by
  have he : ((1 / 2 : ℂ) + Complex.I * t) - 1 = ((-1 / 2 : ℝ) : ℂ) + Complex.I * t := by
    norm_num only [Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_one, Complex.ofReal_ofNat]
    ring
  rw [he, mul_assoc, realPower_cpow_mul_phase hu hx (-1 / 2) t]
  norm_num only [gammaHalfDensity, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.mul_re, zero_mul, one_mul,
    mul_zero, sub_zero, add_zero, Real.exp_zero]
  ring_nf

/-- Input: a positive scale and any real ordinate.
Claim: the real Gamma phase equals its actual positive-density cosine integral.
Proof: use absolute Gamma convergence, commute constant multiplication and real parts,
and identify the integrands. Role: apply moment-controlled interpolation to actual Gamma. -/
theorem gammaHalf_phase_re_eq_cosineIntegral {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re =
      ∫ u : ℝ in Set.Ioi 0, gammaHalfDensity u * Real.cos (t * Real.log (u * x)) := by
  have hs : 0 < ((1 / 2 : ℂ) + Complex.I * t).re := by
    norm_num only [Complex.add_re, Complex.div_ofNat_re, Complex.one_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero,
      sub_zero, add_zero]
  have hi := Complex.GammaIntegral_convergent hs
  rw [Complex.Gamma_eq_integral hs]
  dsimp only [Complex.GammaIntegral]
  calc
    _ =
        (∫ u : ℝ in Set.Ioi 0,
            ((Real.exp (-u) : ℝ) : ℂ) * (u : ℂ) ^ (((1 / 2 : ℂ) + Complex.I * t) - 1) *
              (x : ℂ) ^ (Complex.I * t)).re :=
      by rw [MeasureTheory.integral_mul_const]
    _ =
        ∫ u : ℝ in Set.Ioi 0,
          (((Real.exp (-u) : ℝ) : ℂ) * (u : ℂ) ^ (((1 / 2 : ℂ) + Complex.I * t) - 1) *
              (x : ℂ) ^ (Complex.I * t)).re :=
      (Complex.reCLM.integral_comp_comm (hi.mul_const ((x : ℂ) ^ (Complex.I * t)))).symm
    _ = _ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun u hu ↦ gammaHalf_phase_integrand_re hx hu t)

/-- Input: a positive scale with |log(x)|<=8, an interval, a nonnegative comparison cost MR,
and a comparison function with concave quadratic correction and endpoint gap at least c.
Claim: the actual Gamma phase gap is at least c-(MR+1024)*(b-a)^2/8 throughout the interval.
Proof: use the exact cosine integral and the certified positive second-moment cap 1024.
Role: certify values between spectral nodes without differentiating under an integral. -/
theorem gammaPhase_gap_lower_on_interval {x : ℝ} (hx : 0 < x) (hlog : |Real.log x| ≤ 8)
    {a b MR c t : ℝ} (hab : a < b) (hMR : 0 ≤ MR) {R : ℝ → ℝ}
    (hR : ConcaveOn ℝ (Set.Icc a b) (fun z ↦ R z - MR / 2 * z ^ 2))
    (ha : c ≤ R a + (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * a) * (x : ℂ) ^ (Complex.I * a)).re)
    (hb : c ≤ R b + (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * b) * (x : ℂ) ^ (Complex.I * b)).re)
    (ht : t ∈ Set.Icc a b) :
    c - (MR + 1024) * (b - a) ^ 2 / 8 ≤
      R t + (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  have hw : MeasureTheory.IntegrableOn gammaHalfDensity (Set.Ioi 0) :=
    integrable_gammaPower (by norm_num only : (-1 : ℝ) < -1 / 2)
  have hl :
    MeasureTheory.AEStronglyMeasurable (fun u : ℝ ↦ Real.log (u * x))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (Real.measurable_log.comp (measurable_id.mul_const x)).aestronglyMeasurable
  have hw0 : ∀ᵐ u ∂(MeasureTheory.volume.restrict (Set.Ioi 0)), 0 ≤ gammaHalfDensity u :=
    MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi
      (fun u hu ↦ gammaHalfDensity_nonneg hu.le)
  rw [gammaHalf_phase_re_eq_cosineIntegral hx a] at ha
  rw [gammaHalf_phase_re_eq_cosineIntegral hx b] at hb
  rw [gammaHalf_phase_re_eq_cosineIntegral hx t]
  exact
    cosineIntegral_gap_lower_on_interval hw hl hw0 (integrable_gammaHalf_logSquare hx) hab hMR hR
      (gammaHalf_logSquareMoment_le_1024 hx hlog) ha hb ht

/-- Input: a positive scale and any real ordinate.
Claim: the real Gamma phase is unchanged when the ordinate is negated.
Proof: use its positive-density cosine integral and the evenness of cosine.
Role: reuse positive-ordinate certificates on the negative spectral half-line. -/
theorem gammaHalf_phase_re_neg {x : ℝ} (hx : 0 < x) (t : ℝ) :
    (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * ((-t : ℝ) : ℂ)) *
          (x : ℂ) ^ (Complex.I * ((-t : ℝ) : ℂ))).re =
      (Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re := by
  rw [gammaHalf_phase_re_eq_cosineIntegral hx (-t), gammaHalf_phase_re_eq_cosineIntegral hx t]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
  intro u _
  simp only [neg_mul, Real.cos_neg]

end PseudoPrime.Analysis
