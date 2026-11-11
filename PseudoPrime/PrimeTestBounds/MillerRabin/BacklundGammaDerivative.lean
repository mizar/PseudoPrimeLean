/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FunctionalEquation
public import Mathlib.Analysis.Calculus.LogDeriv
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundDigamma
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaFactorLogDeriv
import PseudoPrime.AnalyticNumberTheory.Gamma.Conjugation

/-! # Reflected gamma-factor logarithmic derivative -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For positive `T` and `0 ≤ u ≤ 1`, the imaginary part of the sum of the
two reflected real-Gamma logarithmic derivatives has absolute value at most
`1/T`. The log-derivative formula and conjugation reduce it to the
telescoping digamma estimate at `1/4 ± u/2 + iT/2`. -/
theorem backlund_gamma_logDeriv_im {T u : ℝ} (hT : 0 < T) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |(logDeriv Complex.Gammaℝ (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I) +
            logDeriv Complex.Gammaℝ (((1 / 2 - u : ℝ) : ℂ) - (T : ℂ) * Complex.I)).im| ≤
      1 / T := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  let t : ℂ := (((1 / 2 - u : ℝ) : ℂ) - (T : ℂ) * Complex.I)
  let a : ℂ := (((1 / 4 + u / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I)
  let b : ℂ := (((1 / 4 - u / 2 : ℝ) : ℂ) + ((T / 2 : ℝ) : ℂ) * Complex.I)
  have hsi : s.im ≠ 0 := by
    dsimp only [s]
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, zero_add, add_zero] using hT.ne'
  have hti : t.im ≠ 0 := by
    dsimp only [t]
    simp only [Complex.sub_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, add_zero, zero_sub, neg_ne_zero]
    exact hT.ne'
  have hA : s / 2 = a := by
    dsimp only [s, a]; push_cast; ring
  have hB : t / 2 = (starRingEnd ℂ) b := by
    dsimp only [t, b]
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg]
    push_cast
    ring
  have hs :=
    AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat (s := s)
      (AnalyticNumberTheory.DirichletLFunction.half_ne_neg_nat_of_im_ne_zero hsi)
  have ht :=
    AnalyticNumberTheory.DirichletLFunction.logDeriv_Gammaℝ_of_half_ne_neg_nat (s := t)
      (AnalyticNumberTheory.DirichletLFunction.half_ne_neg_nat_of_im_ne_zero hti)
  change |(logDeriv Complex.Gammaℝ s + logDeriv Complex.Gammaℝ t).im| ≤ 1 / T
  rw [hs, ht, hA, hB, AnalyticNumberTheory.Gamma.digamma_conj, ← Complex.ofReal_log Real.pi_pos.le]
  simp only [Complex.add_im, Complex.div_ofNat_im, Complex.neg_im, Complex.ofReal_im, zero_div,
    Complex.conj_im, neg_zero, zero_add]
  have h := backlund_digamma_reflection hT hu
  change (1 / 2 : ℝ) * |(Complex.digamma b).im - (Complex.digamma a).im| ≤ 1 / T at h
  have he :
    (Complex.digamma a).im / 2 + -(Complex.digamma b).im / 2 =
      -((1 / 2 : ℝ) * ((Complex.digamma b).im - (Complex.digamma a).im)) := by
    ring
  rw [he, abs_neg, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 1 / 2)]
  exact h

/-- At a positive height, the imaginary logarithmic derivative of the zeta
functional-equation factor on `1/2 ≤ Re s ≤ 3/2` has absolute value at most
`1/T`. The reflected Gamma-factor estimate and the quotient identity give
the bound needed for the Backlund reflection argument. -/
theorem backlundChi_logDeriv_im {T u : ℝ} (hT : 0 < T) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    |(logDeriv AnalyticNumberTheory.RiemannZeta.backlundChi
            (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im| ≤
      1 / T := by
  let s : ℂ := (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I)
  let t : ℂ := (((1 / 2 - u : ℝ) : ℂ) - (T : ℂ) * Complex.I)
  have hsi : s.im ≠ 0 := by
    dsimp only [s]
    simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, mul_zero, zero_add, add_zero] using hT.ne'
  have he : 1 - s = t := by
    dsimp only [s, t]; push_cast; ring
  change |(logDeriv AnalyticNumberTheory.RiemannZeta.backlundChi s).im| ≤ 1 / T
  rw [AnalyticNumberTheory.RiemannZeta.backlundChi_logDeriv hsi, he]
  simp only [Complex.sub_im, Complex.neg_im]
  have h := backlund_gamma_logDeriv_im hT hu
  change |(logDeriv Complex.Gammaℝ s + logDeriv Complex.Gammaℝ t).im| ≤ 1 / T at h
  have he' :
    -(logDeriv Complex.Gammaℝ t).im - (logDeriv Complex.Gammaℝ s).im =
      -((logDeriv Complex.Gammaℝ s).im + (logDeriv Complex.Gammaℝ t).im) := by
    ring
  rw [he', abs_neg]
  simpa only [Complex.add_im] using h

/-- A real phase variation whose derivative on `[0,1]` is the imaginary
logarithmic derivative of the functional-equation factor has absolute value
at most `1/T`. The mean-value inequality integrates the pointwise bound,
and the variation is assumed to vanish at zero. -/
theorem backlund_reflection_error_of_deriv {T : ℝ} (hT : 0 < T) {f : ℝ → ℝ} (hf0 : f 0 = 0)
    (hf :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt f
          (logDeriv AnalyticNumberTheory.RiemannZeta.backlundChi
              (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im
          (Set.Icc 0 1) u) :
    ∀ u ∈ Set.Icc (0 : ℝ) 1, |f u| ≤ 1 / T := by
  intro u hu
  have h :=
    Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (x := 0) (y := u) hf
      (fun x hx => by simpa only [Real.norm_eq_abs] using backlundChi_logDeriv_im hT hx)
      (convex_Icc (0 : ℝ) 1) ⟨le_refl 0, by norm_num only⟩ hu
  simp only [Real.norm_eq_abs, hf0, sub_zero, abs_of_nonneg hu.1] at h
  have hu' : (1 / T) * u ≤ 1 / T := by
    have hm := mul_le_mul_of_nonneg_left hu.2 (one_div_nonneg.mpr hT.le)
    simpa only [mul_one] using hm
  exact h.trans hu'

end PseudoPrime.PrimeTestBounds.MillerRabin
