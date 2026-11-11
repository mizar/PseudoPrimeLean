/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.EulerLogSeries
import Mathlib.NumberTheory.Harmonic.EulerMascheroni

/-! # Finite Euler logarithms of Gamma -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Gamma

/-- The `N`th Euler logarithmic approximation to the normalized Gamma
logarithm. Its finite correction sum converges in the right half-plane. -/
noncomputable def backlundGammaPartial (z : ℂ) (N : ℕ) : ℂ :=
  -(z - 1) * (Real.eulerMascheroniConstant : ℂ) + ∑ j ∈ Finset.range N, logCorrection j z

/-- At positive real part, the finite Euler logarithms converge to the
normalized Gamma logarithm. This follows from the summability of the
existing correction series. -/
theorem gamma_partial_tendsto {z : ℂ} (hz : 0 < z.re) :
    Filter.Tendsto (backlundGammaPartial z) Filter.atTop (nhds (logGammaSeries z)) := by
  have hs := (logCorrection_summable_and_deriv hz).1.hasSum.tendsto_sum_nat
  change
    Filter.Tendsto
      (fun n : ℕ ↦
        -(z - 1) * (Real.eulerMascheroniConstant : ℂ) + ∑ j ∈ Finset.range n, logCorrection j z)
      Filter.atTop (nhds (logGammaSeries z))
  simpa only [logGammaSeries] using hs.const_add (-(z - 1) * (Real.eulerMascheroniConstant : ℂ))

private theorem correction_im (z : ℂ) (k : ℕ) :
    (logCorrection k z).im = z.im / ((k : ℝ) + 1) - (Complex.log (z + k)).im := by
  unfold logCorrection
  have hlog : (Complex.log (k + 1 : ℂ)).im = 0 := by
    rw [← Complex.ofReal_natCast k, ← Complex.ofReal_one, ← Complex.ofReal_add, ←
      Complex.ofReal_log (by positivity)]
    exact Complex.ofReal_im _
  rw [Complex.sub_im, Complex.add_im, hlog, add_zero]
  rw [← Complex.ofReal_natCast k, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.div_ofReal_im,
    Complex.sub_im, Complex.ofReal_im, sub_zero]

/-- The imaginary part of the finite Euler logarithm is the harmonic term minus
the finite sum of logarithm phases. This follows by summing each correction. -/
theorem gamma_partial_im (z : ℂ) (N : ℕ) :
    (backlundGammaPartial z N).im =
      z.im * ((harmonic N : ℝ) - Real.eulerMascheroniConstant) -
        ∑ k ∈ Finset.range N, (Complex.log (z + k)).im := by
  have hh : (harmonic N : ℝ) = ∑ k ∈ Finset.range N, (((k : ℝ) + 1)⁻¹) := by
    simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, Nat.cast_add, Nat.cast_one,
      Rat.cast_add, Rat.cast_one]
  simp only [backlundGammaPartial, Complex.add_im, Complex.mul_im, Complex.neg_re, Complex.neg_im,
    Complex.sub_re, Complex.sub_im, Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    zero_add, sub_zero, Complex.im_sum]
  simp_rw [correction_im]
  rw [Finset.sum_sub_distrib, hh]
  simp only [div_eq_mul_inv, ← Finset.mul_sum]
  ring

end PseudoPrime.AnalyticNumberTheory.Gamma
