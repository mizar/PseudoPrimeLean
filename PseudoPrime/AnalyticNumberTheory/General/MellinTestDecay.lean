/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.FourierExplicitWeights
public import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

/-!
# Mellin decay of compactly supported smooth logarithmic tests

Exponential weighting preserves compact support and smoothness. The Schwartz
Fourier estimate gives arbitrary-power decay on each fixed vertical line.
The real-part-dependent seminorm still requires a uniform strip estimate.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- The compactly supported smooth logarithmic test function multiplied
by exp((1/2-sigma)u), represented as a Schwartz function. Compact support
persists under multiplication and smoothness follows from the exponential
and scalar product rules. Its Fourier seminorms control the Mellin transform
at the fixed real part sigma. -/
noncomputable def weightedLogTestSchwartz (g : ℝ → ℂ) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) : SchwartzMap ℝ ℂ :=
  (hc.smul_left (f := fun u : ℝ ↦ Real.exp (((1 / 2 : ℝ) - σ) * u))).toSchwartzMap
    ((contDiff_const.mul contDiff_id).exp.smul hg)

/-- The Schwartz representation has the original exponentially weighted
test function as its underlying function. The identity is definitional.
This connects the function-level Mellin--Fourier formula with Schwartz
Fourier decay estimates. -/
theorem weightedLogTestSchwartz_coe (g : ℝ → ℂ) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) :
    (weightedLogTestSchwartz g hc hg σ : ℝ → ℂ) = fun u : ℝ ↦
      Real.exp (((1 / 2 : ℝ) - σ) * u) • g u := by
  rfl

/-- For a compactly supported smooth test function and a fixed real part
sigma, frequency to any natural power times the weighted Fourier transform
norm is bounded by the corresponding Schwartz seminorm. Apply the Schwartz
Fourier transform decay bound. This supplies the fixed-real-part majorant
before proving uniformity across a strip. -/
theorem weightedLogTestSchwartz_fourier_bound (g : ℝ → ℂ) (hc : HasCompactSupport g)
    (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ t : ℝ) (k : ℕ) :
    |t| ^ k * ‖FourierTransform.fourier (fun u : ℝ ↦ Real.exp (((1 / 2 : ℝ) - σ) * u) • g u) t‖ ≤
      SchwartzMap.seminorm ℂ k 0
        (FourierTransform.fourier (weightedLogTestSchwartz g hc hg σ)) := by
  have hb :=
    SchwartzMap.norm_pow_mul_le_seminorm ℂ
      (FourierTransform.fourier (weightedLogTestSchwartz g hc hg σ)) k t
  simpa only [Real.norm_eq_abs, SchwartzMap.fourier_coe, weightedLogTestSchwartz_coe] using hb

/-- For an even compactly supported smooth test function, any natural
power of the height times the Mellin transform norm at sigma+iT is bounded
by (2*pi)^k times a Fourier Schwartz seminorm of its exponential weighting.
Use the Mellin--Fourier identity and rescale the frequency T/(2*pi).
The coefficient depends on sigma; uniform control across a real-part strip
is not asserted here. This is the fixed-line decay step for contour limits. -/
theorem mellin_logarithmicTestWeight_power_bound (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ T : ℝ) (k : ℕ) :
    |T| ^ k * ‖mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)‖ ≤
      (2 * Real.pi) ^ k *
        SchwartzMap.seminorm ℂ k 0
          (FourierTransform.fourier (weightedLogTestSchwartz g hc hg σ)) := by
  have hm :
    mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I) =
      FourierTransform.fourier (fun u : ℝ ↦ Real.exp (((1 / 2 : ℝ) - σ) * u) • g u)
        (T / (2 * Real.pi)) := by
    rw [mellin_logarithmicTestWeight g he]
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im, mul_zero, sub_zero, add_zero, Complex.add_im, Complex.mul_im, mul_one, zero_add]
  have hb := weightedLogTestSchwartz_fourier_bound g hc hg σ (T / (2 * Real.pi)) k
  rw [← hm] at hb
  have hp : 0 < 2 * Real.pi := mul_pos (by norm_num only) Real.pi_pos
  have heq :
    |T / (2 * Real.pi)| ^ k * ‖mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)‖ =
      (|T| ^ k * ‖mellin (logarithmicTestWeight g) ((σ : ℂ) + T * Complex.I)‖) /
        (2 * Real.pi) ^ k := by
    rw [abs_div, abs_of_pos hp, div_pow]
    ring
  rw [heq, div_le_iff₀ (pow_pos hp k)] at hb
  exact hb.trans_eq (mul_comm _ _)

end PseudoPrime.AnalyticNumberTheory.General
