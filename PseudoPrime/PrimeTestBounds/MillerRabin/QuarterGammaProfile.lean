/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target028GammaConvolution
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaTailAlgebra

/-! # Shifted profile for the even Gamma convolution -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The sixth-pole inverse Mellin profile in its shifted logarithmic
variable. It vanishes for negative arguments and equals the exponential fifth
moment on the positive half-line, including the kernel normalization. -/
noncomputable def quarterGammaDensity (v : ℝ) : ℝ :=
  if 0 ≤ v then ((27 / 25 : ℝ) ^ 5 / 120) * v ^ 5 * Real.exp (-(27 / 25 : ℝ) * v) else 0

/-- The inverse Mellin profile at `exp (21/8 - v)` is the shifted density.
The support condition is exactly `0 ≤ v`; on that support the rational pole
formula reduces to an exponential fifth moment. -/
theorem quarter_profile_shift (v : ℝ) :
    Analysis.rationalPoleProfile 3 (25 / 54) (21 / 16) (Real.exp (21 / 8 - v)) =
      quarterGammaDensity v := by
  unfold Analysis.rationalPoleProfile quarterGammaDensity
  rw [Real.log_exp]
  by_cases hv : 0 ≤ v
  · rw [ite_eq_left ⟨Real.exp_pos _, by linarith only [hv]⟩, ite_eq_left hv]
    norm_num only [show 2 * 3 - 1 = 5 by decide, Nat.factorial]
    have he : -(((21 / 8 : ℝ) - (21 / 8 - v)) / (25 / 27)) = -(27 / 25 : ℝ) * v := by ring
    rw [he]
    ring
  · rw [ite_eq_right
        (by
          intro h; apply hv; linarith only [h.2]),
      ite_eq_right hv]

/-- The positive-pole resolvent is the convolution of the shifted density
with `exp (-c |v - z|)`, where `z = y + 21/8`. This rewrites the exact
Fourier identity in the logarithmic variables used for the Gamma-tail bound. -/
theorem quarter_pole_density_convolution (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v : ℝ, (quarterGammaDensity v : ℂ) * (Real.exp (-c * |v - (y + 21 / 8)|) : ℂ) := by
  rw [quarter_kernel_pole_centered y hc]
  congr 1
  let f : ℝ → ℂ := fun v ↦ (quarterGammaDensity v : ℂ) * (Real.exp (-c * |v - (y + 21 / 8)|) : ℂ)
  have h := MeasureTheory.integral_add_left_eq_self (μ := MeasureTheory.volume) f (21 / 8 : ℝ)
  calc
    _ = ∫ u : ℝ, f (21 / 8 + u) := by
      apply MeasureTheory.integral_congr_ae
      apply Filter.Eventually.of_forall
      intro u
      dsimp only [f]
      have hu : (21 / 8 : ℝ) - (21 / 8 + u) = -u := by ring
      have harg : (21 / 8 : ℝ) + u - (y + 21 / 8) = u - y := by ring
      rw [← hu, quarter_profile_shift, harg]
    _ = _ := h

/-- The shifted density vanishes on the nonpositive half-line. Hence the
pole convolution may be restricted to the positive half-line, including at
the boundary where its fifth power is zero. -/
theorem quarter_pole_density_positive (y : ℝ) {c : ℝ} (hc : 0 < c) :
    ((1 / (2 * Real.pi) : ℝ) : ℂ) * ((c ^ 2 : ℝ) : ℂ) *
        (∫ t : ℝ,
          (refinedSixPoleKernel.function (Complex.I * t) * Complex.exp (Complex.I * (t : ℂ) * y)) *
            ((1 / (c ^ 2 + t ^ 2) : ℝ) : ℂ)) =
      ((c / 2 : ℝ) : ℂ) *
        ∫ v in Set.Ioi (0 : ℝ),
          (quarterGammaDensity v : ℂ) * (Real.exp (-c * |v - (y + 21 / 8)|) : ℂ) := by
  rw [quarter_pole_density_convolution y hc]
  congr 1
  rw [← MeasureTheory.integral_indicator measurableSet_Ioi]
  apply MeasureTheory.integral_congr_ae
  apply Filter.Eventually.of_forall
  intro v
  dsimp only
  by_cases hv : 0 < v
  · rw [Set.indicator_of_mem (show v ∈ Set.Ioi (0 : ℝ) from hv)]
  · rw [Set.indicator_of_notMem (show v ∉ Set.Ioi (0 : ℝ) from hv)]
    have hv0 : v ≤ 0 := le_of_not_gt hv
    have hd : quarterGammaDensity v = 0 := by
      by_cases heq : v = 0
      · subst v
        norm_num only [quarterGammaDensity, le_refl, ite_true, zero_pow, OfNat.ofNat_ne_zero,
          mul_zero, zero_mul]
      · rw [quarterGammaDensity, ite_eq_right (not_le_of_gt (lt_of_le_of_ne hv0 heq))]
    rw [hd]
    norm_num only [Complex.ofReal_zero, zero_mul]

end PseudoPrime.PrimeTestBounds.MillerRabin
