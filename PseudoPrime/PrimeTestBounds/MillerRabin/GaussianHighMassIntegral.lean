/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelCircle
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianHighKernelCot
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Function.JacobianOneDim

/-! # Change of variables for the high Gaussian mass -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private theorem cot_eq_tan_shift (θ : ℝ) : Real.cot θ = Real.tan (Real.pi / 2 - θ) := by
  rw [Real.cot_eq_cos_div_sin, Real.tan_eq_sin_div_cos, Real.sin_pi_div_two_sub,
    Real.cos_pi_div_two_sub]

private theorem shift_mem_tan {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 Real.pi) :
    Real.pi / 2 - θ ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2) :=
  ⟨by linarith only [hθ.2], by linarith only [hθ.1]⟩

private theorem cot_image_univ {a : ℝ} (ha : 0 < a) :
    (fun θ ↦ a * Real.cot θ) '' Set.Ioo 0 Real.pi = Set.univ := by
  apply Set.eq_univ_of_forall
  intro t
  let u := Real.arctan (t / a)
  have hu := Real.arctan_mem_Ioo (t / a)
  refine ⟨Real.pi / 2 - u, ⟨by linarith only [hu.2], by linarith only [hu.1]⟩, ?_⟩
  change a * Real.cot (Real.pi / 2 - u) = t
  rw [cot_eq_tan_shift, sub_sub_cancel, show Real.tan u = t / a from Real.tan_arctan _]
  exact mul_div_cancel₀ _ ha.ne'

private theorem cot_injOn {a : ℝ} (ha : 0 < a) :
    Set.InjOn (fun θ ↦ a * Real.cot θ) (Set.Ioo 0 Real.pi) := by
  intro θ hθ φ hφ h
  change a * Real.cot θ = a * Real.cot φ at h
  rw [cot_eq_tan_shift, cot_eq_tan_shift, mul_right_inj' ha.ne'] at h
  exact sub_right_injective (Real.injOn_tan (shift_mem_tan hθ) (shift_mem_tan hφ) h)

/-- The absolute high-kernel mass on the real height axis is the weighted
circle-polynomial mass on the open angular interval. The absolute derivative
accounts for the reversing orientation of the scaled cotangent. -/
public theorem high_gaussian_mass_angle (K : HighGaussianKernel) :
    (∫ t : ℝ,
        ‖∑ j ∈ Finset.range (2 * K.degree + 1),
            (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
              (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖) =
      ∫ θ in Set.Ioo (0 : ℝ) Real.pi,
        (K.normalization : ℝ) * ‖K.circlePoly (Complex.exp (2 * (θ : ℂ) * Complex.I))‖ ^ 2 *
          (Real.sin θ ^ 2 / (K.pole : ℝ) ^ 3) := by
  let a : ℝ := K.pole
  have ha : 0 < a := (by norm_num only : (0 : ℝ) < 1 / 2).trans (high_gaussian_pole_gt K)
  let g := fun t : ℝ ↦
    ‖∑ j ∈ Finset.range (2 * K.degree + 1),
        (K.expandedCoeff j : ℂ) * Complex.exp (5 * (Complex.I * (t : ℂ))) /
          (Complex.I * (t : ℂ) + (K.pole : ℂ)) ^ (K.logPower j + 1)‖
  have hs (θ : ℝ) (hθ : θ ∈ Set.Ioo 0 Real.pi) : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2
  have h :=
    MeasureTheory.integral_image_eq_integral_abs_deriv_smul (f := fun θ ↦ a * Real.cot θ) (f' :=
      fun θ ↦ -a / Real.sin θ ^ 2) measurableSet_Ioo
      (fun θ hθ ↦ (high_gaussian_cot_deriv a (hs θ hθ).ne').hasDerivWithinAt) (cot_injOn ha) g
  rw [cot_image_univ ha, MeasureTheory.setIntegral_univ] at h
  change (∫ t : ℝ, g t) = _
  rw [h]
  apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
  intro θ hθ
  have hsin := (hs θ hθ).ne'
  have hc := high_gaussian_cot_circle ha.ne' hsin
  have hj := high_gaussian_cot_jacobian ha hsin
  simp only [a, Complex.ofReal_ratCast] at hc hj
  change |(-a) / Real.sin θ ^ 2| * g (a * Real.cot θ) = _
  rw [neg_div, abs_neg, abs_of_nonneg (div_nonneg ha.le (sq_nonneg _))]
  have hm := high_gaussian_circle_mass K (a * Real.cot θ)
  dsimp only at hm
  change g (a * Real.cot θ) = _ at hm
  rw [hm]
  dsimp only [a]
  rw [hc, ← mul_div_assoc, mul_comm (K.pole / Real.sin θ ^ 2 : ℝ), mul_div_assoc, hj]

end PseudoPrime.PrimeTestBounds.MillerRabin
