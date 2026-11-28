/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseBoxes656
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCurvature
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseInterpolation644

/-! # Four radius comparisons for the section 132 phase sum -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The norm of the combined coefficient is bounded by the four absolute
coordinates because the pole displacement has unit modulus. -/
private theorem phase_kernel_norm (t : ℝ) :
    ‖quarterPhaseKernel656 t‖ ≤
      (|(quarterPhaseRational656 t).re| + |(quarterPhaseRational656 t).im|) +
        (|(quarterPhasePole656 t).re| + |(quarterPhasePole656 t).im|) := by
  rw [quarter_phase_split_656]
  have h : ‖Complex.exp (Complex.I * ((21 / 8 : ℝ) * t : ℝ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      Real.exp_zero]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, h, mul_one]
  exact add_le_add (Complex.norm_le_abs_re_add_abs_im _) (Complex.norm_le_abs_re_add_abs_im _)

/-- On the whole radius range, the certified low-zero phase exceeds
the section 132 lower bound after allowing for the allocated tail and remainder. -/
theorem quarter_phase_head_656 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) {r : ℝ}
    (hr : r ∈ Set.Icc 322 328) :
    -(201 / 40000 : ℝ) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log r) - 6592787 / 1000000000 -
        2665 / 1000000 := by
  let C := fun i : Fin 29 ↦ quarterPhaseKernel656 (g i)
  let Z := fun u : ℝ ↦ pairedPhase g C (2 * Real.log u)
  have h₀ := quarter_phase_endpoint_656_322 hl hu
  have h₁ := quarter_phase_endpoint_656_32275 hl hu
  have h₂ := quarter_phase_endpoint_656_32425 hl hu
  have h₃ := quarter_phase_endpoint_656_32625 hl hu
  have h₄ := quarter_phase_endpoint_656_328 hl hu
  have hC : 2 * (∑ i : Fin 29, (g i) ^ 2 * ‖C i‖) ≤ 29 :=
    (mul_le_mul_of_nonneg_left
          (Finset.sum_le_sum
            (fun i _ ↦ mul_le_mul_of_nonneg_left (phase_kernel_norm (g i)) (sq_nonneg _)))
          (by norm_num only : (0 : ℝ) ≤ 2)).trans
      (quarter_phase_curvature_656 hl hu)
  have transfer {l u v : ℝ} (hl : 0 < l) (hru : r ∈ Set.Icc l u) (hleft : v ≤ Z l)
    (hright : v ≤ Z u)
    (hval :
      -(201 / 40000 : ℝ) ≤
        v - 29 * (u - l) ^ 2 / (2 * l ^ 2) - 6592787 / 1000000000 - 2665 / 1000000) :
    -(201 / 40000 : ℝ) ≤ Z r - 6592787 / 1000000000 - 2665 / 1000000 := by
    let D := fun i ↦ ((g i : ℂ) * Complex.I) * C i
    let E := fun i ↦ ((g i : ℂ) * Complex.I) * D i
    have h :=
      log_phase_lower_of_curvature (f := pairedPhase g C) (f' := pairedPhase g D) (f'' :=
        pairedPhase g E) hl hru (by norm_num only : (0 : ℝ) ≤ 29)
        (fun x _ ↦ (paired_phase_deriv g C x).continuousAt.continuousWithinAt)
        (fun x _ ↦ paired_phase_deriv g C x) (fun x _ ↦ paired_phase_deriv g D x)
        (fun x _ ↦
          (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ phase_term_upper x (g i) (C i)))
                (by norm_num only : (0 : ℝ) ≤ 2)).trans
            hC)
    change min (Z l) (Z u) - _ ≤ Z r at h
    linarith only [h, le_min hleft hright, hval]
  by_cases h1 : r ≤ 1291 / 4
  · exact
      transfer (by norm_num only) ⟨hr.1, h1⟩ h₀
        ((by norm_num only : (4313522 : ℝ) / 1000000000 ≤ 4563762 / 1000000000).trans h₁)
        (by norm_num only)
  by_cases h2 : r ≤ 1297 / 4
  · exact
      transfer (by norm_num only) ⟨(le_of_not_ge h1), h2⟩ h₁
        ((by norm_num only : (4563762 : ℝ) / 1000000000 ≤ 4875145 / 1000000000).trans h₂)
        (by norm_num only)
  by_cases h3 : r ≤ 1305 / 4
  · exact
      transfer (by norm_num only) ⟨(le_of_not_ge h2), h3⟩ h₂
        ((by norm_num only : (4875145 : ℝ) / 1000000000 ≤ 4909557 / 1000000000).trans h₃)
        (by norm_num only)
  · exact
      transfer (by norm_num only) ⟨(le_of_not_ge h3), hr.2⟩
        ((by norm_num only : (4706101 : ℝ) / 1000000000 ≤ 4909557 / 1000000000).trans h₃) h₄
        (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
