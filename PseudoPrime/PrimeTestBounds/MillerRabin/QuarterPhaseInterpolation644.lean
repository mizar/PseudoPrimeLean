/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhasePairs644
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroHeadPhaseDerivative
import PseudoPrime.Analysis.SecondDerivativeInterpolation

/-! # Interpolating the finite section 122 phase sum in logarithmic coordinates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The paired phase sum at logarithmic coordinate x with real
frequencies g and complex coefficients C. The factor two counts both signs. -/
noncomputable def pairedPhase {n : ℕ} (g : Fin n → ℝ) (C : Fin n → ℂ) (x : ℝ) : ℝ :=
  2 * ∑ i : Fin n, (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) * C i).re

private theorem paired_phase_deriv {n : ℕ} (g : Fin n → ℝ) (C : Fin n → ℂ) (x : ℝ) :
    HasDerivAt (pairedPhase g C) (pairedPhase g (fun i ↦ ((g i : ℂ) * Complex.I) * C i) x) x := by
  have h :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun i _ ↦ AnalyticNumberTheory.RiemannZeta.hasDerivAt_re_phase_term (g i) x (C i) 1)
  convert h.const_mul 2 using 1
  · funext y
    unfold pairedPhase
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [div_one, Complex.ofReal_mul]
    congr 1
    rw [show (Complex.I * ((y : ℂ) * (g i : ℂ))) = (g i : ℂ) * (y : ℂ) * Complex.I by ring,
      mul_comm (C i)]
  · unfold pairedPhase
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    simp only [div_one, Complex.ofReal_mul]
    congr 1
    rw [show (Complex.I * ((x : ℂ) * (g i : ℂ))) = (g i : ℂ) * (x : ℂ) * Complex.I by ring]
    ring

private theorem phase_term_upper (x g : ℝ) (C : ℂ) :
    (Complex.exp (Complex.I * ((x * g : ℝ) : ℂ)) *
          (((g : ℂ) * Complex.I) * (((g : ℂ) * Complex.I) * C))).re ≤
      g ^ 2 * ‖C‖ := by
  have h :=
    Complex.re_le_norm
      (Complex.exp (Complex.I * ((x * g : ℝ) : ℂ)) *
        (((g : ℂ) * Complex.I) * (((g : ℂ) * Complex.I) * C)))
  have he : ‖Complex.exp (Complex.I * ((x * g : ℝ) : ℂ))‖ = 1 := by
    rw [Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      Real.exp_zero]
  rw [norm_mul, he, one_mul, norm_mul, norm_mul ((g : ℂ) * Complex.I), norm_mul (g : ℂ),
    Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs] at h
  calc
    _ ≤ |g| * (|g| * ‖C‖) := h
    _ = _ := by rw [← mul_assoc, ← pow_two, sq_abs]

/-- Twice the sum of the squared frequencies times the coefficient norms
bounds the second derivative. Certified endpoint lower bounds thus incur
at most one eighth of this curvature budget times the squared width. -/
theorem paired_phase_interpolate {n : ℕ} (g : Fin n → ℝ) (C : Fin n → ℂ) {a b x B M : ℝ}
    (hab : a < b) (hx : x ∈ Set.Icc a b) (hM : 0 ≤ M)
    (hcurv : 2 * (∑ i : Fin n, (g i) ^ 2 * ‖C i‖) ≤ M) (ha : B ≤ pairedPhase g C a)
    (hb : B ≤ pairedPhase g C b) : B - M * (b - a) ^ 2 / 8 ≤ pairedPhase g C x := by
  apply
    Analysis.lower_bound_on_interval_of_second_deriv_le hab hM (fun y _ ↦ paired_phase_deriv g C y)
      (fun y _ ↦ paired_phase_deriv g (fun i ↦ ((g i : ℂ) * Complex.I) * C i) y) _ ha hb hx
  intro y hy
  unfold pairedPhase
  exact
    (mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ ↦ phase_term_upper y (g i) (C i)))
          (by norm_num only : (0 : ℝ) ≤ 2)).trans
      hcurv

/-- For the certified positive ordinates, interpolate their paired phase
and add the high-zero budget to cover every finite height truncation. -/
theorem quarter_phase_interval_644 (hRH : RiemannHypothesis) :
    ∃ g : Fin 29 → ℝ,
      AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g ∧
        AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g ∧
        ∀ {a b x B M T : ℝ},
          a < b →
            x ∈ Set.Icc a b →
            0 ≤ M →
            100 ≤ T →
            2 * (∑ i : Fin 29, (g i) ^ 2 * ‖quarterPhaseKernel644 (g i)‖) ≤ M →
            B ≤ pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) a →
            B ≤ pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) b →
            B - M * (b - a) ^ 2 / 8 - 0.0061952 ≤
              ∑ ρ ∈ AnalyticNumberTheory.RiemannZeta.zerosUpTo T,
                (AnalyticNumberTheory.RiemannZeta.riemannZetaZeroMultiplicity ρ : ℝ) *
                  (Complex.exp (Complex.I * ((x * ρ.im : ℝ) : ℂ)) *
                      quarterPhaseKernel644 ρ.im).re := by
  obtain ⟨g, hlo, hhi, h⟩ := quarter_phase_brackets_644 hRH
  refine ⟨g, hlo, hhi, ?_⟩
  intro a b x B M T hab hx hM hT hc ha hb
  exact h T hT x _ (paired_phase_interpolate g _ hab hx hM hc ha hb)

end PseudoPrime.PrimeTestBounds.MillerRabin
