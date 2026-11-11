/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundPhaseDerivativeBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundEulerLog
import PseudoPrime.Analysis.ContinuousLogInterval
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundArgDerivative

/-! # Euler-normalized zeta argument on the Backlund segment -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At a positive good height, zeta has a continuous horizontal polar
argument normalized by the Euler logarithm at `3/2 + iT`. A continuous
logarithm lift can be translated to the prescribed right-end value. -/
theorem exists_euler_normalized_arg {T : ℝ} (hT : 0 < T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)) ∧
        (∀ x : ℝ,
          x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
            riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
              (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
                Complex.exp ((φ x : ℂ) * Complex.I)) ∧
        φ (3 / 2) =
          (AnalyticNumberTheory.RiemannZeta.backlundZetaLog
              (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im := by
  let f : ℝ → ℂ := fun x => riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)
  have hf : ContinuousOn f (Set.Icc (-(1 / 2)) (3 / 2)) := by
    intro x hx
    have h1 : (x : ℂ) + (T : ℂ) * Complex.I ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
        Complex.I_im, zero_mul, mul_one, add_zero, zero_add, Complex.one_im] at hi
      linarith only [hT, hi]
    have hc : ContinuousAt (fun y : ℝ => (y : ℂ) + (T : ℂ) * Complex.I) x :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    have hd := (differentiableAt_riemannZeta h1).continuousAt
    exact
      (ContinuousAt.comp (f := fun y : ℝ => (y : ℂ) + (T : ℂ) * Complex.I) hd hc).continuousWithinAt
  have hne : ∀ x ∈ Set.Icc (-(1 / 2) : ℝ) (3 / 2), f x ≠ 0 := by
    intro x hx
    exact zeta_horizontal_ne_zero hT hgood
  have hw :
    Complex.exp
        (AnalyticNumberTheory.RiemannZeta.backlundZetaLog
          (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)) =
      f (3 / 2) := by
    apply AnalyticNumberTheory.RiemannZeta.exp_backlundZetaLog
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  exact Analysis.exists_continuous_arg_Icc_with_value (by norm_num only) hf hne hw

/-- At a good height at least `17`, an Euler-normalized polar argument at
`1/2 + iT` obeys the explicit Backlund bound. The right endpoint contributes
at most `log(14/5)`, while the horizontal variation is controlled by Jensen. -/
theorem euler_normalized_arg_bound {T : ℝ} (hT : 17 ≤ T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hpolar :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    (hnorm :
      φ (3 / 2) =
        (AnalyticNumberTheory.RiemannZeta.backlundZetaLog
            (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im) :
    |φ (1 / 2)| / Real.pi ≤
      Real.log (14 / 5) / Real.pi +
        ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        ((1 / T) / Real.pi) / 2 := by
  have hbound := backlund_phase_bound_good hT hgood hcont hpolar
  have hnorm' : |φ (3 / 2)| ≤ Real.log (14 / 5) := by
    rw [hnorm]
    apply (Complex.abs_im_le_norm _).trans
    apply norm_backlundZetaLog_le_const
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
    norm_num only
  have htri : |φ (1 / 2)| ≤ |φ (3 / 2)| + |φ (3 / 2) - φ (1 / 2)| := by
    have he : φ (1 / 2) = φ (3 / 2) - (φ (3 / 2) - φ (1 / 2)) := by ring
    calc
      |φ (1 / 2)| = |φ (3 / 2) - (φ (3 / 2) - φ (1 / 2))| := congrArg abs he
      _ ≤ |φ (3 / 2)| + |φ (3 / 2) - φ (1 / 2)| := abs_sub _ _
  have hdiv := div_le_div_of_nonneg_right htri Real.pi_pos.le
  rw [add_div] at hdiv
  have hnormdiv := div_le_div_of_nonneg_right hnorm' Real.pi_pos.le
  linarith only [hdiv, hnormdiv, hbound]

/-- Every good height at least `17` admits an Euler-normalized continuous
argument satisfying the explicit Backlund bound at `1/2 + iT`. This packages
the normalized lift with its quantitative endpoint estimate. -/
theorem exists_euler_arg_bound {T : ℝ} (hT : 17 ≤ T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)) ∧
        (∀ x : ℝ,
          x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
            riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
              (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
                Complex.exp ((φ x : ℂ) * Complex.I)) ∧
        φ (3 / 2) =
          (AnalyticNumberTheory.RiemannZeta.backlundZetaLog
              (((3 / 2 : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im ∧
        |φ (1 / 2)| / Real.pi ≤
          Real.log (14 / 5) / Real.pi +
            ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
              (2 * Real.log 2) +
            ((1 / T) / Real.pi) / 2 := by
  obtain ⟨φ, hcont, hpolar, hnorm⟩ := exists_euler_normalized_arg (by linarith only [hT]) hgood
  exact ⟨φ, hcont, hpolar, hnorm, euler_normalized_arg_bound hT hgood hcont hpolar hnorm⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
