/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundPhaseBound
public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundGammaDerivative
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundArgDerivative
import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundFunctionalEquation

/-! # Backlund phase bound from a logarithmic derivative -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- If the reflected zeta-argument variation has the logarithmic derivative
of the functional-equation factor on `[0,1]`, its endpoint variation has
the explicit Backlund bound with error `1/T`. The mean-value estimate supplies
the reflected-error input to the Jensen phase inequality. -/
theorem backlund_phase_bound_of_deriv {T : ℝ} (hT : 17 ≤ T) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hpolar :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    (hderiv :
      ∀ u ∈ Set.Icc (0 : ℝ) 1,
        HasDerivWithinAt (fun v : ℝ => (φ (1 / 2 + v) - φ (1 / 2)) + (φ (1 / 2 - v) - φ (1 / 2)))
          (logDeriv AnalyticNumberTheory.RiemannZeta.backlundChi
              (((1 / 2 + u : ℝ) : ℂ) + (T : ℂ) * Complex.I)).im
          (Set.Icc 0 1) u) :
    |φ (3 / 2) - φ (1 / 2)| / Real.pi ≤
      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        ((1 / T) / Real.pi) / 2 := by
  have hTpos : 0 < T := by linarith only [hT]
  apply backlund_zeta_phase_bound hT (one_div_nonneg.mpr hTpos.le) hcont hpolar
  apply backlund_reflection_error_of_deriv hTpos
  · simp only [add_zero, sub_zero, sub_self]
  · exact hderiv

/-- At a good height at least `17`, every continuous polar argument of zeta
on the Backlund segment satisfies the explicit endpoint phase bound. The
continuous argument derivative and the differentiated functional equation
supply the derivative identity required by the Gamma-factor estimate. -/
theorem backlund_phase_bound_good {T : ℝ} (hT : 17 ≤ T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hpolar :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I)) :
    |φ (3 / 2) - φ (1 / 2)| / Real.pi ≤
      ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
          (2 * Real.log 2) +
        ((1 / T) / Real.pi) / 2 := by
  have hTpos : 0 < T := by linarith only [hT]
  apply backlund_phase_bound_of_deriv hT hcont hpolar
  intro u hu
  have hd :
    ∀ x ∈ Set.Icc (-(1 / 2) : ℝ) (3 / 2),
      HasDerivWithinAt φ (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)).im
        (Set.Icc (-(1 / 2)) (3 / 2)) x := by
    intro x hx
    exact zeta_horizontal_arg_deriv hTpos hgood hcont hpolar hx
  have hf := reflected_arg_deriv hd hu
  rw [AnalyticNumberTheory.RiemannZeta.zeta_reflected_logDeriv_im hTpos
      (zeta_horizontal_ne_zero hTpos hgood)] at hf
  exact hf

/-- Every good height at least `17` admits a continuous polar argument of
zeta on the Backlund segment satisfying the explicit endpoint phase bound.
The argument exists by the continuous-logarithm lift, and the bound follows
from the preceding good-height theorem. -/
theorem exists_backlund_phase_good {T : ℝ} (hT : 17 ≤ T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    ∃ φ : ℝ → ℝ,
      ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)) ∧
        (∀ x : ℝ,
          x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
            riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
              (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
                Complex.exp ((φ x : ℂ) * Complex.I)) ∧
        |φ (3 / 2) - φ (1 / 2)| / Real.pi ≤
          ((3 / 2 : ℝ) * Real.log (14 / 5) + (1 / 2 : ℝ) * Real.log T + 3 / (T - 2) ^ 2) /
              (2 * Real.log 2) +
            ((1 / T) / Real.pi) / 2 := by
  obtain ⟨φ, hcont, hpolar⟩ :=
    exists_zeta_horizontal_arg (a := -(1 / 2 : ℝ)) (b := 3 / 2) (by linarith only [hT])
      (by norm_num only) hgood
  exact ⟨φ, hcont, hpolar, backlund_phase_bound_good hT hgood hcont hpolar⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
