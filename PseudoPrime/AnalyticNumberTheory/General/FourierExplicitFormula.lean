/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.FourierExplicitWeights

/-!
# Transport of a Mellin explicit identity to Fourier form

This file proves the algebraic and transform conversion from the Mellin identity
of Iwaniec--Kowalski Theorem 5.11 to the form used in Theorem 5.12. The Mellin identity
is an explicit hypothesis, not an established general L-function theorem here.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- Given an even complex test function and a Mellin explicit identity for its
logarithmic weight, obtain the Fourier-form arithmetic sum, conductor term, imaginary
pole value, central-line gamma integral, and multiplicity-weighted complex zero sum.
Use reflection of the weight, its square-root form, and the Mellin--Fourier identities.
The input identity must be proved from the L-function's analytic hypotheses elsewhere;
this transport does not establish convergence or the general explicit formula itself. -/
theorem fourier_explicitFormula_of_mellin_identity {ι : Type*} (g : ℝ → ℂ)
    (he : ∀ y : ℝ, g (-y) = g y) (a : ℕ → ℂ) (conductorTerm poleOrder : ℂ) (gammaTerm : ℝ → ℂ)
    (zero : ι → ℂ) (multiplicity : ι → ℕ)
    (hMellin :
      (∑' n : ℕ,
          (a (n + 1) * logarithmicTestWeight g (n + 1) +
            star (a (n + 1)) *
              (((n + 1 : ℕ) : ℝ)⁻¹ • logarithmicTestWeight g (((n + 1 : ℕ) : ℝ)⁻¹)))) =
        logarithmicTestWeight g 1 * conductorTerm + poleOrder * mellin (logarithmicTestWeight g) 1 +
            (1 / (2 * Real.pi) : ℂ) *
              (∫ t : ℝ,
                gammaTerm t *
                  mellin (logarithmicTestWeight g) (((1 / 2 : ℝ) : ℂ) + Complex.I * t)) -
          ∑' j : ι, (multiplicity j : ℂ) * mellin (logarithmicTestWeight g) (zero j)) :
    (∑' n : ℕ, (a (n + 1) + star (a (n + 1))) * g (Real.log (n + 1)) / (Real.sqrt (n + 1) : ℂ)) =
      g 0 * conductorTerm +
          poleOrder * fourierLaplace g (Complex.I * ((1 / (4 * Real.pi) : ℝ) : ℂ)) +
          (1 / (2 * Real.pi) : ℂ) *
            (∫ t : ℝ, gammaTerm t * FourierTransform.fourier g (t / (2 * Real.pi))) -
        ∑' j : ι, (multiplicity j : ℂ) * fourierLaplace g (mellinFourierFrequency (zero j)) := by
  have harith :
    (∑' n : ℕ,
        (a (n + 1) * logarithmicTestWeight g (n + 1) +
          star (a (n + 1)) *
            (((n + 1 : ℕ) : ℝ)⁻¹ • logarithmicTestWeight g (((n + 1 : ℕ) : ℝ)⁻¹)))) =
      ∑' n : ℕ,
        (a (n + 1) + star (a (n + 1))) * g (Real.log (n + 1)) / (Real.sqrt (n + 1) : ℂ) := by
    apply tsum_congr
    intro n
    have hn : 0 < ((n + 1 : ℕ) : ℝ) := Nat.cast_pos.mpr (Nat.succ_pos n)
    simp only [Nat.cast_add, Nat.cast_one] at hn ⊢
    rw [logarithmicTestWeight_reflection g he hn, logarithmicTestWeight_eq_div_sqrt g hn]
    ring
  have hgamma :
    (∫ t : ℝ, gammaTerm t * mellin (logarithmicTestWeight g) (((1 / 2 : ℝ) : ℂ) + Complex.I * t)) =
      ∫ t : ℝ, gammaTerm t * FourierTransform.fourier g (t / (2 * Real.pi)) := by
    apply MeasureTheory.integral_congr_ae
    exact
      MeasureTheory.ae_of_all _
        (fun t => by
          change
            gammaTerm t * mellin (logarithmicTestWeight g) (((1 / 2 : ℝ) : ℂ) + Complex.I * t) = _
          rw [mellin_logarithmicTestWeight_criticalLine g he])
  have hzero :
    (∑' j : ι, (multiplicity j : ℂ) * mellin (logarithmicTestWeight g) (zero j)) =
      ∑' j : ι, (multiplicity j : ℂ) * fourierLaplace g (mellinFourierFrequency (zero j)) := by
    apply tsum_congr
    intro j
    rw [mellin_logarithmicTestWeight_eq_fourierLaplace g he]
  rw [harith, logarithmicTestWeight_one, mellin_logarithmicTestWeight_one g he, hgamma,
    hzero] at hMellin
  exact hMellin

end PseudoPrime.AnalyticNumberTheory.General
