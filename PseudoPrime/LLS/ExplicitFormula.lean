/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SmoothedContour
public import PseudoPrime.LLS.Lemma24
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.WeightedSumIntegral
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MellinWeightedSums

/-!
# Riemann explicit-formula interfaces

This file uses the foundation's weighted-sum integral identities to convert vertical-integral
lower bounds into the finite weighted-sum bounds used in LLS Lemmas 2.1 and 2.4. The two named
propositions separate this conversion from the contour and residue proofs.

The vertical-integral propositions are inputs to the general analytic core. The RH-specific
proofs in RiemannWeightedBounds.lean
instead use the Mellin identities at real part two directly.
-/

@[expose] public section

namespace PseudoPrime.LLS

/--
Vertical-integral lower-bound interface for the logarithmic kernel (LLS Lemma 2.1).

This proposition is a logarithmic contour input to the general analytic core.
The definition separates that input from the Mellin identity converting it to a finite sum.
-/
def LLSRiemannLogVerticalIntegralLowerBound : Prop :=
  ∀ x : ℝ,
    1 < x →
      ∀ τ : ℝ,
        1 < τ →
          x - Real.log (2 * Real.pi) * Real.log x - 1 -
              2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass * (Real.sqrt x + 1) ≤
            ((2 * Real.pi : ℝ)⁻¹ •
                ∫ y : ℝ,
                  AnalyticNumberTheory.RiemannZeta.riemannZetaLogContourKernel x
                    ((τ : ℂ) + y * Complex.I)).re

/--
Vertical-integral lower-bound interface for the reciprocal kernel (LLS Lemma 2.4).

This proposition is a reciprocal contour input to the general analytic core. Its shape
matches the reciprocal kernel's poles and the explicit trivial-zero series.
-/
def LLSRiemannReciprocalVerticalIntegralLowerBound : Prop :=
  ∀ x : ℝ,
    1 < x →
      ∀ τ : ℝ,
        1 < τ →
          Real.log x - (1 + Real.eulerMascheroniConstant) + Real.log (2 * Real.pi) / x -
              AnalyticNumberTheory.RiemannZeta.riemannReciprocalTrivialZeroSeries x -
              2 * AnalyticNumberTheory.RiemannXi.riemannZeroMass / Real.sqrt x ≤
            ((2 * Real.pi : ℝ)⁻¹ •
                ∫ y : ℝ,
                  AnalyticNumberTheory.RiemannZeta.riemannZetaReciprocalContourKernel x
                    ((τ : ℂ) + y * Complex.I)).re

/-- Convert the logarithmic vertical-integral interface into LLS Lemma 2.1's Riemann lower bound. -/
theorem llsRiemannWeightedLowerBound_of_verticalIntegralLowerBound
    (h : LLSRiemannLogVerticalIntegralLowerBound) : LLSRiemannWeightedLowerBound := by
  intro x hx
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have heq :=
    AnalyticNumberTheory.RiemannZeta.logWeightedMangoldtSum_eq_integral hx0 (τ := 2)
      (by norm_num only)
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  rw [hre]
  exact h x hx 2 (by norm_num only)

/-- Convert the reciprocal vertical-integral interface into LLS Lemma 2.4's explicit Riemann
lower bound. -/
theorem llsRiemannReciprocalExplicitLowerBound_of_verticalIntegralLowerBound
    (h : LLSRiemannReciprocalVerticalIntegralLowerBound) :
    LLSRiemannReciprocalExplicitLowerBound := by
  intro x hx
  have hx0 : (0 : ℝ) < x := zero_lt_one.trans hx
  have heq :=
    AnalyticNumberTheory.RiemannZeta.reciprocalWeightedMangoldtSum_eq_integral hx0 (τ := 2)
      (by norm_num only)
  have hre := congrArg Complex.re heq
  rw [Complex.ofReal_re] at hre
  rw [hre]
  exact h x hx 2 (by norm_num only)

end PseudoPrime.LLS
