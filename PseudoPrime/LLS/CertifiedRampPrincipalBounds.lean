/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.ExponentialRampCutoff
public import PseudoPrime.Analysis.FixedPointExponentialIntervals
public import PseudoPrime.LLS.AnchoredEuler128
public import PseudoPrime.Analysis.CertifiedRampPrincipalBounds

/-! # Certified ramp mass for finite-scale principal comparisons -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For the totalized scalar lower cap, replace the exact ramp mass coefficient by
133/160 while retaining the full variable-width error budget. Multiply the certified
mass bound by the nonnegative square root. This gives an explicit scalar input
for positive-scale witness separation. -/
theorem variableRampPrincipalLower_ge_133_160 (x h : ℝ) :
    (133 / 160 : ℝ) * Real.sqrt x - variableRampPrincipalErrorNumerator x h / Real.sqrt x ≤
      variableRampPrincipalLower x h := by
  have hm :=
    mul_le_mul_of_nonneg_right Analysis.ramp_mass_coefficient_ge_133_160 (Real.sqrt_nonneg x)
  dsimp only [variableRampPrincipalLower]
  linarith only [hm]

/-- For nonprincipal GRH data with an admissible width and upper Euler cutoff at least
128, a positive explicit gap using mass 133/160 and the certified anchor constant
excludes prime triviality. Compare with the actual variable-width principal cap and
apply the anchor-128 witness theorem. No unproved mass or anchor premise remains. -/
theorem prime_trivial_false_of_anchor128_mass133 {q A : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hne : χ ≠ 1) (hqA : q ≤ A) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x C b h : ℝ} (hx : 2 ≤ x) (hh : 0 < h) (hhx : h ≤ x) (hb : 128 ≤ b)
    (hcut : b ≤ (99 / 40 : ℝ) * x)
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ.primitiveCharacter ≤ C)
    (hgap :
      0 <
        (133 / 160 : ℝ) * Real.sqrt x - variableRampPrincipalErrorNumerator x h / Real.sqrt x -
            reflectedSplitUpper A C x +
          2 * ((3643 / 1000 : ℝ) - 5 * b ^ (-1 / 4 : ℝ))) :
    ¬(∀ p : ℕ, p.Prime → (p : ℝ) ≤ (99 / 40 : ℝ) * x → χ p = 1) := by
  apply prime_trivial_false_of_certified_anchor128 χ hne hqA hGRH hx hh hhx hb hcut hC
  have hl := variableRampPrincipalLower_ge_133_160 x h
  linarith only [hl, hgap]

end PseudoPrime.LLS
