/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TightCubicConductorBounds
public import PseudoPrime.LLS.PaperStatements.TightCubicConductorBounds

/-! # Uniform exclusions and comparisons for tight cubic radii -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For nonnegative conductor envelope G, the tight sensitive radius squared
is no larger than the former cubic radius squared for the same cost E.
Apply the generic monotonicity of the nonnegative root radius. -/
theorem tightCubicExclusionRadius_sq_le_previous {G E : ℝ} (hG : 0 ≤ G) :
    (tightCubicExclusionRadius G E) ^ 2 ≤ (cubicExclusionRadius G E) ^ 2 := by
  dsimp only [tightCubicExclusionRadius, cubicExclusionRadius]
  have hh :=
    root_radius_sq_mono (B₁ := (10 / 13 : ℝ) * G + 63 / 2) (B₂ := (10 / 13 : ℝ) * G + 34) (D₁ :=
      (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * E) (D₂ := (8 / 5 : ℝ) * G + 33 + (4 / 3 : ℝ) * E)
      (by linarith only [hG]) (by linarith only []) (by linarith only [])
  simpa only [add_assoc] using hh

/-- The tight square-factor radius squared is no larger than the former radius
for the same conductor and square-factor budgets. Root monotonicity applies
after lowering its additive conductor constant from 35 to 65/2. -/
theorem tightCubicSquareFactorRadius_sq_le_previous {G E : ℝ} (hG : 0 ≤ G) :
    (tightCubicSquareFactorRadius G E) ^ 2 ≤ (cubicSquareFactorRadius G E) ^ 2 := by
  dsimp only [tightCubicSquareFactorRadius, cubicSquareFactorRadius]
  exact root_radius_sq_mono (by linarith only [hG]) (by linarith only []) le_rfl

/-- Tight cubic conductor radius with uniform exclusion cost twice the sum
of prime-factor logarithms of m. Its square bounds a prime outside m under
primitive nonprincipal GRH and a conductor logarithm envelope G. -/
noncomputable def tightCubicConductorRadius (G : ℝ) (m : ℕ) : ℝ :=
  tightCubicExclusionRadius G (2 * ∑ p ∈ m.primeFactors, Real.log p)

/-- Under primitive nonprincipal GRH, an excluded integer m≠0 and a
conductor envelope G yield a non-one prime outside m below the tight cubic
conductor radius squared. Bound the sensitive cost by the uniform cost. -/
theorem exists_prime_outside_le_tight_cubic_conductor_radius {f m : ℕ} [NeZero f]
    (χ : DirichletCharacter ℂ f) (hf : 2 ≤ f) (hm : m ≠ 0)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) {G : ℝ} (hlog : Real.log f ≤ G) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ (tightCubicConductorRadius G m) ^ 2 ∧ ¬p ∣ m ∧ χ p ≠ 1 := by
  exact
    exists_prime_outside_le_tight_cubic_exclusion_radius χ hf hm hGRH hp hne hlog
      (AnalyticNumberTheory.Arithmetic.characterExclusionCost_le_twice χ m)

/-- For a nonnegative conductor envelope, the tight sensitive squared radius
is bounded by its uniform exclusion-cost version. Apply the cost bound and
root monotonicity while keeping the same conductor constants. -/
theorem tightCubicExclusionRadius_sq_le_uniform {f : ℕ} (χ : DirichletCharacter ℂ f) (m : ℕ) {G : ℝ}
    (hG : 0 ≤ G) :
    (tightCubicExclusionRadius G (AnalyticNumberTheory.Arithmetic.characterExclusionCost χ m)) ^ 2 ≤
      (tightCubicExclusionRadius G (2 * ∑ p ∈ m.primeFactors, Real.log p)) ^ 2 := by
  have hc := AnalyticNumberTheory.Arithmetic.characterExclusionCost_le_twice χ m
  have hh :=
    root_radius_sq_mono (B₁ := (10 / 13 : ℝ) * G + 63 / 2) (B₂ := (10 / 13 : ℝ) * G + 63 / 2) (D₁ :=
      (8 / 5 : ℝ) * G + 28 +
        (4 / 3 : ℝ) * AnalyticNumberTheory.Arithmetic.characterExclusionCost χ m)
      (D₂ := (8 / 5 : ℝ) * G + 28 + (4 / 3 : ℝ) * (2 * ∑ p ∈ m.primeFactors, Real.log p))
      (by linarith only [hG]) le_rfl (by linarith only [hc])
  simpa only [tightCubicExclusionRadius, add_assoc] using hh

end PseudoPrime.LLS.PaperStatements
