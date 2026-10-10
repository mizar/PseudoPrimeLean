/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Extensions.QNeOneLogWeightedBounds

/-!
# Contradictions for the three Q-ne-one branches

The common weighted-sum estimates contradict the numerical separation bounds.
-/

@[expose] public section

namespace PseudoPrime.LLS.Extensions

/-- For a nonprincipal character with nonzero modulus and conductor, assume an even primitive
character, GRH, both Riemann lower bounds, `y ≥ 12`, `log conductor ≤ y + log 4`,
primitive value zero at two, and value one on odd primes in the specified ranges up to `y²`.
The resulting common lower and upper bounds for the real weighted sum are incompatible
with their strict numerical separation. This proves the zero-branch contradiction used
in the independent witness argument. -/
theorem primitiveLogWeightedBounds_of_qneOne_zero_branch_even_false_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y + Real.log 4) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 0) : False := by
  have hbounds :=
    primitiveLogWeightedBounds_of_qneOne_zero_branch_even_common χ hne heven hGRH
      (le_trans (by norm_num only : (8 : ℝ) ≤ 12) hy) hlogD hriemann hriemannReciprocal hodd h2
  exact qNeOne_common_sandwich_false_of_twelve hy hbounds.1 hbounds.2

/-- The even negative-one branch is impossible under GRH, the two Riemann lower
bounds, odd-prime triviality, `y ≥ 12`, and `log conductor ≤ y`.
The corrected sum `Re S + δ` satisfies the common sandwich, contradicting its numerical
separation. This supplies the negative-one branch of the independent witness argument. -/
theorem primitiveLogWeightedBounds_of_qneOne_neg_one_branch_false_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = -1) : False := by
  have hbounds :=
    primitiveLogWeightedBounds_of_qneOne_neg_one_branch_corrected_common χ hne heven hGRH
      (le_trans (by norm_num only : (8 : ℝ) ≤ 12) hy) hlogD hriemann hriemannReciprocal hodd h2
  exact qNeOne_common_sandwich_false_of_twelve hy hbounds.1 hbounds.2

/-- The even one branch is impossible under GRH, the two Riemann lower bounds,
odd-prime triviality, `y ≥ 12`, and `log conductor ≤ y`.
The real weighted sum satisfies the common sandwich, whose upper envelope is strictly
below its lower envelope. This discharges the one branch of the independent witness argument. -/
theorem primitiveLogWeightedBounds_of_qneOne_one_branch_false_common {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (heven : χ.primitiveCharacter.Even)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 12 ≤ y)
    (hlogD : Real.log χ.conductor ≤ y) (hriemann : LLSRiemannWeightedLowerBound)
    (hriemannReciprocal : LLSRiemannReciprocalLowerBound)
    (hodd :
      ∀ {k p : ℕ},
        k ∈ Finset.Icc 1 ⌊Real.log (y ^ 2) / Real.log 2⌋₊ →
          p ∈ Finset.Ioc 0 ⌊(y ^ 2) ^ ((1 : ℝ) / k)⌋₊ →
          p.Prime → Odd p → (χ.primitiveCharacter p = 1))
    (h2 : χ.primitiveCharacter 2 = 1) : False := by
  have hbounds :=
    primitiveLogWeightedBounds_of_qneOne_one_branch_even_common χ hne heven hGRH
      (le_trans (by norm_num only : (8 : ℝ) ≤ 12) hy) hlogD hriemann hriemannReciprocal hodd h2
  exact qNeOne_common_sandwich_false_of_twelve hy hbounds.1 hbounds.2

end PseudoPrime.LLS.Extensions
