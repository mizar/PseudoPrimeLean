/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.PointwiseWitness
public import PseudoPrime.PseudoSquare.Bounds.RefinedElementaryBounds
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-! # GRH-conditional prime quadratic witness challenges

These statements reproduce GRH and the two explicit Jacobi witness bounds for comparison;
the theorems below apply the library proofs without importing the challenge module.
-/

@[expose] public section

namespace ComparatorChallenges

/-- The integer arguments excluded as trivial zeros for a complex Dirichlet character.
The modulus-one case uses negative even integers; otherwise parity selects the nonpositive
even or negative odd integers. This set defines the zero exclusions used in GRH below. -/
noncomputable def dirichletTrivialZeros {q : ℕ} (χ : DirichletCharacter ℂ q) : Set ℤ := by
  classical
    exact
    if q = 1 then {z | ∃ n : ℕ, z = -2 * ((n : ℤ) + 1)}
    else if χ.Odd then {z | ∃ n : ℕ, z = -2 * (n : ℤ) - 1} else {z | ∃ n : ℕ, z = -2 * (n : ℤ)}

/-- For a nonzero modulus and a Dirichlet character, all zeros outside the excluded integer
set have real part one half. This is the character-level condition used in GRH. -/
def DirichletRiemannHypothesis {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  ∀ s : ℂ,
    χ.LFunction s = 0 → s ∉ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros χ → s.re = (1 : ℝ) / 2

/-- Every primitive complex Dirichlet character of nonzero modulus satisfies the character-level
Riemann hypothesis. This is the explicit assumption in both witness propositions. -/
def GeneralizedRiemannHypothesis : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ.IsPrimitive → DirichletRiemannHypothesis χ

/-- Under GRH, every positive odd nonsquare has an odd-prime Jacobi witness different from one,
bounded by the maximum of five and the squared logarithm. This states the first challenge. -/
def PrimeNeOneWitnessBound : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ n : ℕ,
      0 < n →
        Odd n →
        ¬IsSquare n →
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ max 5 (Real.log (n : ℝ) ^ 2) ∧ jacobiSym n p ≠ 1

/-- Under GRH, every odd nonsquare at least three has an odd-prime Jacobi witness equal to
negative one, bounded by the displayed squared logarithmic expression. This states the second
challenge. -/
def PrimeNegOneWitnessBound : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ n : ℕ,
      3 ≤ n →
        Odd n →
        ¬IsSquare n →
        ∃ p : ℕ,
          p.Prime ∧
            Odd p ∧
            (p : ℝ) ≤
              (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 2) ^ 2 ∧
            jacobiSym n p = -1

/-- The non-one witness bound follows from the library theorem for every positive odd nonsquare. -/
theorem prime_ne_one_witness_bound : PrimeNeOneWitnessBound := fun hGRH n hnpos hn hns ↦
  PseudoPrime.PseudoSquare.exists_prime_ne_one_witness_of_grh (n := n) hGRH hnpos hn hns

/-- The negative-one witness bound follows from the library theorem for every odd nonsquare
at least three. -/
theorem prime_neg_one_witness_bound : PrimeNegOneWitnessBound := fun hGRH n hn3 hn hns ↦
  PseudoPrime.PseudoSquare.exists_negOneWitness_le_refined_elementary (n := n) hGRH hn3 hn hns

end ComparatorChallenges
