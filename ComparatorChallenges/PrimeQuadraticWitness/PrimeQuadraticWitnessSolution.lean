/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.PointwiseWitness
public import PseudoPrime.PseudoSquare.Bounds.RefinedElementaryBounds
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Mathlib.NumberTheory.LSeries.Nonvanishing

/-! # GRH-conditional prime quadratic witness challenges

These statements reproduce GRH and the two explicit Jacobi witness bounds for comparison;
the theorems below apply the library proofs without importing the challenge module.
-/

@[expose] public section

namespace ComparatorChallenges.PrimeQuadraticWitness

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

/-- The Dirichlet Riemann hypothesis for the trivial character modulo one is equivalent to
the Riemann hypothesis for the Riemann zeta function. Identify the character's L-function and
trivial zeros with those of zeta, and use the nonvanishing convention at one. This equivalence
connects the challenge's GRH formulation to the ordinary Riemann hypothesis. -/
theorem dirichletRiemannHypothesis_one_iff :
    DirichletRiemannHypothesis (1 : DirichletCharacter ℂ 1) ↔ RiemannHypothesis := by
  classical
  have htriv (s : ℂ) :
    s ∈ (Int.cast : ℤ → ℂ) '' dirichletTrivialZeros (1 : DirichletCharacter ℂ 1) ↔
      ∃ n : ℕ, s = -2 * ((n : ℂ) + 1) := by
    simp only [Set.mem_image]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, rfl⟩
      refine ⟨n, ?_⟩
      push_cast
      ring
    · rintro ⟨n, rfl⟩
      refine ⟨-2 * ((n : ℤ) + 1), ⟨n, rfl⟩, ?_⟩
      push_cast
      ring
  simp only [DirichletRiemannHypothesis, DirichletCharacter.LFunction_modOne_eq, htriv]
  constructor
  · intro h s hs ht _
    exact h s hs ht
  · intro h s hs ht
    exact h s hs ht (fun he => riemannZeta_one_ne_zero (he ▸ hs))

/-- The challenge's generalized Riemann hypothesis implies the Riemann hypothesis. Apply GRH
to the primitive trivial character modulo one and use the modulus-one equivalence. This provides
the ordinary hypothesis to results that need only the Riemann zeta function. -/
theorem GeneralizedRiemannHypothesis.riemann (h : GeneralizedRiemannHypothesis) :
    RiemannHypothesis := by
  have hDirichlet : DirichletRiemannHypothesis 1 :=
    h 1 1 DirichletCharacter.isPrimitive_one_level_one
  exact dirichletRiemannHypothesis_one_iff.mp hDirichlet

/-- Under GRH, every positive odd nonsquare has an odd-prime Jacobi witness different from one,
bounded by the maximum of five and the squared logarithm. This states the first challenge. -/
def PrimeNeOneWitnessBound : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ n : ℕ,
      Odd n →
        ¬IsSquare n →
        ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ max 5 (Real.log (n : ℝ) ^ 2) ∧ jacobiSym n p ≠ 1

/-- Under GRH, every odd nonsquare at least three has an odd-prime Jacobi witness equal to
negative one, bounded by the displayed squared logarithmic expression. This states the second
challenge. -/
def PrimeNegOneWitnessBound : Prop :=
  GeneralizedRiemannHypothesis →
    ∀ n : ℕ,
      Odd n →
        ¬IsSquare n →
        ∃ p : ℕ,
          p.Prime ∧
            Odd p ∧
            (p : ℝ) ≤
              (Real.log (4 * (n : ℝ)) + (24 / 5 : ℝ) * Real.log (Real.log (4 * (n : ℝ))) + 2) ^ 2 ∧
            jacobiSym n p = -1

/-- The non-one witness bound follows from the library theorem for every positive odd nonsquare. -/
theorem prime_ne_one_witness_bound : PrimeNeOneWitnessBound := fun hGRH n hn hns ↦
  PseudoPrime.PseudoSquare.exists_ne_one_witness_of_odd (n := n) hGRH hn hns

/-- The negative-one witness bound follows from the library theorem for every odd nonsquare
at least three. -/
theorem prime_neg_one_witness_bound : PrimeNegOneWitnessBound := fun hGRH n hn hns ↦
  PseudoPrime.PseudoSquare.exists_neg_one_witness_of_odd (n := n) hGRH hn hns

end ComparatorChallenges.PrimeQuadraticWitness
