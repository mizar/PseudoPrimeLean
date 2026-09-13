/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.Numerics

/-!
# Primitive-character analytic bounds for LLS Part 1

This file gives a shared witness interface for Lemmas 2.2 and 2.3. The witness `b` is intended to
represent `|Re B(χ̃)|`, but the propositions only require a nonnegative real satisfying both bounds.
Keeping the same witness in both inequalities prevents an accidental mismatch between
the explicit-formula upper bound and the reciprocal-weight estimate.
-/

namespace PseudoPrime.LLS

/-- Lemma 2.2's upper-bound shape at the Part 1 radius, parameterized by a real candidate `b`
for `|Re B(χ̃)|`; equality with that quantity is not part of this proposition. -/
def LLSPart1PrimitiveWeightedUpperAt {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) : Prop :=
  let x := (llsTheorem11S1RadiusRoot q) ^ 2
  (AnalyticNumberTheory.Arithmetic.characterLogWeightedSum x χ.primitiveCharacter).re ≤
    (2 * llsTheorem11S1RadiusRoot q + 2 + Real.log x) * b +
        Real.log ((χ.conductor : ℝ) / Real.pi) * Real.log x / 2 -
      11 / 4

/-- Lemmas 2.3--2.4 bound the same zero-mass witness used in Lemma 2.2. -/
def LLSPart1PrimitiveZeroMassUpperAt {q : ℕ} (χ : DirichletCharacter ℂ q) (b : ℝ) : Prop :=
  b ≤ Real.log χ.conductor / 2 + 2 / 5 - llsAuxiliaryTerm q

/-- The shared-witness analytic core needed to prove the primitive upper responsibility. -/
def LLSPart1PrimitiveCoreBounds : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q),
    3000 ≤ q →
      χ ≠ 1 →
      llsTheorem11S1NoSmallPrime χ →
      ∃ b : ℝ, 0 ≤ b ∧ LLSPart1PrimitiveWeightedUpperAt χ b ∧ LLSPart1PrimitiveZeroMassUpperAt χ b

/-- Shared-witness core bounds imply the primitive upper bound consumed by Part 1. -/
theorem llsTheorem11S1PrimitiveUpperBounds_of_core (hcore : LLSPart1PrimitiveCoreBounds) :
    llsTheorem11S1PrimitiveUpperBounds := by
  intro q _ χ hq hχ hsmall
  obtain ⟨b, _, hweighted, hb⟩ := hcore q χ hq hχ hsmall
  have hy : (8 : ℝ) < llsTheorem11S1RadiusRoot q := eight_lt_llsTheorem11S1RadiusRoot hq
  have hlogX : 0 ≤ Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) :=
    Real.log_nonneg (by nlinarith only [hy])
  have hcoefficient :
    0 ≤ 2 * llsTheorem11S1RadiusRoot q + 2 + Real.log ((llsTheorem11S1RadiusRoot q) ^ 2) := by
    linarith only [hy, hlogX]
  rw [LLSPart1PrimitiveWeightedUpperAt] at hweighted
  rw [LLSPart1PrimitiveZeroMassUpperAt] at hb
  rw [llsTheorem11S1PrimitiveUpperBound]
  have hmul := mul_le_mul_of_nonneg_left hb hcoefficient
  exact hweighted.trans (by linarith only [hmul])

/-- The Riemann lower bound and shared-witness primitive core imply LLS Part 1. -/
theorem llsTheorem11S1Character_of_riemann_and_primitive_core (h21 : LLSRiemannWeightedLowerBound)
    (hcore : LLSPart1PrimitiveCoreBounds) : llsTheorem11S1Character :=
  llsTheorem11S1Character_of_riemann_and_primitive
    h21 (llsTheorem11S1PrimitiveUpperBounds_of_core hcore)

end PseudoPrime.LLS
