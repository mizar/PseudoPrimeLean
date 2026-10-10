/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.WeightedComparison
public import PseudoPrime.LLS.Theorem11S2SmallPrimeExclusion
public import PseudoPrime.LLS.PrimitiveLogWeightedBounds
public import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds

/-!
# Weighted character-sum comparison under GRH

For a nontrivial primitive character and cutoff X ≥ 64, the logarithmic and reciprocal
estimates under GRH construct LLSWeightedComparisonCore with b equal to the absolute real part
of the primitive B constant and logarithmic error -11/4. The defect bounds are separate inputs.

For a nontrivial character that is trivial on primes below X, this construction applies to
its primitive inducing character: triviality transfers to that character and makes both
weighted defects zero. This supplies the comparison core used in the Part 2 proof.
-/

@[expose] public section

namespace PseudoPrime.LLS

/-- Under GRH, let ψ be a primitive character modulo f ≥ 2, with ψ ≠ 1 and ψ⁻¹ ≠ 1.
For X ≥ 64 and supplied defect bounds dS and dR, construct the comparison core with
b = |primitiveBRe ψ| and logarithmic error -11/4. The logarithmic and reciprocal estimates
supply the two analytic fields after rewriting log(f/π); the defect fields use the inputs.
This constructor provides a common analytic comparison for applications with different
cutoffs and defect bounds. -/
theorem weightedComparisonCore_generic_of_grh {f : ℕ} [NeZero f] (hf2 : 2 ≤ f)
    {ψ : DirichletCharacter ℂ f} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : ψ.IsPrimitive) (hne : ψ ≠ 1) (hinv : ψ⁻¹ ≠ 1) {X dS dR : ℝ} (hX : 64 ≤ X)
    (hdS : weightedLogDefect ψ X ≤ dS) (hdR : weightedReciprocalDefect ψ X ≤ dR) :
    LLSWeightedComparisonCore ψ X |AnalyticNumberTheory.DirichletLFunction.primitiveBRe ψ| dS dR
      (-(11 / 4))
    where
  logDefect_le := hdS
  reciprocalDefect_le := hdR
  zeroMass_le := by
    have h := primitiveReciprocalRaw hf2 hGRH hprimitive hne hinv hX
    rw [Real.log_div (by exact_mod_cast NeZero.ne f) Real.pi_ne_zero]
    linarith only [h]
  logWeighted_le := by
    have h := primitiveGenericLogWeightedUpper hf2 hGRH hprimitive hne hinv hX
    rw [Real.log_div (by exact_mod_cast NeZero.ne f) Real.pi_ne_zero]
    exact h

/-- Under GRH, a nontrivial character χ of nonzero conductor that is trivial on primes
below X ≥ 64 yields a comparison core for its primitive inducing character, with both defect
bounds zero, b = |primitiveBRe χ.primitiveCharacter|, and logarithmic error -11/4.
The proof establishes nontriviality and conductor at least two, transfers the prime condition,
and uses the resulting zero defects in the generic constructor. This supplies the analytic
comparison for the Part 2 counterexample condition without assuming χ itself is primitive. -/
theorem weightedComparisonCore_of_trivialBelow {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X : ℝ} (hX : 64 ≤ X)
    (htrivial : LLSCharacterTrivialBelow χ X) :
    LLSWeightedComparisonCore χ.primitiveCharacter X
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| 0 0
      (-(11 / 4)) := by
  have hp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hf : 2 ≤ χ.conductor := by
    have h0 := NeZero.pos χ.conductor
    have h1 := AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hp
    exact Nat.succ_le_iff.mpr (Nat.lt_of_le_of_ne h0 (Ne.symm h1))
  have ht := characterTrivialBelow_primitiveCharacter htrivial
  have hx : 0 < X := lt_of_lt_of_le (by norm_num only) hX
  exact
    weightedComparisonCore_generic_of_grh hf hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hp (inv_ne_one.mpr hp) hX
      (weightedLogDefect_eq_zero_of_trivialBelow hx ht).le
      (weightedReciprocalDefect_eq_zero_of_trivialBelow hx ht).le

end PseudoPrime.LLS
