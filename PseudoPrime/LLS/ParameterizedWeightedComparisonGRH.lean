/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.WeightedComparisonGRH
public import PseudoPrime.LLS.ParameterizedLogWeightedBounds
public import PseudoPrime.LLS.ParameterizedReciprocalWeightedBounds

/-! # Weighted comparison with explicit parity main-error bounds -/

@[expose] public section

namespace PseudoPrime.LLS

/-- For a primitive nonprincipal character under GRH and X greater than one,
explicit bounds for both parity main errors construct the weighted comparison.
The reciprocal errors are at most -1/4; the logarithmic error e stays arbitrary.
This removes the fixed cutoff 64 from the analytic constructor. -/
theorem weightedComparisonCore_of_mainErrors {f : ℕ} [NeZero f] (hf2 : 2 ≤ f)
    {ψ : DirichletCharacter ℂ f} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : ψ.IsPrimitive) (hne : ψ ≠ 1) (hinv : ψ⁻¹ ≠ 1) {X dS dR e : ℝ} (hX : 1 < X)
    (hSo : Analysis.primitiveLogOddMainError X ≤ e) (hSe : Analysis.primitiveLogEvenMainError X ≤ e)
    (hRo : Analysis.primitiveReciprocalOddMainError X ≤ -(1 / 4 : ℝ))
    (hRe : Analysis.primitiveReciprocalEvenMainError X ≤ -(1 / 4 : ℝ))
    (hdS : weightedLogDefect ψ X ≤ dS) (hdR : weightedReciprocalDefect ψ X ≤ dR) :
    LLSWeightedComparisonCore ψ X |AnalyticNumberTheory.DirichletLFunction.primitiveBRe ψ| dS dR e
    where
  logDefect_le := hdS
  reciprocalDefect_le := hdR
  zeroMass_le := by
    have h := primitiveReciprocalRaw_of_mainErrors hf2 hGRH hprimitive hne hinv hX hRo hRe
    rw [Real.log_div (by exact_mod_cast NeZero.ne f) Real.pi_ne_zero]
    linarith only [h]
  logWeighted_le := by
    have h := primitiveLogWeightedUpper_of_mainErrors hf2 hGRH hprimitive hne hinv hX hSo hSe
    rw [Real.log_div (by exact_mod_cast NeZero.ne f) Real.pi_ne_zero]
    exact h

/-- Under GRH and prime triviality through X greater than one, explicit
parity-error bounds give a comparison core for the primitive inducing character.
Transfer triviality, set both defects to zero and apply the parameterized constructor.
The numerical cutoff is determined solely by the supplied main-error estimates. -/
theorem weightedComparisonCore_of_trivialBelow_of_mainErrors {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {X e : ℝ} (hX : 1 < X)
    (hSo : Analysis.primitiveLogOddMainError X ≤ e) (hSe : Analysis.primitiveLogEvenMainError X ≤ e)
    (hRo : Analysis.primitiveReciprocalOddMainError X ≤ -(1 / 4 : ℝ))
    (hRe : Analysis.primitiveReciprocalEvenMainError X ≤ -(1 / 4 : ℝ))
    (ht : LLSCharacterTrivialBelow χ X) :
    LLSWeightedComparisonCore χ.primitiveCharacter X
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter| 0 0 e := by
  have hp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hf : 2 ≤ χ.conductor := by
    have h0 := NeZero.pos χ.conductor
    have h1 := AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hp
    exact Nat.succ_le_iff.mpr (Nat.lt_of_le_of_ne h0 (Ne.symm h1))
  have htrivial := characterTrivialBelow_primitiveCharacter ht
  have hx : 0 < X := zero_lt_one.trans hX
  exact
    weightedComparisonCore_of_mainErrors hf hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hp (inv_ne_one.mpr hp) hX hSo hSe hRo
      hRe (weightedLogDefect_eq_zero_of_trivialBelow hx htrivial).le
      (weightedReciprocalDefect_eq_zero_of_trivialBelow hx htrivial).le

end PseudoPrime.LLS
