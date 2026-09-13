/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.LLS.WeightedComparison
import PseudoPrime.LLS.Theorem11S2SmallPrimeExclusion
import PseudoPrime.LLS.PrimitiveLogWeightedBounds
import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds

/-!
# Constructing the common weighted-comparison core from GRH

The primitive logarithmic and reciprocal estimates supply the common core's analytic bounds.
Both estimates are independent of the quadratic refinements and concrete witness applications.
The constructor belongs to the LLS layer and is shared by S2 and the extension consumers.
-/

namespace PseudoPrime.LLS

/--
The generic branch of the common core: under GRH, for any nontrivial primitive character `ψ` with
`ψ⁻¹ ≠ 1` and any cutoff `X ≥ 64`, the witness `b := |primitiveBRe ψ|` and `eS := -11/4` satisfy
`C3`-`C4`, using the already-proved generic theorems
`PseudoPrime.LLS.primitiveReciprocalRaw_of_grh` and
`PseudoPrime.LLS.primitiveGenericLogWeightedUpper_of_grh_generic`. No quadraticity
hypothesis is used. `C1`/`C2` still need the log/reciprocal defect bounds `dS`, `dR` supplied
separately (they depend on how `ψ` was constructed, not on the generic contour estimate).
-/
theorem weightedComparisonCore_generic_of_grh {f : ℕ} [NeZero f] (hf2 : 2 ≤ f)
    {ψ : DirichletCharacter ℂ f}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hprimitive : ψ.IsPrimitive) (hne : ψ ≠ 1) (hinv : ψ⁻¹ ≠ 1) {X dS dR : ℝ} (hX : 64 ≤ X)
    (hdS : weightedLogDefect ψ X ≤ dS) (hdR : weightedReciprocalDefect ψ X ≤ dR) :
    LLSWeightedComparisonCore ψ X
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe ψ| dS dR (-(11 / 4))
    where
  logDefect_le := hdS
  reciprocalDefect_le := hdR
  zeroMass_le := by
    have h :=
      primitiveReciprocalRaw_of_grh hf2 hGRH hprimitive hne hinv hX
    rw [Real.log_div (by exact_mod_cast NeZero.ne f) Real.pi_ne_zero]
    linarith
  logWeighted_le := by
    have h :=
      primitiveGenericLogWeightedUpper_of_grh_generic hf2 hGRH hprimitive
        hne hinv hX
    rw [Real.log_div (by exact_mod_cast NeZero.ne f) Real.pi_ne_zero]
    linarith

/-- The paper branch constructs the common core for the primitive inducing character.
The original character need not be primitive: its strict-cutoff triviality transfers,
forcing both primitive defects to vanish. All analytic fields follow from GRH. -/
theorem weightedComparisonCore_of_trivialBelow {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {X : ℝ} (hX : 64 ≤ X) (htrivial : LLSCharacterTrivialBelow χ X) :
    LLSWeightedComparisonCore χ.primitiveCharacter X
      |AnalyticNumberTheory.DirichletLFunction.primitiveBRe χ.primitiveCharacter|
      0 0 (-(11 / 4)) := by
  have hp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hf : 2 ≤ χ.conductor := by
    have h0 := NeZero.pos χ.conductor
    have h1 := AnalyticNumberTheory.DirichletLFunction.dirichletCharacter_level_ne_one_of_ne_one hp
    omega
  have ht := characterTrivialBelow_primitiveCharacter htrivial
  have hx : 0 < X := lt_of_lt_of_le (by norm_num only) hX
  exact weightedComparisonCore_generic_of_grh hf hGRH
    (DirichletCharacter.primitiveCharacter_isPrimitive χ) hp
    (inv_ne_one.mpr hp) hX (weightedLogDefect_eq_zero_of_trivialBelow hx ht).le
    (weightedReciprocalDefect_eq_zero_of_trivialBelow hx ht).le

end PseudoPrime.LLS
