/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PrimitiveReciprocalWeightedBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ReciprocalTrivialSupport
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.ReciprocalLevelChange
public import PseudoPrime.Analysis.ReciprocalZeroMassBounds
public import PseudoPrime.Analysis.NumericalLogBounds

/-! # Refined reciprocal zero-mass bounds at arbitrary cutoffs -/

@[expose] public section

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, a nonprincipal primitive associate of conductor at least two,
and prime triviality up to x≥64, its zero mass satisfies the full-level raw bound
with saving max(0,log(x)−32873/20800−primeFactorLogSum(q)).
Combine the primitive reciprocal formula with the refined original-level lower bound.
The signed level-change correction is absorbed into log(q), without a quotient loss.
The freely chosen cutoff permits the improved Part 1 radius. -/
theorem primitiveZeroMass_le_refined_fullLevel_raw {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hN : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2 : ℝ) * (1 - 1 / x) * (Real.log q - Real.log Real.pi) -
        max 0 (Real.log x - (32873 / 20800 : ℝ) - primeFactorLogSum q) -
        1 / 4 := by
  have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num only) hx
  have hraw :=
    primitiveReciprocalRaw hN hGRH χ.primitiveCharacter_isPrimitive hne
      (fun hi ↦ hne (inv_eq_one.mp hi)) hx
  have hlower :=
    characterReciprocalWeightedSum_re_ge_refined_lower_bound x χ hx2 hGRH.riemann htrivial
  have hqd : q / χ.conductor ≠ 0 := by
    rw [Nat.div_ne_zero_iff]
    exact ⟨χ.conductor_ne_zero, Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level⟩
  have habsorb := primitiveReciprocalConductorAbsorption x χ hx2 hqd
  rw [characterReciprocalWeightedSum_re_primitive_eq_add_levelChangeCorrection] at hraw
  linarith only [hraw, hlower, habsorb]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH and prime triviality up to x≥64, assume log(q)>8 and sqrt(x)≥log(q).
The primitive zero mass is at most log(q)/2+9/50 minus the refined reciprocal saving.
Absorb the denominator in the full-level raw bound using log(pi)≥57/50.
This supplies the improved Part 1 zero-mass estimate at the actual no-witness cutoff. -/
theorem primitiveZeroMass_le_refined_fullLevel {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hN : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 64 ≤ x)
    (hq : 8 < Real.log q) (hroot : Real.log q ≤ Real.sqrt x)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    |primitiveBRe χ.primitiveCharacter| ≤
      Real.log q / 2 + 9 / 50 - max 0 (Real.log x - (32873 / 20800 : ℝ) - primeFactorLogSum q) := by
  have hraw := primitiveZeroMass_le_refined_fullLevel_raw χ hN hne hGRH hx htrivial
  have hpi : (57 / 50 : ℝ) ≤ Real.log Real.pi := by
    have hl := Analysis.log_two_mul_pi_gt
    rw [Real.log_mul (by norm_num only) Real.pi_ne_zero] at hl
    linarith only [hl, Real.log_two_lt_d9]
  have hs : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_trans (by norm_num only) hx)
  apply Analysis.reciprocalZeroMass_le_refined_bound hq hroot (le_max_left _ _) hpi
  simpa only [hs] using hraw

end PseudoPrime.LLS
