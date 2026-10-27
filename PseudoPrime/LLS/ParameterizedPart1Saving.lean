/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedLogWeightedBounds

/-! # Full-level Part 1 bounds with an arbitrary reciprocal saving -/

@[expose] public section

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Input: a positive cutoff, a pointwise Riemann reciprocal lower bound, and prime triviality.
Claim: the original-level reciprocal sum retains the supplied loss and prime-factor cost.
Proof: combine exact support with nonnegativity before taking the maximum.
Role: accept any future cutoff-dependent reciprocal lower estimate. -/
theorem characterReciprocalWeightedSum_re_ge_of_reciprocal_lower {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) {x r : ℝ} (hx : 0 < x)
    (hR : Real.log x - r ≤ reciprocalWeightedMangoldtSum x)
    (ht : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    max 0 (Real.log x - r - primeFactorLogSum q) ≤ (characterReciprocalWeightedSum x χ).re := by
  apply max_le
  · exact characterReciprocalWeightedSum_re_nonneg_of_prime_trivial x χ hx ht
  · have h := characterReciprocalWeightedSum_re_lower_level_of_prime_trivial x χ hx ht
    linarith only [h, hR]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Input: GRH, nonprincipal primitive associate, cutoff at least 64, and a reciprocal saving A.
Claim: the raw zero-mass bound retains A without fixing a numerical reciprocal loss.
Proof: apply the primitive formula and absorb the exact level-change correction.
Role: separate analytic input improvements from scalar denominator estimates. -/
theorem primitiveZeroMass_le_fullLevel_raw_of_saving {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hN : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x A : ℝ} (hx : 64 ≤ x)
    (hR : A ≤ (characterReciprocalWeightedSum x χ).re) :
    (1 - 1 / Real.sqrt x) ^ 2 * |primitiveBRe χ.primitiveCharacter| ≤
      (1 / 2 : ℝ) * (1 - 1 / x) * (Real.log q - Real.log Real.pi) - A - 1 / 4 := by
  have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num only) hx
  have hraw :=
    primitiveReciprocalRaw hN hGRH χ.primitiveCharacter_isPrimitive hne
      (fun hi ↦ hne (inv_eq_one.mp hi)) hx
  have hqd : q / χ.conductor ≠ 0 := by
    rw [Nat.div_ne_zero_iff]
    exact ⟨χ.conductor_ne_zero, Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level⟩
  have habsorb := primitiveReciprocalConductorAbsorption x χ hx2 hqd
  rw [characterReciprocalWeightedSum_re_primitive_eq_add_levelChangeCorrection] at hraw
  linarith only [hraw, hR, habsorb]

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Input: the raw saving hypotheses, A nonnegative, log level above eight, and root above it.
Claim: the zero mass is at most log(q)/2+9/50-A.
Proof: use the generic scalar denominator absorption.
Role: carry arbitrary reciprocal savings into Part 1. -/
theorem primitiveZeroMass_le_fullLevel_of_saving {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    [NeZero χ.conductor] (hN : 2 ≤ χ.conductor) (hne : χ.primitiveCharacter ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x A : ℝ} (hx : 64 ≤ x)
    (hq : 8 < Real.log q) (hroot : Real.log q ≤ Real.sqrt x) (hA : 0 ≤ A)
    (hR : A ≤ (characterReciprocalWeightedSum x χ).re) :
    |primitiveBRe χ.primitiveCharacter| ≤ Real.log q / 2 + 9 / 50 - A := by
  have hraw := primitiveZeroMass_le_fullLevel_raw_of_saving χ hN hne hGRH hx hR
  have hpi : (57 / 50 : ℝ) ≤ Real.log Real.pi := by
    have hl := Analysis.log_two_mul_pi_gt
    rw [Real.log_mul (by norm_num only) Real.pi_ne_zero] at hl
    linarith only [hl, Real.log_two_lt_d9]
  have hs : (Real.sqrt x) ^ 2 = x := Real.sq_sqrt (le_trans (by norm_num only) hx)
  apply Analysis.reciprocalZeroMass_le_refined_bound hq hroot hA hpi
  simpa only [hs] using hraw

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
/-- Input: the generic full-level reciprocal saving hypotheses.
Claim: the logarithmic character sum obeys the Part 1 upper bound with that saving.
Proof: insert the zero-mass bound in the primitive logarithmic formula and absorb level change.
Role: make all later Part 1 root criteria independent of a fixed reciprocal loss. -/
theorem characterLogWeightedSum_re_le_fullLevel_of_saving {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hN : 2 ≤ χ.conductor)
    (hne : χ.primitiveCharacter ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x A : ℝ} (hx : 64 ≤ x) (hq : 8 < Real.log q) (hroot : Real.log q ≤ Real.sqrt x) (hA : 0 ≤ A)
    (hR : A ≤ (characterReciprocalWeightedSum x χ).re) :
    (characterLogWeightedSum x χ).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) * (Real.log q / 2 + 9 / 50 - A) +
          (1 / 2 : ℝ) * (Real.log q - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num only) hx
  have hraw :=
    primitiveGenericLogWeightedUpper hN hGRH χ.primitiveCharacter_isPrimitive hne
      (fun hi ↦ hne (inv_eq_one.mp hi)) hx
  have hm := primitiveZeroMass_le_fullLevel_of_saving χ hN hne hGRH hx hq hroot hA hR
  have hc : 0 ≤ 2 * Real.sqrt x + 2 + Real.log x :=
    add_nonneg (add_nonneg (mul_nonneg (by norm_num only) (Real.sqrt_nonneg x)) (by norm_num only))
      (Real.log_nonneg (le_trans (by norm_num only) hx))
  have hmul := mul_le_mul_of_nonneg_left hm hc
  have hqd : q / χ.conductor ≠ 0 := by
    rw [Nat.div_ne_zero_iff]
    exact ⟨χ.conductor_ne_zero, Nat.le_of_dvd (NeZero.pos q) χ.conductor_dvd_level⟩
  have habsorb := primitiveLogConductorAbsorption x χ hx2 hqd
  rw [characterLogWeightedSum_re_primitive_eq_add_levelChangeCorrection] at hraw
  nlinarith only [hraw, hmul, habsorb]

end PseudoPrime.LLS
