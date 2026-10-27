/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.RefinedReciprocalZeroMass
public import PseudoPrime.LLS.PrimitiveLogWeightedBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.LogLevelChange

/-! # Refined full-level logarithmic weighted-sum bounds -/

@[expose] public section

namespace PseudoPrime.LLS

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.AnalyticNumberTheory.DirichletLFunction in
/-- Under GRH, prime triviality up to x≥64, log(q)>8, and sqrt(x)≥log(q),
the original-level logarithmic sum has a full-level upper bound with zero-mass
constant 9/50 and reciprocal saving max(0,log(x)−32873/20800−primeFactorLogSum(q)).
Insert the refined zero-mass bound into the primitive logarithmic formula and
absorb the signed level-change correction into log(q).
This is the analytic upper input for the improved Part 1 comparison. -/
theorem characterLogWeightedSum_re_le_refined_fullLevel {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) [NeZero χ.conductor] (hN : 2 ≤ χ.conductor)
    (hne : χ.primitiveCharacter ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 64 ≤ x) (hq : 8 < Real.log q) (hroot : Real.log q ≤ Real.sqrt x)
    (htrivial : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → χ p = 1) :
    (characterLogWeightedSum x χ).re ≤
      (2 * Real.sqrt x + 2 + Real.log x) *
            (Real.log q / 2 + 9 / 50 -
              max 0 (Real.log x - (32873 / 20800 : ℝ) - primeFactorLogSum q)) +
          (1 / 2 : ℝ) * (Real.log q - Real.log Real.pi) * Real.log x -
        11 / 4 := by
  have hx2 : (2 : ℝ) ≤ x := le_trans (by norm_num only) hx
  have hraw :=
    primitiveGenericLogWeightedUpper hN hGRH χ.primitiveCharacter_isPrimitive hne
      (fun hi ↦ hne (inv_eq_one.mp hi)) hx
  have hm := primitiveZeroMass_le_refined_fullLevel χ hN hne hGRH hx hq hroot htrivial
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
