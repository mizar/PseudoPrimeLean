/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PseudoSquare.Bounds.QNeOneLogSq

/-! # Common logarithmic scales for quadratic witness maxima

This module lifts bounds valid at a common real logarithmic scale to natural endpoints.
It belongs to the quadratic-witness API: the conclusions are its negative and non-one
witness maxima. Kernel choices, entrance certificates and selected numerical coefficients
remain in the modules that supply the common-scale witness estimates.
-/

@[expose] public section

namespace PseudoPrime.PseudoSquare

/-- A squared common-scale candidate for a natural endpoint.
Input: a coefficient, an entrance scale and an endpoint, without validity assumptions.
Output: the coefficient times the square of the larger entrance or endpoint logarithm.
Role: bound all earlier inputs directly, without a separate low-input history term. -/
noncomputable def logScaleBound (c E : ℝ) (B : ℕ) : ℝ :=
  c * max E (Real.log B) ^ 2

/-- A common-scale candidate with nonnegative coefficient is nonnegative.
Input: a nonnegative coefficient, arbitrary entrance and endpoint.
Claim: the candidate also covers an empty witness maximum.
Proof: a nonnegative multiple of a square. Role: finite-supremum lifting. -/
theorem logScaleBound_nonneg {c : ℝ} (hc : 0 ≤ c) (E : ℝ) (B : ℕ) : 0 ≤ logScaleBound c E B :=
  mul_nonneg hc (sq_nonneg _)

/-- Negative witness estimates at every common scale bound the full endpoint maximum.
Input: a nonnegative coefficient and a least-witness estimate whenever the logarithm
is below a valid real scale. Claim: every natural endpoint, including zero, is bounded.
Proof: use the larger entrance or endpoint logarithm for each admissible input.
Role: share cumulative lifting among independent analytic common-scale witnesses. -/
theorem QNegOne_le_logScaleBound {c E : ℝ} (hc : 0 ≤ c)
    (hscale :
      ∀ {n : ℕ},
        (hn : Odd n) →
          (hns : ¬IsSquare n) →
          ∀ {L : ℝ},
            E ≤ L →
              Real.log n ≤ L →
              ∀ hw : (NumberTheory.primeNegOneWitnessSet n).Nonempty,
                (NumberTheory.primeNegOneWitness n hw : ℝ) ≤ c * L ^ 2)
    (B : ℕ) : (QNegOne B : ℝ) ≤ logScaleBound c E B :=
  QNegOne_cast_le_of_forall (logScaleBound_nonneg hc E B) fun _n hn ↦
    hscale (NumberTheory.mem_admissibleFinset_iff.mp hn).odd
      (NumberTheory.mem_admissibleFinset_iff.mp hn).not_isSquare (le_max_left _ _)
      ((Real.log_le_log (Nat.cast_pos.mpr (NumberTheory.mem_admissibleFinset_iff.mp hn).pos)
            (Nat.cast_le.mpr (NumberTheory.mem_admissibleFinset_iff.mp hn).le)).trans
        (le_max_right _ _))
      _

/-- Non-one witness estimates at every common scale bound the full endpoint maximum.
Input: a nonnegative coefficient and a least non-one estimate at any covering scale.
Claim: the resulting natural-endpoint maximum is bounded, with empty domains included.
Proof: lift each estimate at the common maximum scale through the finite supremum.
Role: preserve the separate non-one candidate rather than use a negative-only bound. -/
theorem QNeOne_le_logScaleBound {c E : ℝ} (hc : 0 ≤ c)
    (hscale :
      ∀ {n : ℕ},
        (hn : Odd n) →
          (hns : ¬IsSquare n) →
          ∀ {L : ℝ},
            E ≤ L →
              Real.log n ≤ L →
              ∀ hw : (NumberTheory.primeNeOneWitnessSet n).Nonempty,
                (NumberTheory.primeNeOneWitness n hw : ℝ) ≤ c * L ^ 2)
    (B : ℕ) : (QNeOne B : ℝ) ≤ logScaleBound c E B :=
  QNeOne_cast_le_of_forall (logScaleBound_nonneg hc E B) fun _n hn ↦
    hscale (NumberTheory.mem_admissibleFinset_iff.mp hn).odd
      (NumberTheory.mem_admissibleFinset_iff.mp hn).not_isSquare (le_max_left _ _)
      ((Real.log_le_log (Nat.cast_pos.mpr (NumberTheory.mem_admissibleFinset_iff.mp hn).pos)
            (Nat.cast_le.mpr (NumberTheory.mem_admissibleFinset_iff.mp hn).le)).trans
        (le_max_right _ _))
      _

end PseudoPrime.PseudoSquare
