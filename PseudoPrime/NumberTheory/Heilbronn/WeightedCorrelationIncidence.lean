/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.WeightedDifferenceIncidence
public import PseudoPrime.NumberTheory.Heilbronn.InvariantDifferenceIncidence

/-! # Weighted incidences on Heilbronn correlation levels -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- A weighted incidence on a nonzero correlation level has the invariant
Fourier bound with its exact weighted main and square-mass terms.

Input: A prime modulus `p`, a natural-number residue weight `f`, and a level
predicate excluding correlation zero.
Claim: The incidence is at most `card(Ω) * mass(f)^2 / p^2` plus the level
Fourier envelope times `sum(f^2)`.
Proof: Apply the generic weighted Parseval incidence bound to the proved
invariance and unit support of the correlation level.
Role: Supplies the per-band estimate used in the weighted dyadic argument. -/
theorem weightedResidueDifferenceIncidence_le_correlation_level {p : ℕ} [Fact p.Prime]
    (f : ZMod (p ^ 2) → ℕ) (P : ℕ → Prop) (hP : ¬P 0) :
    weightedResidueDifferenceIncidence f (heilbronnCorrelationLevel p P) ≤
      ((heilbronnCorrelationLevel p P).card : ℝ) * (weightedResidueMass f : ℝ) ^ 2 / (p : ℝ) ^ 2 +
        invariantFourierEnvelope p (heilbronnCorrelationLevel p P) *
          ∑ x : ZMod (p ^ 2), (f x : ℝ) ^ 2 := by
  have h :=
    weightedResidueDifferenceIncidence_le_of_fourier_bound f (heilbronnCorrelationLevel p P)
      (invariantFourierEnvelope_nonneg _)
      (fun l hl ↦
        norm_residueCharacterSum_le_invariantFourierEnvelope _
          (heilbronnCorrelationLevel_invariant P) (heilbronnCorrelationLevel_units P hP) hl)
  simpa only [Nat.cast_pow] using h

end PseudoPrime.NumberTheory.Heilbronn
