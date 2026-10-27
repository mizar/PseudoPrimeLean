/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.InvariantCorrelationRows

/-! # Amplification into actual weighted Heilbronn triple correlations -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Every even, multiplicatively invariant natural weight satisfies B²E≤t³Q
on the Heilbronn set, with its actual pair sum B and triple correlation Q.
Derive constant row mass by subgroup scaling, then apply finite incidence
amplification. The statement has no auxiliary matrix or regularity premise. -/
theorem invariant_weight_energy_amplification {p : ℕ} [Fact p.Prime] (g : ZMod (p ^ 2) → ℕ)
    (he : ∀ a, g (-a) = g a) (hg : ∀ γ ∈ shiftedTeichCoset p 0, ∀ a, g (γ * a) = g a) :
    (∑ x : heilbronnElements p, ∑ y : heilbronnElements p, g (x.val - y.val)) ^ 2 *
        heilbronnEnergy p ≤
      (p - 1) ^ 3 *
        ∑ x : heilbronnElements p,
          ∑ y : heilbronnElements p,
            ∑ z : heilbronnElements p,
              g (x.val - y.val) * g (x.val - z.val) *
                Nat.card (cosetDifferenceAt p 0 0 (y.val - z.val)) := by
  have h :=
    PseudoPrime.Analysis.finite_correlation_energy_amplification (heilbronnElements p) g
      (∑ y : heilbronnElements p, g (1 - y.val)) he (invariant_weight_row_sum g hg)
  simpa only [← heilbronn_correlation_eq_finiteDifferenceCorrelation, card_heilbronnElements,
    heilbronnEnergy] using h

end PseudoPrime.NumberTheory.Heilbronn
