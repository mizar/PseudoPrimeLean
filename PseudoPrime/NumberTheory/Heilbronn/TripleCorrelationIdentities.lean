/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteTripleWeightExchange
public import PseudoPrime.NumberTheory.Heilbronn.LevelEnergyAmplification
public import PseudoPrime.NumberTheory.Heilbronn.ThirdEnergyMoments

/-! # Exact three-point correlation identities for Heilbronn amplification -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Three-point correlation C₃(a,b): the number of Heilbronn elements x
with x-a and x-b also in the subgroup. Its full squared mass is exactly
the third difference energy, supplying the amplification Cauchy factor. -/
noncomputable def heilbronnTripleCorrelation (p : ℕ) [Fact p.Prime] (a b : ZMod (p ^ 2)) : ℕ :=
  PseudoPrime.Analysis.finiteTripleCorrelation (heilbronnElements p) a b

/-- Remove the y=z diagonal from the actual weighted triple sum. The
remaining difference y-z is nonzero. This is the part controlled by mixed
third energy; the diagonal must be evaluated separately. -/
noncomputable def weightedHeilbronnOffDiagonal (p : ℕ) [Fact p.Prime] (g : ZMod (p ^ 2) → ℕ) :
    ℕ := by
  classical
    exact
    ∑ x : heilbronnElements p,
      ∑ y : heilbronnElements p,
        ∑ z : heilbronnElements p,
          if y = z then 0
          else
            g (x.val - y.val) * g (x.val - z.val) *
              Nat.card (cosetDifferenceAt p 0 0 (y.val - z.val))

/-- The squared mass of C₃ over all difference pairs is the existing
Heilbronn third energy. Specialize finite Gram duality and the exact
incidence representation. No asymptotic input or extra premise is used. -/
theorem heilbronnTripleCorrelation_square_sum {p : ℕ} [Fact p.Prime] :
    (∑ a : ZMod (p ^ 2), ∑ b : ZMod (p ^ 2), heilbronnTripleCorrelation p a b ^ 2) =
      heilbronnThirdEnergy p := by
  have h := PseudoPrime.Analysis.finite_triple_correlation_square_sum (heilbronnElements p)
  simpa only [← heilbronn_correlation_eq_finiteDifferenceCorrelation, heilbronnTripleCorrelation,
    heilbronnThirdEnergy] using h

/-- Rewrite the full amplified triple sum against C₃. The remaining edge
y-z becomes b-a under a=x-y and b=x-z. Preserve this sign explicitly for
later conversion by evenness of the difference correlation. -/
theorem weightedHeilbronnTriple_eq_correlation_sum {p : ℕ} [Fact p.Prime] (g : ZMod (p ^ 2) → ℕ) :
    weightedHeilbronnTriple p g =
      ∑ a : ZMod (p ^ 2),
        ∑ b : ZMod (p ^ 2),
          g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a)) *
            heilbronnTripleCorrelation p a b := by
  have h :=
    PseudoPrime.Analysis.finite_triple_weight_exchange (heilbronnElements p)
      (fun a b ↦ g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a)))
  simpa only [sub_sub_sub_cancel_left, weightedHeilbronnTriple, heilbronnTripleCorrelation] using h

/-- Rewrite the actual off-diagonal triple sum against C₃, retaining the
nonzero difference condition as a≠b. Apply the same coordinate exchange
and cancellation, so the diagonal exclusion is not an assumed identity. -/
theorem weightedHeilbronnOffDiagonal_eq_correlation_sum {p : ℕ} [Fact p.Prime]
    (g : ZMod (p ^ 2) → ℕ) :
    weightedHeilbronnOffDiagonal p g =
      ∑ a : ZMod (p ^ 2),
        ∑ b : ZMod (p ^ 2),
          (if a = b then 0 else g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a))) *
            heilbronnTripleCorrelation p a b := by
  classical
  have h :=
    PseudoPrime.Analysis.finite_triple_weight_exchange (heilbronnElements p)
      (fun a b ↦ if a = b then 0 else g a * g b * Nat.card (cosetDifferenceAt p 0 0 (b - a)))
  simpa only [sub_right_inj, Subtype.val_inj, sub_sub_sub_cancel_left, weightedHeilbronnOffDiagonal,
    heilbronnTripleCorrelation] using h

end PseudoPrime.NumberTheory.Heilbronn
