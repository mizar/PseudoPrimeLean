/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.GlobalCorrelationTail
public import PseudoPrime.NumberTheory.Heilbronn.CorrelationEnergyMoments

/-! # Cubic tail counts on all unit differences -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Unit differences with correlation at least K, as a finite subset of the
unit subtype. This retains the p-1 copies of each normalized correlation
without enumerating them in a certificate. -/
noncomputable def unitCorrelationThreshold (p : ℕ) [Fact p.Prime] (K : ℕ) :
    Finset { c : ZMod (p ^ 2) // IsUnit c } := by
  classical exact Finset.univ.filter (fun c ↦ K ≤ Nat.card (cosetDifferenceAt p 0 0 c.val))

/-- Any natural-valued function of the unit correlations sums to p-1 times
its normalized sum. Parametrize units by a principal shift and a nonzero
residue and use scaling invariance. This covers all moments and tail counts. -/
theorem sum_unit_correlation_function {p : ℕ} [Fact p.Prime] (F : ℕ → ℕ) :
    (∑ c : { c : ZMod (p ^ 2) // IsUnit c }, F (Nat.card (cosetDifferenceAt p 0 0 c.val))) =
      (p - 1) * ∑ τ : ZMod p, F (normalizedCorrelation p τ) := by
  classical
  have he :=
    Fintype.sum_bijective (unitParameterMap (p := p)) unitParameterMap_bijective
      (fun z : ZMod p × { g : ZMod p // g ≠ 0 } ↦ F (normalizedCorrelation p z.1))
      (fun c : { c : ZMod (p ^ 2) // IsUnit c } ↦ F (Nat.card (cosetDifferenceAt p 0 0 c.val)))
      (fun z ↦ congrArg F (card_cosetDifferenceAt_mul_teichLift 0 0 _ z.2.val z.2.property).symm)
  rw [← he, Fintype.sum_prod_type]
  have hc : Fintype.card { g : ZMod p // g ≠ 0 } = p - 1 := by
    rw [Fintype.card_subtype_compl (fun g : ZMod p ↦ g = 0), ZMod.card, Fintype.card_subtype_eq]
  simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Nat.cast_id, hc]
  rw [Finset.mul_sum]

/-- The number of unit correlations above K is p-1 times the normalized
threshold count. Apply the function-sum identity to a zero-one indicator
and identify the finite filter cardinalities. -/
theorem card_unitCorrelationThreshold {p K : ℕ} [Fact p.Prime] :
    (unitCorrelationThreshold p K).card =
      (p - 1) * (Finset.univ.filter (fun τ : ZMod p ↦ K ≤ normalizedCorrelation p τ)).card := by
  classical
  have h := sum_unit_correlation_function (p := p) (fun v ↦ if K ≤ v then 1 else 0)
  simp only [Finset.sum_boole] at h
  exact h

/-- Every finite unit set whose correlations are at least K has cardinality
at most the full unit threshold count. Embed each residue into the unit
subtype and compare its image with the threshold. This permits arbitrary
correlation bands rather than only complete thresholds. -/
theorem card_le_unitCorrelationThreshold {p K : ℕ} [Fact p.Prime] (S : Finset (ZMod (p ^ 2)))
    (hS : ∀ x ∈ S, IsUnit x) (hK : ∀ x ∈ S, K ≤ Nat.card (cosetDifferenceAt p 0 0 x)) :
    S.card ≤ (unitCorrelationThreshold p K).card := by
  classical
  have hs : S ⊆ (unitCorrelationThreshold p K).image Subtype.val := by
    intro x hx
    apply Finset.mem_image.mpr
    refine ⟨⟨x, hS x hx⟩, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hK x hx⟩
  have hc := Finset.card_le_card hs
  rw [Finset.card_image_of_injective _ Subtype.val_injective] at hc
  exact hc

/-- For odd prime p, a unit set S whose correlations are at least K satisfies
card(S)K³≤262144p³ at every height. Use the exact normalized threshold count
and the all-height cubic tail, retaining the p-1 multiplicity until the last
comparison. This is the cubic band-size input to mixed third energy. -/
theorem card_mul_cube_le_of_unit_correlation_ge {p K : ℕ} [Fact p.Prime] (hodd : Odd p)
    (S : Finset (ZMod (p ^ 2))) (hS : ∀ x ∈ S, IsUnit x)
    (hK : ∀ x ∈ S, K ≤ Nat.card (cosetDifferenceAt p 0 0 x)) : S.card * K ^ 3 ≤ 262144 * p ^ 3 := by
  have hcard := card_le_unitCorrelationThreshold S hS hK
  rw [card_unitCorrelationThreshold] at hcard
  have ht :=
    card_mul_cube_le_of_normalizedCorrelation_ge_all hodd
      (Finset.univ.filter (fun τ : ZMod p ↦ K ≤ normalizedCorrelation p τ))
      (fun τ hτ ↦ (Finset.mem_filter.mp hτ).2)
  calc
    _ ≤
        ((p - 1) * (Finset.univ.filter (fun τ : ZMod p ↦ K ≤ normalizedCorrelation p τ)).card) *
          K ^ 3 :=
      Nat.mul_le_mul_right _ hcard
    _ =
        (p - 1) *
          ((Finset.univ.filter (fun τ : ZMod p ↦ K ≤ normalizedCorrelation p τ)).card * K ^ 3) :=
      by ring
    _ ≤ (p - 1) * (262144 * p ^ 2) := Nat.mul_le_mul_left _ ht
    _ ≤ p * (262144 * p ^ 2) := Nat.mul_le_mul_right _ (Nat.sub_le p 1)
    _ = _ := by ring

/-- Any finite difference set with correlation at least K has cardinality
 times K² bounded by the additive energy. Compare its squared correlations
with the full defining energy sum. This complements the cubic tail count. -/
theorem card_mul_sq_le_of_correlation_ge {p K : ℕ} [Fact p.Prime] (S : Finset (ZMod (p ^ 2)))
    (hK : ∀ x ∈ S, K ≤ Nat.card (cosetDifferenceAt p 0 0 x)) :
    S.card * K ^ 2 ≤ heilbronnEnergy p := by
  calc
    _ = ∑ _x ∈ S, K ^ 2 := (Finset.sum_const_nat (fun _ _ ↦ rfl)).symm
    _ ≤ ∑ x ∈ S, Nat.card (cosetDifferenceAt p 0 0 x) ^ 2 :=
      Finset.sum_le_sum (fun x hx ↦ Nat.pow_le_pow_left (hK x hx) 2)
    _ ≤ _ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ S) (fun _ _ _ ↦ Nat.zero_le _)

end PseudoPrime.NumberTheory.Heilbronn
