/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.CorrelationTail

/-! # Correlation tails at every height -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- For odd prime p and every natural height K, a parameter set on which the
normalized correlation is at least K satisfies the uniform cubic tail bound.
The low-height case follows from the mass bound, and the high-height case
uses the proved Stepanov tail. This supplies all layers of the third moment. -/
theorem card_mul_cube_le_of_normalizedCorrelation_ge_all {p K : ℕ} [Fact p.Prime] (hodd : Odd p)
    (S : Finset (ZMod p)) (hS : ∀ τ ∈ S, K ≤ normalizedCorrelation p τ) :
    S.card * K ^ 3 ≤ 262144 * p ^ 2 := by
  by_cases hK : 64 * p ≤ K ^ 2
  · exact card_mul_cube_le_of_normalizedCorrelation_ge hodd S hS hK
  have hm := Nat.mul_le_mul_right (K ^ 2) (card_mul_le_of_normalizedCorrelation_ge hodd S hS)
  have hk := Nat.mul_le_mul_left p (Nat.le_of_lt (Nat.lt_of_not_ge hK))
  calc
    _ = (S.card * K) * K ^ 2 := by ring
    _ ≤ p * K ^ 2 := hm
    _ ≤ p * (64 * p) := hk
    _ ≤ _ := by nlinarith only [Nat.zero_le (p ^ 2)]

end PseudoPrime.NumberTheory.Heilbronn
