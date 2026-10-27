/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteTripleCorrelations

/-! # Squared weights supported on finite off-diagonal pair sets -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- A weight supported on S and bounded by Δ costs at most Δ⁴ in the
squared mass of an off-diagonal pair kernel. Compare each ambient summand
with its supported indicator bound and sum. The kernel h is arbitrary,
so this separates support bookkeeping from the correlation estimates. -/
theorem finite_supported_off_diagonal_square_le {G : Type*} [Fintype G] [DecidableEq G]
    (S : Finset G) (g : G → ℕ) (h : G → G → ℕ) (Δ : ℕ) (hz : ∀ a, a ∉ S → g a = 0)
    (hg : ∀ a, g a ≤ Δ) :
    (∑ a : G, ∑ b : G, (if a = b then 0 else g a * g b * h a b) ^ 2) ≤
      Δ ^ 4 * ∑ a ∈ S, ∑ b ∈ S, if a = b then 0 else h a b ^ 2 := by
  have hp (a b : G) :
    (if a = b then 0 else g a * g b * h a b) ^ 2 ≤
      if a ∈ S then if b ∈ S then Δ ^ 4 * (if a = b then 0 else h a b ^ 2) else 0 else 0 := by
    by_cases ha : a ∈ S
    · by_cases hb : b ∈ S
      · by_cases hab : a = b
        · simpa only [hb, hab, ite_true, mul_zero, zero_pow (by decide : 2 ≠ 0)] using Nat.zero_le 0
        · simp only [ha, hb, hab, ite_true, ite_false]
          calc
            _ = (g a * g b) ^ 2 * h a b ^ 2 := mul_pow _ _ 2
            _ ≤ (Δ * Δ) ^ 2 * h a b ^ 2 :=
              Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.mul_le_mul (hg a) (hg b)) 2)
            _ = _ := by ring
      · simpa only [hb, ite_false, hz b hb, mul_zero, zero_mul, ite_self,
          zero_pow (by decide : 2 ≠ 0), ha] using Nat.zero_le 0
    · simpa only [ha, ite_false, hz a ha, zero_mul, ite_self, zero_pow (by decide : 2 ≠ 0)] using
        Nat.zero_le 0
  have hs :=
    Finset.sum_le_sum
      (fun a (_ : a ∈ (Finset.univ : Finset G)) ↦
        Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset G)) ↦ hp a b))
  simpa only [Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_mem, Finset.univ_inter,
    ← Finset.mul_sum] using hs

end PseudoPrime.Analysis
