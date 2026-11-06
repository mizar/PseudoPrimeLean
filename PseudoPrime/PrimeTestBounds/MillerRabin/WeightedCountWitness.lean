/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeCount
public import PseudoPrime.PrimeTestBounds.MillerRabin.WeightedPrimeTable
public import PseudoPrime.PrimeTestBounds.MillerRabin.PrimeProductFamilyTransfer

/-! # Weighted recurrence counts yield MR witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A duplicate-free prime list with positive integer weights supplies an MR
rejecting prime when its weighted recurrence count exceeds the local subgroup
cardinality and its budget is below the logarithm of the modulus. The count's
semantic correctness supplies the complete family of repeated prime products. -/
theorem exists_prime_reject_of_weighted_count {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (xs : List ℕ) (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hq : 0 < q) (hnodup : xs.Nodup)
    (hp : ∀ p ∈ xs, Nat.Prime p) (hbound : ∀ p ∈ xs, p ≤ B) (hwpos : ∀ p ∈ xs, 0 < w p)
    (hw : ∀ p ∈ xs, Real.log p ≤ (w p : ℝ) / d) (hbudget : (budget : ℝ) / d < Real.log q)
    (hcount : Nat.card H < weightedPrimeCount w xs budget)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  apply
    exists_prime_reject_of_weight_budget H xs.toFinset B budget w d hd hq
      (fun p hp' ↦ hp p (List.mem_toFinset.mp hp'))
      (fun p hp' ↦ hbound p (List.mem_toFinset.mp hp'))
      (fun p hp' ↦ hwpos p (List.mem_toFinset.mp hp')) (fun p hp' ↦ hw p (List.mem_toFinset.mp hp'))
      hbudget
  · exact (weightedPrimeCount_eq_card w budget xs hnodup hwpos) ▸ hcount
  · exact hpass

/-- A numerical count computed from the list of weights can be transferred to
any duplicate-free prime list carrying those weights. Equal weights remain
separate labels, so grouped prime supplies can use the same certificate. -/
theorem exists_prime_reject_of_weight_list {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (xs weights : List ℕ) (B budget : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hq : 0 < q)
    (hnodup : xs.Nodup) (hp : ∀ p ∈ xs, Nat.Prime p) (hbound : ∀ p ∈ xs, p ≤ B)
    (hwpos : ∀ p ∈ xs, 0 < w p) (hw : ∀ p ∈ xs, Real.log p ≤ (w p : ℝ) / d)
    (he : xs.map w = weights) (hbudget : (budget : ℝ) / d < Real.log q)
    (hcount : Nat.card H < weightedPrimeCount id weights budget)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_reject_of_weighted_count H xs B budget w d hd hq hnodup hp hbound hwpos hw hbudget
    ((congrArg (fun ys ↦ weightedPrimeCount id ys budget) he).symm.trans
        (weightedPrimeCount_map_weights w budget xs).symm ▸
      hcount)
    hpass

/-- A checked finite table can supply the weighted count needed for an MR
rejecting prime. Its first row is used at the requested budget after the table
checker establishes equality with the mathematical recurrence. -/
theorem exists_prime_reject_of_weight_table {n q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (xs weights : List ℕ) (B budget N : ℕ) (w : ℕ → ℕ) (d : ℝ) (hd : 0 < d) (hq : 0 < q)
    (hnodup : xs.Nodup) (hp : ∀ p ∈ xs, Nat.Prime p) (hbound : ∀ p ∈ xs, p ≤ B)
    (hwpos : ∀ p ∈ xs, 0 < w p) (hw : ∀ p ∈ xs, Real.log p ≤ (w p : ℝ) / d)
    (he : xs.map w = weights) (hbudget : (budget : ℝ) / d < Real.log q) (hN : budget ≤ N)
    (row : Array ℕ) (rows : List (Array ℕ))
    (hc : weightedPrimeTableCheck N weights (row :: rows) = true)
    (hcount : Nat.card H < row.getD budget 0)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q)) :
    ∃ p : ℕ, p.Prime ∧ p ≤ B ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) :=
  exists_prime_reject_of_weight_list H xs weights B budget w d hd hq hnodup hp hbound hwpos hw he
    hbudget ((weightedPrimeTableCheck_sound N weights row rows hc budget hN) ▸ hcount) hpass

end PseudoPrime.PrimeTestBounds.MillerRabin
