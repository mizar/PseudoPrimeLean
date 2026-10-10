/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CompositePrimePowers

/-!
# Nonsquare composite Mangoldt sums

Chebyshev reindexing identifies the nonsquare composite contribution with odd
prime-power slices, after the even and exponent-one terms have vanished.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

open Classical in
/-- The logarithmic Mangoldt sum on positive indices through the cutoff that are
neither prime nor squares. Only odd composite prime powers contribute. This is the
unrestricted remainder after removing the square contribution in a residue class. -/
noncomputable def nonsquareCompositeLogWeightedSum (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬n.Prime ∧ ¬IsSquare n), logWeightedMangoldtTerm x n

open Classical in
/-- The exponent-k prime-power slice with prime and square terms set to zero.
Chebyshev reindexing produces these finite slices, allowing even exponents and
exponent one to be removed before applying the odd-power majorant. -/
private noncomputable def nonsquarePrimePowerSlice (x : ℝ) (k : ℕ) : ℝ :=
  ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
    if ¬(p ^ k).Prime ∧ ¬IsSquare (p ^ k) then logWeightedMangoldtTerm x (p ^ k) else 0

/-- The nonsquare composite sum equals its prime-power-supported sum with excluded
terms set to zero. Vanishing Mangoldt coefficients remove the remaining indices.
This supplies the input to Chebyshev's finite prime-power reindexing. -/
private theorem nonsquareCompositeLogWeightedSum_eq_supported (x : ℝ) :
    nonsquareCompositeLogWeightedSum x =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter IsPrimePow,
        if ¬n.Prime ∧ ¬IsSquare n then logWeightedMangoldtTerm x n else 0 := by
  classical
  unfold nonsquareCompositeLogWeightedSum
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : IsPrimePow n
  · rw [ite_eq_left hn]
  · rw [ite_eq_right hn, logWeightedMangoldtTerm_eq_zero_of_not_primePow hn, ite_self]

/-- For an even exponent, the nonsquare slice vanishes because every such power
is a square. This removes all even slices without estimating their weights. -/
private theorem nonsquarePrimePowerSlice_eq_zero_of_even (x : ℝ) {k : ℕ} (hk : Even k) :
    nonsquarePrimePowerSlice x k = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p _
  exact ite_eq_right (fun h ↦ h.2 (hk.isSquare_pow p))

/-- The exponent-one nonsquare composite slice vanishes: each selected base is prime.
This removes the remaining small exponent before the odd-power comparison. -/
private theorem nonsquarePrimePowerSlice_one_eq_zero (x : ℝ) :
    nonsquarePrimePowerSlice x 1 = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro p hp
  rw [pow_one]
  exact ite_eq_right (fun h ↦ h.1 (Finset.mem_filter.mp hp).2)

/-- At a positive cutoff and exponent, the restricted nonsquare slice is bounded by
the full prime slice. The discarded weights are nonnegative at their root cutoffs.
This removes the nonsquare predicate for the later analytic upper estimate. -/
private theorem nonsquarePrimePowerSlice_le {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 0 < k) :
    nonsquarePrimePowerSlice x k ≤
      ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
        logWeightedMangoldtTerm x (p ^ k) := by
  classical
  apply Finset.sum_le_sum
  intro p hp
  by_cases h : ¬(p ^ k).Prime ∧ ¬IsSquare (p ^ k)
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, logWeightedMangoldtTerm_prime_pow_eq_root hx (Finset.mem_filter.mp hp).2 hk]
    exact
      mul_nonneg (Nat.cast_nonneg k)
        (logWeightedMangoldtTerm_nonneg (Real.rpow_pos_of_pos hx _)
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).1
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hp).1).2)

/-- At a positive cutoff, the nonsquare composite Mangoldt sum is at most the sum of
prime-power slices with odd exponent at least three. Reindex by Chebyshev's formula,
remove even and exponent-one slices, and enlarge the remaining nonnegative slices.
This connects the nonsquare residue-class remainder to the Section 4.1 odd-power bound. -/
theorem nonsquareCompositeLogWeightedSum_le_odd_powers {x : ℝ} (hx : 0 < x) :
    nonsquareCompositeLogWeightedSum x ≤
      ∑ k ∈ (Finset.Icc 3 ⌊Real.log x / Real.log 2⌋₊).filter Odd,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter Nat.Prime,
          logWeightedMangoldtTerm x (p ^ k) := by
  classical
  rw [nonsquareCompositeLogWeightedSum_eq_supported, Chebyshev.sum_PrimePow_eq_sum_sum _ hx.le]
  let K := ⌊Real.log x / Real.log 2⌋₊
  have he :
    (∑ k ∈ (Finset.Icc 3 K).filter Odd, nonsquarePrimePowerSlice x k) =
      ∑ k ∈ Finset.Icc 1 K, nonsquarePrimePowerSlice x k := by
    apply Finset.sum_subset
    · intro k hk
      have hki := Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1
      exact Finset.mem_Icc.mpr ⟨(by decide : 1 ≤ 3).trans hki.1, hki.2⟩
    · intro k hk hknot
      obtain ⟨hk1, hkK⟩ := Finset.mem_Icc.mp hk
      by_cases hodd : Odd k
      · have hk3 : ¬3 ≤ k := fun h ↦
          hknot (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨h, hkK⟩, hodd⟩)
        have hk2 : k ≤ 2 := Nat.le_of_lt_succ (Nat.lt_of_not_ge hk3)
        interval_cases k
        · exact nonsquarePrimePowerSlice_one_eq_zero x
        · exact nonsquarePrimePowerSlice_eq_zero_of_even x (by decide)
      · exact nonsquarePrimePowerSlice_eq_zero_of_even x (Nat.not_odd_iff_even.mp hodd)
  change (∑ k ∈ Finset.Icc 1 K, nonsquarePrimePowerSlice x k) ≤ _
  rw [← he]
  apply Finset.sum_le_sum
  intro k hk
  exact
    nonsquarePrimePowerSlice_le hx
      (lt_of_lt_of_le (by decide : 0 < 3) (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1)

end PseudoPrime.AnalyticNumberTheory.Arithmetic
