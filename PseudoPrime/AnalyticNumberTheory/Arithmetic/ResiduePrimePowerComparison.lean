/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.NonsquarePrimePowers
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.SquareCongruenceWeights

/-!
# Square and nonsquare contributions in a prime-free residue class

Split the logarithmic Mangoldt sum into square terms and nonsquare composite terms.
The comparison is arithmetic and does not require a hypothesis on zeta zeros.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

open Classical in
/-- For a positive cutoff and a residue class containing no prime up to that cutoff,
the logarithmic Mangoldt sum is bounded by its square contribution plus the unrestricted
nonsquare composite contribution. Split the finite sum by squareness and enlarge the
nonsquare part using nonnegative weights. This separates the two prime-power estimates
used in the least-prime argument for arithmetic progressions. -/
theorem residue_logWeightedSum_le_square_add_nonsquare {q : ℕ} (a : ZMod q) {x : ℝ} (hx : 0 < x)
    (hno : ∀ p : ℕ, p.Prime → (p : ZMod q) = a → ¬(p : ℝ) ≤ x) :
    (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = a), logWeightedMangoldtTerm x n) ≤
      (∑ n ∈ (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = a),
          logWeightedMangoldtTerm x n) +
        nonsquareCompositeLogWeightedSum x := by
  classical
  let s := (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ (n : ZMod q) = a)
  have hs := Finset.sum_filter_add_sum_filter_not s IsSquare (logWeightedMangoldtTerm x)
  have he :
    s.filter IsSquare = (Finset.Icc 1 ⌊x⌋₊).filter (fun n : ℕ ↦ IsSquare n ∧ (n : ZMod q) = a) := by
    ext n
    simp only [s, Finset.mem_filter, and_assoc, and_comm]
  rw [he] at hs
  have hb :
    (∑ n ∈ s.filter (fun n ↦ ¬IsSquare n), logWeightedMangoldtTerm x n) ≤
      nonsquareCompositeLogWeightedSum x := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      obtain ⟨hnS, hnSq⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnI, hna⟩ := Finset.mem_filter.mp hnS
      obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnI
      have hnX : (n : ℝ) ≤ x := (Nat.cast_le.mpr hnN).trans (Nat.floor_le hx.le)
      exact
        Finset.mem_filter.mpr
          ⟨Finset.mem_Ioc.mpr ⟨Nat.zero_lt_one.trans_le hn1, hnN⟩, (fun hp ↦ hno n hp hna hnX),
            hnSq⟩
    · intro n hn _
      have hni := Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1
      exact logWeightedMangoldtTerm_nonneg hx hni.1 hni.2
  change (∑ n ∈ s, logWeightedMangoldtTerm x n) ≤ _
  linarith only [hs, hb]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
