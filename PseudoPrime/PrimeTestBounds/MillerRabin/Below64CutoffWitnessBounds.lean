/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Below64Part2Bounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! # Prime Miller-Rabin witnesses from the parameterized main-error regime -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, each odd composite n ≥ 1053 has a prime rejecting base
through (log n-2loglog n+2301/500)². Apply the sharper subgroup-image
bound to a proper subgroup containing passing residues.
No coprimality or factorization hypothesis is imposed on the rejecting prime. -/
theorem exists_prime_witness_le_sharperPart2Root_of_1053_le {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 1053 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.sharperPart2CutoffRoot (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn : 1 < n := (by norm_num only : (1 : ℕ) < 1053).trans_le hnLarge
  let : NeZero n := ⟨(zero_lt_one.trans hn).ne'⟩
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.exists_prime_outside_subgroup_image_le_sharperPart2Root_of_1053_le hnLarge H hH hGRH
  exact ⟨p, hp, hb, PrimeTest.not_pass_of_outside_subgroup hpass hout⟩

/-- Under the same assumptions, the least prime rejecting base is bounded
by the sharper Part 2 root squared. Minimize the unbounded rejection
predicate so minimality compares every prime rejecting base. -/
theorem exists_least_prime_witness_le_sharperPart2Root_of_1053_le {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 1053 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (Analysis.sharperPart2CutoffRoot (Real.log n)) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_le_sharperPart2Root_of_1053_le hnOdd hnComposite hnLarge hGRH
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under GRH for odd composite n ≥ 1053, the canonical decomposition
n-1=2^s d has a prime base through the sharper Part 2 cutoff with p^d ≠ 1
and p^(2^j d) ≠ -1 for every j<s. Apply the exact rejection equivalence
to the proved prime witness. -/
theorem exists_prime_rejecting_powers_le_sharperPart2Root_of_1053_le {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 1053 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.sharperPart2CutoffRoot (Real.log n)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_le_sharperPart2Root_of_1053_le hnOdd hnComposite hnLarge hGRH
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
