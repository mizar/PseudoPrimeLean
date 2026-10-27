/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.AdaptiveReciprocalWitnessBounds
public import PseudoPrime.Analysis.AdaptiveReciprocalStrictLogSquare
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! # Miller-Rabin witnesses from the explicit adaptive reciprocal radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: GRH and an odd composite at least 600.
Claim: a prime rejecting Miller-Rabin base lies within the explicit adaptive squared radius.
Proof: apply the adaptive subgroup-image bound to the proper subgroup containing passing bases.
Role: transfer the pointwise reciprocal improvement to the primality-test witness. -/
theorem exists_prime_witness_le_adaptivePart2Root {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hnLarge : 600 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.adaptivePart2CutoffRoot (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn : 1 < n := (by norm_num only : (1 : ℕ) < 600).trans_le hnLarge
  let : NeZero n := ⟨(zero_lt_one.trans hn).ne'⟩
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.exists_prime_outside_subgroup_le_adaptivePart2Root hnLarge H hH hGRH
  exact ⟨p, hp, hb, PrimeTest.not_pass_of_outside_subgroup hpass hout⟩

/-- Input: GRH and an odd composite at least 600.
Claim: the least prime rejecting base has the adaptive bound, with unbounded prime minimality.
Proof: minimize the prime rejection predicate after obtaining a bounded witness.
Role: connect the analytic radius with least-witness tables. -/
theorem exists_least_prime_witness_le_adaptivePart2Root {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 600 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (Analysis.adaptivePart2CutoffRoot (Real.log n)) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_adaptivePart2Root hnOdd hnComposite hnLarge hGRH
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Input: GRH and an odd composite at least 600.
Claim: a prime inside the adaptive radius fails the required canonical power equalities.
Proof: apply the exact characterization of strong Miller-Rabin rejection.
Role: connect the witness theorem to the executable acceptance condition. -/
theorem exists_prime_rejecting_powers_le_adaptivePart2Root {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 600 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.adaptivePart2CutoffRoot (Real.log n)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_adaptivePart2Root hnOdd hnComposite hnLarge hGRH
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

/-- Input: GRH and an odd composite at least 16000.
Claim: the same prime rejecting base satisfies the adaptive bound and lies below log(n)^2.
Proof: combine the bounded witness with the strict adaptive radius comparison.
Role: lower the strict same-witness comparison entrance without a minimum formula. -/
theorem exists_prime_witness_le_adaptivePart2Root_and_lt_log_sq {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 16000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.adaptivePart2CutoffRoot (Real.log n)) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_le_adaptivePart2Root hnOdd hnComposite
      (le_trans (by norm_num only : (600 : ℕ) ≤ 16000) hnLarge) hGRH
  exact ⟨p, hp, hb, hb.trans_lt (Analysis.adaptivePart2Root_sq_lt_log_sq_of_16000_le hnLarge), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
