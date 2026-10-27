/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FinerPart2FromFive
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! # Miller-Rabin prime witnesses with correction 4.5571 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: GRH and an odd composite n>=5.
Claim: a prime rejecting base lies below (log(n)-2*log(log(n))+4.5571)^2.
Proof: apply the entrance-five subgroup-image theorem to the subgroup of passing residues.
Role: transfer the finer LLS constant to Miller-Rabin without a factorization assumption. -/
theorem exists_prime_witness_le_finerPart2Root {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hnLarge : 5 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log n)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn : 1 < n := (by norm_num only : (1 : ℕ) < 5).trans_le hnLarge
  let : NeZero n := ⟨(zero_lt_one.trans hn).ne'⟩
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn hnOdd hnComposite
  obtain ⟨p, hp, hb, hout⟩ := LLS.exists_prime_outside_finerPart2_from_five hGRH hnLarge H hH
  exact ⟨p, hp, hb, PrimeTest.not_pass_of_outside_subgroup hpass hout⟩

/-- Input: GRH and an odd composite n>=5.
Claim: the least prime rejecting base has the finer cutoff, with unbounded prime minimality.
Proof: minimize the rejection predicate after obtaining the bounded witness.
Role: expose the bound for least-witness tables. -/
theorem exists_least_prime_witness_le_finerPart2Root {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 5 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log n)) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_finerPart2Root hnOdd hnComposite hnLarge hGRH
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Input: GRH and an odd composite n>=5.
Claim: a prime within the finer radius fails every required canonical Miller-Rabin power test.
Proof: convert the proved rejection using the exact power characterization.
Role: connect the analytic bound to the executable acceptance condition. -/
theorem exists_prime_rejecting_powers_le_finerPart2Root {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 5 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log n)) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_witness_le_finerPart2Root hnOdd hnComposite hnLarge hGRH
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

/-- Input: GRH and an odd composite n>=17400.
Claim: the same prime witness obeys the finer radius and is strictly below log(n)^2.
Proof: apply the proved strict radius comparison to the bounded witness.
Role: lower the strict logarithmic-square comparison entrance without a minimum formula. -/
theorem exists_prime_witness_le_finerPart2Root_and_lt_log_sq {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hnLarge : 17400 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Analysis.finerPart2CutoffRoot (Real.log n)) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_witness_le_finerPart2Root hnOdd hnComposite
      (le_trans (by norm_num only : 5 ≤ 17400) hnLarge) hGRH
  exact ⟨p, hp, hb, hb.trans_lt (Analysis.finerPart2Root_sq_lt_log_sq_of_17400_le hnLarge), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
