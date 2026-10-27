/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.StrictLogSquareWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.FromLLS

/-! # A strict logarithmic-square Miller–Rabin witness bound starting at 3000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Input: a natural number at least 3000.
Claim: the shifted square is strictly below the unshifted logarithmic square.
Proof: compare the nonnegative roots with their positive rational difference.
This provides the strict numerical improvement on the whole analytic range. -/
theorem strictLogSquare_lt_log_sq {n : ℕ} (hn : 3000 ≤ n) :
    (Real.log n - 1 / 1000) ^ 2 < (Real.log n) ^ 2 := by
  have hroot := LLS.eight_le_log_sub_mill_of_ge_3000 hn
  nlinarith only [hroot]

/-- Input: GRH and an odd composite number at least 3000.
Claim: a prime rejecting base obeys the shifted-square bound, hence lies strictly below log² n.
Proof: apply the strict subgroup estimate to the subgroup containing every passing residue.
This is an analytic witness theorem with no finite input certificate. -/
theorem exists_prime_witness_le_strictLogSquare {n : ℕ} (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 3000 ≤ n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (Real.log n - 1 / 1000) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := (by decide : (1 : ℕ) < 3000).trans_le hn
  let : NeZero n := ⟨(zero_lt_one.trans hn1).ne'⟩
  obtain ⟨H, hH, hpass⟩ :=
    PrimeTest.exists_proper_subgroup_containing_strongMillerRabinPass hn1 hnOdd hnComposite
  obtain ⟨p, hp, hb, hout⟩ :=
    LLS.exists_prime_outside_subgroup_image_le_strictLogSquare hn H hH hGRH
  exact
    ⟨p, hp, hb, hb.trans_lt (strictLogSquare_lt_log_sq hn),
      PrimeTest.not_pass_of_outside_subgroup hpass hout⟩

/-- Input: GRH and an odd number at least 3000.
Claim: primality is equivalent to acceptance at every prime through the shifted-square cutoff.
Proof: use the rejecting witness for composites and the existing prime acceptance theorem.
This is the decision interface for the independent strict analytic bound. -/
theorem prime_iff_millerRabin_for_all_primes_le_strictLogSquare {n : ℕ} (hnOdd : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 3000 ≤ n) :
    (∀ p : ℕ,
        p.Prime →
          (p : ℝ) ≤ (Real.log n - 1 / 1000) ^ 2 → PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ↔
      n.Prime := by
  have hn1 : 1 < n := (by decide : (1 : ℕ) < 3000).trans_le hn
  constructor
  · intro hpass
    by_contra hc
    obtain ⟨p, hp, hb, _, hf⟩ := exists_prime_witness_le_strictLogSquare hnOdd hc hGRH hn
    exact hf (hpass p hp hb)
  · intro hp p hprime hb
    exact
      (prime_iff_millerRabin_for_all_primes_le_log_sq hGRH hn1 hnOdd).mpr hp p hprime
        (hb.trans (strictLogSquare_lt_log_sq hn).le)

end PseudoPrime.PrimeTestBounds.MillerRabin
