/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointLowPrime
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPointwise

/-! # Actual prime witnesses from the nine low pointwise certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every positive pointwise gap at radius at least two yields an actual prime MR witness.
Use an even character trivial on passing residues and contradict its non-one prime. -/
theorem exists_prime_of_pointwise_gap {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {y : ℝ} (hy : 2 ≤ y)
    (hgap :
      0 < LLS.PaperStatements.endpointPointwiseGap (Real.log n) (2096 / 1831) y (Real.log y)) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ y ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  obtain ⟨χ, hne, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  have heven := character_even_of_trivial_on_pass hn ho hpass
  obtain ⟨p, hp, hb, hv⟩ := LLS.PaperStatements.pointwise_ne_one_prime χ hne heven hGRH hy hgap
  exact ⟨p, hp, hb, fun h ↦ hv (hpass p h)⟩

/-- No prime lies strictly between a selected bound and its next prime.
This checks only the small base values, never the composite input. -/
theorem lowPrime_no_intermediate (f : LLS.PaperStatements.LowPrimeProfile) :
    ∀ k ∈ Finset.Ioo f.bound f.nextPrime, ¬Nat.Prime k := by cases f <;> decide +kernel

/-- A prime below the certified next prime is at most the selected bound. -/
theorem lowPrime_round (f : LLS.PaperStatements.LowPrimeProfile) {p : ℕ} (hp : p.Prime)
    (hq : p < f.nextPrime) : p ≤ f.bound := by
  by_contra hn
  exact lowPrime_no_intermediate f p (Finset.mem_Ioo.mpr ⟨lt_of_not_ge hn, hq⟩) hp

/-- Under GRH, the selected low-radius certificate bounds an actual rejecting prime
for every odd composite n>1 below its logarithmic cap. -/
theorem exists_prime_endpointLow (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.logCap) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ f.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hg := LLS.PaperStatements.endpointLowPrime_gap f hL
  obtain ⟨p, hp, hb, hr⟩ :=
    exists_prime_of_pointwise_gap hn ho hc hGRH (LLS.PaperStatements.lowPrime_radius_bounds f).1 hg
  have hq : (p : ℝ) < f.nextPrime := hb.trans_lt (LLS.PaperStatements.lowPrime_radius_bounds f).2
  exact ⟨p, hp, Nat.cast_le.mpr (lowPrime_round f hp (by exact_mod_cast hq)), hr⟩

/-- The least rejecting prime also satisfies the selected low bound.
Apply the existing least-prime extraction to the actual witness theorem. -/
theorem exists_least_endpointLow (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.logCap) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_endpointLow f hn ho hc hGRH hL)

/-- Under GRH, every odd composite n>1 with log n<=401 / 50 has a
prime MR witness at most 23. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint23 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 401 / 50) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 23 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p23 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=401 / 50 has a least
prime MR witness at most 23. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint23 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 401 / 50) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 23 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p23 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=413 / 50 has a
prime MR witness at most 29. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint29 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 413 / 50) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 29 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p29 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=413 / 50 has a least
prime MR witness at most 29. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint29 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 413 / 50) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 29 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p29 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=893 / 100 has a
prime MR witness at most 31. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint31 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 893 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 31 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p31 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=893 / 100 has a least
prime MR witness at most 31. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint31 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 893 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 31 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p31 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=933 / 100 has a
prime MR witness at most 37. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint37 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 933 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 37 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p37 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=933 / 100 has a least
prime MR witness at most 37. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint37 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 933 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 37 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p37 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=238 / 25 has a
prime MR witness at most 41. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint41 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 238 / 25) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 41 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p41 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=238 / 25 has a least
prime MR witness at most 41. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint41 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 238 / 25) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 41 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p41 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=989 / 100 has a
prime MR witness at most 43. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint43 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 989 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 43 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p43 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=989 / 100 has a least
prime MR witness at most 43. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint43 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 989 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 43 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p43 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=521 / 50 has a
prime MR witness at most 47. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint47 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 521 / 50) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 47 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p47 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=521 / 50 has a least
prime MR witness at most 47. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint47 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 521 / 50) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 47 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p47 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=109 / 10 has a
prime MR witness at most 53. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint53 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 109 / 10) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 53 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p53 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=109 / 10 has a least
prime MR witness at most 53. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint53 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 109 / 10) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 53 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p53 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=553 / 50 has a
prime MR witness at most 59. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint59 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 553 / 50) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 59 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLow .p59 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, every odd composite n>1 with log n<=553 / 50 has a least
prime MR witness at most 59. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint59 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 553 / 50) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 59 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLow .p59 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
