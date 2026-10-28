/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.EndpointLowPrimeTight
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointLowPrime

/-! # Actual prime witnesses from extended low-prime certificates -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, the selected low-radius certificate bounds an actual rejecting prime
for every odd composite n>1 below its logarithmic cap. -/
theorem exists_prime_endpointLowTight (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.tightLogCap) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ f.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hg := LLS.PaperStatements.endpointLowPrimeTight_gap f hL
  obtain ⟨p, hp, hb, hr⟩ :=
    exists_prime_of_pointwise_gap hn ho hc hGRH
      (LLS.PaperStatements.lowPrimeTight_radius_bounds f).1 hg
  have hq : (p : ℝ) < f.nextPrime :=
    hb.trans_lt (LLS.PaperStatements.lowPrimeTight_radius_bounds f).2
  exact ⟨p, hp, Nat.cast_le.mpr (lowPrime_round f hp (by exact_mod_cast hq)), hr⟩

/-- The least rejecting prime also satisfies the selected low bound.
Apply the existing least-prime extraction to the actual witness theorem. -/
theorem exists_least_endpointLowTight (f : LLS.PaperStatements.LowPrimeProfile) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.tightLogCap) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_endpointLowTight f hn ho hc hGRH hL)

/-- Under GRH, every odd composite n>1 with log n<=8032 / 1000 has a
prime MR witness at most 23. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint23_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 8032 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 23 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p23 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=8032 / 1000 has a least
prime MR witness at most 23. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint23_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 8032 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 23 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p23 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=8271 / 1000 has a
prime MR witness at most 29. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint29_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 8271 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 29 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p29 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=8271 / 1000 has a least
prime MR witness at most 29. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint29_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 8271 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 29 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p29 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=8934 / 1000 has a
prime MR witness at most 31. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint31_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 8934 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 31 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p31 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=8934 / 1000 has a least
prime MR witness at most 31. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint31_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 8934 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 31 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p31 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=9339 / 1000 has a
prime MR witness at most 37. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint37_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 9339 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 37 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p37 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=9339 / 1000 has a least
prime MR witness at most 37. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint37_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 9339 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 37 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p37 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=9532 / 1000 has a
prime MR witness at most 41. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint41_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 9532 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 41 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p41 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=9532 / 1000 has a least
prime MR witness at most 41. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint41_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 9532 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 41 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p41 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=9902 / 1000 has a
prime MR witness at most 43. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint43_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 9902 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 43 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p43 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=9902 / 1000 has a least
prime MR witness at most 43. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint43_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 9902 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 43 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p43 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=10422 / 1000 has a
prime MR witness at most 47. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint47_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 10422 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 47 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p47 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=10422 / 1000 has a least
prime MR witness at most 47. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint47_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 10422 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 47 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p47 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=10907 / 1000 has a
prime MR witness at most 53. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint53_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 10907 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 53 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p53 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=10907 / 1000 has a least
prime MR witness at most 53. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint53_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 10907 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 53 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p53 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=11062 / 1000 has a
prime MR witness at most 59. Specialize the shared fixed-radius certificate. -/
theorem exists_prime_endpoint59_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 11062 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 59 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_prime_endpointLowTight .p59 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

/-- Under GRH, every odd composite n>1 with log n<=11062 / 1000 has a least
prime MR witness at most 59. Specialize the shared fixed-radius certificate. -/
theorem exists_least_endpoint59_tight {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 11062 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 59 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.LowPrimeProfile.bound, Nat.cast_ofNat] using
    exists_least_endpointLowTight .p59 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.LowPrimeProfile.tightLogCap, Rat.cast_div,
          Rat.cast_ofNat] using hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
