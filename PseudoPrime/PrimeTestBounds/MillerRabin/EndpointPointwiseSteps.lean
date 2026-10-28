/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwiseSteps
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointLowPrime

/-! # Four further pointwise prime witness steps -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- No prime lies strictly between a selected bound and its next prime.
This checks only the small base values, never the composite input. -/
theorem pointwiseStep_no_intermediate (f : LLS.PaperStatements.PointwiseStep) :
    ∀ k ∈ Finset.Ioo f.bound f.nextPrime, ¬Nat.Prime k := by cases f <;> decide +kernel

/-- A prime below the certified next prime is at most the selected bound. -/
theorem pointwiseStep_round (f : LLS.PaperStatements.PointwiseStep) {p : ℕ} (hp : p.Prime)
    (hq : p < f.nextPrime) : p ≤ f.bound := by
  cases f with
  | p61 => exact prime_lt67_le61 hp hq
  | p67 => exact prime_lt71_le67 hp hq
  | p71 =>
    by_contra hn
    exact pointwiseStep_no_intermediate .p71 p (Finset.mem_Ioo.mpr ⟨lt_of_not_ge hn, hq⟩) hp
  | p73 =>
    by_contra hn
    exact pointwiseStep_no_intermediate .p73 p (Finset.mem_Ioo.mpr ⟨lt_of_not_ge hn, hq⟩) hp

/-- Under GRH, the selected pointwise-radius certificate bounds an actual rejecting prime
for every odd composite n>1 below its logarithmic cap. -/
theorem exists_prime_pointwiseStep (f : LLS.PaperStatements.PointwiseStep) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.logCap) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ f.bound ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hg := LLS.PaperStatements.pointwiseStep_gap f hL
  obtain ⟨p, hp, hb, hr⟩ :=
    exists_prime_of_pointwise_gap hn ho hc hGRH
      (LLS.PaperStatements.pointwiseStep_radius_bounds f).1 hg
  have hq : (p : ℝ) < f.nextPrime :=
    hb.trans_lt (LLS.PaperStatements.pointwiseStep_radius_bounds f).2
  exact ⟨p, hp, Nat.cast_le.mpr (pointwiseStep_round f hp (by exact_mod_cast hq)), hr⟩

/-- The least rejecting prime also satisfies the selected pointwise bound.
Apply the existing least-prime extraction to the actual witness theorem. -/
theorem exists_least_pointwiseStep (f : LLS.PaperStatements.PointwiseStep) {n : ℕ} (hn : 1 < n)
    (ho : Odd n) (hc : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ f.logCap) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ f.bound ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (exists_prime_pointwiseStep f hn ho hc hGRH hL)

/-- Under GRH, log n<=11509 / 1000 gives a prime MR witness at most 61.
The fixed-radius pointwise certificate applies to every odd composite n>1. -/
theorem exists_prime_pointwiseStep61 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 11509 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 61 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.PointwiseStep.bound, Nat.cast_ofNat] using
    exists_prime_pointwiseStep .p61 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.PointwiseStep.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, log n<=11509 / 1000 gives a least prime MR witness at most 61.
The fixed-radius pointwise certificate applies to every odd composite n>1. -/
theorem exists_least_pointwiseStep61 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 11509 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 61 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.PointwiseStep.bound, Nat.cast_ofNat] using
    exists_least_pointwiseStep .p61 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.PointwiseStep.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, log n<=1179 / 100 gives a prime MR witness at most 67.
The fixed-radius pointwise certificate applies to every odd composite n>1. -/
theorem exists_prime_pointwiseStep67 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 1179 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 67 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.PointwiseStep.bound, Nat.cast_ofNat] using
    exists_prime_pointwiseStep .p67 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.PointwiseStep.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, log n<=1179 / 100 gives a least prime MR witness at most 67.
The fixed-radius pointwise certificate applies to every odd composite n>1. -/
theorem exists_least_pointwiseStep67 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 1179 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 67 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.PointwiseStep.bound, Nat.cast_ofNat] using
    exists_least_pointwiseStep .p67 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.PointwiseStep.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, log n<=1193 / 100 gives a prime MR witness at most 71.
The fixed-radius pointwise certificate applies to every odd composite n>1. -/
theorem exists_prime_pointwiseStep71 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 1193 / 100) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 71 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.PointwiseStep.bound, Nat.cast_ofNat] using
    exists_prime_pointwiseStep .p71 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.PointwiseStep.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, log n<=1193 / 100 gives a least prime MR witness at most 71.
The fixed-radius pointwise certificate applies to every odd composite n>1. -/
theorem exists_least_pointwiseStep71 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 1193 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 71 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.PointwiseStep.bound, Nat.cast_ofNat] using
    exists_least_pointwiseStep .p71 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.PointwiseStep.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, log n<=12337 / 1000 gives a prime MR witness at most 73.
The fixed-radius pointwise certificate applies to every odd composite n>1. -/
theorem exists_prime_pointwiseStep73 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 12337 / 1000) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 73 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  simpa only [LLS.PaperStatements.PointwiseStep.bound, Nat.cast_ofNat] using
    exists_prime_pointwiseStep .p73 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.PointwiseStep.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- Under GRH, log n<=12337 / 1000 gives a least prime MR witness at most 73.
The fixed-radius pointwise certificate applies to every odd composite n>1. -/
theorem exists_least_pointwiseStep73 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log n ≤ 12337 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 73 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  simpa only [LLS.PaperStatements.PointwiseStep.bound, Nat.cast_ofNat] using
    exists_least_pointwiseStep .p73 hn ho hc hGRH
      (by
        simpa only [LLS.PaperStatements.PointwiseStep.logCap, Rat.cast_div, Rat.cast_ofNat] using
          hL)

/-- A prime below 73 is at most 71; the only intervening base is the composite 72. -/
theorem prime_lt73_le71 {p : ℕ} (hp : p.Prime) (hq : p < 73) : p ≤ 71 := by
  exact pointwiseStep_round .p71 hp hq

/-- A prime below 79 is at most 73; the five intervening bases are composite. -/
theorem prime_lt79_le73 {p : ℕ} (hp : p.Prime) (hq : p < 79) : p ≤ 73 := by
  exact pointwiseStep_round .p73 hp hq

end PseudoPrime.PrimeTestBounds.MillerRabin
