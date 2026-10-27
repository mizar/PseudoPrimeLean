/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleRetainedScaleBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.TwoPoleSignedGammaBounds

/-! # MR prime witnesses from the direct signed two-pole error bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd composite n greater than one under GRH with log n at least 500,
a prime rejecting base lies through (99/40)((500/821)log n+13) squared. Insert the
continuous affine separation into the character-free MR criterion.
No additional numerical or factorization hypothesis remains. -/
theorem exists_prime_strong_witness_le_retainedScaleTwoPole {n : ℕ} [NeZero n] (hn : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 13) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hd := LLS.twoPoleRetained_root_data hL (c := 13) (by norm_num only) (by norm_num only)
  have hx4 : 4 ≤ ((500 / 821 : ℝ) * Real.log n + 13) ^ 2 := hd.2.1
  have hg :=
    LLS.twoPoleRetainedGap_affine_margin hL (c := 13) (C := 523 / 100) (by norm_num only)
      (by norm_num only) (by norm_num only)
  exact
    exists_prime_strong_witness_of_twoPoleConstantGap hn hnOdd hnComposite hGRH
      (by linarith only [hx4] : 2 ≤ ((500 / 821 : ℝ) * Real.log n + 13) ^ 2) (by linarith only [hg])

/-- For every odd composite n under GRH with log n at least 500, a prime MR witness
obeys the affine two-pole bound, which is strictly below (log n) squared.
Derive n greater than one from its logarithm and bound the affine root by 6271log n/10000.
This is the public pointwise bound used in the best-interval comparison. -/
theorem exists_prime_witness_le_retainedScaleTwoPole_log_500 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 13) ^ 2 ∧
        (p : ℝ) < (Real.log n) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨hnOdd.pos.ne'⟩
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr hnOdd.pos
  have ht := Real.log_le_sub_one_of_pos hn0
  have hn : 1 < n := by exact_mod_cast (show (1 : ℝ) < n by linarith only [ht, hL])
  obtain ⟨p, hp, hb, hf⟩ :=
    exists_prime_strong_witness_le_retainedScaleTwoPole hn hnOdd hnComposite hGRH hL
  have hr : 0 ≤ (500 / 821 : ℝ) * Real.log n + 13 := by linarith only [hL]
  have hu : (500 / 821 : ℝ) * Real.log n + 13 ≤ (1271 / 2000 : ℝ) * Real.log n := by
    linarith only [hL]
  have hs := mul_self_le_mul_self hr hu
  have hsq : 0 < (Real.log n) ^ 2 := sq_pos_of_pos (by linarith only [hL])
  exact ⟨p, hp, hb, by nlinarith only [hb, hs, hsq], hf⟩

/-- Under the same hypotheses, the least prime rejecting base obeys the affine
two-pole bound. Minimize the unbounded rejection predicate and compare with the
explicit witness. Leastness ranges over all prime rejecting bases. -/
theorem exists_least_prime_witness_le_retainedScaleTwoPole_log_500 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 13) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_retainedScaleTwoPole_log_500 hnOdd hnComposite hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the same hypotheses, a prime through the affine two-pole cutoff fails
the initial power equality and every negative-one equality in the canonical binary
decomposition of n-1. Apply the exact strong-test rejection equivalence.
This exposes the actual power conditions of the rejecting witness. -/
theorem exists_prime_rejecting_powers_le_retainedScaleTwoPole_log_500 {n : ℕ} (hnOdd : Odd n)
    (hnComposite : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    let (s, d) := Nat.maxPowDvdDiv 2 (n - 1);
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (99 / 40 : ℝ) * ((500 / 821 : ℝ) * Real.log n + 13) ^ 2 ∧
        (p : ZMod n) ^ d ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod n) ^ (2 ^ j * d) ≠ -1 := by
  obtain ⟨p, hp, hb, _, hf⟩ :=
    exists_prime_witness_le_retainedScaleTwoPole_log_500 hnOdd hnComposite hGRH hL
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
