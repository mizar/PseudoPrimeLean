/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030Least
public import PseudoPrime.PrimeTestBounds.MillerRabin.SmallPointwiseBounds

/-! # A global three-tenths bound for rejecting primes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite above one has a prime Miller--Rabin witness
at most the maximum of two and three tenths of the squared logarithm. The
certified small-input classification supplies the lower range. -/
theorem exists_prime_reject_03_global {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 10 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hN : n < 3000
  · obtain ⟨p, hp, hb, hf⟩ := exists_prime_smallInterval hn ho hc hN
    refine ⟨p, hp, hb.trans ?_, hf⟩
    by_cases h : n < 2047
    · rw [smallIntervalBound, ite_eq_left h]
      exact le_max_left _ _
    · rw [smallIntervalBound, ite_eq_right h]
      have hn2047 : 2047 ≤ n := Nat.le_of_not_gt h
      have hlog2047 :=
        (Analysis.rationalLogIntervalCheck_sound
            (show Analysis.rationalLogIntervalCheck 2047 11 12 7 8 = true by decide +kernel)).1
      norm_num only [Rat.cast_ofNat] at hlog2047
      have ht := Real.log_le_log (by norm_num only : (0 : ℝ) < 2047) (Nat.cast_le.mpr hn2047)
      have h7 : (7 : ℝ) ≤ Real.log n := hlog2047.trans ht
      have hs7 := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 7) h7 2
      exact
        (show (3 : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 by nlinarith only [hs7]).trans
          (le_max_right _ _)
  · have hn3000 : 3000 ≤ n := Nat.le_of_not_gt hN
    have hlog3000 :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3000 12 12 8 (801 / 100) = true by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat] at hlog3000
    have ht := Real.log_le_log (by norm_num only : (0 : ℝ) < 3000) (Nat.cast_le.mpr hn3000)
    have h8 : (8 : ℝ) ≤ Real.log n := hlog3000.trans ht
    obtain ⟨p, hp, hb, hf⟩ := exists_prime_reject_03_log8 hn ho hc hGRH h8
    exact ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH the canonical least rejecting prime obeys the global maximum
bound. Apply minimality to the actual rejecting prime constructed above. -/
theorem compositeLeastPrime_le_03_global
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) : (compositeLeastPrime n : ℝ) ≤ max 2 ((3 / 10 : ℝ) * Real.log n ^ 2) := by
  obtain ⟨p, hp, hb, hr⟩ := exists_prime_reject_03_global hn ho hc hGRH
  have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hr
  exact (Nat.cast_le.mpr hm).trans hb

end PseudoPrime.PrimeTestBounds.MillerRabin
