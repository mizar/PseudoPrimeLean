/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.LogTaylorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.SmallPointwiseBounds

/-! # Small-input maximum cutoff for coefficient one quarter -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every odd composite below 3000 has a rejecting prime within the quarter
maximum cutoff. The finite small-input classification gives a prime at most
two below 2047 and at most three above it. -/
theorem exists_prime_reject_quarter_small {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hN : n < 3000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((1 / 4 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hb, hf⟩ := exists_prime_smallInterval hn ho hc hN
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
      (show (3 : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 by nlinarith only [hs7]).trans (le_max_right _ _)

end PseudoPrime.PrimeTestBounds.MillerRabin
