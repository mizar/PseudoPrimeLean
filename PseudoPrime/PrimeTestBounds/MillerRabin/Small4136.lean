/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.SmallPointwiseBounds
public import PseudoPrime.Analysis.LogTaylorBounds

/-! # Small-input max bound for the coefficient 0.4136 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every odd composite with logarithm below 8 has a rejecting prime within
`max 2 ((517/1250) * (log n)²)`. The existing finite classification gives base two except
at 2047, where a certified logarithm lower bound covers the rejecting prime three. -/
theorem exists_prime_reject_small_4136 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hL : Real.log n < 8) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ max 2 ((517 / 1250 : ℝ) * (Real.log n) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have h3000 : (8 : ℝ) ≤ Real.log 3000 := by
    have h :=
      (Analysis.rationalLogIntervalCheck_sound
          (show Analysis.rationalLogIntervalCheck 3000 12 12 8 (801 / 100) = true by
            decide +kernel)).1
    norm_num only [Rat.cast_ofNat] at h
    exact h
  have hN : n < 3000 := by
    by_contra hnN
    have h :=
      Real.log_le_log (by norm_num only : (0 : ℝ) < 3000)
        (Nat.cast_le.mpr (Nat.le_of_not_gt hnN) : (3000 : ℝ) ≤ n)
    linarith only [h, h3000, hL]
  obtain ⟨r, hr, hb, hf⟩ := exists_prime_smallPointwise hn ho hc hN
  by_cases he : n = 2047
  · have h2047 : (7 : ℝ) ≤ Real.log (2047 : ℝ) := by
      have h :=
        (Analysis.rationalLogIntervalCheck_sound
            (show Analysis.rationalLogIntervalCheck 2047 11 12 7 8 = true by decide +kernel)).1
      norm_num only [Rat.cast_ofNat] at h
      exact h
    have h7 : (7 : ℝ) ≤ Real.log n := by simpa only [he, Nat.cast_ofNat] using h2047
    have hs := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 7) h7 2
    have h3 : (3 : ℝ) ≤ (517 / 1250 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hs]
    have hb3 : (r : ℝ) ≤ 3 := by simpa only [smallPointwiseBound, ite_eq_left he] using hb
    exact ⟨r, hr, hb3.trans (h3.trans (le_max_right _ _)), hf⟩
  · have hb2 : (r : ℝ) ≤ 2 := by simpa only [smallPointwiseBound, ite_eq_right he] using hb
    exact ⟨r, hr, hb2.trans (le_max_left _ _), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
