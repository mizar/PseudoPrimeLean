/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridge465
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniformLog8
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven465to700
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven700to1000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven1000to1500
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven1500to2000
import PseudoPrime.PrimeTestBounds.MillerRabin.LeastRejectingPrime

/-! # Three-elevenths bound through logarithmic scale 2000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite of logarithmic scale at most 2000 has a
rejecting prime bounded by the maximum of 2 and three elevenths of its squared
logarithm. The quarter bound covers the small range, and independent uniform
and nonuniform bounds cover the remaining range. -/
theorem three_eleven_max_to2000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 2000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hcoef : (1 / 4 : ℝ) ≤ 3 / 11 := by norm_num only
  by_cases h465 : Real.log n ≤ 465
  · obtain ⟨p, hp, hb, hf⟩ := quarter_max_through465 hn ho hc hGRH h465
    exact ⟨p, hp, hb.trans (max_le_max le_rfl (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))), hf⟩
  have hL : (465 : ℝ) ≤ Real.log n := le_of_not_ge h465
  have hbound :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_cases hu : UniformKorseltTriple n
    · by_cases h700 : Real.log n ≤ 700
      · exact uniform_three_eleven_465_700 hn ho hu hGRH hL h700
      by_cases h1000 : Real.log n ≤ 1000
      · exact uniform_three_eleven_700_1000 hn ho hu hGRH (le_of_not_ge h700) h1000
      by_cases h1500 : Real.log n ≤ 1500
      · exact uniform_three_eleven_1000_1500 hn ho hu hGRH (le_of_not_ge h1000) h1500
      exact uniform_three_eleven_1500_2000 hn ho hu hGRH (le_of_not_ge h1500) hU
    · obtain ⟨p, hp, hb, hf⟩ := quarter_nonuniform_log8 hn ho hc hu hGRH (by linarith only [hL])
      exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  obtain ⟨p, hp, hb, hf⟩ := hbound
  exact ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH, the least rejecting prime of an odd composite of logarithmic
scale at most 2000 satisfies the maximum three-elevenths cutoff. The minimum
is extracted from the bounded rejecting witness. -/
theorem three_eleven_least_to2000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 2000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject (three_eleven_max_to2000 hn ho hc hGRH hU)

end PseudoPrime.PrimeTestBounds.MillerRabin
