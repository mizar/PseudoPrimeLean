/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeElevenths2000
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniformLog8
import PseudoPrime.PrimeTestBounds.MillerRabin.LeastRejectingPrime
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven2000to3000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven3000to4000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven4000to5000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven5000to6000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven6000to7000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven7000to8000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven8000to9000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven9000to10000

/-! # Three-elevenths bound through logarithmic scale 10000 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with logarithm at most 10000 admits a rejecting
prime bounded by the maximum of 2 and three elevenths of its squared logarithm.
The uniform and nonuniform witness intervals cover the remaining range. -/
theorem three_eleven_max_to10000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 10000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h2000 : Real.log n ≤ 2000
  · exact three_eleven_max_to2000 hn ho hc hGRH h2000
  have hL : (2000 : ℝ) ≤ Real.log n := le_of_not_ge h2000
  have hcoef : (1 / 4 : ℝ) ≤ 3 / 11 := by norm_num only
  have hbound :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_cases hu : UniformKorseltTriple n
    · by_cases h3000 : Real.log n ≤ 3000
      · exact uniform_three_eleven_2000_3000 hn ho hu hGRH hL h3000
      by_cases h4000 : Real.log n ≤ 4000
      · exact uniform_three_eleven_3000_4000 hn ho hu hGRH (le_of_not_ge h3000) h4000
      by_cases h5000 : Real.log n ≤ 5000
      · exact uniform_three_eleven_4000_5000 hn ho hu hGRH (le_of_not_ge h4000) h5000
      by_cases h6000 : Real.log n ≤ 6000
      · exact uniform_three_eleven_5000_6000 hn ho hu hGRH (le_of_not_ge h5000) h6000
      by_cases h7000 : Real.log n ≤ 7000
      · exact uniform_three_eleven_6000_7000 hn ho hu hGRH (le_of_not_ge h6000) h7000
      by_cases h8000 : Real.log n ≤ 8000
      · exact uniform_three_eleven_7000_8000 hn ho hu hGRH (le_of_not_ge h7000) h8000
      by_cases h9000 : Real.log n ≤ 9000
      · exact uniform_three_eleven_8000_9000 hn ho hu hGRH (le_of_not_ge h8000) h9000
      exact uniform_three_eleven_9000_10000 hn ho hu hGRH (le_of_not_ge h9000) hU
    · obtain ⟨p, hp, hb, hf⟩ := quarter_nonuniform_log8 hn ho hc hu hGRH (by linarith only [hL])
      exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  obtain ⟨p, hp, hb, hf⟩ := hbound
  exact ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH, the least rejecting prime of an odd composite whose logarithm
is at most 10000 satisfies the maximum three-elevenths cutoff. Extract the
minimum from the bounded witness. -/
theorem three_eleven_least_to10000 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 10000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject (three_eleven_max_to10000 hn ho hc hGRH hU)

end PseudoPrime.PrimeTestBounds.MillerRabin
