/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeElevenths10000
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeEleven10000to10300
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniformLog8
import PseudoPrime.PrimeTestBounds.MillerRabin.LeastRejectingPrime

/-! # Three-elevenths bound through logarithmic scale 10300 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite with logarithm at most 10300 has a least
rejecting prime at most the maximum of 2 and three elevenths of its squared
logarithm. The existing bound and independent type-specific bounds cover the
input range. -/
theorem three_eleven_least_to10300 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 10300) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  by_cases h10000 : Real.log n ≤ 10000
  · exact three_eleven_least_to10000 hn ho hc hGRH h10000
  have hL : (10000 : ℝ) ≤ Real.log n := le_of_not_ge h10000
  have hcoef : (1 / 4 : ℝ) ≤ 3 / 11 := by norm_num only
  have hbound :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_cases hu : UniformKorseltTriple n
    · exact uniform_three_eleven_10000_10300 hn ho hu hGRH hL hU
    · obtain ⟨p, hp, hb, hf⟩ := quarter_nonuniform_log8 hn ho hc hu hGRH (by linarith only [hL])
      exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  obtain ⟨p, hp, hb, hf⟩ := hbound
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
