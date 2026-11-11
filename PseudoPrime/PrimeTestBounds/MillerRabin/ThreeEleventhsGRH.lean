/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LeastPrimeCumulative
import PseudoPrime.PrimeTestBounds.MillerRabin.UniformThreeElevenGRH
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeElevenths10300
import PseudoPrime.PrimeTestBounds.MillerRabin.ThreeElevenths4M
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniformLog8
import PseudoPrime.PrimeTestBounds.MillerRabin.LeastRejectingPrime

/-! # Three-elevenths Miller–Rabin witness bound under GRH -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite `n > 1` has a least rejecting prime at
most `max 2 ((3/11) * log n ^ 2)`. The uniform middle interval is supplied
by its cumulative theorem; the low, high and nonuniform cases use their
respective established bounds. -/
theorem three_eleven_least_of_grh {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  by_cases h10300 : Real.log n ≤ 10300
  · exact three_eleven_least_to10300 hn ho hc hGRH h10300
  have hL : (10300 : ℝ) ≤ Real.log n := le_of_not_ge h10300
  have hbound :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_cases hu : UniformKorseltTriple n
    · by_cases hU : Real.log n ≤ 4000000
      · exact uniform_three_eleven_to4m_grh hn ho hu hGRH hU
      · exact three_eleven_from_4m hn ho hc hGRH (le_of_not_ge hU)
    · obtain ⟨p, hp, hb, hf⟩ := quarter_nonuniform_log8 hn ho hc hu hGRH (by linarith only [hL])
      have hcoef : (1 / 4 : ℝ) ≤ 3 / 11 := by norm_num only
      exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  obtain ⟨p, hp, hb, hf⟩ := hbound
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH, the least prime rejecting an odd composite `n > 1` is at
most `max 2 ((3/11) * log n ^ 2)`. The least-prime specification transfers
the classified witness theorem to `compositeLeastPrime`. -/
theorem composite_least_prime_three_eleven_grh {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    (compositeLeastPrime n : ℝ) ≤ max 2 ((3 / 11 : ℝ) * Real.log n ^ 2) := by
  obtain ⟨p, hp, hb, hf, _⟩ := three_eleven_least_of_grh hn ho hc hGRH
  have hm := (compositeLeastPrime_spec hGRH hn ho hc).2.2 p hp hf
  exact (Nat.cast_le.mpr hm).trans hb

/-- Under GRH and `8 ≤ log n`, the least rejecting prime of an odd
composite `n > 1` is at most `(3/11) * log n ^ 2`. The logarithmic lower
bound makes this expression at least two, so the maximum is unnecessary. -/
theorem composite_least_prime_three_eleven_log8 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 8 ≤ Real.log n) :
    (compositeLeastPrime n : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 := by
  have hh := composite_least_prime_three_eleven_grh hn ho hc hGRH
  have hs : 0 ≤ (Real.log n - 8) ^ 2 := sq_nonneg _
  have hmax : (2 : ℝ) ≤ (3 / 11 : ℝ) * Real.log n ^ 2 := by nlinarith only [hs, hL]
  simpa only [max_eq_right hmax] using hh

end PseudoPrime.PrimeTestBounds.MillerRabin
