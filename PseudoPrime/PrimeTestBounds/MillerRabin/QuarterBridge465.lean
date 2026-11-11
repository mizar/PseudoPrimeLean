/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridge200
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterFrom200
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointPrimitive
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformInterval3988
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite3988400
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite400410
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite410420
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite420430
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite430440
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite440450
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite450460
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformFinite460465
import PseudoPrime.PrimeTestBounds.MillerRabin.LeastRejectingPrime

/-! # Quarter-square bound through logarithmic scale 465 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite whose logarithm is at most 465 has a
rejecting prime bounded by the maximum of 2 and one quarter of its squared
logarithm. The small-input theorem and independent interval bounds cover all
cases. -/
theorem quarter_max_through465 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 465) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((1 / 4 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h200 : Real.log n ≤ 200
  · exact quarter_max_through200 hn ho hc hGRH h200
  have hL : (200 : ℝ) ≤ Real.log n := le_of_not_ge h200
  have hbound :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
    by_cases h39875 : Real.log n ≤ (1595 / 4 : ℝ)
    · exact quarter_from200_to39875 hn ho hc hGRH hL h39875
    by_cases hu : UniformKorseltTriple n
    · by_cases h3988 : Real.log n ≤ (1994 / 5 : ℝ)
      · exact quarter_uniform_39875_3988 hn ho hu hGRH (le_of_not_ge h39875) h3988
      by_cases h400 : Real.log n ≤ 400
      · exact quarter_uniform_3988_400 hn ho hu hGRH (le_of_not_ge h3988) h400
      by_cases h410 : Real.log n ≤ 410
      · exact quarter_uniform_400_410 hn ho hu hGRH (le_of_not_ge h400) h410
      by_cases h420 : Real.log n ≤ 420
      · exact quarter_uniform_410_420 hn ho hu hGRH (le_of_not_ge h410) h420
      by_cases h430 : Real.log n ≤ 430
      · exact quarter_uniform_420_430 hn ho hu hGRH (le_of_not_ge h420) h430
      by_cases h440 : Real.log n ≤ 440
      · exact quarter_uniform_430_440 hn ho hu hGRH (le_of_not_ge h430) h440
      by_cases h450 : Real.log n ≤ 450
      · exact quarter_uniform_440_450 hn ho hu hGRH (le_of_not_ge h440) h450
      by_cases h460 : Real.log n ≤ 460
      · exact quarter_uniform_450_460 hn ho hu hGRH (le_of_not_ge h450) h460
      exact quarter_uniform_460_465 hn ho hu hGRH (le_of_not_ge h460) hU
    · exact quarter_nonuniform_high hn ho hc hu hGRH hL
  obtain ⟨p, hp, hb, hf⟩ := hbound
  exact ⟨p, hp, hb.trans (le_max_right _ _), hf⟩

/-- Under GRH, for an odd composite whose logarithm is at most 465, the least
rejecting prime is bounded by the maximum of 2 and one quarter of the squared
logarithm. Extract the least witness from the bounded witness. -/
theorem quarter_least_through465 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hU : Real.log n ≤ 465) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 2 ((1 / 4 : ℝ) * Real.log n ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact exists_least_prime_reject_of_exists_prime_reject (quarter_max_through465 hn ho hc hGRH hU)

end PseudoPrime.PrimeTestBounds.MillerRabin
