/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterIntersection200
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointPrimitive
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformClosed398375
import PseudoPrime.PrimeTestBounds.MillerRabin.Target028ResidualEndpoint

/-! # Logarithmic-scale witness for the 0.28 cutoff -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd composite of logarithmic scale at least eight has a
rejecting prime below the 0.28 cutoff. The quarter-square bound covers the
range through 200, and the existing high-scale bound covers larger inputs. -/
theorem exists_prime_reject_028_log8 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hcoef : (1 / 4 : ℝ) ≤ 7 / 25 := by norm_num only
  by_cases hU : Real.log n ≤ 200
  · obtain ⟨p, hp, hb, hf⟩ := quarter_all_8_200 hn ho hc hGRH hL hU
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
  · by_cases hu : UniformKorseltTriple n
    · by_cases h398 : Real.log n ≤ (3187 / 8 : ℝ)
      · obtain ⟨p, hp, hb, hf⟩ := quarter_uniform_8_398375 hn ho hu hGRH h398
        exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩
      · exact target028_uniform_high_witness hn ho hu hGRH (by linarith only [h398])
    · obtain ⟨p, hp, hb, hf⟩ := quarter_nonuniform_high hn ho hc hu hGRH (by linarith only [hU])
      exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
