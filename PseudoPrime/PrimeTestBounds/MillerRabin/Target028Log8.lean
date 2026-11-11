/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniformLog8
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterBridge465
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
  by_cases h465 : Real.log n ≤ 465
  · obtain ⟨p, hp, hb, hf⟩ := quarter_max_through465 hn ho hc hGRH h465
    have htwo : (2 : ℝ) ≤ (7 / 25 : ℝ) * Real.log n ^ 2 := by
      nlinarith only [hL, sq_nonneg (Real.log n - 8)]
    exact ⟨p, hp, hb.trans (max_le htwo (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))), hf⟩
  by_cases hu : UniformKorseltTriple n
  · exact target028_uniform_high_witness hn ho hu hGRH (by linarith only [h465])
  · obtain ⟨p, hp, hb, hf⟩ := quarter_nonuniform_log8 hn ho hc hu hGRH hL
    exact ⟨p, hp, hb.trans (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _)), hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
