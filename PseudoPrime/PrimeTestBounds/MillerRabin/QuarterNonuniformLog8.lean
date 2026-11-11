/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterNonuniform200
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterJointPrimitive
import PseudoPrime.PrimeTestBounds.MillerRabin.LeastRejectingPrime

/-! # Nonuniform quarter-square bound on the half-line -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every nonuniform odd composite with logarithm at least 8 admits a
rejecting prime at most one quarter of the logarithm squared. The bounds below
and above 200 supply the two cases independently. -/
theorem quarter_nonuniform_log8 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hU : Real.log n ≤ 200
  · exact quarter_nonuniform_8_200 hn ho hc hu hGRH hL hU
  · exact quarter_nonuniform_high hn ho hc hu hGRH (le_of_not_ge hU)

/-- Under GRH, every nonuniform odd composite with logarithm at least 8 has a
least rejecting prime at most one quarter of its squared logarithm. Extract the
minimum from the half-line witness bound. -/
theorem quarter_nonuniform_least {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hu : ¬UniformKorseltTriple n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (8 : ℝ) ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject (quarter_nonuniform_log8 hn ho hc hu hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
