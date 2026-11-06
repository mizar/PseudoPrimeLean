/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030UniformLow
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030SquareCoverage
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030UniformGaussian

/-! # Combined established 0.30 ranges -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite with logarithm in `[8, 10.614]` has a
0.30 rejecting prime. Square divisors, uniform Korselt triples, and the
remaining squarefree inputs are covered by their respective witness theorems. -/
theorem exists_prime_reject_03_log8_to_10614 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 10614 / 1000) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact
      exists_prime_reject_03_square_8_to_1304 hn ho hp hd hGRH.riemann hL (by linarith only [hU])
  · have hsf : Squarefree n :=
      Nat.squarefree_iff_prime_squarefree.mpr (fun p hp h ↦ hsq ⟨p, hp, (pow_two p).symm ▸ h⟩)
    by_cases hu : UniformKorseltTriple n
    · exact uniformKorselt_reject_03_low hn ho hu hGRH hL (by linarith only [hU])
    · exact exists_prime_reject_03_nonuniform_squarefree hn ho hc hsf hu hGRH hL hU

/-- Under GRH, every odd composite with logarithm at least 8 has a 0.30
rejecting prime on the currently combined low and high ranges. The disjunction
explicitly retains the unproved intermediate range. -/
theorem exists_prime_reject_03_established_ranges {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hcover : Real.log n ≤ 10614 / 1000 ∨ 5250 ≤ Real.log n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  rcases hcover with hlow | hhigh
  · exact exists_prime_reject_03_log8_to_10614 hn ho hc hGRH hL hlow
  · exact exists_prime_reject_03_log5250 hn ho hc hGRH hhigh

end PseudoPrime.PrimeTestBounds.MillerRabin
