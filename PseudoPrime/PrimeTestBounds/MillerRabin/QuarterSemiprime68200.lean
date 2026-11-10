/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterInteriorWitness

/-! # Semiprime witnesses from 68 to 200 -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd product of two distinct ordered primes with logarithm between
68 and 200 has a quarter-square rejecting prime. It has exactly two prime factors,
so the nonuniform interval applies. -/
theorem quarter_semiprime_68_200 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (68 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 200) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (1 / 4 : ℝ) * Real.log n ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hc : ¬n.Prime := by
    rw [hprod]
    exact Nat.not_prime_mul hp.ne_one hq.ne_one
  have hcard : n.primeFactors.card = 2 := by
    rw [hprod, Nat.primeFactors_mul hp.ne_zero hq.ne_zero, hp.primeFactors, hq.primeFactors]
    simpa only [Finset.singleton_union] using Finset.card_pair hpq.ne
  have hu : ¬UniformKorseltTriple n := fun h ↦ by
    have h' := h.2.1
    rw [hcard] at h'
    norm_num only at h'
  exact quarter_common_nonuniform_mid hn ho hc hu hGRH hL hU le_rfl

end PseudoPrime.PrimeTestBounds.MillerRabin
