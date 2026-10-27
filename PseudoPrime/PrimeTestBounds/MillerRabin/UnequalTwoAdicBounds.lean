/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.UnequalTwoAdicSquares
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalSubgroupBounds

/-! # Coefficient 0.282924 for unequal predecessor two-adic valuations

A larger-valuation Korselt prime factor sees every strong pass as a local square.
The smaller-valuation prime factor supplies the sign constraint. The resulting
proper local subgroup gives the explicit 10^142 coefficient bound.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH for odd composite n≥10^142, two prime factors with strictly
different predecessor two-adic valuations give a failing prime base at most
(282924/1000000)log(n)² if the larger-valuation factor satisfies Korselt divisibility.
Every strong pass reduces into its proper local half-exponent kernel, and
the Korselt factor is at most sqrt(n). Neither a global finite-index premise
nor a supplied local size or containment premise is needed in this branch. -/
theorem exists_prime_witness_le_0283_of_unequal_twoAdic_prime_factors {n p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hnOdd : Odd n) (hcomp : ¬n.Prime) (hpn : p ∣ n) (hqn : q ∣ n)
    (hKorselt : p - 1 ∣ n - 1) (hv : padicValNat 2 (q - 1) < padicValNat 2 (p - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 142) hn
  have hpOdd := hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn)
  have hqOdd := hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn)
  have hs := PrimeTest.prime_factor_square_le_of_korselt hn1 hcomp hpn hKorselt
  have hsize : p ^ 2 ≤ 10 ^ 9 * n := hs.trans (Nat.le_mul_of_pos_left n (by decide : 0 < 10 ^ 9))
  exact
    exists_prime_witness_le_0283_of_local_subgroup hnOdd hp.two_le hpn
      (powMonoidHom (p / 2) : (ZMod p)ˣ →* (ZMod p)ˣ).ker
      (PrimeTest.local_half_powerKernel_ne_top hpOdd)
      (fun a ha ↦
        PrimeTest.strongMillerRabinPass_mem_local_half_kernel_of_twoAdic_lt hn1 hnOdd hpOdd hqOdd
          hpn hqn hv ha)
      hGRH hn hsize

end PseudoPrime.PrimeTestBounds.MillerRabin
