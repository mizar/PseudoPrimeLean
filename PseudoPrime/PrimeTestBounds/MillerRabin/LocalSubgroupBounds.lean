/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalSubgroupEnvelope
public import PseudoPrime.PrimeTestBounds.MillerRabin.Local282924Numerics

/-! # Local divisor subgroup bounds for coefficient 0.282924

A proper subgroup at a divisor modulus supplies an ambient MR witness.
The explicit finite-index size bound q²≤10^9*n gives coefficient 282924/1000000
at n≥10^142, including small local moduli through prime-factor witnesses.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd n≥10^142, a proper local subgroup at q dividing n gives a failing
prime base at most (282924/1000000)log(n)² if q²≤10^9*n and all strong passes reduce
into the subgroup. Combine the local LLS envelope with the strict numerical bound.
This retains the arithmetic size and containment inputs for branch classification. -/
theorem exists_prime_local_0282924 {n q : ℕ} [NeZero q] (hnOdd : Odd n) (hq : 2 ≤ q) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n)
    (hsize : q ^ 2 ≤ 10 ^ 9 * n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 142) hn
  obtain ⟨p, hp, hb, hfail⟩ :=
    exists_prime_witness_le_local_subgroup_envelope hn1 hnOdd hq hqn H hH hpass hGRH
  exact ⟨p, hp, (hb.trans_lt (local_envelope_lt_of_square_le hn (NeZero.pos q) hsize)).le, hfail⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
