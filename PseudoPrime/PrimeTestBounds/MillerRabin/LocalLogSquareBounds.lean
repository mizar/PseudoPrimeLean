/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalSubgroupBounds
public import PseudoPrime.LLS.Part2FromFive

/-! # Local MR log-square bounds without a fixed finite envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a proper subgroup at a divisor modulus q at least five
containing every ambient strong pass gives an actual prime failing base at most
log(q)^2. A small local prime divisor already fails; otherwise use LLS from five.
This removes the constant 3000 from the local subgroup envelope. -/
theorem exists_prime_witness_le_local_log_sq {n q : ℕ} [NeZero q] (hn : 1 < n) (hnOdd : Odd n)
    (hq : 5 ≤ q) (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧ (p : ℝ) ≤ (Real.log q) ^ 2 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hs : ∃ p : ℕ, p.Prime ∧ (p : ℝ) < (Real.log q) ^ 2 ∧ p ∣ q
  · obtain ⟨p, hp, hb, hd⟩ := hs
    exact
      ⟨p, hp, hb.le, PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp (hd.trans hqn)⟩
  · have hno (p : ℕ) (hp : p.Prime) (hb : (p : ℝ) < (Real.log q) ^ 2) : ¬p ∣ q := fun hd ↦
      hs ⟨p, hp, hb, hd⟩
    obtain ⟨p, hp, hb, hout⟩ := LLS.llsTheorem11S2_from_five_of_grh hGRH q hq hno H hH
    exact ⟨p, hp, hb, fun hyes ↦ hout (hpass p hyes)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
