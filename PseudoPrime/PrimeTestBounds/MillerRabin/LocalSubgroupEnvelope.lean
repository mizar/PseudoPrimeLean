/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Theorem11S2
public import PseudoPrime.PrimeTest.MillerRabin.Composite

/-! # General local subgroup witness envelope -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a proper subgroup at a divisor modulus q≥2 containing every
ambient strong-pass image gives a failing prime base at most max(3000,log(q)²).
If the local modulus or a prime divisor is small, use that ambient prime divisor;
otherwise apply LLS S2 and exclude passage by the local containment premise.
This is the local-to-global witness bridge used by the finite-index branches. -/
theorem exists_prime_witness_le_local_subgroup_envelope {n q : ℕ} [NeZero q] (hn : 1 < n)
    (hnOdd : Odd n) (hq : 2 ≤ q) (hqn : q ∣ n) (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ max 3000 ((Real.log q) ^ 2) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hlarge : 3000 ≤ q
  · by_cases hsmall : ∃ p : ℕ, p.Prime ∧ (p : ℝ) < (Real.log q) ^ 2 ∧ p ∣ q
    · obtain ⟨p, hp, hb, hd⟩ := hsmall
      exact
        ⟨p, hp, hb.le.trans (le_max_right _ _),
          PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp (dvd_trans hd hqn)⟩
    · have hno : ∀ p : ℕ, p.Prime → (p : ℝ) < (Real.log q) ^ 2 → ¬p ∣ q := by
        intro p hp hb hd
        exact hsmall ⟨p, hp, hb, hd⟩
      obtain ⟨p, hp, hb, hout⟩ := LLS.llsTheorem11S2_of_grh hGRH q hlarge hno H hH
      refine ⟨p, hp, hb.trans (le_max_right _ _), ?_⟩
      intro hyes
      exact hout (hpass p hyes)
  · obtain ⟨p, hp, hd⟩ :=
      Nat.exists_prime_and_dvd (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 1 < 2) hq))
    have hpq := Nat.le_of_dvd (NeZero.pos q) hd
    have hb : (p : ℝ) ≤ 3000 := Nat.cast_le.mpr (hpq.trans (Nat.le_of_lt (lt_of_not_ge hlarge)))
    exact
      ⟨p, hp, hb.trans (le_max_left _ _),
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn hnOdd hp (dvd_trans hd hqn)⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
