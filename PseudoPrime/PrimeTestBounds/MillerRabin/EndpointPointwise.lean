/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.EndpointPointwise
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointFixed67

/-! # Fixed prime witness 61 with the pointwise reciprocal loss -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, every odd composite n>1 with log n<=2877/250 has a prime rejecting MR<=61.
Use an even character trivial on passing residues and its pointwise endpoint gap
at radius 1637/200. Round the resulting prime below 67 down to the bound 61. -/
theorem exists_prime_endpointPointwise61 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 2877 / 250) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ 61 ∧ ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  obtain ⟨χ, hne, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  have heven := character_even_of_trivial_on_pass hn ho hpass
  obtain ⟨p, hp, hb, hneone⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_pointwise χ hne heven hGRH
      (by norm_num only : (8 : ℝ) ≤ 1637 / 200) (LLS.PaperStatements.endpointPointwise61_gap hL)
  have h67 : (p : ℝ) < 67 := hb.trans_lt (by norm_num only)
  have h61 := prime_lt67_le61 hp (by exact_mod_cast h67)
  exact ⟨p, hp, by exact_mod_cast h61, fun h ↦ hneone (hpass p h)⟩

/-- Under the pointwise fixed-61 assumptions, the least rejecting prime is at most 61.
Extract the least prime from the actual rejection theorem. No factorization
or subgroup-index restriction is imposed. -/
theorem exists_least_endpointPointwise61 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : Real.log n ≤ 2877 / 250) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ 61 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn⟩
  exact
    exists_least_prime_reject_of_exists_prime_reject
      (exists_prime_endpointPointwise61 hn ho hc hGRH hL)

end PseudoPrime.PrimeTestBounds.MillerRabin
