/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEightNinthsRange
public import PseudoPrime.PrimeTestBounds.MillerRabin.FullEndpointEightyOneRange

/-! # Prime MR rejecting witnesses from the eight-ninths endpoint radius -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For an odd composite N>1 under GRH and 9<=log N<=81/4, a prime base
through (64/81)(log N)^2 rejects the canonical strong test. Use a character
trivial on passing residues and the sharper original-level endpoint polynomial. -/
theorem exists_prime_reject_le_eightNinths_log_sq {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL9 : 9 ≤ Real.log N) (hU : Real.log N ≤ (81 / 4 : ℝ)) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log N) ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨χ, hχ, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  obtain ⟨p, hp, hb, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_le_eightNinths_log_sq χ hχ hGRH hL9 hU
  refine ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp ?_⟩
  intro ha
  exact hv (hpass p ha)

/-- Under the eight-ninths radius interval hypotheses, a least rejecting prime
satisfies the coefficient-64/81 bound and is minimal among every rejecting prime.
Construct one rejecting base, then minimize the full prime-rejection predicate. -/
theorem exists_least_prime_reject_le_eightNinths_log_sq {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL9 : 9 ≤ Real.log N) (hU : Real.log N ≤ (81 / 4 : ℝ)) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log N) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass N (r : ZMod N) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hpow, hall⟩ := exists_prime_reject_le_eightNinths_log_sq hn ho hc hGRH hL9 hU
  have hf := PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hall⟩
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass N (r : ZMod N) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
