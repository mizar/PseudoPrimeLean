/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointEightyOneRange
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointPolynomial

/-! # Analytic MR bounds through sixty-one and eighty-one percent -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd composite N>1 under GRH with 9<=log N<=26, a prime through
(81/100)(log N)^2 rejects the canonical strong test. Choose a character trivial on
passing residues and apply the continuous endpoint character theorem.
This strengthens the finite-scale analytic MR bound without input enumeration. -/
theorem exists_prime_reject_le_eightyOne_log_sq {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL9 : 9 ≤ Real.log N) (hL26 : Real.log N ≤ 26) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log N) ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨χ, hχ, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  obtain ⟨p, hp, hb, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_le_eightyOne_log_sq χ hχ hGRH hL9 hL26
  refine ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp ?_⟩
  intro ha
  exact hv (hpass p ha)

/-- For odd composite N>1 under GRH with log N<=9, a prime at most sixty-one
rejects the canonical strong test. Apply the original-level character bound to a
character trivial on passing residues. This uses a uniform analytic endpoint certificate. -/
theorem exists_prime_reject_le_sixty_one_of_log_le_nine {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL9 : Real.log N ≤ 9) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        p ≤ 61 ∧ (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨χ, hχ, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  obtain ⟨p, hp, hb, hv⟩ :=
    LLS.PaperStatements.exists_prime_ne_one_le_sixty_one_of_log_le_nine χ hχ hGRH hL9
  refine ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mp ?_⟩
  intro ha
  exact hv (hpass p ha)

/-- Under the coefficient-81/100 interval assumptions, the least rejecting prime
has the same bound and is minimal among all rejecting primes. Minimize the rejection
predicate after constructing a witness. This connects the analytic bound with record tables. -/
theorem exists_least_prime_reject_le_eightyOne_log_sq {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL9 : 9 ≤ Real.log N) (hL26 : Real.log N ≤ 26) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log N) ^ 2 ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass N (r : ZMod N) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hpow, hall⟩ := exists_prime_reject_le_eightyOne_log_sq hn ho hc hGRH hL9 hL26
  have hf := PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hall⟩
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass N (r : ZMod N) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hf⟩)).trans hb, fun r hr hf ↦
      Nat.find_min' hex ⟨hr, hf⟩⟩

/-- Under the log N<=9 assumptions, the least rejecting prime is at most sixty-one
and minimal among all rejecting primes. Minimize the rejection predicate and retain the
natural-number cutoff. No finite classification of composite inputs is used. -/
theorem exists_least_prime_reject_le_sixty_one {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL9 : Real.log N ≤ 9) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        p ≤ 61 ∧ ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass N (r : ZMod N) → p ≤ r := by
  classical
  obtain ⟨p, hp, hb, hpow, hall⟩ :=
    exists_prime_reject_le_sixty_one_of_log_le_nine hn ho hc hGRH hL9
  have hf := PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hall⟩
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass N (r : ZMod N) := ⟨p, hp, hf⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      Nat.le_trans (Nat.find_min' hex ⟨hp, hf⟩) hb, fun r hr hf ↦ Nat.find_min' hex ⟨hr, hf⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
