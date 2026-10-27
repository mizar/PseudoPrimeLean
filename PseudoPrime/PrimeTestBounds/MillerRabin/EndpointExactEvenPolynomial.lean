/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.FullEndpointExactEvenRanges
public import PseudoPrime.PrimeTestBounds.MillerRabin.EndpointEvenPolynomial

/-! # Miller-Rabin bounds from the exact even endpoint -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For odd composites with log N <= 56/5, the exact even endpoint gives a
rejecting prime at most 61. -/
theorem exists_prime_reject_le_sixty_one_exact_even {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log N ≤ 56 / 5) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        p ≤ 61 ∧ (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨p, hp, hp64, hpow, hrest⟩ :=
    exists_prime_reject_le_even_shifted_sixty_four hn ho hc hGRH hL
  have hpNat : p ≤ 64 := by exact_mod_cast hp64
  have hp61 : p ≤ 61 := by
    by_contra hnot
    have hlo : 62 ≤ p := by omega
    interval_cases p <;> norm_num [Nat.Prime] at hp
  refine ⟨p, hp, hp61, hpow, hrest⟩

/-- Transfer a non-one prime supplied by an even character to a rejecting base
for every odd composite, preserving the canonical strong Miller-Rabin power form. -/
private theorem exists_prime_reject_of_even_character_bound {N : ℕ} [NeZero N] {B : ℝ} (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime)
    (hbound :
      ∀ χ : DirichletCharacter ℂ N, χ ≠ 1 → χ.Even → ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ B ∧ χ p ≠ 1) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ B ∧ (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨χ, hχ, hpass⟩ := exists_character_trivial_on_pass hn ho hc
  have heven := character_even_of_trivial_on_pass hn ho hpass
  obtain ⟨p, hp, hb, hv⟩ := hbound χ hχ heven
  have hreject : ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) := by
    intro hpPass
    exact hv (hpass p hpPass)
  have hform := PrimeTest.not_strongMillerRabinPass_iff.mp hreject
  exact ⟨p, hp, hb, hform.1, hform.2⟩

/-- In the first shifted logarithmic interval, every odd composite has a
rejecting prime bounded by the translated `64/81` quadratic. -/
theorem exists_prime_reject_le_sixtyFourEightyFirst_shifted_log_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 523 / 50 ≤ Real.log N) (hLhi : Real.log N ≤ 2171 / 100) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log N - 73 / 50) ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  exact
    exists_prime_reject_of_even_character_bound hn ho hc
      (fun χ hne heven =>
        LLS.PaperStatements.exists_prime_ne_one_le_sixtyFourEightyFirst_shifted_log_sq χ hne heven
          hGRH hLlo hLhi)

/-- On the second shifted interval, every odd composite has a rejecting prime
bounded by the translated `81/100` quadratic. -/
theorem exists_prime_reject_le_eightyOne_shifted_log_sq {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 523 / 50 ≤ Real.log N) (hLhi : Real.log N ≤ 1373 / 50) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log N - 73 / 50) ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  exact
    exists_prime_reject_of_even_character_bound hn ho hc
      (fun χ hne heven =>
        LLS.PaperStatements.exists_prime_ne_one_le_eightyOne_shifted_log_sq χ hne heven hGRH hLlo
          hLhi)

/-- For `log N <= 144/5`, every odd composite has a rejecting prime at most
576. -/
theorem exists_prime_reject_le_576_exact_even {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log N ≤ 144 / 5) :
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℕ) ≤ 576 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_le_even_shifted_fiveHundredSeventySix hn ho hc hGRH hL
  have hnat : p ≤ 576 := by exact_mod_cast hb
  exact ⟨p, hp, hnat, hpow, hrest⟩

/-- On the translated five-piece interval, every odd composite has a rejecting
prime bounded by the shifted midscale radius. -/
theorem exists_prime_reject_le_shifted_midscale_radius_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 706 / 25 ≤ Real.log N) (hLhi : Real.log N ≤ 5283 / 20) :
    let y := LLS.PaperStatements.midscaleEndpointRadius (Real.log N - 73 / 50)
    let (s, a) := Nat.maxPowDvdDiv 2 (N - 1)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ y ^ 2 ∧
        (p : ZMod N) ^ a ≠ 1 ∧ ∀ j : ℕ, j < s → (p : ZMod N) ^ (2 ^ j * a) ≠ -1 := by
  exact
    exists_prime_reject_of_even_character_bound hn ho hc
      (fun χ hne heven => by
        obtain ⟨p, hp, hb, hv⟩ :=
          LLS.PaperStatements.exists_prime_ne_one_le_shifted_midscale_radius_sq χ hne heven hGRH
            hLlo hLhi
        exact ⟨p, hp, hb, hv⟩)

/-- The least rejecting prime also satisfies the exact-even radius-eight bound. -/
theorem exists_least_prime_reject_le_sixty_one_exact_even {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log N ≤ 56 / 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℕ) ≤ 61 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ := exists_prime_reject_le_sixty_one_exact_even hn ho hc hGRH hL
  have hreal : (p : ℝ) ≤ 61 := by exact_mod_cast hb
  obtain ⟨p, hp, hreal, hreject, hmin⟩ :=
    exists_least_prime_reject_of_exists_prime_reject
      ⟨p, hp, hreal, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩
  have hnat : p ≤ 61 := by exact_mod_cast hreal
  exact ⟨p, hp, hnat, hreject, hmin⟩

/-- Least-prime version of the first exact-even shifted quadratic bound. -/
theorem exists_least_prime_reject_le_sixtyFourEightyFirst_shifted_log_sq {N : ℕ} [NeZero N]
    (hn : 1 < N) (ho : Odd N) (hc : ¬N.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 523 / 50 ≤ Real.log N)
    (hLhi : Real.log N ≤ 2171 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log N - 73 / 50) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_le_sixtyFourEightyFirst_shifted_log_sq hn ho hc hGRH hLlo hLhi
  exact
    exists_least_prime_reject_of_exists_prime_reject
      ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩

/-- Least-prime version of the second exact-even shifted quadratic bound. -/
theorem exists_least_prime_reject_le_eightyOne_shifted_log_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 523 / 50 ≤ Real.log N) (hLhi : Real.log N ≤ 1373 / 50) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log N - 73 / 50) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_le_eightyOne_shifted_log_sq hn ho hc hGRH hLlo hLhi
  exact
    exists_least_prime_reject_of_exists_prime_reject
      ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩

/-- Least-prime version of the exact-even fixed radius-24 bound. -/
theorem exists_least_prime_reject_le_576_exact_even {N : ℕ} [NeZero N] (hn : 1 < N) (ho : Odd N)
    (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : Real.log N ≤ 144 / 5) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℕ) ≤ 576 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ := exists_prime_reject_le_576_exact_even hn ho hc hGRH hL
  have hreal : (p : ℝ) ≤ 576 := by exact_mod_cast hb
  obtain ⟨p, hp, hreal, hreject, hmin⟩ :=
    exists_least_prime_reject_of_exists_prime_reject
      ⟨p, hp, hreal, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩
  have hnat : p ≤ 576 := by exact_mod_cast hreal
  exact ⟨p, hp, hnat, hreject, hmin⟩

/-- Least-prime version of the exact-even shifted midscale radius bound. -/
theorem exists_least_prime_reject_le_shifted_midscale_radius_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 706 / 25 ≤ Real.log N) (hLhi : Real.log N ≤ 5283 / 20) :
    let y := LLS.PaperStatements.midscaleEndpointRadius (Real.log N - 73 / 50)
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ y ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  dsimp only
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_le_shifted_midscale_radius_sq hn ho hc hGRH hLlo hLhi
  exact
    exists_least_prime_reject_of_exists_prime_reject
      ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩

/-- The five-piece endpoint radius with shift `7/4` gives a rejecting prime
through its square for levels from `144/5` to `13517/100`. The upper endpoint
keeps the radius at most 128, where the three-band transfer applies. -/
theorem exists_prime_reject_le_7over4_shifted_midscale_radius_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 144 / 5 ≤ Real.log N) (hLhi : Real.log N ≤ 13517 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (LLS.PaperStatements.midscaleEndpointRadius (Real.log N - 7 / 4)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_of_even_character_bound hn ho hc
      (fun χ hne heven => by
        obtain ⟨p, hp, hb, hv⟩ :=
          LLS.PaperStatements.exists_prime_ne_one_le_7over4_shifted_midscale_radius_sq χ hne heven
            hGRH hLlo hLhi
        exact ⟨p, hp, hb, hv⟩)
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩

/-- Least-prime version of the `7/4` shifted five-piece endpoint bound. -/
theorem exists_least_prime_reject_le_7over4_shifted_midscale_radius_sq {N : ℕ} [NeZero N]
    (hn : 1 < N) (ho : Odd N) (hc : ¬N.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 144 / 5 ≤ Real.log N)
    (hLhi : Real.log N ≤ 13517 / 100) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (LLS.PaperStatements.midscaleEndpointRadius (Real.log N - 7 / 4)) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hreject⟩ :=
    exists_prime_reject_le_7over4_shifted_midscale_radius_sq hn ho hc hGRH hLlo hLhi
  exact exists_least_prime_reject_of_exists_prime_reject ⟨p, hp, hb, hreject⟩

/-- Every odd composite from logarithmic scale `43/4` through `22` has a
rejecting prime below the `64/81` quadratic shifted by `7/4`. -/
theorem exists_prime_reject_le_7over4_shifted_eightNinths_log_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 43 / 4 ≤ Real.log N) (hLhi : Real.log N ≤ 22) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log N - 7 / 4) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_of_even_character_bound hn ho hc
      (fun χ hne heven => by
        obtain ⟨p, hp, hb, hv⟩ :=
          LLS.PaperStatements.exists_prime_ne_one_le_7over4_shifted_eightNinths_log_sq χ hne heven
            hGRH hLlo hLhi
        exact ⟨p, hp, hb, hv⟩)
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩

/-- The least rejecting prime inherits the `64/81` seven-fourths shifted
quadratic bound on the interval `43/4 ≤ log N ≤ 22`. -/
theorem exists_least_prime_reject_le_7over4_shifted_eightNinths_log_sq {N : ℕ} [NeZero N]
    (hn : 1 < N) (ho : Odd N) (hc : ¬N.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hLlo : 43 / 4 ≤ Real.log N)
    (hLhi : Real.log N ≤ 22) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (64 / 81 : ℝ) * (Real.log N - 7 / 4) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hreject⟩ :=
    exists_prime_reject_le_7over4_shifted_eightNinths_log_sq hn ho hc hGRH hLlo hLhi
  exact exists_least_prime_reject_of_exists_prime_reject ⟨p, hp, hb, hreject⟩

/-- Every odd composite from logarithmic scale `43/4` through `111/4` has a
rejecting prime below the `81/100` quadratic shifted by `7/4`. -/
theorem exists_prime_reject_le_7over4_shifted_eightyOne_log_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 43 / 4 ≤ Real.log N) (hLhi : Real.log N ≤ 111 / 4) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log N - 7 / 4) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) := by
  obtain ⟨p, hp, hb, hpow, hrest⟩ :=
    exists_prime_reject_of_even_character_bound hn ho hc
      (fun χ hne heven => by
        obtain ⟨p, hp, hb, hv⟩ :=
          LLS.PaperStatements.exists_prime_ne_one_le_7over4_shifted_eightyOne_log_sq χ hne heven
            hGRH hLlo hLhi
        exact ⟨p, hp, hb, hv⟩)
  exact ⟨p, hp, hb, PrimeTest.not_strongMillerRabinPass_iff.mpr ⟨hpow, hrest⟩⟩

/-- The least rejecting prime inherits the `81/100` seven-fourths shifted
quadratic bound on the interval `43/4 ≤ log N ≤ 111/4`. -/
theorem exists_least_prime_reject_le_7over4_shifted_eightyOne_log_sq {N : ℕ} [NeZero N] (hn : 1 < N)
    (ho : Odd N) (hc : ¬N.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hLlo : 43 / 4 ≤ Real.log N) (hLhi : Real.log N ≤ 111 / 4) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (81 / 100 : ℝ) * (Real.log N - 7 / 4) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass N (p : ZMod N) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass N (q : ZMod N) → p ≤ q := by
  obtain ⟨p, hp, hb, hreject⟩ :=
    exists_prime_reject_le_7over4_shifted_eightyOne_log_sq hn ho hc hGRH hLlo hLhi
  exact exists_least_prime_reject_of_exists_prime_reject ⟨p, hp, hb, hreject⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
