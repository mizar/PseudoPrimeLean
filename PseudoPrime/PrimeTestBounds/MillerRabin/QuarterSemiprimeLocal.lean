/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.Decomposition
public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
import PseudoPrime.PrimeTestBounds.MillerRabin.SemiprimeSmallFactor
import PseudoPrime.PrimeTestBounds.MillerRabin.LocalEvenAnchors

/-! # Local-anchor witness for semiprimes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, an odd product of ordered distinct primes whose larger
factor has logarithm at most 11.249 admits a rejecting prime at most 61.
A proper local Fermat kernel and the radius-eight anchor yield a prime at
most 64, which primality rounds down to 61. -/
theorem semiprime_local_anchor61 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (11249 / 1000 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 61 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero q := ⟨Nat.ne_zero_of_lt hq.pos⟩
  let : Fact q.Prime := ⟨hq⟩
  have hqn : q ∣ n := hprod ▸ dvd_mul_left q p
  have hbad : ¬q - 1 ∣ n - 1 := by
    rw [hprod]
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
  let H := (powMonoidHom (n - 1) : (ZMod q)ˣ →* (ZMod q)ˣ).ker
  have hproper : H ≠ ⊤ := NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hbad
  have hpass :
    ∀ a : ℕ,
      PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
        ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q) := by
    intro a ha
    exact PrimeTest.strongMR_local_divisorKernel hn ho hqn ha
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_anchor hn ho hqn H hproper hpass hGRH (b := 8) (d :=
      324969 / 100000) (j := 3) (by decide +kernel) hqlog
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hb
  have hmax : max (8 : ℝ) (11249 / 1000 - 324969 / 100000) ≤ 8 := by apply max_le <;> norm_num only
  have hr64 : (r : ℝ) ≤ 64 := by
    nlinarith only [hb, hmax, le_max_left (8 : ℝ) (11249 / 1000 - 324969 / 100000)]
  have hr64n : r ≤ 64 := by exact_mod_cast hr64
  have hr61 : r ≤ 61 := by
    by_contra h
    have hnp : ∀ k ∈ Finset.Icc 62 64, ¬Nat.Prime k := by decide +kernel
    exact hnp r (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge h), hr64n⟩) hr
  exact ⟨r, hr, hr61, hf⟩

/-- Under GRH, an odd product of ordered distinct primes whose larger
factor has logarithm at most 13.6 admits a rejecting prime at most 97.
A proper local Fermat kernel and the radius-ten anchor yield a prime at
most 100, which primality rounds down to 97. -/
theorem semiprime_local_anchor97 {n p q : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime) (hq : q.Prime)
    (hpq : p < q) (hprod : n = p * q) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hqlog : Real.log q ≤ (68 / 5 : ℝ)) :
    ∃ r : ℕ, r.Prime ∧ r ≤ 97 ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  let : NeZero q := ⟨Nat.ne_zero_of_lt hq.pos⟩
  let : Fact q.Prime := ⟨hq⟩
  have hqn : q ∣ n := hprod ▸ dvd_mul_left q p
  have hbad : ¬q - 1 ∣ n - 1 := by
    rw [hprod]
    exact NumberTheory.not_sub_one_dvd_prime_mul_sub_one_of_lt hp hq hpq
  let H := (powMonoidHom (n - 1) : (ZMod q)ˣ →* (ZMod q)ˣ).ker
  have hproper : H ≠ ⊤ := NumberTheory.local_prime_powerKernel_ne_top_of_not_dvd hbad
  have hpass :
    ∀ a : ℕ,
      PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
        ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q) := by
    intro a ha
    exact PrimeTest.strongMR_local_divisorKernel hn ho hqn ha
  have hc :=
    localCorrectionCheck_sound
      (show localCorrectionCheck (10) (36001 / 10000) 4 = true by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hc
  have hd : (18 / 5 : ℝ) < LLS.PaperStatements.fullEndpointEvenGapCorrection (10 : ℝ) := by
    linarith only [hc]
  obtain ⟨r, hr, hb, hf⟩ :=
    exists_prime_reject_of_local_shift hn ho hqn H hproper hpass hGRH (b := 10) (d := 18 / 5)
      (by norm_num only) hd hqlog
  have hmax : max (10 : ℝ) (68 / 5 - 18 / 5) ≤ 10 := by apply max_le <;> norm_num only
  have hr100 : (r : ℝ) ≤ 100 := by nlinarith only [hb, hmax, le_max_left (10 : ℝ) (68 / 5 - 18 / 5)]
  have hr100n : r ≤ 100 := by exact_mod_cast hr100
  have hr97 : r ≤ 97 := by
    by_contra h
    have hnp : ∀ k ∈ Finset.Icc 98 100, ¬Nat.Prime k := by decide +kernel
    exact hnp r (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge h), hr100n⟩) hr
  exact ⟨r, hr, hr97, hf⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
