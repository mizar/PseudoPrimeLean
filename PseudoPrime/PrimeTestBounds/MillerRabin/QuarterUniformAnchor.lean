/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterUniformLow

/-! # Local-anchor witnesses on the next uniform-triple range -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A proper local subgroup at a divisor of logarithmic size at most two thirds
of the input gives a quarter-square witness on scales 15.621 through 19.498. The radius-8 anchor
gives a prime at most 64, and primality improves this to 61. -/
theorem quarter_local_anchor {n q : ℕ} [NeZero q] (hn : 1 < n) (ho : Odd n) (hqn : q ∣ n)
    (H : Subgroup (ZMod q)ˣ) (hH : H ≠ ⊤)
    (hpass :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod q)ˣ, u ∈ H ∧ (u : ZMod q) = (a : ZMod q))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (15621 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9749 / 500)
    (hq : Real.log q ≤ (2 / 3 : ℝ) * Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  obtain ⟨p, hp, hpbound, hfail⟩ :=
    exists_prime_reject_of_local_anchor hn ho hqn H hH hpass hGRH (b := 8) (d := 324969 / 100000)
      (j := 3) (by decide +kernel) hq
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hpbound
  by_cases hsmall : Real.log n ≤ 84 / 5
  · have hmax : max (8 : ℝ) ((2 / 3 : ℝ) * Real.log n - 324969 / 100000) ≤ 8 := by
      apply max_le le_rfl
      linarith only [hsmall]
    have hp64 : (p : ℝ) ≤ 64 := by
      nlinarith only [hpbound, hmax,
        le_max_left (8 : ℝ) ((2 / 3 : ℝ) * Real.log n - 324969 / 100000)]
    have hp64n : p ≤ 64 := by exact_mod_cast hp64
    have hp61 : p ≤ 61 := by
      by_contra h
      have hnp : ∀ k ∈ Finset.Icc 62 64, ¬Nat.Prime k := by decide +kernel
      exact hnp p (Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt (Nat.lt_of_not_ge h), hp64n⟩) hp
    have hb : (61 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
    exact ⟨p, hp, (Nat.cast_le.mpr hp61).trans hb, hfail⟩
  · have hbig : (16 : ℝ) ≤ Real.log n := by linarith only [hsmall]
    have hmax : max (8 : ℝ) ((2 / 3 : ℝ) * Real.log n - 324969 / 100000) ≤ Real.log n / 2 := by
      apply max_le
      · linarith only [hbig]
      · linarith only [hU]
    have hnonneg : (0 : ℝ) ≤ max 8 ((2 / 3 : ℝ) * Real.log n - 324969 / 100000) :=
      (by norm_num only : (0 : ℝ) ≤ 8).trans (le_max_left _ _)
    have hs := pow_le_pow_left₀ hnonneg hmax 2
    have hb : (p : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hpbound, hs]
    exact ⟨p, hp, hb, hfail⟩

/-- Under GRH, an odd integer with at least three prime factors counted with
multiplicity has a quarter-square witness on logarithmic scales 15.621 through 19.498. The two
smallest factors provide a divisor to which the local subgroup bound applies. -/
theorem quarter_three_anchor {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hk : 3 ≤ ArithmeticFunction.cardFactors n) (hL : (15621 / 1000 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 9749 / 500) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hk2 : 2 ≤ n.primeFactorsList.length := by
    change 2 ≤ ArithmeticFunction.cardFactors n
    exact le_trans (by norm_num only) hk
  obtain ⟨p, q, hp, hq, hd, hm⟩ :=
    NumberTheory.exists_prime_pair_log_mean (Nat.zero_lt_of_lt hn) hk2
  have hkR : (3 : ℝ) ≤ ArithmeticFunction.cardFactors n := Nat.cast_le.mpr hk
  have hkpos : (0 : ℝ) < ArithmeticFunction.cardFactors n := by linarith only [hkR]
  have hlog :
    Real.log ((p * q : ℕ) : ℝ) ≤ 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) := by
    apply (le_div_iff₀ hkpos).mpr
    simpa only [ArithmeticFunction.cardFactors_apply, mul_comm] using hm
  have hratio : 2 * Real.log n / (ArithmeticFunction.cardFactors n : ℝ) ≤ 2 * Real.log n / 3 :=
    div_le_div_of_nonneg_left (mul_nonneg (by norm_num only) (Real.log_natCast_nonneg n))
      (by norm_num only) hkR
  rcases prime_pair_local_data hn ho hp hq hd with hthree | ⟨s, hs, hsn, hsp, H, hproper, hpass⟩
  · have hbound : (3 : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
    exact
      ⟨3, Nat.prime_three, hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · let : NeZero s := ⟨Nat.ne_zero_of_lt hs⟩
    have hslog : Real.log s ≤ (2 / 3 : ℝ) * Real.log n := by
      have h :=
        (Real.log_le_log (Nat.cast_pos.mpr hs) (Nat.cast_le.mpr hsp)).trans (hlog.trans hratio)
      linarith only [h]
    exact quarter_local_anchor hn ho hsn H hproper hpass hGRH hL hU hslog

/-- Under GRH, a uniform Korselt triple with logarithmic scale from 15.621
to 19.498 has a quarter-square rejecting prime. Squarefreeness identifies the
number of prime factors with the multiplicity-counted factor number. -/
theorem quarter_uniform_anchor {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (15621 / 1000 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9749 / 500) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (1 / 4 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  have hlist : n.primeFactorsList.Nodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList (Nat.ne_zero_of_lt hn)).mp hu.1
  have heq : n.primeFactors.card = ArithmeticFunction.cardFactors n := by
    change n.primeFactorsList.toFinset.card = n.primeFactorsList.length
    exact List.toFinset_card_of_nodup hlist
  have hk : 3 ≤ ArithmeticFunction.cardFactors n := by rw [← heq, hu.2.1]
  exact quarter_three_anchor hn ho hGRH hk hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
