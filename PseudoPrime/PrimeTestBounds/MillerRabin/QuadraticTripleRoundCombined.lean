/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleRoundWitness
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleLowCombined

/-! # Prime-rounding bridge for the 0.30 target -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Every odd uniform Korselt triple on `[39.46,39.908]` has, under GRH, a
rejecting prime within the coefficient `3/10` cutoff. The spacing correction
supplies the pointwise pair level; the fixed radius rounds its prime below 479
down to 467. The factor three is treated directly. -/
theorem uniformKorselt_reject_round {n : ℕ} (hn : 1 < n) (ho : Odd n) (hu : UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : (1973 / 50 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 9977 / 250) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  obtain ⟨p, q, r, hp, hq, hr, hpq, hqr, hnp⟩ := uniformKorselt_ordered_factors hu
  have hpn : p ∣ n := hnp ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hqn : q ∣ n := hnp ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrn : r ∣ n := hnp ▸ dvd_mul_left r (p * q)
  have hp2 := ho.ne_two_of_dvd_nat hpn
  have hq2 := ho.ne_two_of_dvd_nat hqn
  have hr2 := ho.ne_two_of_dvd_nat hrn
  by_cases hp3 : p = 3
  · have hthree : 3 ∣ n := hp3 ▸ hpn
    have hbound : (3 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
      nlinarith only [hL, sq_nonneg (Real.log n - 1973 / 50)]
    exact
      ⟨3, Nat.prime_three, hbound,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho Nat.prime_three hthree⟩
  · have hp5 : 5 ≤ (p : ℝ) := by exact_mod_cast hp.five_le_of_ne_two_of_ne_three hp2 hp3
    have hlog : Real.log n < 3 * Real.log 600000 := hU.trans_lt lowBridge_log_600000
    have hshift :=
      uniformKorselt_log_shift_of_log_bound hnp hp hq hr (hp.odd_of_ne_two hp2)
        (hq.odd_of_ne_two hq2) (hr.odd_of_ne_two hr2) hpq hqr hu 600000 hp5 (by norm_num only) hlog
    have hs : Real.log ((p * q : ℕ) : ℝ) ≤ lowRoundLevel := by
      rw [Nat.cast_mul]
      dsimp only [lowRoundLevel]
      linarith only [hshift, lowBridge_spacing_600000, hU]
    have hpqd : p * q ∣ n := hnp ▸ dvd_mul_right (p * q) r
    obtain ⟨a, ha, hab, haf⟩ := exists_prime_reject_pair_round hn ho hp hq hpqd hGRH hs
    have hradius : lowRoundRadius ^ 2 < (479 : ℝ) := by norm_num only [lowRoundRadius]
    have ha479 : a < 479 := by exact_mod_cast hab.trans_lt hradius
    have ha467 := prime_le_467_of_lt_479 ha ha479
    have h467 : (467 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by
      nlinarith only [hL, sq_nonneg (Real.log n - 1973 / 50)]
    exact ⟨a, ha, (Nat.cast_le.mpr ha467).trans h467, haf⟩

/-- Under GRH, every odd composite with logarithm in `[8,39.908]` has a
rejecting prime within the coefficient `3/10` cutoff. The sixty-cell bridge,
the rounded uniform triple branch and existing nonuniform results cover the
overlapping ranges. -/
theorem exists_prime_reject_03_log8_39908 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 9977 / 250) :
    ∃ a : ℕ,
      a.Prime ∧
        (a : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (a : ZMod n) := by
  by_cases hsmall : Real.log n ≤ (988 / 25 : ℝ)
  · exact exists_prime_reject_03_log8_3952 hn ho hc hGRH hL hsmall
  · by_cases hu : UniformKorseltTriple n
    · apply uniformKorselt_reject_round hn ho hu hGRH
      · linarith only [hsmall]
      · exact hU
    · apply exists_prime_reject_03_nonuniform_ranges hn ho hc hu hGRH hL
      left
      linarith only [hU]

end PseudoPrime.PrimeTestBounds.MillerRabin
