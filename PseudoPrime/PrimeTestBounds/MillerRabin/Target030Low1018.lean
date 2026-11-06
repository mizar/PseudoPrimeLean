/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030EarlyBridge
public import PseudoPrime.PrimeTestBounds.MillerRabin.Target030FurtherCells

/-! # Extended 0.30 low-scale coverage -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A prime whose square divides an input of logarithm at most 10.18 is at most
157. The rational logarithm certificate bounds the square below 163 squared,
and primality excludes the remaining integers above 157. -/
theorem square_factor_le_157_at_1018 {n p : ℕ} (hn : 1 < n) (hp : p.Prime) (hdiv : p ^ 2 ∣ n)
    (hU : Real.log n ≤ (509 / 50 : ℝ)) : p ≤ 157 := by
  have hcert :=
    (Analysis.rationalLogIntervalCheck_sound
        (show Analysis.rationalLogIntervalCheck 26569 15 32 (10181 / 1000) 11 = true from by
          decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at hcert
  have hnlt : n < 26569 := by
    have hlog : Real.log (n : ℝ) < Real.log (26569 : ℝ) := by linarith only [hU, hcert]
    exact_mod_cast
      (Real.log_lt_log_iff (Nat.cast_pos.mpr (Nat.zero_lt_of_lt hn))
            (by norm_num only : (0 : ℝ) < 26569)).mp
        hlog
  have hpsq : p ^ 2 < 26569 := (Nat.le_of_dvd (Nat.zero_lt_of_lt hn) hdiv).trans_lt hnlt
  have hp162 : p ≤ 162 := by nlinarith only [hpsq]
  by_contra h
  have hlower : 158 ≤ p := Nat.succ_le_of_lt (Nat.lt_of_not_ge h)
  interval_cases p <;> norm_num only [Nat.prime_def_lt] at hp

set_option maxHeartbeats 4000000 in
-- The finite weighted family requires additional elaboration steps.
/-- Any odd input divisible by a prime square has a 0.30 rejecting prime for
logarithm from 8 through 10.18. The 158-element weighted family exceeds the
local kernel when the prime factor itself is too large. -/
theorem exists_prime_reject_03_square_1018 {n p : ℕ} (hn : 1 < n) (ho : Odd n) (hp : p.Prime)
    (hdiv : p ^ 2 ∣ n) (hL : (8 : ℝ) ≤ Real.log n) (hU : Real.log n ≤ 509 / 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hpn : p ∣ n := (dvd_pow_self p (by decide : 2 ≠ 0)).trans hdiv
  have hp2 : p ≠ 2 := ho.ne_two_of_dvd_nat hpn
  have hB : (19 : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 := by nlinarith only [hL]
  by_cases hpSmall : p ≤ 19
  · exact
      ⟨p, hp, (Nat.cast_le.mpr hpSmall).trans hB,
        PrimeTest.strongMillerRabinPass_not_of_prime_dvd hn ho hp hpn⟩
  · let S := target030FirstPrimes.toFinset
    let w := target030FirstWeight
    let F := weightedPrimeFamily S w 58
    have hprime : ∀ r ∈ S, r.Prime := fun r hr ↦
      (target030_first_prime_supply r (List.mem_toFinset.mp hr)).1
    have hbound : ∀ r ∈ S, r ≤ 19 := fun r hr ↦
      (target030_first_prime_supply r (List.mem_toFinset.mp hr)).2
    have hw : ∀ r ∈ S, Real.log r ≤ (w r : ℝ) / 10 := fun r hr ↦
      target030_first_weight_bounds r (List.mem_toFinset.mp hr)
    have hwpos : ∀ r ∈ S, 1 ≤ w r := fun r hr ↦
      target030First_labels.2.2 r (List.mem_toFinset.mp hr)
    have hsub : ∀ T ∈ F, ∀ r ∈ T, r ∈ S := fun T hT ↦
      ((mem_weightedPrimeFamily S w 58 hwpos T).mp hT).1
    have hcost : ∀ T ∈ F, (T.map w).sum ≤ 58 := fun T hT ↦
      ((mem_weightedPrimeFamily S w 58 hwpos T).mp hT).2
    have hc : F.card = 158 := target030Square_card
    have hp157 := square_factor_le_157_at_1018 hn hp hdiv hU
    have hcount : p - 1 < F.card := by
      rw [hc]
      exact (Nat.sub_lt hp.pos (by decide : 0 < 1)).trans_le (hp157.trans (by decide))
    obtain ⟨r, hr, hb, hf⟩ :=
      exists_prime_reject_prime_pow_weighted hn ho hp hp2 (by decide : 0 < 2) hdiv S F 19 58 w 10
        (by norm_num only) hsub hprime hbound hw hcost
        (square_factor_budget_58 (Nat.lt_of_not_ge hpSmall)) hcount
    exact ⟨r, hr, (Nat.cast_le.mpr hb).trans hB, hf⟩

/-- Under GRH, every odd composite with logarithm from 8 through 10.18 has a
rejecting prime within the 0.30 target. Split into square-divisor, three-factor,
and distinct-semiprime cases and apply their certified witnesses. -/
theorem exists_prime_reject_03_log8_to_1018 {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 509 / 50) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  by_cases hsq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hd⟩ := hsq
    exact exists_prime_reject_03_square_1018 hn ho hp hd hL hU
  · by_cases hk : 3 ≤ ArithmeticFunction.cardFactors n
    · exact exists_prime_reject_03_three_low hn ho hk hL (by linarith only [hU])
    · have hkpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
      have hkne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
        hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
      have hk2 : 2 ≤ ArithmeticFunction.cardFactors n :=
        Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hkpos) hkne.symm)
      have hkeq : ArithmeticFunction.cardFactors n = 2 :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge hk)) hk2
      obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
        NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hkeq
      rcases hpq.eq_or_lt with heq | hlt
      · subst q
        exact False.elim (hsq ⟨p, hp, by rw [hprod, pow_two]⟩)
      · exact
          exists_prime_reject_03_semiprime_10614 hn ho hp hq hlt hprod hGRH hL
            (by linarith only [hU])

/-- Under GRH, every nonuniform squarefree odd composite with at least three
distinct prime factors has a 0.30 rejecting prime. Four factors use the total
factor bound; exactly three use the marked-factor argument. -/
theorem exists_prime_reject_03_nonuniform_factors {n : ℕ} (hn : 1 < n) (ho : Odd n) (hc : ¬n.Prime)
    (hsf : Squarefree n) (hcard : 3 ≤ n.primeFactors.card) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases h4 : 4 ≤ n.primeFactors.card
  · have h := List.toFinset_card_le n.primeFactorsList
    change n.primeFactors.card ≤ ArithmeticFunction.cardFactors n at h
    exact exists_prime_reject_03_four_factors hn ho hc (h4.trans h) hGRH
  · have heq : n.primeFactors.card = 3 :=
      Nat.le_antisymm (Nat.lt_succ_iff.mp (Nat.lt_of_not_ge h4)) hcard
    exact exists_prime_reject_03_nonuniform_three hn ho hsf heq hu hGRH

/-- Under GRH, a nonuniform squarefree odd composite with logarithm from 8
through 10.614 has a 0.30 rejecting prime. The distinct-semiprime cells and
the unrestricted nonuniform three-factor result cover the two factor counts. -/
theorem exists_prime_reject_03_nonuniform_squarefree {n : ℕ} (hn : 1 < n) (ho : Odd n)
    (hc : ¬n.Prime) (hsf : Squarefree n) (hu : ¬UniformKorseltTriple n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : (8 : ℝ) ≤ Real.log n)
    (hU : Real.log n ≤ 10614 / 1000) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  by_cases hcard : 3 ≤ n.primeFactors.card
  · exact exists_prime_reject_03_nonuniform_factors hn ho hc hsf hcard hu hGRH
  · have hk : ArithmeticFunction.cardFactors n = 2 := by
      have hlist : n.primeFactorsList.Nodup :=
        (Nat.squarefree_iff_nodup_primeFactorsList (Nat.ne_zero_of_lt hn)).mp hsf
      have heq : n.primeFactors.card = ArithmeticFunction.cardFactors n := by
        change n.primeFactorsList.toFinset.card = n.primeFactorsList.length
        exact List.toFinset_card_of_nodup hlist
      have hpos := ArithmeticFunction.cardFactors_pos_iff_one_lt.mpr hn
      have hne : ArithmeticFunction.cardFactors n ≠ 1 := fun h ↦
        hc (ArithmeticFunction.cardFactors_eq_one_iff_prime.mp h)
      have hlo : 2 ≤ ArithmeticFunction.cardFactors n :=
        Nat.succ_le_of_lt (lt_of_le_of_ne (Nat.succ_le_of_lt hpos) hne.symm)
      have hhi : ArithmeticFunction.cardFactors n < 3 := heq ▸ Nat.lt_of_not_ge hcard
      exact Nat.le_antisymm (Nat.lt_succ_iff.mp hhi) hlo
    obtain ⟨p, q, hp, hq, hpq, hprod⟩ :=
      NumberTheory.exists_ordered_prime_pair_of_cardFactors_two hn hk
    rcases hpq.eq_or_lt with heq | hlt
    · subst q
      have hnot := (Nat.squarefree_iff_prime_squarefree.mp hsf) p hp
      exact False.elim (hnot (hprod.symm ▸ dvd_rfl))
    · exact exists_prime_reject_03_semiprime_10614 hn ho hp hq hlt hprod hGRH hL hU

end PseudoPrime.PrimeTestBounds.MillerRabin
