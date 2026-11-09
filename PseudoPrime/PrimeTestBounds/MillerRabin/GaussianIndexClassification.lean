/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexClassification
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianIndexWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaLinearCutoffBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaPrefix100WitnessBounds

/-! # Finite Fermat-index classification for Gaussian and Gamma witnesses -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A logarithmic scale of at least 500 implies the finite classification's
decimal starting value. -/
theorem gaussian6fifths_decimal_threshold_of_log {n : ℕ} [NeZero n] (hL : 500 ≤ Real.log n) :
    10 ^ 142 ≤ n := by
  have hExp1 : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp (1 : ℝ)
    norm_num only at h
    exact h
  have hExp10 : (10 : ℝ) ^ 3 ≤ Real.exp 10 := by
    have he : Real.exp 10 = Real.exp 1 ^ (10 : ℕ) := by
      rw [show (10 : ℝ) = (10 : ℕ) * 1 by norm_num only]
      exact Real.exp_nat_mul 1 10
    rw [he]
    calc
      (10 : ℝ) ^ 3 ≤ 2 ^ (10 : ℕ) := by norm_num only
      _ ≤ Real.exp 1 ^ (10 : ℕ) := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2) hExp1 10
  have hExp500 : (10 : ℝ) ^ 150 ≤ Real.exp 500 := by
    have he : Real.exp 500 = Real.exp 10 ^ (50 : ℕ) := by
      rw [show (500 : ℝ) = (50 : ℕ) * 10 by norm_num only]
      exact Real.exp_nat_mul 10 50
    rw [he]
    calc
      (10 : ℝ) ^ 150 = ((10 : ℝ) ^ 3) ^ (50 : ℕ) := by rw [← pow_mul]
      _ ≤ Real.exp 10 ^ (50 : ℕ) := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 10 ^ 3) hExp10 50
  have hnreal : (10 : ℝ) ^ 142 ≤ (n : ℝ) := by
    calc
      (10 : ℝ) ^ 142 ≤ 10 ^ 150 :=
        pow_le_pow_right₀ (by norm_num only : (1 : ℝ) ≤ 10) (by norm_num only : 142 ≤ 150)
      _ ≤ Real.exp 500 := hExp500
      _ ≤ (n : ℝ) := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr (NeZero.pos n))).mp hL
  exact_mod_cast hnreal

/-- The residual squarefree uniform Korselt triple from finite-index
classification has a witness below the Gamma index-100 cutoff from `L ≥ 330`. -/
theorem exists_prime_gamma100_korseltCard_GRH {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 330 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hc
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  exact
    exists_prime_gamma100_threeKorselt_GRH hp hq hr (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- The residual-29 Gaussian estimate closes the uniform three-prime
Korselt branch below `U₁₀₀` from logarithmic scale 240. -/
theorem exists_prime_gamma100Prefix_korseltCard_GRH {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gammaIndex100PrefixUpper (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hc
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  have hn1 : 1 < n := by
    rw [hnprod]
    exact
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn)
  obtain ⟨s, hs, hbound, hfail⟩ :=
    exists_prime_gaussianTriple29_indexFour_GRH hnOdd H hi hpass hGRH hC.le (by linarith only [hL])
  exact ⟨s, hs, hbound.trans (gamma100GaussianTriple29_le_prefix_upper hL), hfail⟩

/-- Under GRH, every odd composite with `log n ≥ 240` has a prime
Miller--Rabin witness bounded by the two-prefix `U₁₀₀` envelope. -/
theorem exists_prime_witness_le_gammaIndex100PrefixUpper {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100PrefixUpper (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rcases gamma100Prefix_witness_or_Korselt_GRH hnOdd hcomp hGRH hL with hWitness | hTriple
  · exact hWitness
  · obtain ⟨hsf, hc, hK, hU⟩ := hTriple
    exact exists_prime_gamma100Prefix_korseltCard_GRH hnOdd hsf hc hK hU hGRH hL

/-- The uniform squarefree Korselt triple remaining after the finite-index
classification has a witness below the 6/5 Gaussian bound. -/
theorem gaussian6_5_primeWitness_korselt_card_GRH {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gaussian6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hc
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  exact
    gaussian6_5_primeWitness_threeKorselt_GRH hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- A squarefree uniform Korselt triple has a witness below the
prefix-improved constant-18 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_gaussian18_korseltCard_GRH {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gaussian18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hc
  have hpMem : p ∈ n.primeFactors := hset ▸ Finset.mem_insert_self p _
  have hqMem : q ∈ n.primeFactors := hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self q _)
  have hrMem : r ∈ n.primeFactors :=
    hset ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_singleton_self r))
  have hp := (Nat.mem_primeFactors.mp hpMem).1
  have hq := (Nat.mem_primeFactors.mp hqMem).1
  have hr := (Nat.mem_primeFactors.mp hrMem).1
  have hpn := (Nat.mem_primeFactors.mp hpMem).2.1
  have hqn := (Nat.mem_primeFactors.mp hqMem).2.1
  have hrn := (Nat.mem_primeFactors.mp hrMem).2.1
  have hprod := (Nat.prod_primeFactors_of_squarefree hsf).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  exact
    exists_prime_gaussian18_threeKorselt_GRH hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- Complete the finite Fermat-index branch at scale 300 using the local
`0.3 L²` bound and the prefix-improved Gaussian bound for the triple remainder. -/
theorem exists_prime_gaussian18_smallFermat_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gaussian18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  rcases
    witness_or_uniformKorselt_log250_GRH hnOdd hcomp (PrimeTest.fermatSubgroup n) le_rfl hi hGRH
      (by linarith only [hL]) with
    hlocal | htriple
  · obtain ⟨s, hs, hbound, hfail⟩ := hlocal
    have hbound' := gaussian18Bound_gt_local_three_tenths hL
    exact ⟨s, hs, hbound.trans (le_of_lt hbound'), hfail⟩
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    have hN27 := pow10_27_le_of_log_ge_250 (by linarith only [hL])
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 27 := by norm_num only
      exact h20000.trans hN27
    exact exists_prime_gaussian18_korseltCard_GRH hnOdd hsf hc hK hU hnlarge hGRH hL

/-- Under GRH, every odd composite with logarithm at least 300 has a prime
strong-MR witness below the prefix-improved constant-18 Gaussian bound. -/
theorem exists_prime_witness_le_gaussianMR18 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gaussian18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hn0 : 0 < n := by
    by_contra hnot
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hnz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hnlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hn0)
  have hn1 : 1 < n := by
    have hn1R : ((1 : ℕ) : ℝ) < (n : ℝ) := by
      norm_num only [Nat.cast_one]
      linarith only [hL, hnlog]
    exact Nat.cast_lt.mp hn1R
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9
  · exact exists_prime_gaussian18_smallFermat_GRH hnOdd hcomp hGRH hi hL
  · have hlarge : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index := by
      have h := (lt_of_not_ge hi).le
      norm_num only at h
      exact h
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 27 := by norm_num only
      exact h20000.trans (pow10_27_le_of_log_ge_250 (by linarith only [hL]))
    have hiR : gaussian6FifthsIndex ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
      norm_num only [gaussian6FifthsIndex]
      exact_mod_cast hlarge
    have hHpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.fermatSubgroup n ∧ (u : ZMod n) = z := by
      intro z hz
      obtain ⟨u, hu, hzu⟩ := PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
      exact ⟨u, hu, hzu⟩
    exact
      exists_prime_gaussian18_largeIndex_GRH hnOdd hnlarge (PrimeTest.fermatSubgroup n) hiR hHpass
        hGRH hL

/-- The least prime rejecting strong MR inherits the prefix-improved
constant-18 Gaussian bound from logarithmic scale 300 onward. -/
theorem exists_least_prime_witness_le_gaussianMR18 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ gaussian18Bound (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ := exists_prime_witness_le_gaussianMR18 hnOdd hcomp hGRH hL
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, fun q hq hreject ↦
      Nat.find_min' hex ⟨hq, hreject⟩⟩

/-- Complete the finite Fermat-index branch for the 6/5 bound at scale 500. -/
theorem gaussian6_5_prime_smallFermatIndex_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gaussian6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  rcases
    witness_0282924_or_uniformKorselt_GRH hnOdd hcomp (PrimeTest.fermatSubgroup n) le_rfl hi hGRH
      hn with
    hlocal | htriple
  · obtain ⟨s, hs, hbound, hfail⟩ := hlocal
    have hbound' := gaussian6FifthsBound_lower hL
    exact ⟨s, hs, hbound.trans (le_of_lt hbound'), hfail⟩
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 142 := by norm_num only
      exact h20000.trans hn
    exact gaussian6_5_primeWitness_korselt_card_GRH hnOdd hsf hc hK hU hnlarge hGRH hL

/-- Under GRH, every odd composite with logarithm at least 500 has a prime
strong-MR witness below the 6/5 Gaussian bound. The Fermat-index split and
the finite Korselt classification are internal to this theorem. -/
theorem exists_prime_witness_le_gaussian6fifths {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gaussian6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hn0 : 0 < n := by
    by_contra hnot
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hnz, Nat.cast_zero, Real.log_zero] at hL
    norm_num only at hL
  have hnlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hn0)
  have hn1 : 1 < n := by
    have hn1R : ((1 : ℕ) : ℝ) < (n : ℝ) := by
      norm_num only [Nat.cast_one]
      linarith only [hL, hnlog]
    exact Nat.cast_lt.mp hn1R
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hN := gaussian6fifths_decimal_threshold_of_log hL
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9
  · exact gaussian6_5_prime_smallFermatIndex_GRH hnOdd hcomp hGRH hN hi hL
  · have hlarge : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index := by
      have h := (lt_of_not_ge hi).le
      norm_num only at h
      exact h
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 142 := by norm_num only
      exact h20000.trans hN
    exact gaussian6_5_prime_largeFermatIndex_GRH hn1 hnOdd hlarge hGRH hL

/-- The least prime rejecting the strong test inherits the 6/5 Gaussian
bound by minimizing the nonempty prime-witness set. -/
theorem exists_least_prime_witness_le_gaussian6fifths {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) ∧
        (s : ℝ) ≤ gaussian6FifthsBound (Real.log n) ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → s ≤ r := by
  classical
  obtain ⟨s, hs, hbound, hfail⟩ := exists_prime_witness_le_gaussian6fifths hnOdd hcomp hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨s, hs, hfail⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hs, hfail⟩)).trans hbound, fun r hr hreject ↦
      Nat.find_min' hex ⟨hr, hreject⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
