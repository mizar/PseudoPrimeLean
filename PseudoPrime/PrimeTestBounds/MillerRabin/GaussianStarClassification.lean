/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexClassification
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianVariableWitnessBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaClippedComparison
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaLinearCutoffBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GammaPrefix100WitnessBounds

/-! # Finite Fermat-index classification for the Gaussian star bound -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A logarithmic scale of at least `600` implies the finite classification's
decimal starting value by comparing `exp 600` with `10^180`. -/
theorem gaussian_star_decimal_threshold_of_log {n : ℕ} [NeZero n] (hL : 600 ≤ Real.log n) :
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
  have hExp600 : (10 : ℝ) ^ 180 ≤ Real.exp 600 := by
    have he : Real.exp 600 = Real.exp 10 ^ (60 : ℕ) := by
      rw [show (600 : ℝ) = (60 : ℕ) * 10 by norm_num only]
      exact Real.exp_nat_mul 10 60
    rw [he]
    calc
      (10 : ℝ) ^ 180 = (10 ^ 3) ^ (60 : ℕ) := by rw [← pow_mul]
      _ ≤ Real.exp 10 ^ (60 : ℕ) := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 10 ^ 3) hExp10 60
  have hnreal : (10 : ℝ) ^ 142 ≤ (n : ℝ) := by
    calc
      (10 : ℝ) ^ 142 ≤ 10 ^ 180 :=
        pow_le_pow_right₀ (by norm_num only : (1 : ℝ) ≤ 10) (by norm_num only : 142 ≤ 180)
      _ ≤ Real.exp 600 := hExp600
      _ ≤ (n : ℝ) := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr (NeZero.pos n))).mp hL
  exact_mod_cast hnreal

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

/-- At logarithmic scale at least 600, the existing finite Fermat-index
classification gives either a local coefficient-0.282924 witness, which lies
below the new Gaussian star bound, or the remaining squarefree uniform
Korselt triple. -/
theorem gaussian_star_small_index_classification {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n)
    (hi : H.index ≤ 10 ^ 9) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 142 ≤ n) (hL : 600 ≤ Real.log n) :
    (∃ r : ℕ,
        r.Prime ∧
          (r : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
          ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  rcases coefficient_0283_witness_or_uniform_korselt_triple hnOdd hcomp H hH hi hGRH hn with
    hlocal | htriple
  · obtain ⟨r, hr, hbound, hfail⟩ := hlocal
    have hcoef := Analysis.gaussianMRStarBound_gt_triangular_coefficient hL
    exact Or.inl ⟨r, hr, hbound.trans (le_of_lt hcoef), hfail⟩
  · exact Or.inr htriple

/-- The squarefree uniform Korselt triple remaining after finite-index
classification has a prime witness below the classified Gaussian star bound. -/
theorem exists_prime_witness_le_gaussian_star_of_uniform_korselt_triple_card {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 600 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
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
    exists_prime_witness_le_gaussian_star_of_three_prime_korselt hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- The residual squarefree uniform Korselt triple from finite-index
classification has a witness below the Gamma index-100 cutoff from `L ≥ 330`. -/
theorem exists_prime_witness_le_gammaIndex100_of_uniform_korselt_triple_card {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
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
    exists_prime_witness_le_gammaIndex100_of_three_prime_korselt hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- The residual-29 Gaussian estimate closes the uniform three-prime
Korselt branch below `U₁₀₀` from logarithmic scale 240. -/
theorem exists_prime_witness_le_gammaIndex100PrefixUpper_of_uniform_korselt_triple_card {n : ℕ}
    (hnOdd : Odd n) (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
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
    exists_prime_witness_le_gammaIndex100GaussianTripleBound29_of_index_four_conductor hnOdd H hi
      hpass hGRH hC.le (by linarith only [hL])
  exact ⟨s, hs, hbound.trans (gammaIndex100GaussianTripleBound29_le_prefix_upper hL), hfail⟩

/-- Under GRH, every odd composite with `log n ≥ 240` has a prime
Miller--Rabin witness bounded by the two-prefix `U₁₀₀` envelope. -/
theorem exists_prime_witness_le_gammaIndex100PrefixUpper {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        (p : ℝ) ≤ gammaIndex100PrefixUpper (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) := by
  rcases
    exists_prime_witness_le_gammaIndex100PrefixUpper_or_uniform_korselt_triple hnOdd hcomp hGRH
      hL with
    hWitness | hTriple
  · exact hWitness
  · obtain ⟨hsf, hc, hK, hU⟩ := hTriple
    exact
      exists_prime_witness_le_gammaIndex100PrefixUpper_of_uniform_korselt_triple_card hnOdd hsf hc
        hK hU hGRH hL

/-- Complete the finite Fermat-index branch at scale `600`: the local
coefficient witness lies below the classified Gaussian bound, and the only
remaining uniform Korselt triple uses its index-four Gaussian witness. -/
theorem exists_prime_witness_le_gaussian_star_of_small_fermat_index {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9) (hL : 600 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  rcases
    gaussian_star_small_index_classification hnOdd hcomp (PrimeTest.fermatSubgroup n) le_rfl hi hGRH
      hn hL with
    hlocal | htriple
  · obtain ⟨s, hs, hbound, hfail⟩ := hlocal
    exact ⟨s, hs, hbound, hfail⟩
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 142 := by norm_num only
      exact h20000.trans hn
    exact
      exists_prime_witness_le_gaussian_star_of_uniform_korselt_triple_card hnOdd hsf hc hK hU
        hnlarge hGRH hL

/-- The uniform squarefree Korselt triple remaining after the finite-index
classification has a witness below the 6/5 Gaussian bound. -/
theorem exists_prime_witness_le_gaussian6fifths_of_uniform_korselt_triple_card {n : ℕ}
    (hnOdd : Odd n) (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
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
    exists_prime_witness_le_gaussian6fifths_of_three_prime_korselt hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- A squarefree uniform Korselt triple has a witness below the
prefix-improved constant-18 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_witness_le_gaussianMR18_of_uniform_korselt_triple_card {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR18Bound (Real.log n) ∧
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
    exists_prime_witness_le_gaussianMR18_of_three_prime_korselt hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- The residual uniform three-prime Korselt case has a witness below the
constant-6 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_witness_le_gaussianMR6_of_uniform_korselt_triple_card {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hnlarge : 20000 ≤ n) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
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
    exists_prime_witness_le_gaussianMR6_of_three_prime_korselt hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hnlarge hGRH hL

/-- Complete the finite Fermat-index branch at scale 300 using the local
`0.3 L²` bound and the prefix-improved Gaussian bound for the triple remainder. -/
theorem exists_prime_witness_le_gaussianMR18_of_small_fermat_index {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  rcases
    finite_index_witness_or_uniform_korselt_triple_log250 hnOdd hcomp (PrimeTest.fermatSubgroup n)
      le_rfl hi hGRH (by linarith only [hL]) with
    hlocal | htriple
  · obtain ⟨s, hs, hbound, hfail⟩ := hlocal
    have hbound' := Analysis.gaussianMR18Bound_gt_local_three_tenths hL
    exact ⟨s, hs, hbound.trans (le_of_lt hbound'), hfail⟩
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    have hN27 := Analysis.ten_pow_twentyseven_le_of_log_ge_250 (by linarith only [hL])
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 27 := by norm_num only
      exact h20000.trans hN27
    exact
      exists_prime_witness_le_gaussianMR18_of_uniform_korselt_triple_card hnOdd hsf hc hK hU hnlarge
        hGRH hL

/-- Complete the finite Fermat-index branch at scale 300 for the constant-6
Gaussian bound. -/
theorem exists_prime_witness_le_gaussianMR6_of_small_fermat_index {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  rcases
    finite_index_witness_or_uniform_korselt_triple_log250 hnOdd hcomp (PrimeTest.fermatSubgroup n)
      le_rfl hi hGRH (by linarith only [hL]) with
    hlocal | htriple
  · obtain ⟨s, hs, hbound, hfail⟩ := hlocal
    have hbound' := Analysis.gaussianMR6Bound_gt_local_three_tenths hL
    exact ⟨s, hs, hbound.trans (le_of_lt hbound'), hfail⟩
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    have hN27 := Analysis.ten_pow_twentyseven_le_of_log_ge_250 (by linarith only [hL])
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 27 := by norm_num only
      exact h20000.trans hN27
    exact
      exists_prime_witness_le_gaussianMR6_of_uniform_korselt_triple_card hnOdd hsf hc hK hU hnlarge
        hGRH hL

/-- Under GRH, every odd composite with logarithm at least 300 has a prime
strong-MR witness below the prefix-improved constant-18 Gaussian bound. -/
theorem exists_prime_witness_le_gaussianMR18 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR18Bound (Real.log n) ∧
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
  · exact exists_prime_witness_le_gaussianMR18_of_small_fermat_index hnOdd hcomp hGRH hi hL
  · have hlarge : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index := by
      have h := (lt_of_not_ge hi).le
      norm_num only at h
      exact h
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 27 := by norm_num only
      exact h20000.trans (Analysis.ten_pow_twentyseven_le_of_log_ge_250 (by linarith only [hL]))
    have hiR : Analysis.gaussianMR6FifthsIndex ≤ ((PrimeTest.fermatSubgroup n).index : ℝ) := by
      norm_num only [Analysis.gaussianMR6FifthsIndex]
      exact_mod_cast hlarge
    have hHpass :
      ∀ z : ZMod n,
        PrimeTest.StrongMillerRabinPass n z →
          ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.fermatSubgroup n ∧ (u : ZMod n) = z := by
      intro z hz
      obtain ⟨u, hu, hzu⟩ := PrimeTest.strongMillerRabinPass_mem_fermatSubgroup hn1 hnOdd hz
      exact ⟨u, hu, hzu⟩
    exact
      exists_prime_witness_le_gaussianMR18_of_index_ge_billion hnOdd hnlarge
        (PrimeTest.fermatSubgroup n) hiR hHpass hGRH hL

/-- Under GRH, every odd composite with logarithm at least 300 has a prime
strong-MR witness below the constant-6 Gaussian bound. -/
theorem exists_prime_witness_le_gaussianMR6 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
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
  · exact exists_prime_witness_le_gaussianMR6_of_small_fermat_index hnOdd hcomp hGRH hi hL
  · have hlarge : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index := by
      have h := (lt_of_not_ge hi).le
      norm_num only at h
      exact h
    exact exists_prime_witness_le_gaussianMR6_of_large_fermat_index hn1 hnOdd hlarge hGRH hL

/-- The least prime rejecting strong MR inherits the constant-6 Gaussian
bound from logarithmic scale 300 onward. -/
theorem exists_least_prime_witness_le_gaussianMR6 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ := exists_prime_witness_le_gaussianMR6 hnOdd hcomp hGRH hL
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, fun q hq hreject ↦
      Nat.find_min' hex ⟨hq, hreject⟩⟩

/-- The least prime rejecting strong MR inherits the prefix-improved
constant-18 Gaussian bound from logarithmic scale 300 onward. -/
theorem exists_least_prime_witness_le_gaussianMR18 {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ p : ℕ,
      p.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n) ∧
        (p : ℝ) ≤ Analysis.gaussianMR18Bound (Real.log n) ∧
        ∀ q : ℕ, q.Prime → ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) → p ≤ q := by
  classical
  obtain ⟨p, hp, hbound, hreject⟩ := exists_prime_witness_le_gaussianMR18 hnOdd hcomp hGRH hL
  have hex : ∃ q : ℕ, q.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (q : ZMod n) := ⟨p, hp, hreject⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hp, hreject⟩)).trans hbound, fun q hq hreject ↦
      Nat.find_min' hex ⟨hq, hreject⟩⟩

/-- Complete the finite Fermat-index branch for the 6/5 bound at scale 500. -/
theorem exists_prime_witness_le_gaussian6fifths_of_small_fermat_index {n : ℕ} [NeZero n]
    (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n)
    (hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  rcases
    coefficient_0283_witness_or_uniform_korselt_triple hnOdd hcomp (PrimeTest.fermatSubgroup n)
      le_rfl hi hGRH hn with
    hlocal | htriple
  · obtain ⟨s, hs, hbound, hfail⟩ := hlocal
    have hbound' := Analysis.gaussianMR6FifthsBound_lower hL
    exact ⟨s, hs, hbound.trans (le_of_lt hbound'), hfail⟩
  · obtain ⟨hsf, hc, hK, hU⟩ := htriple
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 142 := by norm_num only
      exact h20000.trans hn
    exact
      exists_prime_witness_le_gaussian6fifths_of_uniform_korselt_triple_card hnOdd hsf hc hK hU
        hnlarge hGRH hL

/-- Under GRH, every odd composite whose logarithmic scale is at least `600`
has a prime failing strong Miller--Rabin below the classified Gaussian star
bound. The Fermat-index split and finite Korselt classification are internal. -/
theorem exists_prime_witness_le_gaussian_star {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 600 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hn0 : 0 < n := by
    by_contra hnot
    have hnz : n = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hnz, Nat.cast_zero, Real.log_zero] at hL
    norm_num at hL
  have hnlog := Real.log_le_sub_one_of_pos (Nat.cast_pos.mpr hn0)
  have hn1 : 1 < n := by
    have hn1R : ((1 : ℕ) : ℝ) < (n : ℝ) := by
      norm_num only [Nat.cast_one]
      linarith only [hL, hnlog]
    exact Nat.cast_lt.mp hn1R
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hN := gaussian_star_decimal_threshold_of_log hL
  by_cases hi : (PrimeTest.fermatSubgroup n).index ≤ 10 ^ 9
  · exact exists_prime_witness_le_gaussian_star_of_small_fermat_index hnOdd hcomp hGRH hN hi hL
  · have hlarge : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index := by
      have h := (lt_of_not_ge hi).le
      norm_num only at h
      exact h
    exact exists_prime_witness_le_gaussian_star_of_large_fermat_index hn1 hnOdd hlarge hGRH hL

/-- Under GRH, every odd composite with logarithm at least 500 has a prime
strong-MR witness below the 6/5 Gaussian bound. The Fermat-index split and
the finite Korselt classification are internal to this theorem. -/
theorem exists_prime_witness_le_gaussian6fifths {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
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
  · exact exists_prime_witness_le_gaussian6fifths_of_small_fermat_index hnOdd hcomp hGRH hN hi hL
  · have hlarge : 1000000000 ≤ (PrimeTest.fermatSubgroup n).index := by
      have h := (lt_of_not_ge hi).le
      norm_num only at h
      exact h
    have hnlarge : 20000 ≤ n := by
      have h20000 : 20000 ≤ 10 ^ 142 := by norm_num only
      exact h20000.trans hN
    exact exists_prime_witness_le_gaussian6fifths_of_large_fermat_index hn1 hnOdd hlarge hGRH hL

/-- The least prime rejecting the strong test inherits the 6/5 Gaussian
bound by minimizing the nonempty prime-witness set. -/
theorem exists_least_prime_witness_le_gaussian6fifths {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) ∧
        (s : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → s ≤ r := by
  classical
  obtain ⟨s, hs, hbound, hfail⟩ := exists_prime_witness_le_gaussian6fifths hnOdd hcomp hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨s, hs, hfail⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hs, hfail⟩)).trans hbound, fun r hr hreject ↦
      Nat.find_min' hex ⟨hr, hreject⟩⟩

/-- For `L >= 600`, the classified Gaussian bound is strictly below the
index-four Gamma expression, so it improves that branch wherever both apply. -/
theorem gaussian_star_bound_lt_gamma_index_four {L : ℝ} (hL : 600 ≤ L) :
    Analysis.gaussianMRStarBound L < (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by
  have hstar := Analysis.gaussianMRStarBound_lt_seven_tenths hL
  have hindex : (7 / 10 : ℝ) * L ^ 2 ≤ (99 / 40 : ℝ) * ((107 / 200 : ℝ) * L + 24 / 5) ^ 2 := by
    nlinarith only [hL]
  exact lt_of_lt_of_le hstar hindex

/-- From $L=500$ onward the 6/5 Gaussian bound is below the two-prefix
clipped-log Gamma envelope. -/
theorem gaussian6fifths_bound_lt_gammaClippedUpper {L : ℝ} (hL : 500 ≤ L) :
    Analysis.gaussianMR6FifthsBound L < gammaClippedUpper L := by
  have h6 := Analysis.gaussianMR6FifthsBound_lt_sevenTenths_sq hL
  have hgamma := gammaClippedUpper_ge_sevenTenths_sq (L := L) (by linarith only [hL])
  exact lt_of_lt_of_le h6 hgamma

/-- From $L=600$ onward the classified Gaussian bound is below the new
two-prefix clipped-log Gamma envelope. -/
theorem gaussian_star_bound_lt_gammaClippedUpper {L : ℝ} (hL : 600 ≤ L) :
    Analysis.gaussianMRStarBound L < gammaClippedUpper L := by
  have hstar := Analysis.gaussianMRStarBound_lt_seven_tenths hL
  have hgamma := gammaClippedUpper_ge_sevenTenths_sq (L := L) (by linarith only [hL])
  exact lt_of_lt_of_le hstar hgamma

/-- From scale 600 onward, the 6/5 Gaussian bound improves the classified
star bound by a strict factor below `2601/2800`. -/
theorem gaussian6fifths_bound_lt_gaussian_star {L : ℝ} (hL : 600 ≤ L) :
    Analysis.gaussianMR6FifthsBound L < Analysis.gaussianMRStarBound L := by
  have hratio := Analysis.gaussianMR6FifthsBound_lt_gaussianMRStarBound_ratio hL
  have hstarpos : 0 < Analysis.gaussianMRStarBound L := by
    have hroot := Analysis.gaussianMRStarRoot_pos hL
    dsimp only [Analysis.gaussianMRStarBound, Analysis.gaussianMRStarRadius]
    positivity
  have hcoef : (2601 / 2800 : ℝ) < 1 := by norm_num only
  have hscaled :
    (2601 / 2800 : ℝ) * Analysis.gaussianMRStarBound L < Analysis.gaussianMRStarBound L := by
    have hmul := mul_lt_mul_of_pos_right hcoef hstarpos
    simpa only [one_mul] using hmul
  exact hratio.trans hscaled

/-- The least prime strong-MR witness inherits the classified Gaussian star
bound by minimizing the prime rejection predicate over the nonempty witness set. -/
theorem exists_least_prime_witness_le_gaussian_star {n : ℕ} (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 600 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) ∧
        (s : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ∀ r : ℕ, r.Prime → ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) → s ≤ r := by
  classical
  obtain ⟨s, hs, hbound, hfail⟩ := exists_prime_witness_le_gaussian_star hnOdd hcomp hGRH hL
  have hex : ∃ r : ℕ, r.Prime ∧ ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := ⟨s, hs, hfail⟩
  exact
    ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
      (Nat.cast_le.mpr (Nat.find_min' hex ⟨hs, hfail⟩)).trans hbound, fun r hr hreject ↦
      Nat.find_min' hex ⟨hr, hreject⟩⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
