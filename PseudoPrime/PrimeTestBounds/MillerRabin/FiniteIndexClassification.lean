/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexStructure
public import PseudoPrime.PrimeTestBounds.MillerRabin.FiniteIndexScaleBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalSubgroupBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.LocalThreeTenthsBounds
public import PseudoPrime.NumberTheory.UnitPowerKernelProperness
public import Mathlib.NumberTheory.CarmichaelNumber
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianKorseltTriple

/-! # Exhaustion of finite-index Miller–Rabin branches

The local branches leave only a squarefree uniform-valuation Korselt triple.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At logarithmic scale 250, the low-index arithmetic classification gives
either a local LLS witness below `0.3 (log n)^2` or the remaining uniform
Korselt triple. The finite-index structure itself is supplied by the
coefficient-free dichotomy above. -/
theorem witness_or_uniformKorselt_log250_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 10 ^ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 250 ≤ Real.log n) :
    (∃ p : ℕ,
        p.Prime ∧
          (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  have hN27 := pow10_27_le_of_log_ge_250 hL
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 27) hN27
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  let J : ℕ := 10 ^ 9
  have hJ : 1 ≤ J := by norm_num only [J]
  have hJ3 : J ^ 3 ≤ n := by
    calc
      J ^ 3 = 10 ^ 27 := by norm_num only [J]
      _ ≤ n := hN27
  rcases
    localSubgroup_or_uniformKorseltTriple hn1 hnOdd hcomp H hH hJ hJ3
      (by simpa only [J] using hi) with
    hlocal | htriple
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
    have hqsize : q ^ 2 ≤ 10 ^ 9 * n := by simpa only [J] using hsize
    obtain ⟨p, hp, hpbound, hpFail⟩ :=
      PrimeTestBounds.MillerRabin.exists_prime_witness_le_local_subgroup_envelope hn1 hnOdd hq hqn K
        hproper hpass hGRH
    have hlocalBound :=
      local_envelope_lt_of_square_le_log250 (Nat.pos_of_ne_zero (NeZero.ne n)) hL hqpos hqsize
    exact Or.inl ⟨p, hp, (hpbound.trans_lt hlocalBound).le, hpFail⟩
  · exact Or.inr htriple

/-- At logarithmic scale 240, the low-index arithmetic classification gives
either a local LLS witness below `0.3 (log n)^2` or the remaining uniform
Korselt triple. The finite-index structure itself is supplied by the
coefficient-free dichotomy above. -/
theorem witness_or_uniformKorselt_log240_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 10 ^ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 240 ≤ Real.log n) :
    (∃ p : ℕ,
        p.Prime ∧
          (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  have hN27 := pow10_27_le_of_log_ge_240 hL
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 27) hN27
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  let J : ℕ := 10 ^ 9
  have hJ : 1 ≤ J := by norm_num only [J]
  have hJ3 : J ^ 3 ≤ n := by
    calc
      J ^ 3 = 10 ^ 27 := by norm_num only [J]
      _ ≤ n := hN27
  rcases
    localSubgroup_or_uniformKorseltTriple hn1 hnOdd hcomp H hH hJ hJ3
      (by simpa only [J] using hi) with
    hlocal | htriple
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    have hqpos : 0 < q := lt_of_lt_of_le (by decide : 0 < 2) hq
    have hqsize : q ^ 2 ≤ 10 ^ 9 * n := by simpa only [J] using hsize
    obtain ⟨p, hp, hpbound, hpFail⟩ :=
      PrimeTestBounds.MillerRabin.exists_prime_witness_le_local_subgroup_envelope hn1 hnOdd hq hqn K
        hproper hpass hGRH
    have hlocalBound :=
      local_envelope_lt_of_square_le_log240 (Nat.pos_of_ne_zero (NeZero.ne n)) hL hqpos hqsize
    exact Or.inl ⟨p, hp, (hpbound.trans_lt hlocalBound).le, hpFail⟩
  · exact Or.inr htriple

/-- For odd composite n at least 10^142, a subgroup inside the Fermat subgroup
with index at most 10^9 yields a coefficient-0.282924 witness unless n is a squarefree
Korselt triple with uniform predecessor two-adic valuations. Apply the four
local witness branches and Korselt's criterion to exhaust the remaining cases.
This isolates the only finite-index branch still needing a smaller start. -/
theorem witness_0282924_or_uniformKorselt_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n) (hcomp : ¬n.Prime)
    (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n) (hi : H.index ≤ 10 ^ 9)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 142 ≤ n) :
    (∃ r : ℕ,
        r.Prime ∧
          (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
          ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 142) hn
  let J : ℕ := 10 ^ 9
  have hJ : 1 ≤ J := by norm_num only [J]
  have hJ3 : J ^ 3 ≤ n := by
    calc
      J ^ 3 = 10 ^ 27 := by norm_num only [J]
      _ ≤ 10 ^ 142 := by norm_num only
      _ ≤ n := hn
  rcases
    localSubgroup_or_uniformKorseltTriple hn1 hnOdd hcomp H hH hJ hJ3
      (by simpa only [J] using hi) with
    hlocal | htriple
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    exact
      Or.inl
        (exists_prime_local_0282924 hnOdd hq hqn K hproper hpass hGRH hn
          (by simpa only [J] using hsize))
  · exact Or.inr htriple

/-- Under GRH, a squarefree odd n with exactly three prime factors, Korselt
divisibility, and uniform predecessor valuations has a coefficient-0.282924
witness for n at least 10^434782608696. Enumerate its prime factors and apply
the existing Gaussian triple theorem. This consumes the classification output. -/
theorem exists_prime_0282924_korseltTriple_GRH {n : ℕ} (hnOdd : Odd n) (hsf : Squarefree n)
    (hc : n.primeFactors.card = 3) (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
    (hU :
      ∀ p q : ℕ, p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hn : 10 ^ 434782608696 ≤ n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
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
    exists_prime_gaussian_0282924_korselt_GRH hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hGRH hn

/-- Under GRH, an odd composite n at least 10^434782608696 has a failing prime
base at most (282924/1000000)log(n)^2 if a subgroup inside its Fermat subgroup has index
at most 10^9. Exhaust the local branches and apply the Gaussian triple result
to the sole remaining case. The subgroup need not contain all strong passes.
This closes the finite-index side at the current triple start. -/
theorem exists_prime_0282924_smallFermatIndex_GRH {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n)
    (hi : H.index ≤ 10 ^ 9) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 434782608696 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hn142 : 10 ^ 142 ≤ n :=
    (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 10) (by decide : (142 : ℕ) ≤ 434782608696)).trans hn
  rcases witness_0282924_or_uniformKorselt_GRH hnOdd hcomp H hH hi hGRH hn142 with hw | ht
  · obtain ⟨r, hr, hb, hfail⟩ := hw
    exact ⟨r, hr, hb, hfail⟩
  · exact exists_prime_0282924_korseltTriple_GRH hnOdd ht.1 ht.2.1 ht.2.2.1 ht.2.2.2 hGRH hn

end PseudoPrime.PrimeTestBounds.MillerRabin
