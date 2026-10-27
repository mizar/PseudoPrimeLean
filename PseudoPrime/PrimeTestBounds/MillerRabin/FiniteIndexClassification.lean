/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.NumberTheory.CarmichaelNumber
public import PseudoPrime.PrimeTestBounds.MillerRabin.FourPrimeFactorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.UnequalTwoAdicBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.SquareFactorBounds
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianKorseltTriple

/-! # Exhaustion of finite-index Miller–Rabin branches

The local branches leave only a squarefree uniform-valuation Korselt triple.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- An arithmetic finite-index dichotomy for a subgroup of the Fermat subgroup.
Either a proper local subgroup receives every ambient strong-MR pass at a
divisor modulus whose square is at most `J * n`, or `n` is a squarefree
uniform Korselt triple. This classification does not use GRH or a witness
coefficient. -/
theorem finite_index_local_subgroup_or_uniform_korselt_triple {n J : ℕ} [NeZero n] (hn1 : 1 < n)
    (hnOdd : Odd n) (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ)
    (hH : H ≤ PrimeTest.fermatSubgroup n) (hJ : 1 ≤ J) (hJ3 : J ^ 3 ≤ n) (hi : H.index ≤ J) :
    (∃ q : ℕ,
        2 ≤ q ∧
          q ∣ n ∧
          q ^ 2 ≤ J * n ∧
          ∃ K : Subgroup (ZMod q)ˣ,
            K ≠ ⊤ ∧
              ∀ a : ℕ,
                PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
                  ∃ u : (ZMod q)ˣ, u ∈ K ∧ (u : ZMod q) = (a : ZMod q)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  by_cases hNon : ∃ p : ℕ, p.Prime ∧ p ∣ n ∧ ¬p - 1 ∣ n - 1
  · obtain ⟨p, hp, hpn, hdiv⟩ := hNon
    let : Fact p.Prime := ⟨hp⟩
    obtain ⟨m, rfl⟩ := hpn
    have hmpos : 0 < m := by
      by_contra hnot
      have hm0 : m = 0 := Nat.eq_zero_of_not_pos hnot
      subst m
      simp only [mul_zero, Nat.not_lt_zero] at hn1
    have hmne : m ≠ 1 := by
      intro hm
      exact hdiv (by simpa only [hm, mul_one] using (dvd_refl (p - 1)))
    have hm1 : 1 < m := lt_of_le_of_ne (Nat.succ_le_of_lt hmpos) (Ne.symm hmne)
    have hlocalSize := PrimeTest.prime_factor_square_le_local_powerKernel_index_mul (p := p) hm1
    have hlocalIndex := PrimeTest.local_powerKernel_index_le_of_le_fermat (dvd_mul_right p m) H hH
    have hsize : p ^ 2 ≤ J * (p * m) := by
      exact hlocalSize.trans (Nat.mul_le_mul_right (p * m) (hlocalIndex.trans hi))
    let K := (powMonoidHom (p * m - 1) : (ZMod p)ˣ →* (ZMod p)ˣ).ker
    have hproper : K ≠ ⊤ := PrimeTest.local_prime_powerKernel_ne_top_of_not_dvd hdiv
    have hcontain :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass (p * m) (a : ZMod (p * m)) →
          ∃ u : (ZMod p)ˣ, u ∈ K ∧ (u : ZMod p) = (a : ZMod p) := by
      intro a ha
      exact
        PrimeTest.strongMillerRabinPass_mem_local_prime_powerKernel hn1 hnOdd (dvd_mul_right p m) ha
    exact Or.inl ⟨p, hp.two_le, dvd_mul_right p m, hsize, ⟨K, hproper, hcontain⟩⟩
  have hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1 := by
    intro p hp hpn
    exact Classical.byContradiction (fun h ↦ hNon ⟨p, hp, hpn, h⟩)
  by_cases hSq : ∃ p : ℕ, p.Prime ∧ p ^ 2 ∣ n
  · obtain ⟨p, hp, hsq⟩ := hSq
    let : Fact p.Prime := ⟨hp⟩
    have hpn : p ∣ n := dvd_trans ⟨p, by rw [pow_two]⟩ hsq
    have hpOdd := hnOdd.ne_two_of_dvd_nat hpn
    have hlow := PrimeTest.prime_le_local_square_powerKernel_index hn1 hp hpOdd hsq
    have hup := PrimeTest.local_divisor_powerKernel_index_le_of_le_fermat hsq H hH
    have hpJ : p ≤ J := hlow.trans (hup.trans hi)
    have hfourth : p ^ 4 ≤ J ^ 4 := Nat.pow_le_pow_left hpJ 4
    have hJfourth : J ^ 4 ≤ J * n := by
      calc
        J ^ 4 = J * J ^ 3 := by
          rw [pow_succ]; ring
        _ ≤ J * n := Nat.mul_le_mul_left J hJ3
    have hsize : (p ^ 2) ^ 2 ≤ J * n := by
      rw [← pow_mul]
      exact hfourth.trans hJfourth
    let K := (powMonoidHom (n - 1) : (ZMod (p ^ 2))ˣ →* (ZMod (p ^ 2))ˣ).ker
    have hproper : K ≠ ⊤ := by
      intro ht
      change p ≤ K.index at hlow
      rw [ht, Subgroup.index_top] at hlow
      exact (not_le_of_gt hp.one_lt) hlow
    have hcontain :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod (p ^ 2))ˣ, u ∈ K ∧ (u : ZMod (p ^ 2)) = (a : ZMod (p ^ 2)) := by
      intro a ha
      exact PrimeTest.strongMillerRabinPass_mem_local_divisor_powerKernel hn1 hnOdd hsq ha
    exact
      Or.inl
        ⟨p ^ 2, hp.two_le.trans (Nat.le_self_pow (by decide : 2 ≠ 0) p), hsq, hsize,
          ⟨K, hproper, hcontain⟩⟩
  have hsf : Squarefree n :=
    Nat.squarefree_iff_prime_squarefree.mpr (fun p hp hsq ↦ hSq ⟨p, hp, (pow_two p).symm ▸ hsq⟩)
  by_cases hBad :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ∣ n ∧ q ∣ n ∧ padicValNat 2 (q - 1) < padicValNat 2 (p - 1)
  · obtain ⟨p, q, hp, hq, hpn, hqn, hv⟩ := hBad
    let : Fact p.Prime := ⟨hp⟩
    let : Fact q.Prime := ⟨hq⟩
    have hpOdd := hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn)
    have hqOdd := hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn)
    have hsize' := PrimeTest.prime_factor_square_le_of_korselt hn1 hcomp hpn (hK p hp hpn)
    have hsize : p ^ 2 ≤ J * n := by
      exact hsize'.trans (Nat.le_mul_of_pos_left n (Nat.succ_le_iff.mp hJ))
    let K := (powMonoidHom (p / 2) : (ZMod p)ˣ →* (ZMod p)ˣ).ker
    have hproper := PrimeTest.local_half_powerKernel_ne_top hpOdd
    have hcontain :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ u : (ZMod p)ˣ, u ∈ K ∧ (u : ZMod p) = (a : ZMod p) := by
      intro a ha
      exact
        PrimeTest.strongMillerRabinPass_mem_local_half_kernel_of_twoAdic_lt hn1 hnOdd hpOdd hqOdd
          hpn hqn hv ha
    exact Or.inl ⟨p, hp.two_le, hpn, hsize, ⟨K, hproper, hcontain⟩⟩
  have hU :
    ∀ p q : ℕ,
      p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1) := by
    intro p q hp hq hpn hqn
    exact
      le_antisymm (le_of_not_gt (fun h ↦ hBad ⟨p, q, hp, hq, hpn, hqn, h⟩))
        (le_of_not_gt (fun h ↦ hBad ⟨q, p, hq, hp, hqn, hpn, h⟩))
  by_cases hFour : 4 ≤ n.primeFactors.card
  · obtain ⟨p, q, hp, hq, hpq, hpqn, hsize'⟩ :=
      NumberTheory.exists_prime_pair_modulus_square_le (Nat.zero_lt_of_lt hn1) hFour
    let : Fact p.Prime := ⟨hp⟩
    let : Fact q.Prime := ⟨hq⟩
    let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
    have hpn : p ∣ n := (dvd_mul_right p q).trans hpqn
    have hqn : q ∣ n := (dvd_mul_left q p).trans hpqn
    have hpOdd := hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn)
    have hqOdd := hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn)
    let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (hnOdd.ne_two_of_dvd_nat hpn).symm⟩
    let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (hnOdd.ne_two_of_dvd_nat hqn).symm⟩
    let E := 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2
    obtain ⟨kp, hkp, hEp⟩ :=
      PrimeTest.canonical_sign_exponent_local_half hp.one_lt hpOdd hn1 hnOdd (hK p hp hpn)
    obtain ⟨kq, hkq, hEq⟩ :=
      PrimeTest.canonical_sign_exponent_local_half hq.one_lt hqOdd hn1 hnOdd (hK q hq hqn)
    rw [hU q p hq hp hqn hpn] at hEq
    have hproper :=
      PrimeTest.signSubgroup_pair_ne_top_of_local_half_odd hpOdd hqOdd hpq hkp hkq hEp hEq
    have hcontain :
      ∀ a : ℕ,
        PrimeTest.StrongMillerRabinPass n (a : ZMod n) →
          ∃ v : (ZMod (p * q))ˣ,
            v ∈ PrimeTest.signSubgroup (p * q) E ∧ (v : ZMod (p * q)) = (a : ZMod (p * q)) := by
      intro a ha
      obtain ⟨u, hu, hua⟩ :=
        PrimeTest.strongMillerRabinPass_mem_signSubgroup hn1 hnOdd ha hp hpOdd hpn
      refine ⟨ZMod.unitsMap hpqn u, PrimeTest.signSubgroup_unitsMap_mem hpqn u hu, ?_⟩
      rw [ZMod.unitsMap_val, hua, ZMod.cast_natCast hpqn]
    have hsize : (p * q) ^ 2 ≤ J * n := by
      exact hsize'.trans (Nat.le_mul_of_pos_left n (Nat.succ_le_iff.mp hJ))
    exact
      Or.inl
        ⟨p * q, hp.two_le.trans (Nat.le_mul_of_pos_right p hq.pos), hpqn, hsize,
          ⟨PrimeTest.signSubgroup (p * q) E, hproper, hcontain⟩⟩
  have hn2 : 2 < n := by
    by_contra hnot
    have hnle : n ≤ 2 := Nat.le_of_not_gt hnot
    have heq : n = 2 := le_antisymm hnle (Nat.succ_le_iff.mpr hn1)
    subst n
    exact (by decide : ¬Odd 2) hnOdd
  have hC := Nat.isCarmichael_iff_korselt.mpr ⟨hn2, hcomp, hsf, hK⟩
  have hc3 : n.primeFactors.card = 3 :=
    le_antisymm (Nat.le_of_lt_succ (lt_of_not_ge hFour)) hC.three_le_card_primeFactors
  exact Or.inr ⟨hsf, hc3, hK, hU⟩

/-- At logarithmic scale 250, the low-index arithmetic classification gives
either a local LLS witness below `0.3 (log n)^2` or the remaining uniform
Korselt triple. The finite-index structure itself is supplied by the
coefficient-free dichotomy above. -/
theorem finite_index_witness_or_uniform_korselt_triple_log250 {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n)
    (hi : H.index ≤ 10 ^ 9) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 250 ≤ Real.log n) :
    (∃ p : ℕ,
        p.Prime ∧
          (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  have hN27 := Analysis.ten_pow_twentyseven_le_of_log_ge_250 hL
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 27) hN27
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  let J : ℕ := 10 ^ 9
  have hJ : 1 ≤ J := by norm_num only [J]
  have hJ3 : J ^ 3 ≤ n := by
    calc
      J ^ 3 = 10 ^ 27 := by norm_num only [J]
      _ ≤ n := hN27
  rcases
    finite_index_local_subgroup_or_uniform_korselt_triple hn1 hnOdd hcomp H hH hJ hJ3
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
      Analysis.mr_local_envelope_lt_of_square_le_log250 (Nat.pos_of_ne_zero (NeZero.ne n)) hL hqpos
        hqsize
    exact Or.inl ⟨p, hp, (hpbound.trans_lt hlocalBound).le, hpFail⟩
  · exact Or.inr htriple

/-- At logarithmic scale 240, the low-index arithmetic classification gives
either a local LLS witness below `0.3 (log n)^2` or the remaining uniform
Korselt triple. The finite-index structure itself is supplied by the
coefficient-free dichotomy above. -/
theorem finite_index_witness_or_uniform_korselt_triple_log240 {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n)
    (hi : H.index ≤ 10 ^ 9) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hL : 240 ≤ Real.log n) :
    (∃ p : ℕ,
        p.Prime ∧
          (p : ℝ) ≤ (3 / 10 : ℝ) * (Real.log n) ^ 2 ∧
          ¬PrimeTest.StrongMillerRabinPass n (p : ZMod n)) ∨
      (Squarefree n ∧
        n.primeFactors.card = 3 ∧
        (∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1) ∧
        (∀ p q : ℕ,
          p.Prime → q.Prime → p ∣ n → q ∣ n → padicValNat 2 (p - 1) = padicValNat 2 (q - 1))) := by
  have hN27 := Analysis.ten_pow_twentyseven_le_of_log_ge_240 hL
  have hn1 : 1 < n := lt_of_lt_of_le (by decide : 1 < 10 ^ 27) hN27
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  let J : ℕ := 10 ^ 9
  have hJ : 1 ≤ J := by norm_num only [J]
  have hJ3 : J ^ 3 ≤ n := by
    calc
      J ^ 3 = 10 ^ 27 := by norm_num only [J]
      _ ≤ n := hN27
  rcases
    finite_index_local_subgroup_or_uniform_korselt_triple hn1 hnOdd hcomp H hH hJ hJ3
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
      Analysis.mr_local_envelope_lt_of_square_le_log240 (Nat.pos_of_ne_zero (NeZero.ne n)) hL hqpos
        hqsize
    exact Or.inl ⟨p, hp, (hpbound.trans_lt hlocalBound).le, hpFail⟩
  · exact Or.inr htriple

/-- For odd composite n at least 10^142, a subgroup inside the Fermat subgroup
with index at most 10^9 yields a coefficient-0.282924 witness unless n is a squarefree
Korselt triple with uniform predecessor two-adic valuations. Apply the four
local witness branches and Korselt's criterion to exhaust the remaining cases.
This isolates the only finite-index branch still needing a smaller start. -/
theorem coefficient_0283_witness_or_uniform_korselt_triple {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n)
    (hi : H.index ≤ 10 ^ 9) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 142 ≤ n) :
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
    finite_index_local_subgroup_or_uniform_korselt_triple hn1 hnOdd hcomp H hH hJ hJ3
      (by simpa only [J] using hi) with
    hlocal | htriple
  · obtain ⟨q, hq, hqn, hsize, K, hproper, hpass⟩ := hlocal
    let : NeZero q := ⟨Nat.ne_zero_of_lt (lt_of_lt_of_le (by decide : 0 < 2) hq)⟩
    exact
      Or.inl
        (exists_prime_witness_le_0283_of_local_subgroup hnOdd hq hqn K hproper hpass hGRH hn
          (by simpa only [J] using hsize))
  · exact Or.inr htriple

/-- Under GRH, a squarefree odd n with exactly three prime factors, Korselt
divisibility, and uniform predecessor valuations has a coefficient-0.282924
witness for n at least 10^434782608696. Enumerate its prime factors and apply
the existing Gaussian triple theorem. This consumes the classification output. -/
theorem exists_prime_witness_le_0283_of_uniform_korselt_triple_card {n : ℕ} (hnOdd : Odd n)
    (hsf : Squarefree n) (hc : n.primeFactors.card = 3)
    (hK : ∀ p : ℕ, p.Prime → p ∣ n → p - 1 ∣ n - 1)
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
    exists_prime_witness_le_gaussian_0283_of_three_prime_korselt hp hq hr
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpn))
      (hq.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hK p hp hpn)
      (hK q hq hqn) (hK r hr hrn) (hU p q hp hq hpn hqn) (hU p r hp hr hpn hrn) hGRH hn

/-- Under GRH, an odd composite n at least 10^434782608696 has a failing prime
base at most (282924/1000000)log(n)^2 if a subgroup inside its Fermat subgroup has index
at most 10^9. Exhaust the local branches and apply the Gaussian triple result
to the sole remaining case. The subgroup need not contain all strong passes.
This closes the finite-index side at the current triple start. -/
theorem exists_prime_witness_le_0283_of_small_fermat_index {n : ℕ} [NeZero n] (hnOdd : Odd n)
    (hcomp : ¬n.Prime) (H : Subgroup (ZMod n)ˣ) (hH : H ≤ PrimeTest.fermatSubgroup n)
    (hi : H.index ≤ 10 ^ 9) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hn : 10 ^ 434782608696 ≤ n) :
    ∃ r : ℕ,
      r.Prime ∧
        (r : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (r : ZMod n) := by
  have hn142 : 10 ^ 142 ≤ n :=
    (pow_le_pow_right₀ (by decide : (1 : ℕ) ≤ 10) (by decide : (142 : ℕ) ≤ 434782608696)).trans hn
  rcases coefficient_0283_witness_or_uniform_korselt_triple hnOdd hcomp H hH hi hGRH hn142 with hw |
    ht
  · obtain ⟨r, hr, hb, hfail⟩ := hw
    exact ⟨r, hr, hb, hfail⟩
  · exact
      exists_prime_witness_le_0283_of_uniform_korselt_triple_card hnOdd ht.1 ht.2.1 ht.2.2.1
        ht.2.2.2 hGRH hn

end PseudoPrime.PrimeTestBounds.MillerRabin
