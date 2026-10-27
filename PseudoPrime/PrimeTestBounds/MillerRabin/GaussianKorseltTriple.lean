/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianThreePrimeSign
public import PseudoPrime.PrimeTest.MillerRabin.KorseltSignIndex
public import PseudoPrime.PrimeTest.MillerRabin.TripleTwoAdic

/-! # Gaussian coefficient 0.282924 for the complete three-prime Korselt branch

Three distinct odd prime factors with Korselt divisibility and a common
two-adic predecessor valuation give a prime failing MR base at the explicit cutoff.
Canonical exponents, index four, pass containment and conductors are derived.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- A uniform three-prime Korselt modulus determines the half exponent,
index-four common-sign subgroup, and pass containment independently of any
analytic cutoff. The returned arithmetic data can feed each witness bound. -/
theorem three_prime_korselt_sign_subgroup_data {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) :
    ∃ kp kq kr : ℕ,
      Odd kp ∧
        Odd kq ∧
        Odd kr ∧
        (n - 1) / 2 = (p / 2) * kp ∧
        (n - 1) / 2 = (q / 2) * kq ∧
        (n - 1) / 2 = (r / 2) * kr ∧
        (PrimeTest.signSubgroup n ((n - 1) / 2)).index = 4 ∧
        (∀ z : ZMod n,
          PrimeTest.StrongMillerRabinPass n z →
            ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n ((n - 1) / 2) ∧ (u : ZMod n) = z) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm (hpOdd.ne_two_of_dvd_nat (dvd_refl p)))⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm (hqOdd.ne_two_of_dvd_nat (dvd_refl q)))⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm (hrOdd.ne_two_of_dvd_nat (dvd_refl r)))⟩
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hpn : p ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hqn : q ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrn : r ∣ n := hn ▸ dvd_mul_left r (p * q)
  have hnv : padicValNat 2 (n - 1) = padicValNat 2 (p - 1) := by
    rw [hn]
    exact
      PrimeTest.twoAdic_triple_pred_eq_of_equal_predecessor_valuations hp.one_lt hq.one_lt hr.one_lt
        hpOdd hqOdd hrOdd hpv hprv
  have hpvn := hnv.symm
  have hqvn := hpv.symm.trans hpvn
  have hrvn := hprv.symm.trans hpvn
  let kp := (n - 1) / (p - 1)
  let kq := (n - 1) / (q - 1)
  let kr := (n - 1) / (r - 1)
  have hkp : Odd kp := PrimeTest.odd_korselt_quotient_of_equal_twoAdic hn1 hpdiv hpvn
  have hkq : Odd kq := PrimeTest.odd_korselt_quotient_of_equal_twoAdic hn1 hqdiv hqvn
  have hkr : Odd kr := PrimeTest.odd_korselt_quotient_of_equal_twoAdic hn1 hrdiv hrvn
  have hEp : (n - 1) / 2 = (p / 2) * kp := by
    dsimp only [kp]
    exact PrimeTest.half_exponent_eq_local_half_mul_korselt_quotient hpOdd hpdiv
  have hEq : (n - 1) / 2 = (q / 2) * kq := by
    dsimp only [kq]
    exact PrimeTest.half_exponent_eq_local_half_mul_korselt_quotient hqOdd hqdiv
  have hEr : (n - 1) / 2 = (r / 2) * kr := by
    dsimp only [kr]
    exact PrimeTest.half_exponent_eq_local_half_mul_korselt_quotient hrOdd hrdiv
  have hcopPQ : p.Coprime q :=
    hp.coprime_iff_not_dvd.mpr (fun h ↦ hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
  have hcopPR : p.Coprime r :=
    hp.coprime_iff_not_dvd.mpr (fun h ↦ hpr ((Nat.dvd_prime hr).mp h |>.resolve_left hp.ne_one))
  have hcopQR : q.Coprime r :=
    hq.coprime_iff_not_dvd.mpr (fun h ↦ hqr ((Nat.dvd_prime hr).mp h |>.resolve_left hq.ne_one))
  have hi :=
    PrimeTest.index_signSubgroup_three_primes_eq_four_of_local_half_odd hpOdd hqOdd hrOdd hkp hkq
      hkr hEp hEq hEr hcopPQ hcopPR hcopQR
  rw [← hn] at hi
  have hpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z →
        ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n ((n - 1) / 2) ∧ (u : ZMod n) = z := by
    intro z hz
    exact
      PrimeTest.strongMillerRabinPass_mem_half_signSubgroup_of_equal_twoAdic hn1 hnOdd hp hpOdd hpn
        hpvn hz
  exact ⟨kp, kq, kr, hkp, hkq, hkr, hEp, hEq, hEr, hi, hpass⟩

/-- A three-prime Korselt modulus determines the common-sign subgroup, its
index, strong-pass containment, and exact conductor-log sum independently of
any analytic cutoff. The returned data can feed each witness bound. -/
theorem three_prime_korselt_conductor_subgroup_data {n p q r : ℕ} [NeZero n] (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) :
    ∃ H : Subgroup (ZMod n)ˣ,
      H.index = 4 ∧
        (∀ z : ZMod n,
          PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) ∧
        LLS.PaperStatements.subgroupConductorLogSum H = 2 * Real.log n := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm (hpOdd.ne_two_of_dvd_nat (dvd_refl p)))⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm (hqOdd.ne_two_of_dvd_nat (dvd_refl q)))⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm (hrOdd.ne_two_of_dvd_nat (dvd_refl r)))⟩
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  have hpn : p ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hqn : q ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrn : r ∣ n := hn ▸ dvd_mul_left r (p * q)
  obtain ⟨kp, kq, kr, hkp, hkq, hkr, hEp, hEq, hEr, hi, hpass⟩ :=
    three_prime_korselt_sign_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv hqdiv
      hrdiv hpv hprv
  let H := PrimeTest.signSubgroup n ((n - 1) / 2)
  obtain ⟨a, ha⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hqOdd hpn hqn hkp hkq hEp hEq hpq
  obtain ⟨b, hb⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hpOdd hrOdd hpn hrn hkp hkr hEp hEr hpr
  obtain ⟨c, hc⟩ :=
    PrimeTest.exists_paired_sign_annihilator_with_conductor hqOdd hrOdd hqn hrn hkq hkr hEq hEr hqr
  have hnon : ∀ d : NumberTheory.subgroupAnnihilator H, 1 < d.val.conductor → d ≠ 1 := by
    intro d hd he
    rw [he, Subgroup.coe_one, DirichletCharacter.conductor_one] at hd
    exact (lt_irrefl 1) hd
  have ha1 : a ≠ 1 := hnon a (ha ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hq.pos))
  have hb1 : b ≠ 1 := hnon b (hb ▸ hp.one_lt.trans_le (Nat.le_mul_of_pos_right p hr.pos))
  have hc1 : c ≠ 1 := hnon c (hc ▸ hq.one_lt.trans_le (Nat.le_mul_of_pos_right q hr.pos))
  obtain ⟨hab, hac, hbc⟩ :=
    LLS.PaperStatements.three_characters_ne_of_pairwise_product_conductors H a b c ha hb hc hp.pos
      hq.pos hr.pos hpq hpr hqr
  have hs :=
    LLS.PaperStatements.nonprincipal_annihilator_eq_three_of_index_four H hi a b c ha1 hb1 hc1 hab
      hac hbc
  have hC :=
    LLS.PaperStatements.subgroupConductorLogSum_eq_twice_log_of_three_conductors H a b c hab hac hbc
      hs ha hb hc hp.pos hq.pos hr.pos hn
  exact ⟨H, hi, hpass, hC⟩

/-- Under GRH, a modulus n≥10^434782608696 that is the product of three
distinct odd primes satisfying Korselt divisibility and equal predecessor two-adic
valuations has a prime failing MR base at most (282924/1000000)log(n)². The odd triple
preserves the predecessor valuation; each Korselt quotient is odd. Construct the
half-exponent common-sign subgroup, prove index four and pass containment, then
apply the actual Gaussian three-prime theorem. No additional analytic, subgroup,
conductor or exponent condition remains in this three-prime branch. -/
theorem exists_prime_witness_le_gaussian_0283_of_three_prime_korselt {n p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hN : 10 ^ 434782608696 ≤ n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ (282924 / 1000000 : ℝ) * (Real.log n) ^ 2 ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  let : Fact p.Prime := ⟨hp⟩
  let : Fact q.Prime := ⟨hq⟩
  let : Fact r.Prime := ⟨hr⟩
  let : Fact (2 < p) := ⟨lt_of_le_of_ne hp.two_le (Ne.symm (hpOdd.ne_two_of_dvd_nat (dvd_refl p)))⟩
  let : Fact (2 < q) := ⟨lt_of_le_of_ne hq.two_le (Ne.symm (hqOdd.ne_two_of_dvd_nat (dvd_refl q)))⟩
  let : Fact (2 < r) := ⟨lt_of_le_of_ne hr.two_le (Ne.symm (hrOdd.ne_two_of_dvd_nat (dvd_refl r)))⟩
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hpn : p ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_right p q) r
  have hqn : q ∣ n := hn ▸ dvd_mul_of_dvd_left (dvd_mul_left q p) r
  have hrn : r ∣ n := hn ▸ dvd_mul_left r (p * q)
  have hnv : padicValNat 2 (n - 1) = padicValNat 2 (p - 1) := by
    rw [hn]
    exact
      PrimeTest.twoAdic_triple_pred_eq_of_equal_predecessor_valuations hp.one_lt hq.one_lt hr.one_lt
        hpOdd hqOdd hrOdd hpv hprv
  have hpvn := hnv.symm
  have hqvn := hpv.symm.trans hpvn
  have hrvn := hprv.symm.trans hpvn
  have hkp := PrimeTest.odd_korselt_quotient_of_equal_twoAdic hn1 hpdiv hpvn
  have hkq := PrimeTest.odd_korselt_quotient_of_equal_twoAdic hn1 hqdiv hqvn
  have hkr := PrimeTest.odd_korselt_quotient_of_equal_twoAdic hn1 hrdiv hrvn
  have hEp := PrimeTest.half_exponent_eq_local_half_mul_korselt_quotient hpOdd hpdiv
  have hEq := PrimeTest.half_exponent_eq_local_half_mul_korselt_quotient hqOdd hqdiv
  have hEr := PrimeTest.half_exponent_eq_local_half_mul_korselt_quotient hrOdd hrdiv
  have hcopPQ : p.Coprime q :=
    hp.coprime_iff_not_dvd.mpr (fun h ↦ hpq ((Nat.dvd_prime hq).mp h |>.resolve_left hp.ne_one))
  have hcopPR : p.Coprime r :=
    hp.coprime_iff_not_dvd.mpr (fun h ↦ hpr ((Nat.dvd_prime hr).mp h |>.resolve_left hp.ne_one))
  have hcopQR : q.Coprime r :=
    hq.coprime_iff_not_dvd.mpr (fun h ↦ hqr ((Nat.dvd_prime hr).mp h |>.resolve_left hq.ne_one))
  have hi :=
    PrimeTest.index_signSubgroup_three_primes_eq_four_of_local_half_odd hpOdd hqOdd hrOdd hkp hkq
      hkr hEp hEq hEr hcopPQ hcopPR hcopQR
  rw [← hn] at hi
  have hpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z →
        ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n ((n - 1) / 2) ∧ (u : ZMod n) = z := by
    intro z hz
    exact
      PrimeTest.strongMillerRabinPass_mem_half_signSubgroup_of_equal_twoAdic hn1 hnOdd hp hpOdd hpn
        hpvn hz
  exact
    exists_prime_witness_le_gaussian_0283_of_three_prime_sign_subgroup hnOdd hpOdd hqOdd hrOdd hpn
      hqn hrn hkp hkq hkr hEp hEq hEr hpq hpr hqr hn hi hpass hGRH hN

/-- At scale `600`, a three-prime Korselt modulus with a common predecessor
two-adic valuation has a prime failing strong MR below the classified Gaussian
star bound. -/
theorem exists_prime_witness_le_gaussian_star_of_three_prime_korselt {n p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 600 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMRStarBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact exists_prime_witness_le_gaussian_star_of_index_four hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- For a uniform three-prime Korselt modulus, the shared arithmetic subgroup
data closes the new Gamma index-100 bound from logarithmic scale 330. -/
theorem exists_prime_witness_le_gammaIndex100_of_three_prime_korselt {n p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 330 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gammaIndex100Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact
    exists_prime_witness_le_gammaIndex100_of_index_four_conductor hnlarge hnOdd H hi hpass hGRH
      hC.le hL

/-- A uniform three-prime Korselt modulus has a witness below the 6/5
Gaussian bound from logarithmic scale 500. -/
theorem exists_prime_witness_le_gaussian6fifths_of_three_prime_korselt {n p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6FifthsBound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact exists_prime_witness_le_gaussian6fifths_of_index_four hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- A uniform three-prime Korselt modulus has a witness below the constant-6
Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_witness_le_gaussianMR6_of_three_prime_korselt {n p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR6Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact exists_prime_witness_le_gaussianMR6_of_index_four hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- A uniform three-prime Korselt modulus has a witness below the
prefix-improved constant-18 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_witness_le_gaussianMR18_of_three_prime_korselt {n p q r : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q)
    (hpr : p ≠ r) (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ Analysis.gaussianMR18Bound (Real.log n) ∧
        ¬PrimeTest.StrongMillerRabinPass n (s : ZMod n) := by
  have hnOdd : Odd n := hn ▸ (hpOdd.mul hqOdd).mul hrOdd
  have hn1 : 1 < n :=
    hn ▸
      hp.one_lt.trans_le
        ((Nat.le_mul_of_pos_right p hq.pos).trans (Nat.le_mul_of_pos_right (p * q) hr.pos))
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨H, hi, hpass, hC⟩ :=
    three_prime_korselt_conductor_subgroup_data hp hq hr hpOdd hqOdd hrOdd hpq hpr hqr hn hpdiv
      hqdiv hrdiv hpv hprv
  exact exists_prime_witness_le_gaussianMR18_of_index_four hnOdd hnlarge H hi hpass hGRH hC.le hL

end PseudoPrime.PrimeTestBounds.MillerRabin
