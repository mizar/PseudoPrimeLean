/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianThreePrimeSign
public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltSubgroup

/-! # Gaussian coefficient 0.282924 for the complete three-prime Korselt branch

Three distinct odd prime factors with Korselt divisibility and a common
two-adic predecessor valuation give a prime failing MR base at the explicit cutoff.
Canonical exponents, index four, pass containment and conductors are derived.
-/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Under GRH, a modulus n≥10^434782608696 that is the product of three
distinct odd primes satisfying Korselt divisibility and equal predecessor two-adic
valuations has a prime failing MR base at most (282924/1000000)log(n)². The odd triple
preserves the predecessor valuation; each Korselt quotient is odd. Construct the
half-exponent common-sign subgroup, prove index four and pass containment, then
apply the actual Gaussian three-prime theorem. No additional analytic, subgroup,
conductor or exponent condition remains in this three-prime branch. -/
theorem exists_prime_gaussian_0282924_korselt_GRH {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
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
      PrimeTest.twoAdic_triple_pred_eq_of_pred_valuations hp.one_lt hq.one_lt hr.one_lt hpOdd hqOdd
        hrOdd hpv hprv
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
    PrimeTest.signSubgroup_index_three_primes_eq_four hpOdd hqOdd hrOdd hkp hkq hkr hEp hEq hEr
      hcopPQ hcopPR hcopQR
  rw [← hn] at hi
  have hpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z →
        ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n ((n - 1) / 2) ∧ (u : ZMod n) = z := by
    intro z hz
    exact PrimeTest.strongPass_mem_half_signSubgroup_of_twoAdic_eq hn1 hnOdd hp hpOdd hpn hpvn hz
  exact
    exists_prime_gaussian_0282924_signTriple_GRH hnOdd hpOdd hqOdd hrOdd hpn hqn hrn hkp hkq hkr hEp
      hEq hEr hpq hpr hqr hn hi hpass hGRH hN

/-- For a uniform three-prime Korselt modulus, the shared arithmetic subgroup
data closes the new Gamma index-100 bound from logarithmic scale 330. -/
theorem exists_prime_gamma100_threeKorselt_GRH {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
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
  exact exists_prime_gamma100_indexFour_GRH hnlarge hnOdd H hi hpass hGRH hC.le hL

/-- A uniform three-prime Korselt modulus has a witness below the 6/5
Gaussian bound from logarithmic scale 500. -/
theorem gaussian6_5_primeWitness_threeKorselt_GRH {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 500 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gaussian6FifthsBound (Real.log n) ∧
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
  exact gaussian6_5_primeWitness_index_four_GRH hnOdd hnlarge H hi hpass hGRH hC.le hL

/-- A uniform three-prime Korselt modulus has a witness below the
prefix-improved constant-18 Gaussian bound from logarithmic scale 300. -/
theorem exists_prime_gaussian18_threeKorselt_GRH {n p q r : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hr : r.Prime) (hpOdd : Odd p) (hqOdd : Odd q) (hrOdd : Odd r) (hpq : p ≠ q) (hpr : p ≠ r)
    (hqr : q ≠ r) (hn : n = p * q * r) (hpdiv : p - 1 ∣ n - 1) (hqdiv : q - 1 ∣ n - 1)
    (hrdiv : r - 1 ∣ n - 1) (hpv : padicValNat 2 (p - 1) = padicValNat 2 (q - 1))
    (hprv : padicValNat 2 (p - 1) = padicValNat 2 (r - 1)) (hnlarge : 20000 ≤ n)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hL : 300 ≤ Real.log n) :
    ∃ s : ℕ,
      s.Prime ∧
        (s : ℝ) ≤ gaussian18Bound (Real.log n) ∧
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
  exact exists_prime_gaussian18_indexFour_GRH hnOdd hnlarge H hi hpass hGRH hC.le hL

end PseudoPrime.PrimeTestBounds.MillerRabin
