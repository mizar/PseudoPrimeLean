/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.UniformKorseltTriple
public import PseudoPrime.PrimeTest.MillerRabin.PairedQuadraticAnnihilator
public import PseudoPrime.PrimeTest.MillerRabin.KorseltSignIndex
public import PseudoPrime.PrimeTest.MillerRabin.TripleTwoAdic
public import PseudoPrime.LLS.PaperStatements.ThreeConductorSum

/-! Arithmetic subgroup data for uniform three-prime Korselt moduli. -/

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
      PrimeTest.twoAdic_triple_pred_eq_of_pred_valuations hp.one_lt hq.one_lt hr.one_lt hpOdd hqOdd
        hrOdd hpv hprv
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
    PrimeTest.signSubgroup_index_three_primes_eq_four hpOdd hqOdd hrOdd hkp hkq hkr hEp hEq hEr
      hcopPQ hcopPR hcopQR
  rw [← hn] at hi
  have hpass :
    ∀ z : ZMod n,
      PrimeTest.StrongMillerRabinPass n z →
        ∃ u : (ZMod n)ˣ, u ∈ PrimeTest.signSubgroup n ((n - 1) / 2) ∧ (u : ZMod n) = z := by
    intro z hz
    exact PrimeTest.strongPass_mem_half_signSubgroup_of_twoAdic_eq hn1 hnOdd hp hpOdd hpn hpvn hz
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
    LLS.PaperStatements.three_characters_ne_of_product_conductors H a b c ha hb hc hp.pos hq.pos
      hr.pos hpq hpr hqr
  have hs :=
    LLS.PaperStatements.nonprincipal_annihilator_eq_three_of_index_four H hi a b c ha1 hb1 hc1 hab
      hac hbc
  have hC :=
    LLS.PaperStatements.subgroupConductorLogSum_eq_two_log_of_three H a b c hab hac hbc hs ha hb hc
      hp.pos hq.pos hr.pos hn
  exact ⟨H, hi, hpass, hC⟩

/-- An odd uniform Korselt triple supplies an index-four subgroup containing
all strong-MR passing residues, with conductor-log sum exactly `2 log n`.
Enumerating the three prime factors connects the factorization predicate to
the existing common-sign subgroup construction. -/
theorem uniformKorselt_subgroup_data {n : ℕ} [NeZero n] (ho : Odd n) (hu : UniformKorseltTriple n) :
    ∃ H : Subgroup (ZMod n)ˣ,
      H.index = 4 ∧
        (∀ z : ZMod n,
          PrimeTest.StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z) ∧
        LLS.PaperStatements.subgroupConductorLogSum H = 2 * Real.log n := by
  obtain ⟨p, q, r, hpq, hpr, hqr, hset⟩ := Finset.card_eq_three.mp hu.2.1
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
  have hprod := (Nat.prod_primeFactors_of_squarefree hu.1).symm
  rw [hset] at hprod
  have hnprod : n = p * q * r := by
    simpa only [Finset.prod_insert, Finset.prod_singleton, Finset.mem_insert, Finset.mem_singleton,
      hpq, hpr, hqr, or_self, not_false_eq_true, mul_assoc] using hprod
  exact
    three_prime_korselt_conductor_subgroup_data hp hq hr
      (hp.odd_of_ne_two (ho.ne_two_of_dvd_nat hpn)) (hq.odd_of_ne_two (ho.ne_two_of_dvd_nat hqn))
      (hr.odd_of_ne_two (ho.ne_two_of_dvd_nat hrn)) hpq hpr hqr hnprod (hu.2.2.1 p hp hpn)
      (hu.2.2.1 q hq hqn) (hu.2.2.1 r hr hrn) (hu.2.2.2 p q hp hq hpn hqn)
      (hu.2.2.2 p r hp hr hpn hrn)

end PseudoPrime.PrimeTestBounds.MillerRabin
