/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.UnitPowerImageBounds
public import PseudoPrime.NumberTheory.PrimeFactorCongruence
public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroupCardinality
public import PseudoPrime.PrimeTest.MillerRabin.LocalFermatIndexSize

/-! # Index-four sign subgroups from local prime-factor conditions -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- For odd composite n≠9, an exponent E gives a sign subgroup of index at
least four if E is nonzero, 2*E divides n-1, and every prime factor is coprime
to E with strictly larger local two-adic valuation. A hypothetical small index
gives an image of fewer than eight elements; its modulus classification leaves
only two distinct primes, which contradict the Fermat divisibility conditions.
This is the general arithmetic index bound for the canonical MR sign exponent. -/
theorem four_le_index_signSubgroup_of_local_conditions {n E : ℕ} [NeZero n] (hn1 : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime) (hn9 : n ≠ 9) (hE : E ≠ 0) (hdiv : 2 * E ∣ n - 1)
    (hpE : ∀ p : ℕ, p.Prime → p ∣ n → ¬p ∣ E)
    (hv : ∀ p : ℕ, p.Prime → p ∣ n → padicValNat 2 E < padicValNat 2 (p - 1)) :
    4 ≤ (signSubgroup n E).index := by
  have hgt : 2 < n := lt_of_le_of_ne hn1 (Ne.symm (hnOdd.ne_two_of_dvd_nat dvd_rfl))
  let : Fact (2 < n) := ⟨hgt⟩
  have hne : (-1 : (ZMod n)ˣ) ≠ 1 := fun h ↦ ZMod.neg_one_ne_one (n := n) (congrArg Units.val h)
  obtain ⟨hroot, _⟩ :=
    NumberTheory.exists_negative_root_and_even_image_of_local_twoAdic_lt hn1 hnOdd hE hv
  have hindex := two_mul_index_signSubgroup_of_neg_one_mem_image hne hroot
  by_contra hnot
  have hi : (signSubgroup n E).index < 4 := lt_of_not_ge hnot
  have hsmall : Nat.card (powMonoidHom E : (ZMod n)ˣ →* (ZMod n)ˣ).range < 8 := by
    rw [← hindex]
    linarith only [hi]
  rcases
    NumberTheory.prime_or_nine_or_two_primes_of_card_unitPowerImage_lt_eight hn1 hnOdd hE hpE hv
      hsmall with
    hp | hn | ⟨p, q, hp, hq, hpq, rfl⟩
  · exact hnComposite hp
  · exact hn9 hn
  · let : NeZero p := ⟨hp.ne_zero⟩
    let : NeZero q := ⟨hq.ne_zero⟩
    have hp2 := hnOdd.ne_two_of_dvd_nat (dvd_mul_right p q)
    have hq2 := hnOdd.ne_two_of_dvd_nat (dvd_mul_left q p)
    have hpe : 2 ∣ p.totient / p.totient.gcd E := by
      rw [Nat.totient_prime hp]
      exact NumberTheory.two_dvd_div_gcd_of_twoAdic_lt hE (hv p hp (dvd_mul_right p q))
    have hqe : 2 ∣ q.totient / q.totient.gcd E := by
      rw [Nat.totient_prime hq]
      exact NumberTheory.two_dvd_div_gcd_of_twoAdic_lt hE (hv q hq (dvd_mul_left q p))
    rcases lt_or_gt_of_ne hpq with hlt | hgt
    · exact (not_lt_of_ge (four_le_index_signSubgroup_two_primes hp hq hp2 hq2 hlt hdiv hpe hqe)) hi
    · have hdiv' : 2 * E ∣ q * p - 1 := by simpa only [Nat.mul_comm q p] using hdiv
      have h4 := four_le_index_signSubgroup_two_primes hq hp hq2 hp2 hgt hdiv' hqe hpe
      rw [Nat.mul_comm q p] at h4
      exact (not_lt_of_ge h4) hi

/-- For odd n>1, a prime divisor with minimal two-adic valuation of p-1
defines a nonzero sign exponent E=2^(t-1)*oddPart(n-1). Twice E divides n-1,
and every prime divisor is coprime to E with larger local two-adic valuation.
Transfer the common residue-one congruence through the prime factorization and
use the canonical decomposition. These conditions drive the global index bound. -/
private theorem sign_exponent_facts_of_minimal_prime {n p : ℕ} (hn1 : 1 < n) (hnOdd : Odd n)
    (hp : p.Prime) (hpd : p ∣ n)
    (hmin : ∀ q : ℕ, q.Prime → q ∣ n → padicValNat 2 (p - 1) ≤ padicValNat 2 (q - 1)) :
    let t := padicValNat 2 (p - 1)
    let E := 2 ^ (t - 1) * Nat.divMaxPow (n - 1) 2
    E ≠ 0 ∧
      2 * E ∣ n - 1 ∧
      ∀ q : ℕ, q.Prime → q ∣ n → ¬q ∣ E ∧ padicValNat 2 E < padicValNat 2 (q - 1) := by
  let t := padicValNat 2 (p - 1)
  let d := Nat.divMaxPow (n - 1) 2
  let E := 2 ^ (t - 1) * d
  have hpOdd := hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpd)
  have ht : 0 < t := (odd_sub_canonical_decomp hp.one_lt hpOdd).1
  have hdec := odd_sub_canonical_decomp hn1 hnOdd
  have hPow : 2 ^ t ∣ n - 1 :=
    NumberTheory.dvd_sub_one_of_forall_prime_dvd (Nat.ne_zero_of_lt hn1)
      (fun q hq hd ↦ (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hq.one_lt)).mpr (hmin q hq hd))
  have hts : t ≤ padicValNat 2 (n - 1) :=
    (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hn1)).mp hPow
  have hd0 : d ≠ 0 := by
    intro h
    apply hdec.2.1.not_two_dvd_nat
    change 2 ∣ d
    rw [h]
    exact dvd_zero 2
  have hE0 : E ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) hd0
  have hval : padicValNat 2 E = t - 1 := by
    rw [padicValNat.mul (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) hd0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hdec.2.1.not_two_dvd_nat, Nat.add_zero]
  have hE2 : 2 * E = 2 ^ t * d := by
    change 2 * (2 ^ (t - 1) * d) = 2 ^ t * d
    rw [← Nat.mul_assoc, Nat.mul_comm 2 (2 ^ (t - 1)), ← pow_succ, Nat.sub_add_cancel ht]
  have hdiv : 2 * E ∣ n - 1 := by
    rw [hE2, hdec.2.2]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 hts) d
  refine ⟨hE0, hdiv, ?_⟩
  intro q hq hqd
  have hcop : q.Coprime (n - 1) :=
    ((Nat.coprime_self_sub_right hn1.le).mpr (Nat.coprime_one_right n)).of_dvd_left hqd
  refine ⟨hq.coprime_iff_not_dvd.mp (hcop.of_dvd_right ((dvd_mul_left E 2).trans hdiv)), ?_⟩
  rw [hval]
  exact lt_of_lt_of_le (Nat.sub_lt ht (by decide : 0 < 1)) (hmin q hq hqd)

/-- Every odd composite n≠9 has a unit subgroup of index at least four containing
all strong Miller–Rabin passes. Choose a prime divisor with minimal two-adic
valuation of p-1, form its sign subgroup, and apply the global image classification
and pass-containment theorem. This supplies the arithmetic input for the uniform
Gamma coefficient-0.66 witness bound without a restriction on the factorization. -/
theorem exists_index_ge_four_subgroup_containing_strongMillerRabinPass {n : ℕ} (hn1 : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime) (hn9 : n ≠ 9) :
    ∃ H : Subgroup (ZMod n)ˣ,
      4 ≤ H.index ∧
        ∀ z : ZMod n, StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨p, hpm, hmin⟩ :=
    Finset.exists_min_image n.primeFactors (fun p ↦ padicValNat 2 (p - 1))
      (Nat.nonempty_primeFactors.mpr hn1)
  have hp := (Nat.mem_primeFactors.mp hpm).1
  have hpd := (Nat.mem_primeFactors.mp hpm).2.1
  have hm : ∀ q : ℕ, q.Prime → q ∣ n → padicValNat 2 (p - 1) ≤ padicValNat 2 (q - 1) :=
    fun q hq hd ↦ hmin q (hq.mem_primeFactors hd (NeZero.ne n))
  let E := 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2
  have hfac := sign_exponent_facts_of_minimal_prime hn1 hnOdd hp hpd hm
  refine
    ⟨signSubgroup n E,
      four_le_index_signSubgroup_of_local_conditions hn1 hnOdd hnComposite hn9 hfac.1 hfac.2.1
        (fun q hq hd ↦ (hfac.2.2 q hq hd).1) (fun q hq hd ↦ (hfac.2.2 q hq hd).2),
      ?_⟩
  intro z hz
  exact
    strongMillerRabinPass_mem_signSubgroup hn1 hnOdd hz hp
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpd)) hpd

/-- The minimum-two-adic sign subgroup has index at least four, contains every
strong Miller–Rabin pass, and lies inside the Fermat subgroup. The last property
follows because twice its defining exponent divides `n - 1`; it supports the
finite-index classification when the index is below the Gamma threshold. -/
theorem exists_index_ge_four_subgroup_containing_passes_with_fermat {n : ℕ} (hn1 : 1 < n)
    (hnOdd : Odd n) (hnComposite : ¬n.Prime) (hn9 : n ≠ 9) :
    ∃ H : Subgroup (ZMod n)ˣ,
      4 ≤ H.index ∧
        H ≤ fermatSubgroup n ∧
        ∀ z : ZMod n, StrongMillerRabinPass n z → ∃ u : (ZMod n)ˣ, u ∈ H ∧ (u : ZMod n) = z := by
  let : NeZero n := ⟨Nat.ne_zero_of_lt hn1⟩
  obtain ⟨p, hpm, hmin⟩ :=
    Finset.exists_min_image n.primeFactors (fun p ↦ padicValNat 2 (p - 1))
      (Nat.nonempty_primeFactors.mpr hn1)
  have hp := (Nat.mem_primeFactors.mp hpm).1
  have hpd := (Nat.mem_primeFactors.mp hpm).2.1
  have hm : ∀ q : ℕ, q.Prime → q ∣ n → padicValNat 2 (p - 1) ≤ padicValNat 2 (q - 1) :=
    fun q hq hd ↦ hmin q (hq.mem_primeFactors hd (NeZero.ne n))
  let E := 2 ^ (padicValNat 2 (p - 1) - 1) * Nat.divMaxPow (n - 1) 2
  have hfac := sign_exponent_facts_of_minimal_prime hn1 hnOdd hp hpd hm
  refine
    ⟨signSubgroup n E,
      four_le_index_signSubgroup_of_local_conditions hn1 hnOdd hnComposite hn9 hfac.1 hfac.2.1
        (fun q hq hd ↦ (hfac.2.2 q hq hd).1) (fun q hq hd ↦ (hfac.2.2 q hq hd).2),
      signSubgroup_le_fermatSubgroup_of_two_mul_dvd hfac.2.1, ?_⟩
  intro z hz
  exact
    strongMillerRabinPass_mem_signSubgroup hn1 hnOdd hz hp
      (hp.odd_of_ne_two (hnOdd.ne_two_of_dvd_nat hpd)) hpd

/-- For odd n>1, odd d, and positive t no larger than any local valuation,
the exponent 2^(t-1)*d has a negative unit preimage. Its two-adic valuation is
t-1, so the local-to-global negative-fiber theorem applies.
This supplies the shared fiber for the exact common-sign cardinality and index formulas. -/
private theorem exists_sign_power_negative {n t d : ℕ} (hn1 : 1 < n) (hnOdd : Odd n) (ht0 : 0 < t)
    (hd : Odd d) (ht : ∀ p : ℕ, p.Prime → p ∣ n → t ≤ padicValNat 2 (p - 1)) :
    ∃ u : (ZMod n)ˣ, u ^ (2 ^ (t - 1) * d) = -1 := by
  have hd0 : d ≠ 0 := by
    intro h
    apply hd.not_two_dvd_nat
    rw [h]
    exact dvd_zero 2
  have hE : 2 ^ (t - 1) * d ≠ 0 := mul_ne_zero (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) hd0
  have hval : padicValNat 2 (2 ^ (t - 1) * d) = t - 1 := by
    rw [padicValNat.mul (pow_ne_zero _ (by decide : (2 : ℕ) ≠ 0)) hd0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hd.not_two_dvd_nat, Nat.add_zero]
  exact
    (NumberTheory.exists_negative_root_and_even_image_of_local_twoAdic_lt hn1 hnOdd hE
        (fun p hp hdvd ↦ by
          rw [hval]
          exact lt_of_lt_of_le (Nat.sub_lt ht0 (by decide : 0 < 1)) (ht p hp hdvd))).1

/-- For odd n>1, the signs in the unit group modulo n are distinct.
The modulus is greater than two, and equality of the units would imply equality
of their residues. This justifies the disjoint fibers in the exact subgroup counts. -/
private theorem units_neg_one_ne_one_of_odd {n : ℕ} (hn1 : 1 < n) (hnOdd : Odd n) :
    (-1 : (ZMod n)ˣ) ≠ 1 := by
  have hgt : 2 < n := lt_of_le_of_ne hn1 (Ne.symm (hnOdd.ne_two_of_dvd_nat dvd_rfl))
  let : Fact (2 < n) := ⟨hgt⟩
  exact fun h ↦ ZMod.neg_one_ne_one (n := n) (congrArg Units.val h)

/-- For odd n>1, odd d, and positive t bounded by every local valuation,
with each prime divisor coprime to E=2^(t-1)*d, the sign subgroup has cardinality
2^(1+r*(t-1))*prod gcd(d,oddPart(p-1)). Lift one common negative sign and double
the factorized kernel cardinality. This is the exact H_t cardinality in the MR plan. -/
theorem card_signSubgroup_of_factorization_twoAdic {n t d : ℕ} [NeZero n] (hn1 : 1 < n)
    (hnOdd : Odd n) (ht0 : 0 < t) (hd : Odd d)
    (ht : ∀ p : ℕ, p.Prime → p ∣ n → t ≤ padicValNat 2 (p - 1))
    (hpE : ∀ p : ℕ, p.Prime → p ∣ n → p.Coprime (2 ^ (t - 1) * d)) :
    Nat.card (signSubgroup n (2 ^ (t - 1) * d)) =
      2 ^ (1 + n.primeFactors.card * (t - 1)) *
        ∏ p ∈ n.primeFactors, d.gcd (Nat.divMaxPow (p - 1) 2) := by
  rw [card_signSubgroup_of_neg_one_mem_image (units_neg_one_ne_one_of_odd hn1 hnOdd)
      (exists_sign_power_negative hn1 hnOdd ht0 hd ht),
    NumberTheory.card_unitPowerKernel_factorization_twoAdic (NeZero.ne n) hnOdd hd ht hpE, pow_add,
    pow_one]
  exact (Nat.mul_assoc _ _ _).symm

/-- For odd n>1, odd d, and positive t bounded by every local valuation,
with each prime divisor coprime to E=2^(t-1)*d, the sign-subgroup index is
2^(sum(valuation(p-1)-t)+r-1) times prod p^(a-1)*oddPart(p-1)/gcd(d,oddPart(p-1)).
The power image is twice the subgroup index, and its exact factorization has
at least one factor two. This is the general MR index formula with integer quotients. -/
theorem signSubgroup_index_of_prime_factorization {n t d : ℕ} [NeZero n] (hn1 : 1 < n)
    (hnOdd : Odd n) (ht0 : 0 < t) (hd : Odd d)
    (ht : ∀ p : ℕ, p.Prime → p ∣ n → t ≤ padicValNat 2 (p - 1))
    (hpE : ∀ p : ℕ, p.Prime → p ∣ n → p.Coprime (2 ^ (t - 1) * d)) :
    (signSubgroup n (2 ^ (t - 1) * d)).index =
      2 ^ ((∑ p ∈ n.primeFactors, (padicValNat 2 (p - 1) - t)) + n.primeFactors.card - 1) *
        ∏ p ∈ n.primeFactors,
          p ^ (n.factorization p - 1) *
            (Nat.divMaxPow (p - 1) 2 / d.gcd (Nat.divMaxPow (p - 1) 2)) := by
  let S := (∑ p ∈ n.primeFactors, (padicValNat 2 (p - 1) - t)) + n.primeFactors.card
  let P :=
    ∏ p ∈ n.primeFactors,
      p ^ (n.factorization p - 1) * (Nat.divMaxPow (p - 1) 2 / d.gcd (Nat.divMaxPow (p - 1) 2))
  have hindex :=
    two_mul_index_signSubgroup_of_neg_one_mem_image (units_neg_one_ne_one_of_odd hn1 hnOdd)
      (exists_sign_power_negative hn1 hnOdd ht0 hd ht)
  have hquot :
    (signSubgroup n (2 ^ (t - 1) * d)).index =
      Nat.card (powMonoidHom (2 ^ (t - 1) * d) : (ZMod n)ˣ →* (ZMod n)ˣ).range / 2 := by
    rw [← hindex]
    exact (Nat.mul_div_cancel_left _ (by decide : 0 < 2)).symm
  rw [hquot,
    NumberTheory.card_unitPowerImage_factorization_twoAdic (NeZero.ne n) hnOdd ht0 hd ht hpE]
  change (2 ^ S * P) / 2 = 2 ^ (S - 1) * P
  have hS : 1 ≤ S :=
    (Finset.card_pos.mpr (Nat.nonempty_primeFactors.mpr hn1)).trans_le
      (Nat.le_add_left n.primeFactors.card _)
  have hpow : 2 ^ S = 2 * 2 ^ (S - 1) := by
    calc
      _ = 2 ^ (S - 1 + 1) := congrArg (fun k ↦ 2 ^ k) (Nat.sub_add_cancel hS).symm
      _ = _ := by rw [pow_succ, Nat.mul_comm]
  rw [hpow, Nat.mul_assoc, Nat.mul_div_cancel_left _ (by decide : 0 < 2)]

/-- The sign subgroup modulo 9 with exponent one has index three.
Its image has cardinality phi(9)=6, so the common-sign index is half of six.
This records the exceptional canonical MR subgroup in the index-four classification. -/
theorem signSubgroup_nine_index : (signSubgroup 9 1).index = 3 := by
  let : NeZero (9 : ℕ) := ⟨by decide⟩
  let : IsCyclic (ZMod 9)ˣ := ZMod.isCyclic_units_of_prime_pow 3 (by decide) (by decide) 2
  have hindex :=
    two_mul_index_signSubgroup_of_neg_one_mem_image
      (units_neg_one_ne_one_of_odd (by decide : 1 < 9) (by decide : Odd 9))
      (show ∃ u : (ZMod 9)ˣ, u ^ 1 = -1 from ⟨-1, pow_one _⟩)
  rw [IsCyclic.card_powMonoidHom_range, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient] at hindex
  have hphi : Nat.totient 9 = 6 := by
    change Nat.totient (3 ^ 2) = 6
    rw [Nat.totient_prime_pow (by decide : Nat.Prime 3) (by decide : 0 < 2)]
    rfl
  rw [hphi, Nat.gcd_one_right, Nat.div_one] at hindex
  linarith only [hindex]

end PseudoPrime.PrimeTest
