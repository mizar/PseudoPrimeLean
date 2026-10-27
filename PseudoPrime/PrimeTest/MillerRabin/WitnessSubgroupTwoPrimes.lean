/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.WitnessSubgroupCardinality

/-! # Index-four pass-containing subgroups for two distinct odd primes -/

@[expose] public section

namespace PseudoPrime.PrimeTest

/-- A divisor common to m-1 and n-1 divides m*n-1 when m,n are positive.
Multiplication of congruences with residue one proves the claim. This transfers
the smaller local two-adic exponent to the canonical decomposition of the product. -/
private theorem dvd_product_sub_one {m n k : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) (hkm : k ∣ m - 1)
    (hkn : k ∣ n - 1) : k ∣ m * n - 1 := by
  have h := ((Nat.modEq_iff_dvd' hm).mpr hkm).mul ((Nat.modEq_iff_dvd' hn).mpr hkn)
  rw [one_mul] at h
  exact h.dvd'

/-- For two odd primes, choose the sign exponent using the smaller two-adic
valuation of p-1 and q-1 and the odd part of p*q-1. It is nonzero, twice it divides
p*q-1, and both local power images are even. Congruence multiplication bounds
the product valuation, and quotient valuations certify the local image conditions.
These are the arithmetic inputs for the two-prime index-four theorem. -/
private theorem two_prime_sign_exponent_facts {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hp2 : p ≠ 2)
    (hq2 : q ≠ 2) :
    let t := min (padicValNat 2 (p - 1)) (padicValNat 2 (q - 1))
    let E := 2 ^ (t - 1) * Nat.divMaxPow (p * q - 1) 2
    E ≠ 0 ∧
      2 * E ∣ p * q - 1 ∧ 2 ∣ p.totient / p.totient.gcd E ∧ 2 ∣ q.totient / q.totient.gcd E := by
  let t := min (padicValNat 2 (p - 1)) (padicValNat 2 (q - 1))
  let d := Nat.divMaxPow (p * q - 1) 2
  let E := 2 ^ (t - 1) * d
  have hn : 1 < p * q := by nlinarith only [hp.two_le, hq.two_le]
  have hdec := odd_sub_canonical_decomp hn ((hp.odd_of_ne_two hp2).mul (hq.odd_of_ne_two hq2))
  have ht : 0 < t :=
    lt_min (odd_sub_canonical_decomp hp.one_lt (hp.odd_of_ne_two hp2)).1
      (odd_sub_canonical_decomp hq.one_lt (hq.odd_of_ne_two hq2)).1
  have hdp : 2 ^ t ∣ p - 1 :=
    (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hp.one_lt)).mpr (min_le_left _ _)
  have hdq : 2 ^ t ∣ q - 1 :=
    (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hq.one_lt)).mpr (min_le_right _ _)
  have hts : t ≤ padicValNat 2 (p * q - 1) :=
    (padicValNat_dvd_iff_le (Nat.sub_ne_zero_of_lt hn)).mp
      (dvd_product_sub_one hp.one_lt.le hq.one_lt.le hdp hdq)
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
  refine ⟨hE0, ?_, ?_, ?_⟩
  · rw [hE2, hdec.2.2]
    exact Nat.mul_dvd_mul_right (pow_dvd_pow 2 hts) d
  · apply NumberTheory.two_dvd_div_gcd_of_twoAdic_lt hE0
    rw [hval, Nat.totient_prime hp]
    exact lt_of_lt_of_le (Nat.sub_lt ht (by decide : 0 < 1)) (min_le_left _ _)
  · apply NumberTheory.two_dvd_div_gcd_of_twoAdic_lt hE0
    rw [hval, Nat.totient_prime hq]
    exact lt_of_lt_of_le (Nat.sub_lt ht (by decide : 0 < 1)) (min_le_right _ _)

/-- For two distinct odd primes p<q, there is a subgroup of units modulo p*q
of index at least four containing every strong Miller–Rabin pass. Choose the
sign subgroup from the smaller local two-adic exponent. The local even-image
conditions exclude index two, and reduction to the prime attaining the minimum
proves pass containment. This closes the squarefree two-prime subgroup branch. -/
theorem exists_index_ge_four_subgroup_containing_passes_two_primes {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hp2 : p ≠ 2) (hq2 : q ≠ 2) (hpq : p < q) :
    ∃ H : Subgroup (ZMod (p * q))ˣ,
      4 ≤ H.index ∧
        ∀ z : ZMod (p * q),
          StrongMillerRabinPass (p * q) z →
            ∃ u : (ZMod (p * q))ˣ, u ∈ H ∧ (u : ZMod (p * q)) = z := by
  let : NeZero p := ⟨hp.ne_zero⟩
  let : NeZero q := ⟨hq.ne_zero⟩
  let : NeZero (p * q) := ⟨mul_ne_zero hp.ne_zero hq.ne_zero⟩
  let E :=
    2 ^ (min (padicValNat 2 (p - 1)) (padicValNat 2 (q - 1)) - 1) * Nat.divMaxPow (p * q - 1) 2
  have hfac := two_prime_sign_exponent_facts hp hq hp2 hq2
  refine
    ⟨signSubgroup (p * q) E,
      four_le_index_signSubgroup_two_primes hp hq hp2 hq2 hpq hfac.2.1 hfac.2.2.1 hfac.2.2.2, ?_⟩
  have hn : 1 < p * q := by nlinarith only [hp.two_le, hq.two_le]
  have hnOdd := (hp.odd_of_ne_two hp2).mul (hq.odd_of_ne_two hq2)
  intro z hz
  by_cases hmin : padicValNat 2 (p - 1) ≤ padicValNat 2 (q - 1)
  · dsimp only [E]
    rw [min_eq_left hmin]
    exact
      strongMillerRabinPass_mem_signSubgroup hn hnOdd hz hp (hp.odd_of_ne_two hp2)
        (dvd_mul_right p q)
  · dsimp only [E]
    rw [min_eq_right (le_of_not_ge hmin)]
    exact
      strongMillerRabinPass_mem_signSubgroup hn hnOdd hz hq (hq.odd_of_ne_two hq2)
        (dvd_mul_left q p)

end PseudoPrime.PrimeTest
