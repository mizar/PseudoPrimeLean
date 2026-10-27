/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Algebra.Squarefree.Basic
public import Mathlib.Data.Finset.Defs
public import Mathlib.Data.Nat.Factorization.Basic
public import Mathlib.NumberTheory.CarmichaelNumber
public import Mathlib.NumberTheory.PrimeCounting
public import PseudoPrime.NumberTheory.PrimeProductSubgroupCounting

/-! # Finite products of primes

Finite prime-product identities and elementary divisibility facts that do not
depend on the AGP construction or Miller–Rabin testing.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory.PrimeProducts

/--
Inputs: a finite set of distinct natural primes.

Claim: the product is squarefree, and its prime factors are exactly the set.

Proof: distinct primes are pairwise coprime; use the finite-product
squarefreeness theorem and `Nat.primeFactors_prod`.

Role: supplies the prime-factor description for finite products in the
number-theory and AGP modules.
-/
theorem squarefree_prime_product_primeFactors (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    Squarefree (S.prod id) ∧ (S.prod id).primeFactors = S := by
  have hpair : Set.Pairwise (S : Set ℕ) (Function.onFun IsRelPrime fun p : ℕ => p) := by
    intro p hp q hq hpq
    exact (Nat.coprime_iff_isRelPrime).mp ((Nat.coprime_primes (hprime p hp) (hprime q hq)).2 hpq)
  have hsq : Squarefree (S.prod id) := by
    apply Finset.squarefree_prod_of_pairwise_isCoprime hpair
    intro p hp
    exact (hprime p hp).squarefree
  exact ⟨hsq, Nat.primeFactors_prod hprime⟩

/--
Inputs: a finite set of natural primes and a prime dividing their product.

Claim: the prime is one of the factors in the finite set.

Proof: use the prime-divides-finite-product criterion, then the divisors of a
prime.

Role: transfers properties of selected factors to every prime divisor of the
product.
-/
theorem exists_eq_of_prime_dvd_finset_prime_product {S : Finset ℕ} (hprime : ∀ p ∈ S, Nat.Prime p)
    {r : ℕ} (hr : Nat.Prime r) (hrdiv : r ∣ ∏ p ∈ S, p) : ∃ p ∈ S, p = r := by
  obtain ⟨p, hp, hpr⟩ :=
    (Prime.dvd_finsetProd_iff ((Nat.prime_iff).mp hr) (fun p : ℕ => p)).mp hrdiv
  rcases (hprime p hp).eq_one_or_self_of_dvd r hpr with h | h
  · exact False.elim ((Nat.ne_of_gt (Nat.Prime.one_lt hr)) h)
  · exact ⟨p, hp, h.symm⟩

/--
Inputs: a finite set whose members are congruent to `3` modulo `4`.

Claim: the product is odd.

Proof: each factor is odd; induction over the finite product preserves
oddness.

Role: provides the parity condition for products built from such primes.
-/
theorem odd_finset_product_of_mod_four_eq_three {S : Finset ℕ} (hmod : ∀ p ∈ S, p % 4 = 3) :
    Odd (∏ p ∈ S, p) := by
  classical
    induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact ⟨0, rfl⟩
  | @insert p S hpnot ih =>
    rw [Finset.prod_insert hpnot]
    have hpmod2 : p % 2 = 1 := by
      calc
        p % 2 = (p % 4) % 2 := (Nat.mod_mod_of_dvd p (by decide : 2 ∣ 4)).symm
        _ = 3 % 2 := congrArg (fun x : ℕ => x % 2) (hmod p (Finset.mem_insert_self p S))
        _ = 1 := by decide
    have hmodS : ∀ q ∈ S, q % 4 = 3 := by
      intro q hq
      exact hmod q (Finset.mem_insert_of_mem hq)
    exact (Nat.odd_iff.mpr hpmod2).mul (ih hmodS)

/--
Inputs: `p = d * k + 1` and `d ∣ L`.

Claim: `p - 1` divides `k * L`.

Proof: write `L = d * e`; then `k * L = (d * k) * e`.

Role: converts a divisor progression into the common divisibility condition
used by Korselt's criterion.
-/
theorem predecessor_dvd_mul_of_eq_mul_add_one {p d k L : ℕ} (hp : p = d * k + 1) (hd : d ∣ L) :
    p - 1 ∣ k * L := by
  rw [hp, Nat.add_sub_cancel]
  obtain ⟨e, he⟩ := hd
  refine ⟨e, ?_⟩
  calc
    k * L = k * (d * e) := congrArg (fun x : ℕ => k * x) he
    _ = (d * k) * e := by ac_rfl

/--
Purpose: collect all primes at most `z`.

Definition: filter `Finset.range (z + 1)` by primality.

Output: exactly the primes `p ≤ z`.

Role: defines finite prime products and sieve factor sets.
-/
def primeSetLE (z : ℕ) : Finset ℕ :=
  (Finset.range (z + 1)).filter Nat.Prime

/-- The cardinality of `primeSetLE z` is the prime-counting function. -/
theorem primeSetLE_card (z : ℕ) : (primeSetLE z).card = Nat.primeCounting z := by
  rw [primeSetLE, ← Nat.primesLE_eq_filter_range, Nat.primesLE_card_eq_primeCounting]

/-- The product of primes at most `z` is squarefree with the expected factors. -/
theorem primeProductLE_data (z : ℕ) :
    Squarefree ((primeSetLE z).prod id) ∧ ((primeSetLE z).prod id).primeFactors = primeSetLE z := by
  apply squarefree_prime_product_primeFactors
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- Select the primes at most `z` that are coprime to a modulus `Q`. -/
def primeSetLECoprime (z Q : ℕ) : Finset ℕ :=
  (primeSetLE z).filter (fun p => Nat.Coprime p Q)

/-- The selected prime product is squarefree with exactly the selected factors. -/
theorem primeProductLECoprime_data (z Q : ℕ) :
    Squarefree ((primeSetLECoprime z Q).prod id) ∧
      ((primeSetLECoprime z Q).prod id).primeFactors = primeSetLECoprime z Q := by
  have hprime : ∀ p ∈ primeSetLECoprime z Q, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  exact squarefree_prime_product_primeFactors (primeSetLECoprime z Q) hprime

/-- The selected prime product is coprime to `Q`. -/
theorem primeProductLECoprime_coprime (z Q : ℕ) :
    Nat.Coprime ((primeSetLECoprime z Q).prod id) Q := by
  apply Nat.Coprime.prod_left
  intro p hp
  exact (Finset.mem_filter.mp hp).2

/-- Every prime factor of the selected product is at most `z`. -/
theorem primeProductLECoprime_small (z Q : ℕ) :
    ∀ p : ℕ, Nat.Prime p → p ∣ (primeSetLECoprime z Q).prod id → p ≤ z := by
  intro p hp hpdiv
  have hPpos : (primeSetLECoprime z Q).prod id ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro q hq
    exact Nat.Prime.ne_zero ((Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).2)
  have hpFactors : p ∈ ((primeSetLECoprime z Q).prod id).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpdiv, hPpos⟩
  rw [(primeProductLECoprime_data z Q).2] at hpFactors
  have hpLE := (Finset.mem_filter.mp (Finset.mem_filter.mp hpFactors).1).1
  exact
    Nat.le_of_lt_succ (by simpa only [primeSetLE, Finset.mem_filter, Finset.mem_range] using hpLE)

/-- A squarefree `n ≤ z` coprime to `Q` divides the selected prime product. -/
theorem primeProductLECoprime_dvd_of_squarefree_le {n z Q : ℕ} (hn : Squarefree n) (hnz : n ≤ z)
    (hnQ : Nat.Coprime n Q) : n ∣ (primeSetLECoprime z Q).prod id := by
  classical
  have hn0 : n ≠ 0 := hn.ne_zero
  have hsub : n.primeFactors ⊆ ((primeSetLECoprime z Q).prod id).primeFactors := by
    intro p hp
    rw [(primeProductLECoprime_data z Q).2]
    have hp' := Nat.mem_primeFactors.mp hp
    have hpz : p ≤ z := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp'.2.1) hnz
    have hcop : Nat.Coprime p Q := Nat.Coprime.of_dvd_left hp'.2.1 hnQ
    unfold primeSetLECoprime primeSetLE
    exact
      Finset.mem_filter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpz), hp'.1⟩, hcop⟩
  have hfac : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    have hpos := hp'.1.factorization_pos_of_dvd hn0 hp'.2.1
    exact Nat.le_antisymm (hn.natFactorization_le_one p) (Nat.succ_le_of_lt hpos)
  have hnprod : n = ∏ p ∈ n.primeFactors, p := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    apply Finset.prod_congr rfl
    intro p hp
    rw [hfac p hp, pow_one]
  have hPne : (primeSetLECoprime z Q).prod id ≠ 0 := (primeProductLECoprime_data z Q).1.ne_zero
  have hprodDvd := (Nat.prod_primeFactors_dvd_iff hPne).2 hsub
  rw [hnprod]
  exact hprodDvd

/-- A squarefree `n ≤ z` divides the product of all primes at most `z`. -/
theorem primeProductLE_dvd_of_squarefree_le {n z : ℕ} (hn : Squarefree n) (hnz : n ≤ z) :
    n ∣ (primeSetLE z).prod id := by
  classical
  have hn0 : n ≠ 0 := hn.ne_zero
  have hsub : n.primeFactors ⊆ ((primeSetLE z).prod id).primeFactors := by
    intro p hp
    rw [(primeProductLE_data z).2]
    have hp' := Nat.mem_primeFactors.mp hp
    have hpz : p ≤ z := le_trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hp'.2.1) hnz
    unfold primeSetLE
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hpz), hp'.1⟩
  have hfac : ∀ p ∈ n.primeFactors, n.factorization p = 1 := by
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    have hpos := hp'.1.factorization_pos_of_dvd hn0 hp'.2.1
    exact Nat.le_antisymm (hn.natFactorization_le_one p) (Nat.succ_le_of_lt hpos)
  have hnprod : n = ∏ p ∈ n.primeFactors, p := by
    conv_lhs => rw [Nat.prod_primeFactors_pow_factorization hn0]
    apply Finset.prod_congr rfl
    intro p hp
    rw [hfac p hp, pow_one]
  have hPpos : 0 < (primeSetLE z).prod id := by
    apply Finset.prod_pos
    intro p hp
    exact Nat.Prime.pos (Finset.mem_filter.mp hp).2
  have hprodDvd := (Nat.prod_primeFactors_dvd_iff (Nat.ne_of_gt hPpos)).2 hsub
  rw [hnprod]
  exact hprodDvd

/-- The product of primes at most `z` is positive, including the empty case. -/
theorem primeProductLE_pos (z : ℕ) : 0 < (primeSetLE z).prod id := by
  apply Finset.prod_pos
  intro p hp
  exact Nat.Prime.pos (Finset.mem_filter.mp hp).2

/-- The prime-factor count of the product through `z` is `Nat.primeCounting z`. -/
theorem primeProductLE_primeFactors_card (z : ℕ) :
    (((primeSetLE z).prod id).primeFactors).card = Nat.primeCounting z := by
  have hdata := primeProductLE_data z
  rw [hdata.2, primeSetLE_card]

/--
Purpose: list products formed from exactly `s` distinct elements of a finite
prime set.

Definition: map each `s`-element subset to the product of its members.

Inputs: a finite set `P` of primes and a factor count `s`.

Output: the set of products that use exactly `s` distinct primes from `P`.

Role: this general form can represent the fixed-size divisors of the seed
integer produced by the first Proposition 1.5 application.
-/
noncomputable def fixedPrimeFactorProductsOf (P : Finset ℕ) (s : ℕ) : Finset ℕ :=
  (P.powersetCard s).image (fun U => U.prod id)

open PseudoPrime.NumberTheory in
/--
Inputs: a finite set `P` of primes and a factor count `s`.

Claim: `fixedPrimeFactorProductsOf P s` has exactly `choose P.card s` elements.

Content: unique factorization makes the product map injective on subsets of
distinct primes.

Proof: apply the prime-product injectivity lemma and the cardinality formula
for `powersetCard`.

Role: this is the exact fixed-factor divisor count for an arbitrary seed.
-/
theorem fixedPrimeFactorProductsOf_card (P : Finset ℕ) (s : ℕ) (hprime : ∀ p ∈ P, Nat.Prime p) :
    (fixedPrimeFactorProductsOf P s).card = Nat.choose P.card s := by
  classical
  rw [fixedPrimeFactorProductsOf, Finset.card_image_of_injOn]
  · exact Finset.card_powersetCard s P
  · intro U hU V hV hUV
    apply prime_finset_product_injective
    · intro p hp
      exact hprime p ((Finset.mem_powersetCard.mp hU).1 hp)
    · intro p hp
      exact hprime p ((Finset.mem_powersetCard.mp hV).1 hp)
    · exact hUV

/--
Inputs: a finite set `P` of primes and a factor count `s`.

Claim: the number of fixed-size products from `P` is at least
`(P.card + 1 - s)^s / s!`.

Content: this is the standard lower estimate for the binomial coefficient.

Proof: rewrite the exact cardinality and apply `Nat.pow_le_choose`.

Role: this exposes a quantitative lower bound for the second-stage divisor
family built from the seed prime factors.
-/
theorem fixedPrimeFactorProductsOf_card_lower_bound (P : Finset ℕ) (s : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) :
    (((P.card + 1 - s : ℕ) : ℝ) ^ s) / (s.factorial : ℝ) ≤
      ((fixedPrimeFactorProductsOf P s).card : ℝ) := by
  rw [fixedPrimeFactorProductsOf_card P s hprime]
  exact Nat.pow_le_choose (α := ℝ) s P.card

/--
Inputs: a finite factor set of size at least `2 * s` and a positive `s`.

Claim: the binomial lower bound is at least `(P.card / (2 * s)) ^ s`.

Content: `P.card + 1 - s` is at least half of `P.card`, and `s! ≤ s ^ s`.
These estimates put the fixed-size product count in the scale used in
reliable, §2.

Proof: compare the bases after division by `s`, then use the factorial bound
and `Nat.pow_le_choose`.

Role: this removes the factorial denominator when estimating the second-stage
prime supply.
-/
theorem fixedPrimeFactorProductsOf_binomial_ratio_lower_bound (P : Finset ℕ) (s : ℕ) (hs : 0 < s)
    (hsmall : 2 * s ≤ P.card) :
    ((P.card : ℝ) / (2 * (s : ℝ))) ^ s ≤ (((P.card + 1 - s : ℕ) : ℝ) ^ s) / (s.factorial : ℝ) := by
  have hsubNat : P.card ≤ 2 * (P.card + 1 - s) := by
    clear * - hsmall
    omega
  have hsubR : (P.card : ℝ) ≤ 2 * ((P.card + 1 - s : ℕ) : ℝ) := by exact_mod_cast hsubNat
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hhalf : (P.card : ℝ) / 2 ≤ ((P.card + 1 - s : ℕ) : ℝ) :=
    (div_le_iff₀ (by norm_num only : (0 : ℝ) < 2)).2 (by simpa only [mul_comm] using hsubR)
  have hratio : (P.card : ℝ) / (2 * (s : ℝ)) ≤ ((P.card + 1 - s : ℕ) : ℝ) / (s : ℝ) := by
    calc
      (P.card : ℝ) / (2 * (s : ℝ)) = ((P.card : ℝ) / 2) / (s : ℝ) := by ring
      _ ≤ ((P.card + 1 - s : ℕ) : ℝ) / (s : ℝ) := div_le_div_of_nonneg_right hhalf (le_of_lt hsR)
  have hpow : ((P.card : ℝ) / (2 * (s : ℝ))) ^ s ≤ (((P.card + 1 - s : ℕ) : ℝ) / (s : ℝ)) ^ s :=
    pow_le_pow_left₀
      (div_nonneg (Nat.cast_nonneg _) (le_of_lt (mul_pos (by norm_num only : (0 : ℝ) < 2) hsR)))
      hratio s
  have hfactNat : s.factorial ≤ s ^ s := Nat.factorial_le_pow s
  have hfactR : (s.factorial : ℝ) ≤ (s : ℝ) ^ s := by exact_mod_cast hfactNat
  have hfactPos : (0 : ℝ) < (s.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos s
  have hratio' :
    (((P.card + 1 - s : ℕ) : ℝ) / (s : ℝ)) ^ s ≤
      ((P.card + 1 - s : ℕ) : ℝ) ^ s / (s.factorial : ℝ) := by
    rw [div_pow]
    exact div_le_div_of_nonneg_left (pow_nonneg (Nat.cast_nonneg _) _) hfactPos hfactR
  exact le_trans hpow hratio'

/--
Inputs: a finite set of primes with at least `2 * s` elements and `s > 0`.

Claim: the number of products of exactly `s` distinct primes is at least
`(P.card / (2 * s)) ^ s`.

Proof: combine the binomial ratio estimate with the exact cardinality formula
for `fixedPrimeFactorProductsOf`.

Role: this is the denominator-free finite count used by the second AGP stage.
-/
theorem fixedPrimeFactorProductsOf_card_lower_bound_of_two_mul_le (P : Finset ℕ) (s : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hs : 0 < s) (hsmall : 2 * s ≤ P.card) :
    ((P.card : ℝ) / (2 * (s : ℝ))) ^ s ≤ ((fixedPrimeFactorProductsOf P s).card : ℝ) := by
  exact
    le_trans (fixedPrimeFactorProductsOf_binomial_ratio_lower_bound P s hs hsmall)
      (fixedPrimeFactorProductsOf_card_lower_bound P s hprime)

/--
Inputs: a seed-size lower bound `(T + 1) / 2 ≤ P.card` and a factor size
`s` with `4 * s ≤ T + 1`.

Claim: `T / (4 * s) ≤ P.card / (2 * s)`.

Content: the seed-size lower bound implies `T ≤ 2 * P.card`, while the scale
condition ensures the selected factor size fits in the prime-factor set.

Role: this compares the paper's seed parameter with the actual factor count.
-/
theorem fixedFactorRatio_le_of_seedFactorCount (P : Finset ℕ) (T s : ℕ)
    (hFactorCount : (T + 1) / 2 ≤ P.card) (hs : 0 < s) (hscale : 4 * s ≤ T + 1) :
    ((T : ℝ) / (4 * (s : ℝ))) ^ s ≤ ((P.card : ℝ) / (2 * (s : ℝ))) ^ s := by
  have hsmall : 2 * s ≤ P.card := by
    clear * - hFactorCount hscale
    omega
  have hTtwoNat : T ≤ 2 * P.card := by
    have hhalf : T ≤ 2 * ((T + 1) / 2) := by
      clear * - hFactorCount
      omega
    exact le_trans hhalf (Nat.mul_le_mul_left 2 hFactorCount)
  have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
  have hquarter : (T : ℝ) / 4 ≤ (P.card : ℝ) / 2 := by
    apply (div_le_div_iff₀ (by norm_num only : (0 : ℝ) < 4) (by norm_num only : (0 : ℝ) < 2)).2
    have hTtwoR : (T : ℝ) ≤ 2 * (P.card : ℝ) := by exact_mod_cast hTtwoNat
    nlinarith only [hTtwoR]
  have hratio : (T : ℝ) / (4 * (s : ℝ)) ≤ (P.card : ℝ) / (2 * (s : ℝ)) := by
    calc
      (T : ℝ) / (4 * (s : ℝ)) = ((T : ℝ) / 4) / (s : ℝ) := by ring
      _ ≤ ((P.card : ℝ) / 2) / (s : ℝ) := div_le_div_of_nonneg_right hquarter (le_of_lt hsR)
      _ = (P.card : ℝ) / (2 * (s : ℝ)) := by ring
  exact
    pow_le_pow_left₀
      (div_nonneg (Nat.cast_nonneg _) (le_of_lt (mul_pos (by norm_num only : (0 : ℝ) < 4) hsR)))
      hratio s

end PseudoPrime.NumberTheory.PrimeProducts
