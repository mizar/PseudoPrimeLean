/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.SeedModulus
public import PseudoPrime.NumberTheory.PrimeProducts
public import PseudoPrime.NumberTheory.TotientProductBounds

/-! # PrimeProductBounds

Primorial, fixed-factor product, and explicit scale estimates.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: the seed data and cutoff condition used by the original arithmetic
completion interface.

Claim: the tail product has the same modulus-four properties and size bounds
as `seed_auxiliary_modulus_arithmetic_bounds_of_N_le_x`.

Content: the cutoff is at most `x`, so the supplied condition `N ≤ cutoff`
implies the bound `N ≤ x` required by the generalized result.

Role: this preserves the existing interface for constructions that place the
entire initial modulus below the Proposition 1.5 cutoff.
-/
theorem seed_auxiliary_modulus_arithmetic_bounds {x N T k : ℕ} {S : Finset ℕ} {L : ℕ} (hx : 2 ≤ x)
    (hNpos : 0 < N) (hNcut : N ≤ reliableProp15DivisorCutoff x) (hk : 0 < k) (hkpow : k ^ 5 ≤ x ^ 3)
    (hScard : S.card = T + 1) (hTpower : (T + 1) ^ 4 ≤ x)
    (hS :
      ∀ p ∈ S, Nat.Prime p ∧ p ≤ x ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1)
    (hL : L = (S.filter (fun p => 60 * S.card < p)).prod id) (hLsq : Squarefree L)
    (hLprimeFactors : L.primeFactors = S.filter (fun p => 60 * S.card < p))
    (hLreciprocal : (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ))
    (hLlambda : ArithmeticFunction.carmichael L ∣ k * N)
    (hprimeCount : 2 * Nat.primeCounting (60 * S.card) ≤ S.card) :
    Nat.Coprime L 4 ∧
      L.primeFactors.card ^ 4 ≤ x ∧
      (∀ r, r ∣ L → Nat.Prime r → r ≤ x) ∧
      2 < L ∧
      3 ≤ ArithmeticFunction.carmichael L ∧
      ReliableProp15ModFourInput L x ∧
      L ≤ x ^ (T + 1) ∧ ArithmeticFunction.carmichael L ≤ x ^ 2 := by
  have hxone : 1 ≤ x := le_trans (by norm_num only : 1 ≤ 2) hx
  have hNleX : N ≤ x := le_trans hNcut (reliableProp15DivisorCutoff_le_self hxone)
  exact
    seed_auxiliary_modulus_arithmetic_bounds_of_N_le_x hx hNpos hNleX hk hkpow hScard hTpower hS hL
      hLsq hLprimeFactors hLreciprocal hLlambda hprimeCount

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a natural cutoff `z`.

Claim: the prime product `N_z` lies below the divisor cutoff for `N_z ^ 5`.

Content: the fifth-power cutoff lemma applies because `N_z` is positive.

Proof: combine `primeProductLE_pos` with
`le_reliableProp15DivisorCutoff_fifth_power`.

Role: this gives a canonical prime-supply parameter for the full-divisor
initial-count bridge.
-/
theorem primeProductLE_le_divisorCutoff_fifth_power (z : ℕ) :
    (primeSetLE z).prod id ≤ reliableProp15DivisorCutoff ((primeSetLE z).prod id ^ 5) := by
  exact le_reliableProp15DivisorCutoff_fifth_power ((primeSetLE z).prod id) (primeProductLE_pos z)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Purpose: enumerate products of exactly `s` distinct primes at most `z`.

Definition: take the products of all `s`-element subsets of `primeSetLE z`.

Inputs: a prime cutoff `z` and a requested number `s` of prime factors.

Output: a finite set of squarefree divisors of the primorial whose elements
are at most `z ^ s`.

Role: this is the fixed-prime-factor divisor family used in reliable §2.
-/
def fixedPrimeFactorProducts (z s : ℕ) : Finset ℕ :=
  (primeSetLE z).powersetCard s |>.image (fun U ↦ U.prod id)

open PseudoPrime.NumberTheory.PrimeProducts in
open PseudoPrime.NumberTheory in
/--
Inputs: a prime cutoff `z` and a factor count `s`.

Claim: `fixedPrimeFactorProducts z s` has exactly `choose (π(z), s)` elements.

Content: distinct subsets give distinct products by unique factorization.

Proof: use injectivity of finite products of distinct primes and the
cardinality formula for `powersetCard`.

Role: this is the binomial divisor count in the first reliable §2 construction.
-/
theorem fixedPrimeFactorProducts_card (z s : ℕ) :
    (fixedPrimeFactorProducts z s).card = Nat.choose (Nat.primeCounting z) s := by
  classical
  rw [fixedPrimeFactorProducts, Finset.card_image_of_injOn]
  · rw [Finset.card_powersetCard, primeSetLE_card]
  · intro U hU V hV hUV
    apply prime_finset_product_injective
    · intro p hp
      exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hU).1 hp)).2
    · intro p hp
      exact (Finset.mem_filter.mp ((Finset.mem_powersetCard.mp hV).1 hp)).2
    · exact hUV

/--
Inputs: a prime cutoff `z` and a factor count `s`.

Claim: the number of fixed-factor prime products is at least
$(\pi(z)+1-s)^s/s!$.

Content: the lower bound is the standard binomial estimate used to quantify
the divisor supply in reliable §2.

Proof: rewrite the exact cardinality as a binomial coefficient and apply
`Nat.pow_le_choose` over the reals.

Role: this exposes the explicit lower estimate needed for choosing the initial
prime-product parameters.
-/
theorem fixedPrimeFactorProducts_card_lower_bound (z s : ℕ) :
    (((Nat.primeCounting z + 1 - s : ℕ) : ℝ) ^ s) / (s.factorial : ℝ) ≤
      ((fixedPrimeFactorProducts z s).card : ℝ) := by
  rw [fixedPrimeFactorProducts_card]
  exact Nat.pow_le_choose (α := ℝ) s (Nat.primeCounting z)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a seed-size lower bound `(T + 1) / 2 ≤ P.card` and a factor size
`s` with `4 * s ≤ T + 1`.

Claim: `(T / (4 * s)) ^ s` is at most the fixed-factor product count.

Content: the seed-size hypotheses imply both `2 * s ≤ P.card` and
`T / (4 * s) ≤ P.card / (2 * s)`; the previous binomial estimate then applies.

Role: this carries the first-stage seed parameter directly into the second
stage's divisor count.
-/
theorem fixedPrimeFactorProductsOf_card_lower_bound_of_seed_factor_count (P : Finset ℕ) (T s : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hFactorCount : (T + 1) / 2 ≤ P.card) (hs : 0 < s)
    (hscale : 4 * s ≤ T + 1) :
    ((T : ℝ) / (4 * (s : ℝ))) ^ s ≤ ((fixedPrimeFactorProductsOf P s).card : ℝ) := by
  have hsmall : 2 * s ≤ P.card := by
    clear * - hFactorCount hscale
    omega
  have hTtoP := fixedFactorRatio_le_of_seedFactorCount P T s hFactorCount hs hscale
  exact
    le_trans hTtoP (fixedPrimeFactorProductsOf_card_lower_bound_of_two_mul_le P s hprime hs hsmall)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a nonzero squarefree modulus `L`, a finite subset of its prime
factors, and a bound for each selected prime.

Claim: every product of exactly `s` selected prime factors belongs to
`restrictedDivisors L y` whenever the `s`-fold size bound is at most `y`.

Content: the subset product divides the squarefree product `L`, while its
size is bounded by multiplying the common prime bound `s` times.

Proof: use divisibility of products over subsets and `prod_le_pow_card`.

Role: this supplies the finite divisor inclusion needed for the second,
modulus-four application of Proposition 1.5.
-/
theorem fixedPrimeFactorProductsOf_subset_restrictedDivisors {L y s B : ℕ} {P : Finset ℕ}
    (hL : L ≠ 0) (hSquarefree : Squarefree L) (hP : P ⊆ L.primeFactors) (hPbound : ∀ p ∈ P, p ≤ B)
    (hcut : B ^ s ≤ y) {d : ℕ} (hd : d ∈ fixedPrimeFactorProductsOf P s) :
    d ∈ restrictedDivisors L y := by
  classical
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hd
  have hU' := Finset.mem_powersetCard.mp hU
  apply Finset.mem_filter.mpr
  constructor
  · rw [Nat.mem_divisors]
    constructor
    · calc
        U.prod id ∣ P.prod id := Finset.prod_dvd_prod_of_subset U P id hU'.1
        _ ∣ L.primeFactors.prod id := Finset.prod_dvd_prod_of_subset P L.primeFactors id hP
        _ = L := by
          change (∏ p ∈ L.primeFactors, p) = L
          exact Nat.prod_primeFactors_of_squarefree hSquarefree
    · exact hL
  · calc
      U.prod id ≤ B ^ U.card := Finset.prod_le_pow_card U id B (fun p hp => hPbound p (hU'.1 hp))
      _ = B ^ s := by rw [hU'.2]
      _ ≤ y := hcut

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a nonzero squarefree modulus, a finite subset of its prime factors,
and a common bound for the selected primes.

Claim: the binomial lower bound for the fixed-size product family also bounds
the cardinality of the corresponding restricted divisors.

Proof: inject the product family into the restricted divisor set, then apply
the binomial estimate for its exact cardinality.

Role: this is the finite counting bridge from the seed prime factors to the
second application of Proposition 1.5.
-/
theorem fixedPrimeFactorProductsOf_lower_bound_restrictedDivisors {L y s B : ℕ} {P : Finset ℕ}
    (hL : L ≠ 0) (hSquarefree : Squarefree L) (hP : P ⊆ L.primeFactors)
    (hPprime : ∀ p ∈ P, Nat.Prime p) (hPbound : ∀ p ∈ P, p ≤ B) (hcut : B ^ s ≤ y) :
    (((P.card + 1 - s : ℕ) : ℝ) ^ s) / (s.factorial : ℝ) ≤ ((restrictedDivisors L y).card : ℝ) := by
  have hcard : (fixedPrimeFactorProductsOf P s).card ≤ (restrictedDivisors L y).card := by
    apply Finset.card_le_card
    intro d hd
    exact fixedPrimeFactorProductsOf_subset_restrictedDivisors hL hSquarefree hP hPbound hcut hd
  have hlower :
    (((P.card + 1 - s : ℕ) : ℝ) ^ s) / (s.factorial : ℝ) ≤
      ((fixedPrimeFactorProductsOf P s).card : ℝ) :=
    fixedPrimeFactorProductsOf_card_lower_bound P s hPprime
  exact le_trans hlower (Nat.cast_le.mpr hcard)

/--
Inputs: a nonzero squarefree modulus L, a common bound for its prime
factors, and a cutoff containing every product of s bounded factors.

Claim: the binomial lower bound formed from the number of prime factors of L
is a lower bound for the restricted divisors of L.

Proof: specialize the finite-prime-set divisor bridge to all prime factors of
L, deriving their primality and size bound from prime-factor membership.

Role: this is the direct divisor-count interface for the second Proposition
1.5 application to the seed-tail product.
-/
theorem primeFactorProducts_lower_bound_restrictedDivisors {L y s B : ℕ} (hL : L ≠ 0)
    (hSquarefree : Squarefree L) (hFactorBound : ∀ r, r ∣ L → Nat.Prime r → r ≤ B)
    (hcut : B ^ s ≤ y) :
    (((L.primeFactors.card + 1 - s : ℕ) : ℝ) ^ s) / (s.factorial : ℝ) ≤
      ((restrictedDivisors L y).card : ℝ) := by
  have hPsubset : L.primeFactors ⊆ L.primeFactors := by
    intro p hp
    exact hp
  have hPprime : ∀ p ∈ L.primeFactors, Nat.Prime p := by
    intro p hp
    exact (Nat.mem_primeFactors.mp hp).1
  have hPbound : ∀ p ∈ L.primeFactors, p ≤ B := by
    intro p hp
    have hpFactors := Nat.mem_primeFactors.mp hp
    exact hFactorBound p hpFactors.2.1 hpFactors.1
  exact
    fixedPrimeFactorProductsOf_lower_bound_restrictedDivisors hL hSquarefree hPsubset hPprime
      hPbound hcut

/--
Inputs: a prime cutoff `z`, a factor count `s`, and a member of
`fixedPrimeFactorProducts z s`.

Claim: the represented product is at most `z ^ s`.

Proof: each factor is at most `z`, and the indexing subset has cardinality `s`.

Role: this records the direct size estimate for each fixed-factor divisor.
-/
theorem fixedPrimeFactorProducts_le_primePower {z s d : ℕ} (hd : d ∈ fixedPrimeFactorProducts z s) :
    d ≤ z ^ s := by
  classical
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hd
  have hU' := Finset.mem_powersetCard.mp hU
  calc
    U.prod id ≤ z ^ U.card := by
      apply Finset.prod_le_pow_card
      intro p hp
      have hpMem := hU'.1 hp
      have hpRange := (Finset.mem_filter.mp hpMem).1
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hpRange)
    _ = z ^ s := by rw [hU'.2]

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z`, a factor count `s`, and a divisor cutoff containing the
primorial `∏_{p ≤ z} p`.

Claim: every fixed-size prime product below `z` is a divisor in the restricted
divisor family of the primorial.

Content: its factors form a subset of the primorial's prime factors, so the
product divides the primorial and is no larger than it.

Proof: bound the product by a power using the cardinality of its indexing set,
then use divisibility of products over subsets.

Role: this embeds the binomial family into the divisor count of Proposition 1.5.
-/
theorem fixedPrimeFactorProducts_subset_restrictedDivisors {z s x : ℕ}
    (hcut : (primeSetLE z).prod id ≤ reliableProp15DivisorCutoff x) :
    fixedPrimeFactorProducts z s ⊆
      restrictedDivisors ((primeSetLE z).prod id) (reliableProp15DivisorCutoff x) := by
  classical
  intro d hd
  obtain ⟨U, hU, rfl⟩ := Finset.mem_image.mp hd
  have hU' := Finset.mem_powersetCard.mp hU
  have hdiv : U.prod id ∣ (primeSetLE z).prod id :=
    Finset.prod_dvd_prod_of_subset U (primeSetLE z) id hU'.1
  have hNpos : 0 < (primeSetLE z).prod id := primeProductLE_pos z
  have hprodle : U.prod id ≤ (primeSetLE z).prod id := Nat.le_of_dvd hNpos hdiv
  exact
    (mem_restrictedDivisors (Nat.ne_of_gt (primeProductLE_pos z))).mpr ⟨hdiv, le_trans hprodle hcut⟩

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a prime cutoff `z`, a factor count `s`, and a Proposition 1.5 cutoff
that contains the primorial.

Claim: the restricted divisors of the primorial include at least
`choose (π(z), s)` elements.

Content: the products of distinct `s`-subsets of primes at most `z` are
distinct, divide the primorial, and lie below the given cutoff.

Proof: embed `fixedPrimeFactorProducts` into `restrictedDivisors`, then compare
finite cardinalities.

Role: this is the discrete fixed-factor-count input needed for the original
reliable §2 parameter choice.
-/
theorem choose_le_restrictedDivisors_card_of_fixedPrimeFactorProducts {z s x : ℕ}
    (hcut : (primeSetLE z).prod id ≤ reliableProp15DivisorCutoff x) :
    Nat.choose (Nat.primeCounting z) s ≤
      (restrictedDivisors ((primeSetLE z).prod id) (reliableProp15DivisorCutoff x)).card := by
  have hsubset :
    fixedPrimeFactorProducts z s ⊆
      restrictedDivisors ((primeSetLE z).prod id) (reliableProp15DivisorCutoff x) :=
    fixedPrimeFactorProducts_subset_restrictedDivisors hcut
  calc
    Nat.choose (Nat.primeCounting z) s = (fixedPrimeFactorProducts z s).card :=
      (fixedPrimeFactorProducts_card z s).symm
    _ ≤ (restrictedDivisors ((primeSetLE z).prod id) (reliableProp15DivisorCutoff x)).card :=
      Finset.card_le_card hsubset

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a natural cutoff `z`.

Claim: the product of all primes at most `z` is at most
`z ^ Nat.primeCounting z`.

Content: each prime factor is at most `z`, and the factor count is exactly
`Nat.primeCounting z`.

Proof: apply the finite product power bound and rewrite the cardinality.

Role: this sharper product estimate is the direct size input for choosing the
initial modulus below the divisor cutoff.
-/
theorem primeProductLE_bound_by_count (z : ℕ) :
    (primeSetLE z).prod id ≤ z ^ Nat.primeCounting z := by
  calc
    (primeSetLE z).prod id ≤ z ^ (primeSetLE z).card := by
      apply Finset.prod_le_pow_card
      intro p hp
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    _ = z ^ Nat.primeCounting z := by rw [primeSetLE_card]

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a positive natural cutoff `z`.

Claim: the product of all primes at most `z` is at most `z ^ (z + 1)`.

Content: every factor is at most `z`, and there are at most `z + 1` factors.

Proof: bound the finite product by the cutoff raised to the set cardinality,
then compare cardinalities and exponents.

Role: this coarse estimate supplies an elementary size bound for the initial
auxiliary modulus.
-/
theorem primeProductLE_bound {z : ℕ} (hz : 0 < z) : (primeSetLE z).prod id ≤ z ^ (z + 1) := by
  calc
    (primeSetLE z).prod id ≤ z ^ (primeSetLE z).card := by
      apply Finset.prod_le_pow_card
      intro p hp
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    _ ≤ z ^ (z + 1) :=
      Nat.pow_le_pow_right hz
        (calc
          (primeSetLE z).card ≤ (Finset.range (z + 1)).card := Finset.card_filter_le _ _
          _ = z + 1 := Finset.card_range (z + 1))

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z` with `2 ≤ z`.

Claim: the logarithm of the fifth power of the prime product up to `z` is at
most `5 * (z + 1) * log z`.

Content: `primeProductLE_bound` bounds the product by `z ^ (z + 1)`; applying
the increasing logarithm and the natural-power logarithm formula gives the
estimate.

Proof: compare the positive natural products, apply `Real.log_le_log`, then
rewrite the logarithm of each natural power.

Role: this bounds the denominator in the initial divisor-count coefficient
when the prime-supply parameter is the fifth power of the initial modulus.
-/
theorem log_primeProductLE_fifth_power_le {z : ℕ} (hz : 2 ≤ z) :
    Real.log ((((primeSetLE z).prod id : ℕ) ^ 5 : ℕ) : ℝ) ≤
      5 * ((z + 1 : ℕ) : ℝ) * Real.log (z : ℝ) := by
  have hprod := primeProductLE_bound (Nat.lt_of_lt_of_le Nat.zero_lt_two hz)
  have hprodR : (((primeSetLE z).prod id : ℕ) : ℝ) ≤ ((z ^ (z + 1) : ℕ) : ℝ) := by
    exact_mod_cast hprod
  have hlogR : Real.log (((primeSetLE z).prod id : ℕ) : ℝ) ≤ Real.log ((z ^ (z + 1) : ℕ) : ℝ) :=
    Real.log_le_log (by exact_mod_cast primeProductLE_pos z) hprodR
  have hlog :
    Real.log (((primeSetLE z).prod id : ℕ) : ℝ) ≤ ((z + 1 : ℕ) : ℝ) * Real.log (z : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow] at hlogR
    exact hlogR
  rw [Nat.cast_pow, Real.log_pow]
  have hlog5 := mul_le_mul_of_nonneg_left hlog (by norm_num only : (0 : ℝ) ≤ 5)
  linear_combination hlog5

/--
Inputs: a natural number `m` with `10 ≤ m`.

Claim: `m ^ 3 ≤ 2 ^ m`.

Content: the induction step bounds the next cube by twice the preceding cube.

Proof: use `m ≥ 10` to compare the cubic increment with the preceding cube,
then lift the inequality through the induction hypothesis.

Role: this elementary growth estimate simplifies the explicit Chebyshev lower
bound at arguments of the form `2 ^ m`.
-/
theorem powTwo_ge_cube {m : ℕ} (hm : 10 ≤ m) : m ^ 3 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => norm_num only
  | succ n hn
    ih =>
    have hn3 : 10 * n ^ 2 ≤ n ^ 3 := by
      calc
        10 * n ^ 2 ≤ n * n ^ 2 := Nat.mul_le_mul_right (n ^ 2) hn
        _ = n ^ 3 := by ring
    have hstep : (n + 1) ^ 3 ≤ 2 * n ^ 3 := by
      have hnreal : (10 : ℝ) ≤ n := by exact_mod_cast hn
      have hn3real : (10 : ℝ) * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by exact_mod_cast hn3
      have hstepReal : ((n + 1) : ℝ) ^ 3 ≤ 2 * (n : ℝ) ^ 3 := by nlinarith only [hnreal, hn3real]
      exact_mod_cast hstepReal
    calc
      (n + 1) ^ 3 ≤ 2 * n ^ 3 := hstep
      _ ≤ 2 * 2 ^ n := Nat.mul_le_mul_left 2 ih
      _ = 2 ^ (n + 1) := by
        rw [pow_succ]; norm_num only [Nat.mul_comm]

/--
Inputs: a natural number `m` with `10 ≤ m`.

Claim: at least `3 * m` primes are at most `2 ^ m`.

Content: specialize `Chebyshev.pi_ge` and use the logarithm identities for
powers of two; the cubic growth estimate absorbs the logarithmic correction.

Proof: bound `2 ^ m` below by `3 * m ^ 2 + m + 1`, and bound
`log (2 ^ m + 1)` above by `(m + 1) * log 2`.

Role: this supplies an exponential lower bound for the initial prime product's
divisor count.
-/
theorem primeCounting_two_pow_lower {m : ℕ} (hm : 10 ≤ m) : 3 * m ≤ Nat.primeCounting (2 ^ m) := by
  have hcube := powTwo_ge_cube hm
  have hlinear : 3 * m ^ 2 + m + 1 ≤ m ^ 3 := by nlinarith only [hm]
  have hsmall : 3 * m ^ 2 + m + 1 ≤ 2 ^ m := le_trans hlinear hcube
  have hpi := Chebyshev.pi_ge (2 ^ m)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hlogpow : Real.log ((2 ^ m : ℕ) : ℝ) = m * Real.log (2 : ℝ) := by
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlogplus : Real.log (((2 ^ m + 1 : ℕ) : ℝ)) ≤ (m + 1) * Real.log (2 : ℝ) := by
    have harg : (2 ^ m + 1 : ℕ) ≤ 2 ^ (m + 1) := by
      have hnat : 2 ^ m + 1 ≤ 2 ^ m + 2 ^ m := by
        have h1 : 1 ≤ 2 ^ m := by omega
        omega
      rw [pow_succ]
      nlinarith only [hnat]
    have hpos : (0 : ℝ) < ((2 ^ m + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.zero_lt_succ (2 ^ m)
    have hlogarg : Real.log (((2 ^ m + 1 : ℕ) : ℝ)) ≤ Real.log ((2 ^ (m + 1) : ℕ) : ℝ) :=
      Real.log_le_log hpos (by exact_mod_cast harg)
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat] at hlogarg
    push_cast at hlogarg ⊢
    exact hlogarg
  have hsmallR : (3 * m ^ 2 + m + 1 : ℝ) ≤ (2 ^ m : ℕ) := by exact_mod_cast hsmall
  have hmul := mul_le_mul_of_nonneg_right hsmallR (le_of_lt hlog2)
  have hnum :
    (3 * (m : ℝ) ^ 2) * Real.log 2 ≤
      ((2 ^ m : ℕ) : ℝ) * Real.log 2 - Real.log ((2 ^ m + 1 : ℕ) : ℝ) := by
    nlinarith only [hmul, hlogplus]
  have hden : 0 < (m : ℝ) * Real.log 2 := by
    exact mul_pos (by exact_mod_cast (by omega : 0 < m)) hlog2
  have hpiReal : (3 * (m : ℝ)) ≤ (Nat.primeCounting (2 ^ m) : ℝ) := by
    rw [hlogpow] at hpi
    have hquot :
      (3 * (m : ℝ)) ≤
        (((2 ^ m : ℕ) : ℝ) * Real.log 2 - Real.log ((2 ^ m + 1 : ℕ) : ℝ)) /
          ((m : ℝ) * Real.log 2) := by
      apply (le_div_iff₀ hden).2
      nlinarith only [hnum, hden]
    have hpi' :
      (((2 ^ m : ℕ) : ℝ) * Real.log 2 - Real.log (((2 ^ m + 1 : ℕ) : ℝ))) / ((m : ℝ) * Real.log 2) ≤
        (Nat.primeCounting (2 ^ m) : ℝ) := by
      simpa only [Nat.cast_add, Nat.cast_one] using hpi
    exact le_trans hquot hpi'
  exact_mod_cast hpiReal

/--
Inputs: a positive coefficient `c₀` and real threshold `T`.

Claim: some `m ≥ 10` makes `c₀ * m ^ 4 / (10 * log 2)` exceed `T`.

Proof: choose `m` above the scaled threshold and use `m ≤ m ^ 4`.

Role: this supplies the growth parameter for the initial divisor count.
-/
theorem exists_polynomial_threshold {c₀ : ℝ} (hc₀ : 0 < c₀) (T : ℝ) (x₀ : ℕ) :
    ∃ m : ℕ, 10 ≤ m ∧ x₀ ≤ m ∧ T < c₀ * (m : ℝ) ^ 4 / (10 * Real.log 2) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  let R : ℝ := max 10 (max (x₀ : ℝ) (10 * T * Real.log 2 / c₀))
  obtain ⟨m, hm⟩ := exists_nat_gt (R + 1)
  have hmR : R + 1 < (m : ℝ) := by exact_mod_cast hm
  have hm10 : 10 ≤ m := by
    have hR : 10 ≤ R := le_max_left 10 _
    exact_mod_cast (le_of_lt (by linarith only [hmR, hR] : (10 : ℝ) < (m : ℝ)))
  have hmX : x₀ ≤ m := by
    have hRx : (x₀ : ℝ) ≤ R := le_trans (le_max_left _ _) (le_max_right 10 _)
    exact_mod_cast (le_of_lt (by linarith only [hmR, hRx] : (x₀ : ℝ) < (m : ℝ)))
  have hmR' : 10 * T * Real.log 2 / c₀ < (m : ℝ) := by
    have hR' : 10 * T * Real.log 2 / c₀ ≤ R :=
      le_trans (le_max_right (x₀ : ℝ) _) (le_max_right (10 : ℝ) _)
    linarith only [hmR, hR']
  have hmreal : (10 : ℝ) ≤ m := by exact_mod_cast hm10
  have hmle2 : (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hmreal]
  have h1le2 : (1 : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith only [hmreal]
  have hm2le4 : (m : ℝ) ^ 2 ≤ (m : ℝ) ^ 4 := by
    calc
      (m : ℝ) ^ 2 = 1 * (m : ℝ) ^ 2 := by ring
      _ ≤ (m : ℝ) ^ 2 * (m : ℝ) ^ 2 := mul_le_mul_of_nonneg_right h1le2 (sq_nonneg (m : ℝ))
      _ = (m : ℝ) ^ 4 := by ring
  have hmpow : (m : ℝ) ≤ (m : ℝ) ^ 4 := le_trans hmle2 hm2le4
  have hlin : 10 * T * Real.log 2 < c₀ * (m : ℝ) := by
    have h := (div_lt_iff₀ hc₀).1 hmR'
    simpa only [mul_comm] using h
  have hpow : 10 * T * Real.log 2 < c₀ * (m : ℝ) ^ 4 := by
    calc
      10 * T * Real.log 2 < c₀ * (m : ℝ) := hlin
      _ ≤ c₀ * (m : ℝ) ^ 4 := mul_le_mul_of_nonneg_left hmpow (le_of_lt hc₀)
  refine ⟨m, hm10, hmX, ?_⟩
  apply (lt_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 10) hlog2)).2
  nlinarith only [hpow]

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a natural cutoff `z`.

Claim: the product of primes at most `z` is at least `2 ^ π(z)`.

Content: each factor in `primeSetLE z` is a prime and hence at least two.

Proof: compare the product factorwise with the constant product and rewrite
the cardinality as `Nat.primeCounting z`.

Role: this shows that the initial modulus grows beyond any prescribed lower
cutoff as `z` increases.
-/
theorem primeProductLE_ge_two_pow_primeCounting (z : ℕ) :
    2 ^ Nat.primeCounting z ≤ (primeSetLE z).prod id := by
  have hprod :=
    Finset.prod_le_prod (s := primeSetLE z) (f := fun _ : ℕ => 2) (g := id)
      (by
        intro p hp
        exact (Finset.mem_filter.mp hp).2.two_le)
  rw [Finset.prod_const, primeSetLE_card] at hprod
  exact hprod

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a positive initial-count coefficient and a natural threshold.

Claim: for some cutoff `z`, the coefficient at `x = (∏_{p ≤ z} p) ^ 5`
times the full divisor count exceeds the threshold.

Content: set `z = 2 ^ m`; Chebyshev gives at least `3 * m` prime factors,
while the product logarithm is bounded by `5 * (z + 1) * log z`.

Proof: combine the explicit prime-count lower bound, the product-log bound,
and polynomial growth in `m`.

Role: this makes the initial auxiliary-modulus cutoff and divisor threshold
simultaneously attainable, assuming the uniform Proposition 1.5 count.
-/
theorem exists_primeProductLE_initial_count {c₀ : ℝ} (hc₀ : 0 < c₀) (T x₀ : ℕ) :
    ∃ z : ℕ,
      2 ≤ z ∧
        x₀ ≤ ((primeSetLE z).prod id : ℕ) ^ 5 ∧
        (T : ℝ) <
          reliableProp15Coefficient c₀ 1 (((primeSetLE z).prod id : ℕ) ^ 5) *
            ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
  obtain ⟨m, hm, hmx₀, hpoly⟩ := exists_polynomial_threshold hc₀ (T : ℝ) x₀
  let z : ℕ := 2 ^ m
  let N : ℕ := (primeSetLE z).prod id
  let x : ℕ := N ^ 5
  have hz : 2 ≤ z := by
    dsimp [z]
    calc
      2 = 2 ^ 1 := by norm_num only
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) (by omega)
  have hNpos : 0 < N := by
    dsimp [N]
    exact primeProductLE_pos z
  have hdata := primeProductLE_data z
  have htwo : 2 ∈ primeSetLE z := by
    unfold primeSetLE
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), Nat.prime_two⟩
  have htwoN : 2 ∈ N.primeFactors := by
    change 2 ∈ ((primeSetLE z).prod id).primeFactors
    rw [hdata.2]
    exact htwo
  have hNdiv : 2 ∣ N := Nat.dvd_of_mem_primeFactors htwoN
  have hNge : 2 ≤ N := Nat.le_of_dvd hNpos hNdiv
  have hNpow : N ≤ x := by
    dsimp [x]
    exact Nat.le_self_pow (by norm_num only : 5 ≠ 0) N
  have hpi := primeCounting_two_pow_lower hm
  have hmle3 : m ≤ m ^ 3 := by
    have hm1 : 1 ≤ m := by omega
    calc
      m = m * 1 := by omega
      _ ≤ m * m := Nat.mul_le_mul_left m hm1
      _ = m ^ 2 := by ring
      _ ≤ m ^ 2 * m := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (m ^ 2) hm1
      _ = m ^ 3 := by ring
  have hcube := powTwo_ge_cube hm
  have hmleZ : m ≤ z := by
    dsimp [z]
    exact le_trans hmle3 hcube
  have hpiLower : m ≤ Nat.primeCounting z := by
    dsimp [z]
    exact le_trans (by omega : m ≤ 3 * m) hpi
  have hpowLower : 2 ^ m ≤ 2 ^ Nat.primeCounting z := Nat.pow_le_pow_right (by omega) hpiLower
  have hNlower : 2 ^ Nat.primeCounting z ≤ N := by
    dsimp [N]
    exact primeProductLE_ge_two_pow_primeCounting z
  have hx₀ : x₀ ≤ x := by
    calc
      x₀ ≤ m := hmx₀
      _ ≤ z := hmleZ
      _ ≤ N := le_trans hpowLower hNlower
      _ ≤ x := hNpow
  have hxlarge : 1 < x := lt_of_lt_of_le (by omega : 1 < N) hNpow
  have hlogxpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hxlarge)
  have hlogx := log_primeProductLE_fifth_power_le hz
  have hlogz : Real.log (z : ℝ) = (m : ℝ) * Real.log 2 := by
    dsimp [z]
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  let D : ℝ := 5 * ((z + 1 : ℕ) : ℝ) * (m : ℝ) * Real.log 2
  have hDpos : 0 < D := by
    dsimp [D]
    exact
      mul_pos
        (mul_pos
          (mul_pos (by norm_num only : (0 : ℝ) < 5) (by exact_mod_cast (by omega : 0 < z + 1)))
          (by exact_mod_cast (by omega : 0 < m)))
        hlog2
  have hlogxD : Real.log (x : ℝ) ≤ D := by
    have hlogx' : Real.log (x : ℝ) ≤ 5 * ((z + 1 : ℕ) : ℝ) * ((m : ℝ) * Real.log 2) := by
      simpa only [N, x, hlogz] using hlogx
    dsimp [D]
    nlinarith only [hlogx']
  have hcoefeq : reliableProp15Coefficient c₀ 1 x = c₀ / Real.log (x : ℝ) := by
    simp only [reliableProp15Coefficient, Nat.totient_one, Nat.cast_one, one_mul]
  have hcoeflow : c₀ / D ≤ reliableProp15Coefficient c₀ 1 x := by
    rw [hcoefeq]
    apply (div_le_div_iff₀ hDpos hlogxpos).2
    have hmul := mul_le_mul_of_nonneg_left hlogxD (le_of_lt hc₀)
    nlinarith only [hmul]
  have hpowNat : 2 ^ (3 * m) ≤ 2 ^ Nat.primeCounting z :=
    Nat.pow_le_pow_right (by omega)
      (by
        dsimp [z]; exact hpi)
  have hpowR : ((2 ^ (3 * m) : ℕ) : ℝ) ≤ ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
    exact_mod_cast hpowNat
  have hcoefpos : 0 < reliableProp15Coefficient c₀ 1 x := by
    rw [hcoefeq]
    exact div_pos hc₀ hlogxpos
  have hscaled :
    c₀ / D * ((2 ^ (3 * m) : ℕ) : ℝ) ≤
      reliableProp15Coefficient c₀ 1 x * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
    calc
      c₀ / D * ((2 ^ (3 * m) : ℕ) : ℝ) ≤
          reliableProp15Coefficient c₀ 1 x * ((2 ^ (3 * m) : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeflow (by exact_mod_cast Nat.zero_le _)
      _ ≤ reliableProp15Coefficient c₀ 1 x * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hpowR (le_of_lt hcoefpos)
  have hmle3 : m ≤ m ^ 3 := by
    have hm1 : 1 ≤ m := by omega
    calc
      m = m * 1 := by omega
      _ ≤ m * m := Nat.mul_le_mul_left m hm1
      _ = m ^ 2 := by ring
      _ ≤ m ^ 2 * m := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (m ^ 2) hm1
      _ = m ^ 3 := by ring
  have hm2le3 : m ^ 2 ≤ m ^ 3 := by
    have hm1 : 1 ≤ m := by omega
    calc
      m ^ 2 = m ^ 2 * 1 := by omega
      _ ≤ m ^ 2 * m := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (m ^ 2) hm1
      _ = m ^ 3 := by ring
  have hmpow5 : m ^ 5 ≤ z ^ 2 := by
    calc
      m ^ 5 = m ^ 2 * m ^ 3 := by ring
      _ ≤ m ^ 3 * m ^ 3 := Nat.mul_le_mul_right (m ^ 3) hm2le3
      _ ≤ z * z := Nat.mul_le_mul hcube hcube
      _ = z ^ 2 := by ring
  have hprod : z * m ^ 5 ≤ z ^ 3 := by
    calc
      z * m ^ 5 ≤ z * z ^ 2 := Nat.mul_le_mul_left z hmpow5
      _ = z ^ 3 := by ring
  have hpow3 : 2 ^ (3 * m) = z ^ 3 := by
    dsimp [z]
    rw [Nat.mul_comm 3 m, pow_mul]
  have hprodR : (z : ℝ) * (m : ℝ) ^ 5 ≤ ((2 ^ (3 * m) : ℕ) : ℝ) := by
    rw [hpow3]
    exact_mod_cast hprod
  have hzadd : ((z + 1 : ℕ) : ℝ) ≤ 2 * z := by exact_mod_cast (by omega : z + 1 ≤ 2 * z)
  have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hDupper : D ≤ 10 * (z : ℝ) * m * Real.log 2 := by
    dsimp [D]
    have hmul :=
      mul_le_mul_of_nonneg_right hzadd
        (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 5) (mul_nonneg hmnonneg (le_of_lt hlog2)))
    nlinarith only [hmul]
  have hcross : c₀ * (m : ℝ) ^ 4 * D ≤ c₀ * ((2 ^ (3 * m) : ℕ) : ℝ) * (10 * Real.log 2) := by
    have hm4nonneg : 0 ≤ (m : ℝ) ^ 4 := by
      calc
        0 ≤ ((m : ℝ) ^ 2) ^ 2 := sq_nonneg ((m : ℝ) ^ 2)
        _ = (m : ℝ) ^ 4 := by ring
    calc
      c₀ * (m : ℝ) ^ 4 * D ≤ c₀ * (m : ℝ) ^ 4 * (10 * z * m * Real.log 2) := by
        exact mul_le_mul_of_nonneg_left hDupper (mul_nonneg (le_of_lt hc₀) hm4nonneg)
      _ = c₀ * ((z : ℝ) * (m : ℝ) ^ 5) * (10 * Real.log 2) := by ring
      _ ≤ c₀ * ((2 ^ (3 * m) : ℕ) : ℝ) * (10 * Real.log 2) := by
        exact
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprodR (le_of_lt hc₀))
            (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 10) (le_of_lt hlog2))
  have hratio' : c₀ * (m : ℝ) ^ 4 / (10 * Real.log 2) ≤ (c₀ * ((2 ^ (3 * m) : ℕ) : ℝ)) / D := by
    apply (div_le_div_iff₀ (mul_pos (by norm_num only : (0 : ℝ) < 10) hlog2) hDpos).2
    exact hcross
  have hratio : c₀ * (m : ℝ) ^ 4 / (10 * Real.log 2) ≤ c₀ / D * ((2 ^ (3 * m) : ℕ) : ℝ) := by
    simpa only [div_mul_eq_mul_div] using hratio'
  refine ⟨z, hz, ?_, ?_⟩
  · exact hx₀
  · exact lt_of_lt_of_le hpoly (le_trans hratio hscaled)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a positive Proposition 1.5 coefficient and an integer `m ≥ 10`.

Claim: for the primorial through `2 ^ m`, the modulus-one divisor-count
lower bound is at least `c₀ * 2^(2m) / (10 * m * log 2)`.

Proof: Chebyshev gives at least `3 * m` primes through `2 ^ m`, so the
primorial and divisor count dominate the corresponding cubic powers. The
primorial logarithm is at most `10 * 2^m * m * log 2`. Keeping the full cubic
lower bound, rather than reducing it using `m^3 ≤ 2^m`, gives the stated
stronger estimate.

Role: this explicit growth estimate lets the initial seed size be chosen as a
polynomial factor larger than the primorial cutoff, for the later P2 estimate.
-/
theorem primeProductLE_count_lower_bound_of_two_pow {c₀ : ℝ} (hc₀ : 0 < c₀) {m : ℕ} (hm : 10 ≤ m) :
    c₀ * ((2 ^ m : ℕ) : ℝ) ^ 2 / (10 * (m : ℝ) * Real.log 2) ≤
      reliableProp15Coefficient c₀ 1 (((primeSetLE (2 ^ m)).prod id : ℕ) ^ 5) *
        ((2 ^ Nat.primeCounting (2 ^ m) : ℕ) : ℝ) := by
  let z : ℕ := 2 ^ m
  let N : ℕ := (primeSetLE z).prod id
  let x : ℕ := N ^ 5
  have hz : 2 ≤ z := by
    dsimp [z]
    exact le_trans (by norm_num only : 2 ≤ 2) (Nat.le_self_pow (by omega : m ≠ 0) 2)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hlogz : Real.log (z : ℝ) = (m : ℝ) * Real.log 2 := by
    dsimp [z]
    rw [Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  have hlogx0 := log_primeProductLE_fifth_power_le hz
  have hlogx : Real.log (x : ℝ) ≤ 10 * (z : ℝ) * (m : ℝ) * Real.log 2 := by
    have hzadd : ((z + 1 : ℕ) : ℝ) ≤ 2 * (z : ℝ) := by exact_mod_cast (by omega : z + 1 ≤ 2 * z)
    have hmnonneg : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    have hmul := mul_le_mul_of_nonneg_right hzadd (mul_nonneg hmnonneg (le_of_lt hlog2))
    have hmul5 := mul_le_mul_of_nonneg_left hmul (by norm_num only : (0 : ℝ) ≤ 5)
    have hlogx0' : Real.log (x : ℝ) ≤ 5 * ((z + 1 : ℕ) : ℝ) * ((m : ℝ) * Real.log 2) := by
      simpa only [N, x, hlogz] using hlogx0
    nlinarith only [hlogx0', hmul5]
  have hpi := primeCounting_two_pow_lower hm
  have hpow3 : 2 ^ (3 * m) = z ^ 3 := by
    dsimp [z]
    rw [Nat.mul_comm 3 m, pow_mul]
  have hcountNat : z ^ 3 ≤ 2 ^ Nat.primeCounting z := by
    rw [← hpow3]
    exact Nat.pow_le_pow_right (by omega) hpi
  have hNlower : z ^ 3 ≤ N := by
    calc
      z ^ 3 ≤ 2 ^ Nat.primeCounting z := hcountNat
      _ ≤ N := by
        dsimp [N]
        exact primeProductLE_ge_two_pow_primeCounting z
  have hzlepow : z ≤ z ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) z
  have hNgt : 1 < N := by
    have hzgt : 1 < z := by omega
    exact lt_of_lt_of_le hzgt (le_trans hzlepow hNlower)
  have hxgt : 1 < x := by
    dsimp [x]
    exact lt_of_lt_of_le hNgt (Nat.le_self_pow (by norm_num only : 5 ≠ 0) N)
  have hlogxpos : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hxgt)
  have hcoefeq : reliableProp15Coefficient c₀ 1 x = c₀ / Real.log (x : ℝ) := by
    simp only [reliableProp15Coefficient, Nat.totient_one, Nat.cast_one, one_mul]
  have hcoefpos : 0 < reliableProp15Coefficient c₀ 1 x := by
    rw [hcoefeq]
    exact div_pos hc₀ hlogxpos
  have hdenpos : 0 < 10 * (z : ℝ) * (m : ℝ) * Real.log 2 := by
    exact
      mul_pos
        (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 10) (by exact_mod_cast (by omega : 0 < z)))
          (by exact_mod_cast (by omega : 0 < m)))
        hlog2
  have hcoeflower :
    c₀ / (10 * (z : ℝ) * (m : ℝ) * Real.log 2) ≤ reliableProp15Coefficient c₀ 1 x := by
    rw [hcoefeq]
    apply (div_le_div_iff₀ hdenpos hlogxpos).2
    have hmul := mul_le_mul_of_nonneg_left hlogx (le_of_lt hc₀)
    nlinarith only [hmul]
  have hcountR : (z : ℝ) ^ 3 ≤ ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by exact_mod_cast hcountNat
  have hcoefcount :
    c₀ / (10 * (z : ℝ) * (m : ℝ) * Real.log 2) * (z : ℝ) ^ 3 ≤
      reliableProp15Coefficient c₀ 1 x * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
    calc
      c₀ / (10 * (z : ℝ) * (m : ℝ) * Real.log 2) * (z : ℝ) ^ 3 ≤
          reliableProp15Coefficient c₀ 1 x * (z : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hcoeflower (by positivity)
      _ ≤ reliableProp15Coefficient c₀ 1 x * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hcountR (le_of_lt hcoefpos)
  have hdenM : 0 < 10 * (m : ℝ) * Real.log 2 :=
    mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 10) (by exact_mod_cast (by omega : 0 < m))) hlog2
  have hratio :
    c₀ * (z : ℝ) ^ 2 / (10 * (m : ℝ) * Real.log 2) ≤
      c₀ / (10 * (z : ℝ) * (m : ℝ) * Real.log 2) * (z : ℝ) ^ 3 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_div_iff₀ hdenM hdenpos).2
    nlinarith only
  simpa only [z, N, x] using le_trans hratio hcoefcount

/--
Inputs: a positive count coefficient, an exponent `m ≥ 10`, and a positive
primorial power `J`.

Claim: the reliable initial count at the prime bound `N^(5J)`, where
`N = ∏_{p ≤ 2^m} p`, is at least `c₀ * 2^(2m) / (10 J m log 2)` times
`2^π(2^m)`.

Proof: apply the exponent-one estimate with coefficient `c₀ / J`; the logarithm
of `N^(5J)` is `J` times the logarithm of `N^5`, so the coefficients agree.

Role: matches the initial seed count to the same primorial power used by the
full-divisor P2 scale.
-/
theorem primeProductLE_count_lower_bound_of_two_pow_power {c₀ : ℝ} (hc₀ : 0 < c₀) {m J : ℕ}
    (hm : 10 ≤ m) (hJ : 0 < J) :
    c₀ * ((2 ^ m : ℕ) : ℝ) ^ 2 / (10 * (J : ℝ) * (m : ℝ) * Real.log 2) ≤
      reliableProp15Coefficient c₀ 1
          ((((PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ m)).prod id : ℕ) ^ 5) ^ J) *
        ((2 ^ Nat.primeCounting (2 ^ m) : ℕ) : ℝ) := by
  have hJr : (0 : ℝ) < (J : ℝ) := by exact_mod_cast hJ
  have hscaled :=
    primeProductLE_count_lower_bound_of_two_pow (c₀ := c₀ / (J : ℝ)) (div_pos hc₀ hJr) hm
  let N : ℕ := (PseudoPrime.NumberTheory.PrimeProducts.primeSetLE (2 ^ m)).prod id
  have hNgt : 1 < N := by
    have hpi := primeCounting_two_pow_lower hm
    have hpow : 2 ^ (3 * m) ≤ N := by
      calc
        2 ^ (3 * m) ≤ 2 ^ Nat.primeCounting (2 ^ m) := Nat.pow_le_pow_right (by omega : 1 ≤ 2) hpi
        _ ≤ N := by
          dsimp only [N]
          exact primeProductLE_ge_two_pow_primeCounting _
    have hm10 : 1 < 2 ^ m := by
      have htwo : 2 ≤ 2 ^ m := Nat.le_self_pow (by omega : m ≠ 0) 2
      omega
    have hpowle : 2 ^ m ≤ 2 ^ (3 * m) := by
      apply Nat.pow_le_pow_right (by omega : 1 ≤ 2)
      omega
    exact lt_of_lt_of_le hm10 (le_trans hpowle hpow)
  have hlog : 0 < Real.log (((N ^ 5 : ℕ) : ℝ)) := by
    apply Real.log_pos
    exact_mod_cast (Nat.one_lt_pow (by norm_num only : 5 ≠ 0) hNgt)
  have hcoef :
    reliableProp15Coefficient c₀ 1 ((N ^ 5) ^ J) =
      reliableProp15Coefficient (c₀ / (J : ℝ)) 1 (N ^ 5) := by
    unfold reliableProp15Coefficient
    simp only [Nat.totient_one, Nat.cast_one, one_mul]
    rw [Nat.cast_pow, Real.log_pow]
    push_cast
    field_simp
  calc
    c₀ * ((2 ^ m : ℕ) : ℝ) ^ 2 / (10 * (J : ℝ) * (m : ℝ) * Real.log 2) =
        (c₀ / (J : ℝ)) * ((2 ^ m : ℕ) : ℝ) ^ 2 / (10 * (m : ℝ) * Real.log 2) :=
      by field_simp
    _ ≤
        reliableProp15Coefficient (c₀ / (J : ℝ)) 1 (N ^ 5) *
          ((2 ^ Nat.primeCounting (2 ^ m) : ℕ) : ℝ) :=
      by simpa only [N] using hscaled
    _ = reliableProp15Coefficient c₀ 1 ((N ^ 5) ^ J) * ((2 ^ Nat.primeCounting (2 ^ m) : ℕ) : ℝ) :=
      by rw [hcoef]

/--
Inputs: a positive real scale `a`, a minimum threshold `M`, and a minimum
cutoff parameter `x₀`.

Claim: for some `m ≥ 10` and `z = 2 ^ m`, the seed size
`T = floor (a * z * m^2)` is at least `M`, satisfies `4 * z * m ≤ T + 1`,
and obeys `(T + 1)^4 ≤ z^15`.

Proof: choose `m` above the finitely many thresholds imposed by `a`, `M`, and
`x₀`. The estimate `m^3 ≤ 2^m` controls both the floor lower bound and the
fourth-power size condition.

Role: this supplies a seed size proportional to `z * m^2` while the later
fixed-factor size can be `z * m`, linking the first-stage and P2 scales.
-/
theorem exists_primeProductLE_seed_scale {a : ℝ} (ha : 0 < a) (M x₀ : ℕ) :
    ∃ m z T : ℕ,
      10 ≤ m ∧
        x₀ ≤ m ∧
        z = 2 ^ m ∧
        T = Nat.floor (a * (z : ℝ) * (m : ℝ) ^ 2) ∧
        M ≤ T ∧ 4 * z * m ≤ T + 1 ∧ (T + 1) ^ 4 ≤ z ^ 15 := by
  let r1 : ℝ := max (((M : ℝ) + 1) / a) (max (4 / a) a)
  let r2 : ℝ := max (x₀ : ℝ) r1
  let R : ℝ := max 10 r2
  have hR10 : (10 : ℝ) ≤ R := le_max_left 10 r2
  have hRx₀ : (x₀ : ℝ) ≤ R := le_trans (le_max_left _ _) (le_max_right 10 r2)
  have hRM : ((M : ℝ) + 1) / a ≤ R := by
    dsimp [R, r2, r1]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hR4 : 4 / a ≤ R := by
    dsimp [R, r2, r1]
    exact
      le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hRa : a ≤ R := by
    dsimp [R, r2, r1]
    exact
      le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  obtain ⟨m, hm⟩ := exists_nat_gt (R + 1)
  have hmR : R + 1 < (m : ℝ) := by exact_mod_cast hm
  have hmgt : R < (m : ℝ) := by linarith only [hmR]
  have hm10 : 10 ≤ m := by
    have h : (10 : ℝ) < (m : ℝ) := lt_of_le_of_lt hR10 hmgt
    exact_mod_cast (le_of_lt h)
  have hmx₀ : x₀ ≤ m := by
    have h : (x₀ : ℝ) < (m : ℝ) := lt_of_le_of_lt hRx₀ hmgt
    exact_mod_cast (le_of_lt h)
  have hMam : (M : ℝ) + 1 < a * (m : ℝ) := by
    have hlt : ((M : ℝ) + 1) / a < (m : ℝ) := lt_of_le_of_lt hRM hmgt
    simpa only [mul_comm] using (div_lt_iff₀ ha).1 hlt
  have h4m : (4 : ℝ) < a * (m : ℝ) := by
    have hlt : 4 / a < (m : ℝ) := lt_of_le_of_lt hR4 hmgt
    simpa only [mul_comm] using (div_lt_iff₀ ha).1 hlt
  have ham : a < (m : ℝ) := lt_of_le_of_lt hRa hmgt
  let z : ℕ := 2 ^ m
  let T : ℕ := Nat.floor (a * (z : ℝ) * (m : ℝ) ^ 2)
  have hcube := powTwo_ge_cube hm10
  have hz : 2 ≤ z := by
    dsimp [z]
    exact le_trans (by norm_num only : 2 ≤ 2) (Nat.le_self_pow (by omega : m ≠ 0) 2)
  have hcubeR : (m : ℝ) ^ 3 ≤ (z : ℝ) := by
    dsimp [z]
    exact_mod_cast hcube
  have hmle5 : (m : ℝ) ≤ (m : ℝ) ^ 5 := by
    exact_mod_cast (Nat.le_self_pow (by norm_num only : 5 ≠ 0) m)
  have hmul1 := mul_le_mul_of_nonneg_right hcubeR (sq_nonneg (m : ℝ))
  have hmul2 := mul_le_mul_of_nonneg_left hmul1 (le_of_lt ha)
  have hMle5 : a * (m : ℝ) ≤ a * (m : ℝ) ^ 5 := mul_le_mul_of_nonneg_left hmle5 (le_of_lt ha)
  have hAlower : (M : ℝ) + 1 < a * (z : ℝ) * (m : ℝ) ^ 2 := by
    calc
      (M : ℝ) + 1 < a * (m : ℝ) := hMam
      _ ≤ a * (m : ℝ) ^ 5 := hMle5
      _ ≤ a * (z : ℝ) * (m : ℝ) ^ 2 := by nlinarith only [hmul2]
  have hApos : 0 ≤ a * (z : ℝ) * (m : ℝ) ^ 2 := by positivity
  have hMreal : (M : ℝ) ≤ a * (z : ℝ) * (m : ℝ) ^ 2 := by linarith only [hAlower]
  have hMfloor : M ≤ T := by
    apply (Nat.le_floor_iff hApos).2
    exact_mod_cast hMreal
  have hzRpos : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hscaleReal : (4 : ℝ) * (z : ℝ) * (m : ℝ) < a * (z : ℝ) * (m : ℝ) ^ 2 := by
    have hmul := mul_lt_mul_of_pos_right h4m (mul_pos hzRpos hmRpos)
    nlinarith only [hmul]
  have hfloorlt := Nat.lt_floor_add_one (a * (z : ℝ) * (m : ℝ) ^ 2)
  have hscale : 4 * z * m ≤ T + 1 := by
    have hlt : (4 : ℝ) * (z : ℝ) * (m : ℝ) < (T : ℝ) + 1 := by
      simpa only [T, Nat.cast_add, Nat.cast_one] using lt_trans hscaleReal hfloorlt
    exact_mod_cast (le_of_lt hlt)
  have hamsmall : a * (m : ℝ) ^ 2 < (z : ℝ) := by
    calc
      a * (m : ℝ) ^ 2 < (m : ℝ) ^ 3 := by
        exact (mul_lt_mul_of_pos_right ham (sq_pos_of_pos hmRpos)).trans_eq (by ring)
      _ ≤ (z : ℝ) := hcubeR
  have hAsmall : a * (z : ℝ) * (m : ℝ) ^ 2 < (z : ℝ) ^ 2 := by
    calc
      a * (z : ℝ) * (m : ℝ) ^ 2 = (z : ℝ) * (a * (m : ℝ) ^ 2) := by ring
      _ < (z : ℝ) * (z : ℝ) := mul_lt_mul_of_pos_left hamsmall hzRpos
      _ = (z : ℝ) ^ 2 := by ring
  have hfloorSmall : T < z ^ 2 := by
    apply (Nat.floor_lt hApos).2
    exact_mod_cast hAsmall
  have hTplus : T + 1 ≤ z ^ 2 := by omega
  have hTpower : (T + 1) ^ 4 ≤ z ^ 15 := by
    calc
      (T + 1) ^ 4 ≤ (z ^ 2) ^ 4 := Nat.pow_le_pow_left hTplus 4
      _ = z ^ 8 := by rw [← pow_mul]
      _ ≤ z ^ 15 := Nat.pow_le_pow_right (by omega) (by norm_num only)
  exact ⟨m, z, T, hm10, hmx₀, rfl, rfl, hMfloor, hscale, hTpower⟩

/-
Inputs: a positive real scale `a`, a minimum seed size `M`, and a minimum
cutoff parameter `x₀`.

Claim: for some `m ≥ 10` and `z = 2 ^ m`, the seed size
`T = floor (a * z^2 / m)` exceeds `M`, satisfies `4 * z * m ≤ T + 1`,
and obeys `(T + 1)^4 ≤ z^15`.

Proof: use `m^3 ≤ 2^m` to show `m ≤ z`, so `z^2 / m ≥ m`. The same cubic
estimate makes the seed scale dominate `z * m`, while `a < m` bounds `T`
by `z^2`, leaving room in the fourth-power constraint.

Role: this stronger seed scale retains the full cubic lower bound for the
primorial divisor count and improves the base of the later fixed-size product
count.
-/
theorem exists_primeProductLE_quadratic_seed_scale {a : ℝ} (ha : 0 < a) (M x₀ : ℕ) :
    ∃ m z T : ℕ,
      10 ≤ m ∧
        x₀ ≤ m ∧
        z = 2 ^ m ∧
        T = Nat.floor (a * (z : ℝ) ^ 2 / (m : ℝ)) ∧
        M ≤ T ∧ 4 * z * m ≤ T + 1 ∧ (T + 1) ^ 4 ≤ z ^ 15 := by
  let r1 : ℝ := max (((M : ℝ) + 1) / a) (max (4 / a) a)
  let r2 : ℝ := max (x₀ : ℝ) r1
  let R : ℝ := max 10 r2
  have hR10 : (10 : ℝ) ≤ R := le_max_left 10 r2
  have hRx₀ : (x₀ : ℝ) ≤ R := le_trans (le_max_left _ _) (le_max_right 10 r2)
  have hRM : ((M : ℝ) + 1) / a ≤ R := by
    dsimp [R, r2, r1]
    exact le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))
  have hR4 : 4 / a ≤ R := by
    dsimp [R, r2, r1]
    exact
      le_trans (le_max_left _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  have hRa : a ≤ R := by
    dsimp [R, r2, r1]
    exact
      le_trans (le_max_right _ _)
        (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _)))
  obtain ⟨m, hm⟩ := exists_nat_gt (R + 1)
  have hmR : R + 1 < (m : ℝ) := by exact_mod_cast hm
  have hmgt : R < (m : ℝ) := by linarith only [hmR]
  have hm10 : 10 ≤ m := by
    have h : (10 : ℝ) < (m : ℝ) := lt_of_le_of_lt hR10 hmgt
    exact_mod_cast (le_of_lt h)
  have hmx₀ : x₀ ≤ m := by
    have h : (x₀ : ℝ) < (m : ℝ) := lt_of_le_of_lt hRx₀ hmgt
    exact_mod_cast (le_of_lt h)
  have hMam : (M : ℝ) + 1 < a * (m : ℝ) := by
    have hlt : ((M : ℝ) + 1) / a < (m : ℝ) := lt_of_le_of_lt hRM hmgt
    simpa only [mul_comm] using (div_lt_iff₀ ha).1 hlt
  have h4m : (4 : ℝ) < a * (m : ℝ) := by
    have hlt : 4 / a < (m : ℝ) := lt_of_le_of_lt hR4 hmgt
    simpa only [mul_comm] using (div_lt_iff₀ ha).1 hlt
  have ham : a < (m : ℝ) := lt_of_le_of_lt hRa hmgt
  let z : ℕ := 2 ^ m
  let T : ℕ := Nat.floor (a * (z : ℝ) ^ 2 / (m : ℝ))
  have hcube := powTwo_ge_cube hm10
  have hz : 2 ≤ z := by
    dsimp [z]
    exact le_trans (by norm_num only : 2 ≤ 2) (Nat.le_self_pow (by omega : m ≠ 0) 2)
  have hcubeR : (m : ℝ) ^ 3 ≤ (z : ℝ) := by
    dsimp [z]
    exact_mod_cast hcube
  have hzRpos : 0 < (z : ℝ) := by exact_mod_cast (by omega : 0 < z)
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hmleZ : (m : ℝ) ≤ (z : ℝ) := by
    exact_mod_cast
      (le_trans (Nat.le_self_pow (by norm_num only : 3 ≠ 0) m) (by simpa only [z] using hcube))
  have hbase : (m : ℝ) ≤ (z : ℝ) ^ 2 / (m : ℝ) := by
    rw [le_div_iff₀ hmRpos]
    have h1 := mul_le_mul_of_nonneg_left hmleZ (le_of_lt hmRpos)
    have h2 := mul_le_mul_of_nonneg_right hmleZ (le_of_lt hzRpos)
    simpa only [pow_two] using le_trans h1 h2
  have hApos : 0 ≤ a * (z : ℝ) ^ 2 / (m : ℝ) :=
    div_nonneg (mul_nonneg (le_of_lt ha) (sq_nonneg (z : ℝ))) (le_of_lt hmRpos)
  have hAlower : (M : ℝ) + 1 < a * (z : ℝ) ^ 2 / (m : ℝ) := by
    calc
      (M : ℝ) + 1 < a * (m : ℝ) := hMam
      _ ≤ a * ((z : ℝ) ^ 2 / (m : ℝ)) := mul_le_mul_of_nonneg_left hbase (le_of_lt ha)
      _ = a * (z : ℝ) ^ 2 / (m : ℝ) := by ring
  have hMfloor : M ≤ T := by
    apply (Nat.le_floor_iff hApos).2
    exact_mod_cast (by linarith only [hAlower] : (M : ℝ) ≤ a * (z : ℝ) ^ 2 / (m : ℝ))
  have hscaleReal : (4 : ℝ) * (z : ℝ) * (m : ℝ) < a * (z : ℝ) ^ 2 / (m : ℝ) := by
    rw [lt_div_iff₀ hmRpos]
    have hscaled : 4 * (m : ℝ) ^ 2 < a * (z : ℝ) := by
      have hmul := mul_lt_mul_of_pos_right h4m (sq_pos_of_pos hmRpos)
      have hlow := mul_le_mul_of_nonneg_left hcubeR (le_of_lt ha)
      nlinarith only [hmul, hlow]
    have hmulZ := mul_lt_mul_of_pos_right hscaled hzRpos
    calc
      4 * (z : ℝ) * (m : ℝ) * (m : ℝ) = 4 * (m : ℝ) ^ 2 * (z : ℝ) := by ring
      _ < a * (z : ℝ) * (z : ℝ) := hmulZ
      _ = a * (z : ℝ) ^ 2 := by ring
  have hfloorlt := Nat.lt_floor_add_one (a * (z : ℝ) ^ 2 / (m : ℝ))
  have hscale : 4 * z * m ≤ T + 1 := by
    have hlt : (4 : ℝ) * (z : ℝ) * (m : ℝ) < (T : ℝ) + 1 := by
      simpa only [T, Nat.cast_add, Nat.cast_one] using lt_trans hscaleReal hfloorlt
    exact_mod_cast (le_of_lt hlt)
  have hAupper : a * (z : ℝ) ^ 2 / (m : ℝ) ≤ (z : ℝ) ^ 2 := by
    rw [div_le_iff₀ hmRpos]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_right (le_of_lt ham) (sq_nonneg (z : ℝ))
  have hTle : (T : ℝ) ≤ (z : ℝ) ^ 2 := le_trans (Nat.floor_le hApos) hAupper
  have hzge2R : 2 ≤ (z : ℝ) := by exact_mod_cast hz
  have hzsq : 0 ≤ (z : ℝ) ^ 2 := sq_nonneg (z : ℝ)
  have htwoZsq := mul_le_mul_of_nonneg_left hzge2R hzsq
  have hTplusR : (T : ℝ) + 1 ≤ (z : ℝ) ^ 3 := by
    have hzsqge1 : 1 ≤ (z : ℝ) ^ 2 := by nlinarith only [hzge2R, sq_nonneg ((z : ℝ) - 2)]
    have hzpow : 2 * (z : ℝ) ^ 2 ≤ (z : ℝ) ^ 3 := by nlinarith only [htwoZsq]
    nlinarith only [hTle, hzsqge1, hzpow]
  have hTplus : T + 1 ≤ z ^ 3 := by exact_mod_cast hTplusR
  have hTpower : (T + 1) ^ 4 ≤ z ^ 15 := by
    calc
      (T + 1) ^ 4 ≤ (z ^ 3) ^ 4 := Nat.pow_le_pow_left hTplus 4
      _ = z ^ 12 := by rw [← pow_mul]
      _ ≤ z ^ 15 := Nat.pow_le_pow_right (by omega) (by norm_num only)
  exact ⟨m, z, T, hm10, hmx₀, rfl, rfl, hMfloor, hscale, hTpower⟩

/--
Purpose: record a cutoff beyond which the Chebyshev prime-counting estimate
ensures that at most half of the integers up to `60 * n` are prime.

Definition: choose a natural threshold from
`eventually_primeCounting_sixty_mul_le_half`.

Role: the initial Proposition 1.5 count uses this fixed cutoff to guarantee
that its finite seed-prime set is large enough for the reciprocal-tail bound.
-/
noncomputable def primeTailCountThreshold : ℕ :=
  Classical.choose (Filter.eventually_atTop.1 eventually_primeCounting_sixty_mul_le_half)

/--
Inputs: a natural number `n` above `primeTailCountThreshold`.

Claim: `2 * Nat.primeCounting (60 * n) ≤ n`.

Content: this is the uniform form of the eventual Chebyshev estimate used by
the finite seed-prime selection.

Proof: apply the witness chosen in `primeTailCountThreshold`.

Role: this supplies the small-prime count bound for the large seed-prime tail.
-/
theorem primeCounting_bound_of_primeTailCountThreshold {n : ℕ} (hn : primeTailCountThreshold ≤ n) :
    2 * Nat.primeCounting (60 * n) ≤ n := by
  exact
    Classical.choose_spec (Filter.eventually_atTop.1 eventually_primeCounting_sixty_mul_le_half) n
      hn

/--
Purpose: record a cutoff beyond which the Chebyshev estimate ensures that at
most half of the integers up to `120 * n` are prime.

Definition: choose a natural threshold from
`eventually_primeCounting_mul_le_half 120`.

Role: this threshold supplies the count needed for a seed tail with reciprocal
sum at most `1 / 120`.
-/
noncomputable def primeTailCountThreshold120 : ℕ :=
  Classical.choose
    (Filter.eventually_atTop.1 (eventually_primeCounting_mul_le_half 120 (by norm_num only)))

/--
Inputs: a natural number `n` above `primeTailCountThreshold120`.

Claim: `2 * Nat.primeCounting (120 * n) ≤ n`.

Proof: apply the witness chosen in `primeTailCountThreshold120`.

Role: this supplies the small-prime count bound for the improved seed tail.
-/
theorem primeCounting_bound_of_primeTailCountThreshold120 {n : ℕ}
    (hn : primeTailCountThreshold120 ≤ n) : 2 * Nat.primeCounting (120 * n) ≤ n := by
  exact
    Classical.choose_spec
      (Filter.eventually_atTop.1 (eventually_primeCounting_mul_le_half 120 (by norm_num only))) n hn

/--
Purpose: record a cutoff beyond which at most half of the integers up to
`1024 * n` are prime.

Definition: choose a natural threshold from
`eventually_primeCounting_mul_le_half 1024`.

Role: this threshold supplies the reciprocal-prime bound `1 / 1024` for the
large-prime tail of a finite seed set.
-/
noncomputable def primeTailCountThreshold1024 : ℕ :=
  Classical.choose
    (Filter.eventually_atTop.1 (eventually_primeCounting_mul_le_half 1024 (by norm_num only)))

/--
Inputs: a natural number `n` above `primeTailCountThreshold1024`.

Claim: `2 * Nat.primeCounting (1024 * n) ≤ n`.

Proof: apply the witness chosen in `primeTailCountThreshold1024`.

Role: this supplies the small-prime count bound for the strong seed tail.
-/
theorem primeCounting_bound_of_primeTailCountThreshold1024 {n : ℕ}
    (hn : primeTailCountThreshold1024 ≤ n) : 2 * Nat.primeCounting (1024 * n) ≤ n := by
  exact
    Classical.choose_spec
      (Filter.eventually_atTop.1 (eventually_primeCounting_mul_le_half 1024 (by norm_num only))) n
      hn

/--
Inputs: the chosen eventual threshold for the `1024` prime-count tail estimate.

Claim: the threshold is at least `2`, since the tail inequality fails at `n = 1`.

Proof: Chebyshev's lower bound gives at least one prime at most `2^10 = 1024`,
which contradicts the tail inequality if the threshold were at most `1`.

Role: ensures the P2 floor-defined seed count is at least two, giving a positive
lower bound for its unfloored expression.
-/
theorem primeTailCountThreshold1024_ge_two : 2 ≤ primeTailCountThreshold1024 := by
  by_contra h
  have hthreshold : primeTailCountThreshold1024 ≤ 1 := by omega
  have hbound :=
    primeCounting_bound_of_primeTailCountThreshold1024 (n := 1)
      (le_trans hthreshold (by norm_num only))
  have hpi := primeCounting_two_pow_lower (m := 10) (by norm_num only)
  have hpow : (2 : ℕ) ^ 10 = 1024 := by norm_num only
  rw [hpow] at hpi
  have hbound' : 2 * Nat.primeCounting 1024 ≤ 1 := by simpa only [Nat.mul_one] using hbound
  omega

end PseudoPrime.AnalyticNumberTheory.AGP
