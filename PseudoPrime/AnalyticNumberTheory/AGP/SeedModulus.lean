/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.ReliableProp15
public import PseudoPrime.NumberTheory.PrimeProducts

/-! # SeedModulus

Carmichael and prime-tail auxiliary-modulus constructions.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: a finite set `S` of primes and a natural number `M` divisible by every
predecessor `p - 1` for `p ∈ S`.

Claim: the Carmichael function of the product of `S` divides `M`.

Content: this packages the prime-factor Carmichael formula and the finite LCM
into a single divisibility statement.

Proof: distinct primes are pairwise coprime, so the Carmichael function of the
product is the LCM of the individual values `p - 1`.

Role: this supplies the Carmichael-exponent bound for finite sets of seed
primes.
-/
theorem carmichael_prod_dvd_of_prime_predecessors_dvd (S : Finset ℕ) (M : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hpred : ∀ p ∈ S, p - 1 ∣ M) :
    ArithmeticFunction.carmichael (S.prod id) ∣ M := by
  have hpairs : Set.Pairwise S (Nat.Coprime.onFun id) := by
    intro p hp q hq hpq
    change Nat.Coprime p q
    rw [Nat.Prime.coprime_iff_not_dvd (hprime p hp)]
    intro hpq'
    exact hpq ((Nat.prime_dvd_prime_iff_eq (hprime p hp) (hprime q hq)).mp hpq')
  rw [ArithmeticFunction.carmichael_finsetProd hpairs]
  apply Finset.lcm_dvd
  intro p hp
  simpa only [Function.comp_apply, id_eq,
    ArithmeticFunction.carmichael_of_prime (hprime p hp)] using hpred p hp

/--
Inputs: a finite set of distinct primes and one selected prime in that set.

Claim: the predecessor of the selected prime divides the Carmichael function
of the product of the finite set.

Content: the Carmichael function of a pairwise-coprime prime product is the
least common multiple of the prime predecessors.

Proof: rewrite with `ArithmeticFunction.carmichael_finsetProd` and use the
selected term's divisibility into the finite least common multiple.

Role: this gives a lower bound for the Carmichael function of the tail product.
-/
theorem prime_predecessor_dvd_carmichael_prime_product (S : Finset ℕ) (p : ℕ) (hp : p ∈ S)
    (hprime : ∀ q ∈ S, Nat.Prime q) : p - 1 ∣ ArithmeticFunction.carmichael (S.prod id) := by
  have hpairs : Set.Pairwise S (Nat.Coprime.onFun id) := by
    intro q hq r hr hqr
    change Nat.Coprime q r
    rw [Nat.Prime.coprime_iff_not_dvd (hprime q hq)]
    intro hqr'
    exact hqr ((Nat.prime_dvd_prime_iff_eq (hprime q hq) (hprime r hr)).mp hqr')
  rw [ArithmeticFunction.carmichael_finsetProd hpairs]
  have hmem : ArithmeticFunction.carmichael p ∣ S.lcm (ArithmeticFunction.carmichael ∘ id) :=
    Finset.dvd_lcm (f := ArithmeticFunction.carmichael ∘ id) hp
  simpa only [Function.comp_apply, id_eq,
    ArithmeticFunction.carmichael_of_prime (hprime p hp)] using hmem

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a finite set `S` of primes, a multiplier `K`, and a modulus `N`, such
that every `p ∈ S` has the form `d * K + 1` for some `d ∣ N`.

Claim: the Carmichael function of the product of `S` divides `K * N`.

Content: this is the auxiliary Carmichael bound obtained from the seed-prime
shape in reliable §2.

Proof: each predecessor divides `K * N`; apply the finite prime-product
Carmichael bound.

Role: this connects the initial progression prime supply to the later
construction of the auxiliary modulus `L`.
-/
theorem carmichael_prod_dvd_of_divisor_form_seed (S : Finset ℕ) (K N : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hseed : ∀ p ∈ S, ∃ d, d ∣ N ∧ p = d * K + 1) :
    ArithmeticFunction.carmichael (S.prod id) ∣ K * N := by
  apply carmichael_prod_dvd_of_prime_predecessors_dvd S (K * N) hprime
  intro p hp
  obtain ⟨d, hd, hform⟩ := hseed p hp
  exact predecessor_dvd_mul_of_eq_mul_add_one hform hd

/--
Inputs: a finite set `P` of natural numbers, a positive lower bound `T`, and
the pointwise bound `T ≤ p` for every `p ∈ P`.

Claim: the sum of the reciprocals of the elements of `P` is at most
`P.card / T`.

Content: this converts a lower bound on selected primes into the reciprocal-sum
condition in reliable, Proposition 1.5.

Proof: bound each reciprocal by `1 / T` and sum the pointwise inequalities.

Role: this estimate will control the reciprocal sum for the large seed primes
used to build the auxiliary modulus.
-/
theorem reciprocal_sum_le_card_div_of_lower_bound (P : Finset ℕ) (T : ℕ) (hT : 0 < T)
    (hLower : ∀ p ∈ P, T ≤ p) : (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (P.card : ℝ) / T := by
  calc
    (∑ p ∈ P, (p : ℝ)⁻¹) ≤ ∑ p ∈ P, (T : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPos : 0 < p := lt_of_lt_of_le hT (hLower p hp)
      exact
        (inv_le_inv₀ (by exact_mod_cast hpPos) (by exact_mod_cast hT)).2
          (by exact_mod_cast hLower p hp)
    _ = (P.card : ℝ) * (T : ℝ)⁻¹ := by simp only [Finset.sum_const, nsmul_eq_mul]
    _ = (P.card : ℝ) / T := by rw [div_eq_mul_inv]

/--
Inputs: a finite set `S` of natural numbers, a positive cutoff `T`, and a
bound showing that at most half of `S` is at most `T`.

Claim: the elements of `S` greater than `T` comprise at least half of `S`, and
their reciprocal sum is at most their cardinality divided by `T`.

Content: this selects many large seed primes while controlling their
reciprocal sum; the hypothesis on the small elements is supplied by a prime
counting estimate in the analytic construction.

Proof: partition `S` at `T`, then apply
`reciprocal_sum_le_card_div_of_lower_bound` to the upper part.

Role: this is the finite selection step needed to verify the reciprocal-sum
condition in reliable, Proposition 1.5.
-/
theorem tail_filter_large_card_and_reciprocal_bound (S : Finset ℕ) (T : ℕ) (hT : 0 < T)
    (hsmall : 2 * (S.filter (fun p => p ≤ T)).card ≤ S.card) :
    let P := S.filter (fun p => T < p)
    S.card ≤ 2 * P.card ∧ P.card ≤ S.card ∧ (∑ p ∈ P, (p : ℝ)⁻¹) ≤ (P.card : ℝ) / T := by
  classical
  let P := S.filter (fun p => T < p)
  have hpart : (S.filter (fun p => p ≤ T)).card + P.card = S.card := by
    simpa only [P, not_le] using (Finset.card_filter_add_card_filter_not (s := S) (fun p => p ≤ T))
  have hsmall' : (S.filter (fun p => p ≤ T)).card ≤ P.card := by omega
  have hcard : S.card ≤ 2 * P.card := by omega
  have hsubset : P ⊆ S := Finset.filter_subset _ _
  refine ⟨hcard, Finset.card_mono hsubset, ?_⟩
  apply reciprocal_sum_le_card_div_of_lower_bound P T hT
  intro p hp
  exact Nat.le_of_lt ((Finset.mem_filter.mp hp).2)

/--
Inputs: a finite set `S` of natural numbers, a positive cutoff `T`, with at
most half its elements at most `T` and `60 * S.card ≤ T`.

Claim: the reciprocal sum over the elements greater than `T` is at most
`1 / 60`.

Content: this gives the reciprocal-sum threshold required by reliable,
Proposition 1.5 from a cardinality bound on the selected set.

Proof: use the large-tail estimate and compare the tail cardinality with
`S.card`.

Role: this packages the finite part of the reciprocal-sum condition for the
initial seed-prime construction.
-/
theorem tail_filter_reciprocal_sum_le_one_sixtieth (S : Finset ℕ) (T : ℕ) (hT : 0 < T)
    (hsmall : 2 * (S.filter (fun p => p ≤ T)).card ≤ S.card) (hscale : 60 * S.card ≤ T) :
    (∑ p ∈ S.filter (fun p => T < p), (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) := by
  have hbound := tail_filter_large_card_and_reciprocal_bound S T hT hsmall
  rcases hbound with ⟨_, hsubsetCard, hsum⟩
  have hnat : 60 * (S.filter (fun p => T < p)).card ≤ T :=
    Nat.le_trans (Nat.mul_le_mul_left 60 hsubsetCard) hscale
  have hreal : (60 : ℝ) * ((S.filter (fun p => T < p)).card : ℝ) ≤ T := by exact_mod_cast hnat
  apply le_trans hsum
  rw [div_le_iff₀ (by exact_mod_cast hT)]
  calc
    ((S.filter (fun p => T < p)).card : ℝ) =
        (1 / 60 : ℝ) * (60 * ((S.filter (fun p => T < p)).card : ℝ)) :=
      by field_simp
    _ ≤ (1 / 60 : ℝ) * T := mul_le_mul_of_nonneg_left hreal (by norm_num only)

/--
Inputs: a finite set `S` of natural numbers, a positive cutoff `T`, and a
bound showing that at most half of `S` is at most `T`; let `C` be a positive
cutoff multiplier with `C * S.card ≤ T`.

Claim: the reciprocal sum over elements of `S` greater than `T` is at most
`1 / C`.

Content: this gives a parameterized version of the reciprocal-tail estimate.

Proof: bound the tail sum by its cardinality divided by `T`, then use the
tail cardinality bound and the cutoff scale.

Role: this allows the seed construction to trade a larger cutoff for a smaller
reciprocal sum.
-/
theorem tail_filter_reciprocal_sum_le_inverse_cutoff (S : Finset ℕ) (T C : ℕ) (hT : 0 < T)
    (hC : 0 < C) (hsmall : 2 * (S.filter (fun p => p ≤ T)).card ≤ S.card)
    (hscale : C * S.card ≤ T) : (∑ p ∈ S.filter (fun p => T < p), (p : ℝ)⁻¹) ≤ (C : ℝ)⁻¹ := by
  have hbound := tail_filter_large_card_and_reciprocal_bound S T hT hsmall
  rcases hbound with ⟨_, hsubsetCard, hsum⟩
  have hnat : C * (S.filter (fun p => T < p)).card ≤ T :=
    Nat.le_trans (Nat.mul_le_mul_left C hsubsetCard) hscale
  have hreal : (C : ℝ) * ((S.filter (fun p => T < p)).card : ℝ) ≤ T := by exact_mod_cast hnat
  apply le_trans hsum
  rw [div_le_iff₀ (by exact_mod_cast hT)]
  calc
    ((S.filter (fun p => T < p)).card : ℝ) =
        (C : ℝ)⁻¹ * ((C : ℝ) * (S.filter (fun p => T < p)).card) :=
      by field_simp
    _ ≤ (C : ℝ)⁻¹ * T := mul_le_mul_of_nonneg_left hreal (inv_nonneg.mpr (by exact_mod_cast hC.le))

/--
Inputs: a sufficiently large natural number `n`.

Claim: at most half of the integers up to `60 * n` are prime, in the precise
form `2 * Nat.primeCounting (60 * n) ≤ n`.

Content: this is a consequence of Chebyshev's asymptotic upper bound for the
prime-counting function and supplies the cutoff estimate for a large finite
set of seed primes.

Proof: apply `Chebyshev.eventually_primeCounting_le` at `60 * n`, then use the
growth of `log (60 * n)` to absorb its fixed coefficient.

Role: this provides the analytic input for selecting a large seed-prime tail
with reciprocal sum at most `1 / 60`.
-/
theorem eventually_primeCounting_sixty_mul_le_half :
    ∀ᶠ n : ℕ in Filter.atTop, 2 * Nat.primeCounting (60 * n) ≤ n := by
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hscale : Filter.Tendsto (fun n : ℕ => (60 : ℝ) * n) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by norm_num only) hcast
  have hcount :=
    hscale.eventually (Chebyshev.eventually_primeCounting_le (by norm_num only : (0 : ℝ) < 1))
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, 120 * (Real.log 4 + 1) ≤ Real.log ((60 : ℝ) * n) :=
    (Real.tendsto_log_atTop.comp hscale).eventually_ge_atTop _
  filter_upwards [hcount, hlog] with n hcount hlog
  have hfloor : Nat.floor ((60 : ℝ) * (n : ℝ)) = 60 * n := by
    calc
      Nat.floor ((60 : ℝ) * (n : ℝ)) = Nat.floor ((60 * n : ℕ) : ℝ) := by
        congr 1
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      _ = 60 * n := Nat.floor_natCast _
  have hcount' :
    (Nat.primeCounting (60 * n) : ℝ) ≤
      (Real.log 4 + 1) * ((60 : ℝ) * n) / Real.log ((60 : ℝ) * n) := by
    rw [← hfloor]
    exact hcount
  have hC : 0 < Real.log 4 + 1 :=
    add_pos_of_pos_of_nonneg (Real.log_pos (by norm_num only)) (by norm_num only)
  have hden : 0 < Real.log ((60 : ℝ) * n) := lt_of_lt_of_le (mul_pos (by norm_num only) hC) hlog
  have hpiHalf : (Nat.primeCounting (60 * n) : ℝ) ≤ (n : ℝ) / 2 := by
    calc
      _ ≤ (Real.log 4 + 1) * ((60 : ℝ) * n) / Real.log ((60 : ℝ) * n) := hcount'
      _ ≤ (n : ℝ) / 2 := by
        rw [div_le_iff₀ hden]
        calc
          (Real.log 4 + 1) * ((60 : ℝ) * n) = ((n : ℝ) / 2) * (120 * (Real.log 4 + 1)) := by ring
          _ ≤ ((n : ℝ) / 2) * Real.log ((60 : ℝ) * n) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
  have hpi : (2 : ℝ) * (Nat.primeCounting (60 * n) : ℝ) ≤ n := by
    calc
      _ ≤ (2 : ℝ) * ((n : ℝ) / 2) := mul_le_mul_of_nonneg_left hpiHalf (by norm_num only)
      _ = n := by ring
  exact_mod_cast hpi

/--
Inputs: a positive natural cutoff multiplier `C`.

Claim: for all sufficiently large `n`, at most half of the integers up to
`C * n` are prime, in the form `2 * Nat.primeCounting (C * n) ≤ n`.

Content: this is the Chebyshev estimate with an arbitrary fixed linear scale.

Proof: apply the prime-counting upper bound at `C * n` and use the growth of
`log (C * n)` to absorb its coefficient.

Role: this supplies the eventual count estimate for reciprocal-tail cutoffs
other than sixty.
-/
theorem eventually_primeCounting_mul_le_half (C : ℕ) (hC : 0 < C) :
    ∀ᶠ n : ℕ in Filter.atTop, 2 * Nat.primeCounting (C * n) ≤ n := by
  have hcast : Filter.Tendsto (fun n : ℕ => (n : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  have hscale : Filter.Tendsto (fun n : ℕ => (C : ℝ) * n) Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (by exact_mod_cast hC) hcast
  have hcount :=
    hscale.eventually (Chebyshev.eventually_primeCounting_le (by norm_num only : (0 : ℝ) < 1))
  have hlog : ∀ᶠ n : ℕ in Filter.atTop, 2 * (C : ℝ) * (Real.log 4 + 1) ≤ Real.log ((C : ℝ) * n) :=
    (Real.tendsto_log_atTop.comp hscale).eventually_ge_atTop _
  filter_upwards [hcount, hlog] with n hcount hlog
  have hfloor : Nat.floor ((C : ℝ) * (n : ℝ)) = C * n := by
    calc
      Nat.floor ((C : ℝ) * (n : ℝ)) = Nat.floor ((C * n : ℕ) : ℝ) := by
        congr 1
        norm_num only [Nat.cast_mul]
      _ = C * n := Nat.floor_natCast _
  have hcount' :
    (Nat.primeCounting (C * n) : ℝ) ≤
      (Real.log 4 + 1) * ((C : ℝ) * n) / Real.log ((C : ℝ) * n) := by
    rw [← hfloor]
    exact hcount
  have hlog4 : 0 < Real.log 4 + 1 :=
    add_pos_of_pos_of_nonneg (Real.log_pos (by norm_num only)) (by norm_num only)
  have hden : 0 < Real.log ((C : ℝ) * n) :=
    lt_of_lt_of_le (mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 2) (by exact_mod_cast hC)) hlog4)
      hlog
  have hpiHalf : (Nat.primeCounting (C * n) : ℝ) ≤ (n : ℝ) / 2 := by
    calc
      _ ≤ (Real.log 4 + 1) * ((C : ℝ) * n) / Real.log ((C : ℝ) * n) := hcount'
      _ ≤ (n : ℝ) / 2 := by
        rw [div_le_iff₀ hden]
        calc
          (Real.log 4 + 1) * ((C : ℝ) * n) = ((n : ℝ) / 2) * (2 * (C : ℝ) * (Real.log 4 + 1)) := by
            ring
          _ ≤ ((n : ℝ) / 2) * Real.log ((C : ℝ) * n) :=
            mul_le_mul_of_nonneg_left hlog (by positivity)
  have hpi : (2 : ℝ) * (Nat.primeCounting (C * n) : ℝ) ≤ n := by
    calc
      _ ≤ (2 : ℝ) * ((n : ℝ) / 2) := mul_le_mul_of_nonneg_left hpiHalf (by norm_num only)
      _ = n := by ring
  exact_mod_cast hpi

/--
Inputs: a finite set `S` of primes and a natural cutoff `T`.

Claim: at most `Nat.primeCounting T` elements of `S` are at most `T`.

Content: this compares a finite subset of primes with the full set counted by
the prime-counting function.

Proof: embed the filtered set into `Nat.primesLE T` and compare cardinalities.

Role: this converts the Chebyshev estimate into the small-side bound required
by the finite reciprocal-sum selection.
-/
theorem prime_filter_card_le_primeCounting (S : Finset ℕ) (T : ℕ) (hprime : ∀ p ∈ S, Nat.Prime p) :
    (S.filter (fun p => p ≤ T)).card ≤ Nat.primeCounting T := by
  have hsubset : S.filter (fun p => p ≤ T) ⊆ Nat.primesLE T := by
    intro p hp
    simp only [Finset.mem_filter] at hp
    simp only [Nat.mem_primesLE]
    exact ⟨hp.2, hprime p hp.1⟩
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact Finset.card_mono hsubset

/--
Inputs: a nonempty finite set `S` of primes whose cardinality satisfies
`2 * Nat.primeCounting (60 * S.card) ≤ S.card`.

Claim: the elements of `S` greater than `60 * S.card` comprise at least half
of `S`, and their reciprocal sum is at most `1 / 60`.

Content: the prime-counting hypothesis follows for sufficiently large `S.card`
from `eventually_primeCounting_sixty_mul_le_half`.

Proof: bound the small part by `Nat.primeCounting`, then apply the tail
selection theorem at cutoff `60 * S.card`.

Role: this packages the reciprocal-sum and cardinality conditions needed for
the large-prime subset in reliable §2.
-/
theorem prime_tail_reciprocal_sum_le_one_sixtieth (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hS : 0 < S.card) (hcard : 2 * Nat.primeCounting (60 * S.card) ≤ S.card) :
    let T := 60 * S.card
    S.card ≤ 2 * (S.filter (fun p => T < p)).card ∧
      (∑ p ∈ S.filter (fun p => T < p), (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) := by
  let T := 60 * S.card
  have hT : 0 < T := Nat.mul_pos (by decide) hS
  have hsmallCount := prime_filter_card_le_primeCounting S T hprime
  have hsmall : 2 * (S.filter (fun p => p ≤ T)).card ≤ S.card :=
    Nat.le_trans (Nat.mul_le_mul_left 2 hsmallCount) hcard
  have htail := tail_filter_large_card_and_reciprocal_bound S T hT hsmall
  have hreciprocal := tail_filter_reciprocal_sum_le_one_sixtieth S T hT hsmall (by rfl)
  exact ⟨htail.1, hreciprocal⟩

/--
Inputs: a nonempty finite set of primes, a positive cutoff multiplier `C`, and
the prime-counting estimate at `C * S.card`.

Claim: the primes in `S` greater than `C * S.card` comprise at least half of
`S`, and their reciprocal sum is at most `1 / C`.

Content: this combines the finite tail estimate with the prime-counting bound.

Proof: bound the small part by `Nat.primeCounting`, then use
`tail_filter_reciprocal_sum_le_inverse_cutoff`.

Role: this is the parameterized seed-tail selection theorem.
-/
theorem prime_tail_reciprocal_sum_le_inverse_cutoff (S : Finset ℕ) (C : ℕ) (hC : 0 < C)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hS : 0 < S.card)
    (hcount : 2 * Nat.primeCounting (C * S.card) ≤ S.card) :
    let T := C * S.card
    S.card ≤ 2 * (S.filter (fun p => T < p)).card ∧
      (∑ p ∈ S.filter (fun p => T < p), (p : ℝ)⁻¹) ≤ (C : ℝ)⁻¹ := by
  let T := C * S.card
  have hT : 0 < T := Nat.mul_pos hC hS
  have hsmallCount := prime_filter_card_le_primeCounting S T hprime
  have hsmall : 2 * (S.filter (fun p => p ≤ T)).card ≤ S.card :=
    Nat.le_trans (Nat.mul_le_mul_left 2 hsmallCount) hcount
  have htail := tail_filter_large_card_and_reciprocal_bound S T hT hsmall
  have hreciprocal := tail_filter_reciprocal_sum_le_inverse_cutoff S T C hT hC hsmall (by rfl)
  exact ⟨htail.1, hreciprocal⟩

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a nonempty finite set `S` of primes, a common multiplier `K`, and a
modulus `N`, with each seed prime `p = d * K + 1` for some `d ∣ N`; assume
`S` also satisfies the prime-counting threshold for its cardinality.

Claim: the product of the seed primes above `60 * S.card` is squarefree, has
the selected primes as its prime factors, has reciprocal-prime sum at most
`1 / 60`, and has Carmichael value dividing `K * N`.

Content: this combines the finite reciprocal-sum selection with the initial
progression shape in reliable §2.

Proof: restrict the prime and divisor-form hypotheses to the large tail, then
apply the squarefree-product and Carmichael-product formulas.

Role: this provides the main arithmetic fields of the auxiliary modulus; the
remaining construction must bound its factor count and meet the P2 threshold.
-/
theorem seed_prime_tail_auxiliary_modulus_data (S : Finset ℕ) (K N : ℕ)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hseed : ∀ p ∈ S, ∃ d, d ∣ N ∧ p = d * K + 1) (hS : 0 < S.card)
    (hcount : 2 * Nat.primeCounting (60 * S.card) ≤ S.card) :
    let P := S.filter (fun p => 60 * S.card < p)
    let L := P.prod id
    Squarefree L ∧
      L.primeFactors = P ∧
      (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
      ArithmeticFunction.carmichael L ∣ K * N ∧ S.card ≤ 2 * P.card := by
  classical
  let P := S.filter (fun p => 60 * S.card < p)
  let L := P.prod id
  have hprimeP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact hprime p (Finset.mem_filter.mp hp).1
  have hseedP : ∀ p ∈ P, ∃ d, d ∣ N ∧ p = d * K + 1 := by
    intro p hp
    exact hseed p (Finset.mem_filter.mp hp).1
  have htail := prime_tail_reciprocal_sum_le_one_sixtieth S hprime hS hcount
  have hproduct := squarefree_prime_product_primeFactors P hprimeP
  have hlambda := carmichael_prod_dvd_of_divisor_form_seed P K N hprimeP hseedP
  refine ⟨hproduct.1, hproduct.2, ?_, hlambda, htail.1⟩
  rw [hproduct.2]
  exact htail.2

/--
Inputs: an exact seed-set size, the prime-factor description of its cutoff
tail, and the tail cardinality lower bound.

Claim: the tail modulus has at least `floor(t / 2)` distinct prime factors.

Proof: rewrite the tail product's prime factors as the selected tail, convert
the cardinality estimate to `t ≤ 2 * ω(L)`, and apply the real floor bound.

Role: supplies the exponent lower bound for the full-divisor P2 concentration
comparison.
-/
theorem seed_tail_prime_factor_floor_half {S : Finset ℕ} {L t C : ℕ} (hScard : S.card = t)
    (hLprimeFactors : L.primeFactors = S.filter (fun p => C * S.card < p))
    (hTailCard : S.card ≤ 2 * (S.filter (fun p => C * S.card < p)).card) :
    Nat.floor ((t : ℝ) / 2) ≤ L.primeFactors.card := by
  have hNat : t ≤ 2 * L.primeFactors.card := by
    rw [← hScard, hLprimeFactors]
    exact hTailCard
  have hNatReal : (t : ℝ) ≤ 2 * (L.primeFactors.card : ℝ) := by exact_mod_cast hNat
  have hReal : (t : ℝ) / 2 ≤ (L.primeFactors.card : ℝ) := by nlinarith only [hNatReal]
  have hfloor : (Nat.floor ((t : ℝ) / 2) : ℝ) ≤ (L.primeFactors.card : ℝ) :=
    le_trans (Nat.floor_le (by positivity)) hReal
  exact_mod_cast hfloor

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a nonempty finite set of seed primes in the divisor form, a positive
cutoff multiplier `C`, and the prime-counting estimate at `C * S.card`.

Claim: the product of seed primes above that cutoff is squarefree, has exactly
those primes as factors, has reciprocal sum at most `1 / C`, and has
Carmichael value dividing `K * N`.

Content: this is the arbitrary-cutoff form of the auxiliary-modulus data
theorem.

Proof: restrict the prime and divisor-form hypotheses to the tail and apply
the finite product and reciprocal-sum results.

Role: this connects the improved seed-tail estimate to the AGP auxiliary
modulus.
-/
theorem seed_prime_tail_auxiliary_modulus_data_of_cutoff (S : Finset ℕ) (K N C : ℕ) (hC : 0 < C)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hseed : ∀ p ∈ S, ∃ d, d ∣ N ∧ p = d * K + 1) (hS : 0 < S.card)
    (hcount : 2 * Nat.primeCounting (C * S.card) ≤ S.card) :
    let P := S.filter (fun p => C * S.card < p)
    let L := P.prod id
    Squarefree L ∧
      L.primeFactors = P ∧
      (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (C : ℝ)⁻¹ ∧
      ArithmeticFunction.carmichael L ∣ K * N ∧ S.card ≤ 2 * P.card := by
  classical
  let P := S.filter (fun p => C * S.card < p)
  let L := P.prod id
  have hprimeP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact hprime p (Finset.mem_filter.mp hp).1
  have hseedP : ∀ p ∈ P, ∃ d, d ∣ N ∧ p = d * K + 1 := by
    intro p hp
    exact hseed p (Finset.mem_filter.mp hp).1
  have htail := prime_tail_reciprocal_sum_le_inverse_cutoff S C hC hprime hS hcount
  have hproduct := squarefree_prime_product_primeFactors P hprimeP
  have hlambda := carmichael_prod_dvd_of_divisor_form_seed P K N hprimeP hseedP
  refine ⟨hproduct.1, hproduct.2, ?_, hlambda, htail.1⟩
  rw [hproduct.2]
  exact htail.2

/--
Inputs: a nonempty finite set of primes satisfying the prime-counting cutoff.

Claim: the product of the primes above the cutoff is greater than `2`, and its
Carmichael function is at least `3`.

Content: the tail has at least half the seed primes; any selected tail prime
has predecessor dividing the Carmichael function of the prime product.

Proof: derive tail nonemptiness from the cardinality estimate, then use the
finite-product Carmichael formula and the selected prime predecessor.

Role: this supplies the lower-bound fields required by the P2 construction.
-/
theorem seed_prime_tail_p2_lower_bounds (S : Finset ℕ) (hprime : ∀ p ∈ S, Nat.Prime p)
    (hS : 0 < S.card) (hcount : 2 * Nat.primeCounting (60 * S.card) ≤ S.card) :
    let P := S.filter (fun p => 60 * S.card < p)
    let L := P.prod id
    2 < L ∧ 3 ≤ ArithmeticFunction.carmichael L := by
  classical
  let P := S.filter (fun p => 60 * S.card < p)
  let L := P.prod id
  have htail := prime_tail_reciprocal_sum_le_one_sixtieth S hprime hS hcount
  have hcard : S.card ≤ 2 * P.card := by
    dsimp [P]
    exact htail.1
  have hSone : 1 ≤ S.card := Nat.succ_le_of_lt hS
  have h60 : 60 ≤ 60 * S.card := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 60 hSone
  have hPpos : 0 < P.card := by
    by_contra hP
    have hPzero : P.card = 0 := Nat.eq_zero_of_not_pos hP
    rw [hPzero, Nat.mul_zero] at hcard
    exact (Nat.not_le_of_gt hS) hcard
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hPpos
  have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
  have hpcut : 60 * S.card < p := (Finset.mem_filter.mp hp).2
  have hPprime : ∀ q ∈ P, Nat.Prime q := by
    intro q hq
    exact hprime q (Finset.mem_filter.mp hq).1
  have hpprime : Nat.Prime p := hprime p hpS
  have hpgt60 : 60 < p := lt_of_le_of_lt h60 hpcut
  have hpgt2 : 2 < p := lt_trans (by norm_num only : 2 < 60) hpgt60
  have hLpos : 0 < L := by
    dsimp [L]
    apply Finset.prod_pos
    intro q hq
    exact Nat.Prime.pos (hPprime q hq)
  have hpdiv : p ∣ L := by
    dsimp [L]
    exact Finset.dvd_prod_of_mem id hp
  have hPpairwise : Set.Pairwise P (Nat.Coprime.onFun id) := by
    intro q hq r hr hqr
    change Nat.Coprime q r
    rw [Nat.Prime.coprime_iff_not_dvd (hPprime q hq)]
    intro hqr'
    exact hqr ((Nat.prime_dvd_prime_iff_eq (hPprime q hq) (hPprime r hr)).mp hqr')
  have hCarmichaelPos : 0 < ArithmeticFunction.carmichael L := by
    dsimp [L]
    rw [ArithmeticFunction.carmichael_finsetProd hPpairwise]
    apply Nat.pos_of_ne_zero
    apply (Finset.lcm_ne_zero_iff).2
    intro q hq
    have hqprime := hPprime q hq
    have hqcut : 60 * S.card < q := (Finset.mem_filter.mp hq).2
    have hqgt60 : 60 < q := lt_of_le_of_lt h60 hqcut
    have hqgt2 : 2 < q := lt_trans (by norm_num only : 2 < 60) hqgt60
    have hqgt1 : 1 < q := lt_trans (by norm_num only : 1 < 2) hqgt2
    simpa only [Function.comp_apply, id_eq, ArithmeticFunction.carmichael_of_prime hqprime] using
      (Nat.ne_of_gt (Nat.sub_pos_of_lt hqgt1))
  have hprevdiv : p - 1 ∣ ArithmeticFunction.carmichael L := by
    dsimp [L]
    exact prime_predecessor_dvd_carmichael_prime_product P p hp hPprime
  have h4p : 4 ≤ p := le_of_lt (lt_trans (by norm_num only : 4 < 60) hpgt60)
  have hprev3 : 3 ≤ p - 1 := by
    have hsub := Nat.sub_le_sub_right h4p 1
    norm_num only at hsub
    exact hsub
  change 2 < L ∧ 3 ≤ ArithmeticFunction.carmichael L
  exact
    ⟨lt_of_lt_of_le hpgt2 (Nat.le_of_dvd hLpos hpdiv),
      le_trans hprev3 (Nat.le_of_dvd hCarmichaelPos hprevdiv)⟩

/--
Inputs: a nonempty finite set of primes, a cutoff multiplier `C > 4`, and the
prime-counting estimate at `C * S.card`.

Claim: the product of seed primes above that cutoff exceeds `2`, and its
Carmichael function is at least `3`.

Proof: use the tail cardinality bound to select a prime, then apply the
prime-product Carmichael formula to its predecessor.

Role: this supplies the P2 lower-bound fields for arbitrary cutoff scales.
-/
theorem seed_prime_tail_p2_lower_bounds_of_cutoff (S : Finset ℕ) (C : ℕ) (hC : 4 < C)
    (hprime : ∀ p ∈ S, Nat.Prime p) (hS : 0 < S.card)
    (hcount : 2 * Nat.primeCounting (C * S.card) ≤ S.card) :
    let P := S.filter (fun p => C * S.card < p)
    let L := P.prod id
    2 < L ∧ 3 ≤ ArithmeticFunction.carmichael L := by
  classical
  let P := S.filter (fun p => C * S.card < p)
  let L := P.prod id
  have hCpos : 0 < C := lt_trans (by norm_num only : 0 < 4) hC
  have htail := prime_tail_reciprocal_sum_le_inverse_cutoff S C hCpos hprime hS hcount
  have hcard : S.card ≤ 2 * P.card := by
    dsimp [P]
    exact htail.1
  have hCscale : C ≤ C * S.card := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left C (Nat.succ_le_of_lt hS)
  have hPpos : 0 < P.card := by
    by_contra hP
    have hPzero : P.card = 0 := Nat.eq_zero_of_not_pos hP
    rw [hPzero, Nat.mul_zero] at hcard
    exact (Nat.not_le_of_gt hS) hcard
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hPpos
  have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
  have hpcut : C * S.card < p := (Finset.mem_filter.mp hp).2
  have hPprime : ∀ q ∈ P, Nat.Prime q := by
    intro q hq
    exact hprime q (Finset.mem_filter.mp hq).1
  have hpprime : Nat.Prime p := hprime p hpS
  have hpgtC : C < p := lt_of_le_of_lt hCscale hpcut
  have htwoC : 2 < C := lt_trans (by norm_num only : 2 < 4) hC
  have hpgt2 : 2 < p := lt_trans htwoC hpgtC
  have hLpos : 0 < L := by
    dsimp [L]
    apply Finset.prod_pos
    intro q hq
    exact Nat.Prime.pos (hPprime q hq)
  have hpdiv : p ∣ L := by
    dsimp [L]
    exact Finset.dvd_prod_of_mem id hp
  have hPpairwise : Set.Pairwise P (Nat.Coprime.onFun id) := by
    intro q hq r hr hqr
    change Nat.Coprime q r
    rw [Nat.Prime.coprime_iff_not_dvd (hPprime q hq)]
    intro hqr'
    exact hqr ((Nat.prime_dvd_prime_iff_eq (hPprime q hq) (hPprime r hr)).mp hqr')
  have hCarmichaelPos : 0 < ArithmeticFunction.carmichael L := by
    dsimp [L]
    rw [ArithmeticFunction.carmichael_finsetProd hPpairwise]
    apply Nat.pos_of_ne_zero
    apply (Finset.lcm_ne_zero_iff).2
    intro q hq
    have hqprime := hPprime q hq
    have hqcut : C * S.card < q := (Finset.mem_filter.mp hq).2
    have hqgtC : C < q := lt_of_le_of_lt hCscale hqcut
    have honeC : 1 < C := lt_trans (by norm_num only : 1 < 4) hC
    have hqgt1 : 1 < q := lt_trans honeC hqgtC
    simpa only [Function.comp_apply, id_eq, ArithmeticFunction.carmichael_of_prime hqprime] using
      (Nat.ne_of_gt (Nat.sub_pos_of_lt hqgt1))
  have hprevdiv : p - 1 ∣ ArithmeticFunction.carmichael L := by
    dsimp [L]
    exact prime_predecessor_dvd_carmichael_prime_product P p hp hPprime
  have h4p : 4 ≤ p := le_of_lt (lt_trans hC hpgtC)
  have hprev3 : 3 ≤ p - 1 := by
    have hsub := Nat.sub_le_sub_right h4p 1
    norm_num only at hsub
    exact hsub
  change 2 < L ∧ 3 ≤ ArithmeticFunction.carmichael L
  exact
    ⟨lt_of_lt_of_le hpgt2 (Nat.le_of_dvd hLpos hpdiv),
      le_trans hprev3 (Nat.le_of_dvd hCarmichaelPos hprevdiv)⟩

/--
Inputs: a seed set with exactly `T + 1` primes, its large-prime tail product,
the Carmichael divisibility relation, and bounds `N ≤ x` and `(T + 1)^4 ≤ x`.

Claim: the tail product satisfies the arithmetic side conditions for the
modulus-four application of Proposition 1.5, with explicit bounds on its size
and Carmichael value.

Content: the tail primes are odd and exceed the seed cutoff, their factor count
is at most the seed size, and the Carmichael value divides `k * N`. The bounds
`k ≤ x` and `N ≤ x` control the Carmichael value by `x^2`.

Proof: combine the finite tail lemmas, the Carmichael lower-bound lemma, and
the bounds `k ≤ x` and `N ≤ x`.

Role: this common arithmetic completion is shared by fixed-factor and
all-divisor seed constructions.
-/
theorem seed_auxiliary_modulus_arithmetic_bounds_of_N_le_x {x N T k : ℕ} {S : Finset ℕ} {L : ℕ}
    (hx : 2 ≤ x) (hNpos : 0 < N) (hNleX : N ≤ x) (hk : 0 < k) (hkpow : k ^ 5 ≤ x ^ 3)
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
  have hFilterSubset : S.filter (fun p => 60 * S.card < p) ⊆ S := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hFactorCard : L.primeFactors.card ≤ S.card := by
    rw [hLprimeFactors]
    exact Finset.card_le_card hFilterSubset
  have hFactorPower : L.primeFactors.card ^ 4 ≤ x := by
    calc
      L.primeFactors.card ^ 4 ≤ S.card ^ 4 := Nat.pow_le_pow_left hFactorCard 4
      _ = (T + 1) ^ 4 := by rw [hScard]
      _ ≤ x := hTpower
  have hLpos : 0 < L := by
    rw [hL]
    apply Finset.prod_pos
    intro p hp
    exact Nat.Prime.pos (hS p (Finset.mem_filter.mp hp).1).1
  have hLcoprimeTwo : Nat.Coprime L 2 := by
    rw [hL]
    apply Nat.Coprime.prod_left
    intro p hp
    have hprime := (hS p (Finset.mem_filter.mp hp).1).1
    have hSpos : 0 < S.card := by
      rw [hScard]; exact Nat.succ_pos T
    have hSone : 1 ≤ S.card := Nat.succ_le_iff.mpr hSpos
    have hsixty : 60 ≤ 60 * S.card := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 60 hSone
    have hcut := (Finset.mem_filter.mp hp).2
    have hpgt2 : 2 < p := by
      have htwo60 : 2 < 60 := by norm_num only
      exact lt_trans htwo60 (lt_of_le_of_lt hsixty hcut)
    rw [Nat.coprime_two_right]
    exact Nat.Prime.odd_of_ne_two hprime (ne_of_gt hpgt2)
  have hLcoprimeFour : Nat.Coprime L 4 := by
    simpa only [show (4 : ℕ) = 2 ^ 2 by norm_num only] using (Nat.Coprime.pow_right 2 hLcoprimeTwo)
  have hFactorBound : ∀ r, r ∣ L → Nat.Prime r → r ≤ x := by
    intro r hr hprime
    have hmem : r ∈ L.primeFactors := Nat.mem_primeFactors.mpr ⟨hprime, hr, Nat.ne_of_gt hLpos⟩
    rw [hLprimeFactors] at hmem
    exact (hS r (Finset.mem_filter.mp hmem).1).2.1
  have hSpos : 0 < S.card := by
    rw [hScard]; exact Nat.succ_pos T
  have hP2 := seed_prime_tail_p2_lower_bounds S (fun p hp => (hS p hp).1) hSpos hprimeCount
  change
    2 < (S.filter (fun p => 60 * S.card < p)).prod id ∧
      3 ≤ ArithmeticFunction.carmichael ((S.filter (fun p => 60 * S.card < p)).prod id) at hP2
  rw [← hL] at hP2
  have hProp15Input : ReliableProp15ModFourInput L x :=
    ⟨hLsq, hLcoprimeFour, hFactorPower, hLreciprocal⟩
  have hxone : 1 ≤ x := le_trans (by norm_num only : 1 ≤ 2) hx
  have hTailCardLe : (S.filter (fun p => 60 * S.card < p)).card ≤ S.card :=
    Finset.card_le_card hFilterSubset
  have hLbound : L ≤ x ^ (T + 1) := by
    calc
      L = (S.filter (fun p => 60 * S.card < p)).prod id := hL
      _ ≤ x ^ (S.filter (fun p => 60 * S.card < p)).card := by
        apply Finset.prod_le_pow_card
        intro p hp
        exact (hS p (Finset.mem_filter.mp hp).1).2.1
      _ ≤ x ^ S.card := Nat.pow_le_pow_right hxone hTailCardLe
      _ = x ^ (T + 1) := by rw [hScard]
  have hx3le5 : x ^ 3 ≤ x ^ 5 := Nat.pow_le_pow_right hxone (by norm_num only : 3 ≤ 5)
  have hkX5 : k ^ 5 ≤ x ^ 5 := le_trans hkpow hx3le5
  have hkX : k ≤ x := (Nat.pow_le_pow_iff_left (by norm_num only : 5 ≠ 0)).mp hkX5
  have hkN : k * N ≤ x ^ 2 := by
    calc
      k * N ≤ x * x := Nat.mul_le_mul hkX hNleX
      _ = x ^ 2 := by rw [pow_two]
  have hLambdaBound : ArithmeticFunction.carmichael L ≤ x ^ 2 :=
    le_trans (Nat.le_of_dvd (Nat.mul_pos hk hNpos) hLlambda) hkN
  exact
    ⟨hLcoprimeFour, hFactorPower, hFactorBound, hP2.1, hP2.2, hProp15Input, hLbound, hLambdaBound⟩

/--
Inputs: seed data with cutoff multiplier `C ≥ 60`, the reciprocal-sum bound
`1 / C`, and the size bounds used for the modulus-four application.

Claim: the tail product satisfies `ReliableProp15ModFourInput` together with
the P2, factor-size, and Carmichael bounds.

Content: the stronger reciprocal-sum estimate implies reliable's fixed
`1 / 60` condition while the larger cutoff preserves oddness and the P2
lower bound.

Proof: repeat the finite arithmetic completion at cutoff `C`, and weaken the
reciprocal-sum field using `60 ≤ C`.

Role: this converts the improved seed-tail output into the arithmetic input
required by Proposition 1.5.
-/
theorem seed_auxiliary_modulus_arithmetic_bounds_of_cutoff_of_N_le_x (C : ℕ) (hC60 : 60 ≤ C)
    {x N T k : ℕ} {S : Finset ℕ} {L : ℕ} (hx : 2 ≤ x) (hNpos : 0 < N) (hNleX : N ≤ x) (hk : 0 < k)
    (hkpow : k ^ 5 ≤ x ^ 3) (hScard : S.card = T + 1) (hTpower : (T + 1) ^ 4 ≤ x)
    (hS :
      ∀ p ∈ S, Nat.Prime p ∧ p ≤ x ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1)
    (hL : L = (S.filter (fun p => C * S.card < p)).prod id) (hLsq : Squarefree L)
    (hLprimeFactors : L.primeFactors = S.filter (fun p => C * S.card < p))
    (hLreciprocal : (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (C : ℝ)⁻¹)
    (hLlambda : ArithmeticFunction.carmichael L ∣ k * N)
    (hprimeCount : 2 * Nat.primeCounting (C * S.card) ≤ S.card) :
    Nat.Coprime L 4 ∧
      L.primeFactors.card ^ 4 ≤ x ∧
      (∀ r, r ∣ L → Nat.Prime r → r ≤ x) ∧
      2 < L ∧
      3 ≤ ArithmeticFunction.carmichael L ∧
      ReliableProp15ModFourInput L x ∧
      L ≤ x ^ (T + 1) ∧ ArithmeticFunction.carmichael L ≤ x ^ 2 := by
  have hC4 : 4 < C := lt_of_lt_of_le (by norm_num only : 4 < 60) hC60
  have hFilterSubset : S.filter (fun p => C * S.card < p) ⊆ S := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hFactorCard : L.primeFactors.card ≤ S.card := by
    rw [hLprimeFactors]
    exact Finset.card_le_card hFilterSubset
  have hFactorPower : L.primeFactors.card ^ 4 ≤ x := by
    calc
      L.primeFactors.card ^ 4 ≤ S.card ^ 4 := Nat.pow_le_pow_left hFactorCard 4
      _ = (T + 1) ^ 4 := by rw [hScard]
      _ ≤ x := hTpower
  have hLpos : 0 < L := by
    rw [hL]
    apply Finset.prod_pos
    intro p hp
    exact Nat.Prime.pos (hS p (Finset.mem_filter.mp hp).1).1
  have hLcoprimeTwo : Nat.Coprime L 2 := by
    rw [hL]
    apply Nat.Coprime.prod_left
    intro p hp
    have hprime := (hS p (Finset.mem_filter.mp hp).1).1
    have hSpos : 0 < S.card := by
      rw [hScard]; exact Nat.succ_pos T
    have hSone : 1 ≤ S.card := Nat.succ_le_iff.mpr hSpos
    have hCscale : C ≤ C * S.card := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left C hSone
    have hcut := (Finset.mem_filter.mp hp).2
    have hpgt2 : 2 < p :=
      lt_trans (lt_trans (by norm_num only : 2 < 4) hC4) (lt_of_le_of_lt hCscale hcut)
    rw [Nat.coprime_two_right]
    exact Nat.Prime.odd_of_ne_two hprime (ne_of_gt hpgt2)
  have hLcoprimeFour : Nat.Coprime L 4 := by
    simpa only [show (4 : ℕ) = 2 ^ 2 by norm_num only] using (Nat.Coprime.pow_right 2 hLcoprimeTwo)
  have hFactorBound : ∀ r, r ∣ L → Nat.Prime r → r ≤ x := by
    intro r hr hprime
    have hmem : r ∈ L.primeFactors := Nat.mem_primeFactors.mpr ⟨hprime, hr, Nat.ne_of_gt hLpos⟩
    rw [hLprimeFactors] at hmem
    exact (hS r (Finset.mem_filter.mp hmem).1).2.1
  have hSpos : 0 < S.card := by
    rw [hScard]; exact Nat.succ_pos T
  have hP2 :=
    seed_prime_tail_p2_lower_bounds_of_cutoff S C hC4 (fun p hp => (hS p hp).1) hSpos hprimeCount
  change
    2 < (S.filter (fun p => C * S.card < p)).prod id ∧
      3 ≤ ArithmeticFunction.carmichael ((S.filter (fun p => C * S.card < p)).prod id) at hP2
  rw [← hL] at hP2
  have hCreciprocal : (C : ℝ)⁻¹ ≤ (1 / 60 : ℝ) := by
    rw [one_div]
    have hCposReal : (0 : ℝ) < C := by
      exact_mod_cast (lt_of_lt_of_le (by norm_num only : 0 < 60) hC60)
    exact (inv_le_inv₀ hCposReal (by norm_num only)).2 (by exact_mod_cast hC60)
  have hLreciprocal60 : (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) :=
    le_trans hLreciprocal hCreciprocal
  have hProp15Input : ReliableProp15ModFourInput L x :=
    ⟨hLsq, hLcoprimeFour, hFactorPower, hLreciprocal60⟩
  have hxone : 1 ≤ x := le_trans (by norm_num only : 1 ≤ 2) hx
  have hTailCardLe : (S.filter (fun p => C * S.card < p)).card ≤ S.card :=
    Finset.card_le_card hFilterSubset
  have hLbound : L ≤ x ^ (T + 1) := by
    calc
      L = (S.filter (fun p => C * S.card < p)).prod id := hL
      _ ≤ x ^ (S.filter (fun p => C * S.card < p)).card := by
        apply Finset.prod_le_pow_card
        intro p hp
        exact (hS p (Finset.mem_filter.mp hp).1).2.1
      _ ≤ x ^ S.card := Nat.pow_le_pow_right hxone hTailCardLe
      _ = x ^ (T + 1) := by rw [hScard]
  have hx3le5 : x ^ 3 ≤ x ^ 5 := Nat.pow_le_pow_right hxone (by norm_num only : 3 ≤ 5)
  have hkX5 : k ^ 5 ≤ x ^ 5 := le_trans hkpow hx3le5
  have hkX : k ≤ x := (Nat.pow_le_pow_iff_left (by norm_num only : 5 ≠ 0)).mp hkX5
  have hkN : k * N ≤ x ^ 2 := by
    calc
      k * N ≤ x * x := Nat.mul_le_mul hkX hNleX
      _ = x ^ 2 := by rw [pow_two]
  have hLambdaBound : ArithmeticFunction.carmichael L ≤ x ^ 2 :=
    le_trans (Nat.le_of_dvd (Nat.mul_pos hk hNpos) hLlambda) hkN
  exact
    ⟨hLcoprimeFour, hFactorPower, hFactorBound, hP2.1, hP2.2, hProp15Input, hLbound, hLambdaBound⟩

end PseudoPrime.AnalyticNumberTheory.AGP
