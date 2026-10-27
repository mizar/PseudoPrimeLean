/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.PrimeProductBounds

/-! # SeedConstruction

Initial seed selection and auxiliary-modulus assembly.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

/--
Inputs: the uniform form of reliable, Proposition 1.5 for modulus `1`, a
squarefree initial modulus `N`, a count threshold `T`, and a lower bound for
the restricted-divisor count.

Claim: if `T` is at least `primeTailCountThreshold`, the initial count supplies
exactly `T + 1` seed primes and a tail product whose reciprocal sum is at most
`1 / 60` and whose Carmichael value divides `k * N`.

Content: fixing the seed-set size makes later estimates of the number of prime
factors of the auxiliary modulus explicit.

Proof: take a subset of exactly `T + 1` primes from the count output, then
apply the prime-tail selection and finite prime-product lemmas.

Role: this is the threshold-parameterized arithmetic stage in reliable §2.
-/
theorem exists_seed_auxiliary_modulus_of_initial_uniform_count_with_threshold (c₀ : ℝ)
    (x₀ x N T : ℕ) (hT : primeTailCountThreshold ≤ T)
    (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x) (hN : N ≠ 0)
    (hSquarefree : Squarefree N)
    (hlower :
      (T : ℝ) <
        reliableProp15Coefficient c₀ 1 x *
          ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ)) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold < S.card ∧
        S.card = T + 1 ∧
        (∀ p ∈ S,
          Nat.Prime p ∧ p ≤ x ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * N ∧
        S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card := by
  obtain ⟨k, hk, hkpow, S, hSsize, hS⟩ :=
    exists_prime_set_of_reliable_prop15_uniform_count c₀ 1 1 x₀ N x T hcount hx hN hSquarefree
      (Nat.coprime_one_right N) hlower
  obtain ⟨Ssmall, hSsmall_sub, hSsmall_card⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := T + 1) (Nat.succ_le_of_lt hSsize)
  have hSsmallSize : primeTailCountThreshold < Ssmall.card := by
    rw [hSsmall_card]
    exact lt_of_le_of_lt hT (Nat.lt_succ_self _)
  have hprime : ∀ p ∈ Ssmall, Nat.Prime p := by
    intro p hp
    exact (hS p (hSsmall_sub hp)).1
  have hseed : ∀ p ∈ Ssmall, ∃ d, d ∣ N ∧ p = d * k + 1 := by
    intro p hp
    rcases hS p (hSsmall_sub hp) with ⟨_, _, _, d, hd, _, heq⟩
    exact ⟨d, hd, heq⟩
  have hSpos : 0 < Ssmall.card := lt_of_le_of_lt (Nat.zero_le _) hSsmallSize
  have hprimeCount := primeCounting_bound_of_primeTailCountThreshold (Nat.le_of_lt hSsmallSize)
  obtain ⟨hLsq, hLprimeFactors, hLreciprocal, hLlambda, hLcard⟩ :=
    seed_prime_tail_auxiliary_modulus_data Ssmall k N hprime hseed hSpos hprimeCount
  refine
    ⟨k, Ssmall, (Ssmall.filter (fun p => 60 * Ssmall.card < p)).prod id, hk, hkpow, hSsmallSize,
      hSsmall_card, ?_, rfl, hLsq, hLprimeFactors, hLreciprocal, hLlambda, hLcard⟩
  intro p hp
  rcases hS p (hSsmall_sub hp) with ⟨hpPrime, hpx, _, d, hd, hcut, hpeq⟩
  exact ⟨hpPrime, hpx, d, hd, hcut, hpeq⟩

/--
Inputs: the uniform modulus-one count from reliable, Proposition 1.5, a seed
threshold `T`, and a lower bound for the restricted-divisor count.

Claim: the initial count supplies exactly `T + 1` seed primes and a tail
product above `120 * S.card` whose reciprocal sum is at most `1 / 120`.

Content: the larger cutoff preserves at least half of the selected seed primes
and improves the reciprocal-sum input for the later average coefficient.

Proof: select a subset of size `T + 1`, apply the 120-cutoff
prime-counting estimate, and form the tail product.

Role: this supplies the improved reciprocal bound to the generalized AGP
average-count argument.
-/
theorem exists_seed_auxiliary_modulus_of_initial_uniform_count_with_threshold120 (c₀ : ℝ)
    (x₀ x N T : ℕ) (hT : primeTailCountThreshold120 ≤ T)
    (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x) (hN : N ≠ 0)
    (hSquarefree : Squarefree N)
    (hlower :
      (T : ℝ) <
        reliableProp15Coefficient c₀ 1 x *
          ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ)) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold120 < S.card ∧
        S.card = T + 1 ∧
        (∀ p ∈ S,
          Nat.Prime p ∧ p ≤ x ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 120 * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => 120 * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 120 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * N ∧
        S.card ≤ 2 * (S.filter (fun p => 120 * S.card < p)).card := by
  obtain ⟨k, hk, hkpow, S, hSsize, hS⟩ :=
    exists_prime_set_of_reliable_prop15_uniform_count c₀ 1 1 x₀ N x T hcount hx hN hSquarefree
      (Nat.coprime_one_right N) hlower
  obtain ⟨Ssmall, hSsmall_sub, hSsmall_card⟩ :=
    Finset.exists_subset_card_eq (s := S) (n := T + 1) (Nat.succ_le_of_lt hSsize)
  have hSsmallSize : primeTailCountThreshold120 < Ssmall.card := by
    rw [hSsmall_card]
    exact lt_of_le_of_lt hT (Nat.lt_succ_self _)
  have hprime : ∀ p ∈ Ssmall, Nat.Prime p := by
    intro p hp
    exact (hS p (hSsmall_sub hp)).1
  have hseed : ∀ p ∈ Ssmall, ∃ d, d ∣ N ∧ p = d * k + 1 := by
    intro p hp
    rcases hS p (hSsmall_sub hp) with ⟨_, _, _, d, hd, _, heq⟩
    exact ⟨d, hd, heq⟩
  have hSpos : 0 < Ssmall.card := lt_of_le_of_lt (Nat.zero_le _) hSsmallSize
  have hprimeCount := primeCounting_bound_of_primeTailCountThreshold120 (Nat.le_of_lt hSsmallSize)
  obtain ⟨hLsq, hLprimeFactors, hLreciprocal, hLlambda, hLcard⟩ :=
    seed_prime_tail_auxiliary_modulus_data_of_cutoff Ssmall k N 120 (by norm_num only) hprime hseed
      hSpos hprimeCount
  have hLreciprocal' :
    (∑ p ∈ ((Ssmall.filter (fun p => 120 * Ssmall.card < p)).prod id).primeFactors, (p : ℝ)⁻¹) ≤
      (1 / 120 : ℝ) := by
    simpa only [one_div, Nat.cast_ofNat] using hLreciprocal
  refine
    ⟨k, Ssmall, (Ssmall.filter (fun p => 120 * Ssmall.card < p)).prod id, hk, hkpow, hSsmallSize,
      hSsmall_card, ?_, rfl, hLsq, hLprimeFactors, hLreciprocal', hLlambda, hLcard⟩
  intro p hp
  rcases hS p (hSsmall_sub hp) with ⟨hpPrime, hpx, _, d, hd, hcut, hpeq⟩
  exact ⟨hpPrime, hpx, d, hd, hcut, hpeq⟩

/--
Inputs: the initial modulus-one count, its seed threshold, `N ≤ x`, and the
fourth-power bound for the selected seed-set size.

Claim: the `1 / 120` seed-tail construction also supplies every arithmetic
field of `ReliableProp15ModFourInput`, the P2 lower bounds, and the modulus
size bounds.

Content: the general cutoff arithmetic lemma weakens the reciprocal sum to
reliable's fixed `1 / 60` admissibility condition while retaining the sharper
`1 / 120` result separately.

Proof: construct the improved tail, apply its Chebyshev count threshold, and
complete the modulus-four arithmetic estimates.

Role: this makes the improved seed modulus usable as input to the later
Proposition 1.5 and prime-supply stages.
-/
theorem exists_seed_auxiliary_modulus_with_prop15_input120 (c₀ : ℝ) (x₀ x N T : ℕ)
    (hT : primeTailCountThreshold120 ≤ T) (hcount : ReliableProp15UniformCount c₀ 1 1 x₀)
    (hx : x₀ ≤ x) (hN : N ≠ 0) (hSquarefree : Squarefree N) (hNleX : N ≤ x)
    (hTpower : (T + 1) ^ 4 ≤ x)
    (hlower :
      (T : ℝ) <
        reliableProp15Coefficient c₀ 1 x *
          ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ)) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold120 < S.card ∧
        S.card = T + 1 ∧
        (∀ p ∈ S,
          Nat.Prime p ∧ p ≤ x ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 120 * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => 120 * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 120 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * N ∧
        S.card ≤ 2 * (S.filter (fun p => 120 * S.card < p)).card ∧
        Nat.Coprime L 4 ∧
        L.primeFactors.card ^ 4 ≤ x ∧
        (∀ r, r ∣ L → Nat.Prime r → r ≤ x) ∧
        2 < L ∧
        3 ≤ ArithmeticFunction.carmichael L ∧
        ReliableProp15ModFourInput L x ∧
        L ≤ x ^ (T + 1) ∧ ArithmeticFunction.carmichael L ≤ x ^ 2 := by
  obtain
    ⟨k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda,
      hLcard⟩ :=
    exists_seed_auxiliary_modulus_of_initial_uniform_count_with_threshold120 c₀ x₀ x N T hT hcount
      hx hN hSquarefree hlower
  have hprimeCount := primeCounting_bound_of_primeTailCountThreshold120 (Nat.le_of_lt hSsize)
  have hxTwo : 2 ≤ x := le_trans hcount.1 hx
  have hLreciprocalC : (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (120 : ℝ)⁻¹ := by
    simpa only [one_div, Nat.cast_ofNat] using hLreciprocal
  have harithmetic :=
    seed_auxiliary_modulus_arithmetic_bounds_of_cutoff_of_N_le_x 120 (by norm_num only) hxTwo
      (Nat.pos_of_ne_zero hN) hNleX hk hkpow hScard hTpower hS hL hLsq hLprimeFactors hLreciprocalC
      hLlambda hprimeCount
  exact
    ⟨k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda,
      hLcard, harithmetic⟩

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a uniform modulus-one count, a seed threshold `T`, and a choice of
`z` and `s` whose primorial fits below the Proposition 1.5 cutoff.

Claim: a strict lower bound from $(\pi(z)+1-s)^s/s!$ supplies the threshold-sized
seed set and its auxiliary prime product.

Content: the fixed-factor products embed into the restricted divisors of the
primorial; the existing reliable-count construction then selects the seed
primes and controls their large-prime tail.

Proof: transfer the binomial lower bound through the divisor-set inclusion,
verify positivity of the modulus-one coefficient, and apply the established
seed construction.

Role: this connects the original fixed-factor divisor count to the finite
arithmetic stage of reliable §2.
-/
theorem exists_seed_auxiliary_modulus_of_fixedFactorCount (c₀ : ℝ) (hc₀ : 0 < c₀) (x₀ x z s T : ℕ)
    (hT : primeTailCountThreshold ≤ T) (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x)
    (hcut : (primeSetLE z).prod id ≤ reliableProp15DivisorCutoff x)
    (hlower :
      (T : ℝ) <
        reliableProp15Coefficient c₀ 1 x *
          ((((Nat.primeCounting z + 1 - s : ℕ) ^ s : ℕ) : ℝ) / (s.factorial : ℝ))) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold < S.card ∧
        S.card = T + 1 ∧
        (∀ p ∈ S,
          Nat.Prime p ∧
            p ≤ x ∧
            ∃ d, d ∣ (primeSetLE z).prod id ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
        S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card := by
  have hxnat : 1 < x := by exact lt_of_lt_of_le (by norm_num only : 1 < 2) (le_trans hcount.1 hx)
  have hxreal : (1 : ℝ) < (x : ℝ) := by exact_mod_cast hxnat
  have hlog : 0 < Real.log (x : ℝ) := Real.log_pos hxreal
  have hcoefeq : reliableProp15Coefficient c₀ 1 x = c₀ / Real.log (x : ℝ) := by
    simp only [reliableProp15Coefficient, Nat.totient_one, Nat.cast_one, one_mul]
  have hcoef : 0 < reliableProp15Coefficient c₀ 1 x := by
    rw [hcoefeq]
    exact div_pos hc₀ hlog
  have hdivcard := choose_le_restrictedDivisors_card_of_fixedPrimeFactorProducts (s := s) hcut
  have hdivcardR :
    ((Nat.choose (Nat.primeCounting z) s : ℕ) : ℝ) ≤
      ((restrictedDivisors ((primeSetLE z).prod id) (reliableProp15DivisorCutoff x)).card : ℝ) := by
    exact Nat.cast_le.mpr hdivcard
  have hbinomial :
    ((((Nat.primeCounting z + 1 - s : ℕ) ^ s : ℕ) : ℝ) / (s.factorial : ℝ)) ≤
      ((Nat.choose (Nat.primeCounting z) s : ℕ) : ℝ) := by
    simpa only [Nat.cast_pow] using Nat.pow_le_choose (α := ℝ) s (Nat.primeCounting z)
  have hchooseLE :
    ((((Nat.primeCounting z + 1 - s : ℕ) ^ s : ℕ) : ℝ) / (s.factorial : ℝ)) ≤
      ((restrictedDivisors ((primeSetLE z).prod id) (reliableProp15DivisorCutoff x)).card : ℝ) :=
    le_trans hbinomial hdivcardR
  have hscaled := mul_le_mul_of_nonneg_left hchooseLE (le_of_lt hcoef)
  have hlower' := lt_of_lt_of_le hlower hscaled
  have hNpos := primeProductLE_pos z
  have hNdata := primeProductLE_data z
  exact
    exists_seed_auxiliary_modulus_of_initial_uniform_count_with_threshold c₀ x₀ x
      ((primeSetLE z).prod id) T hT hcount hx (Nat.ne_of_gt hNpos) hNdata.1 hlower'

/--
Inputs: the uniform modulus-1 count, a squarefree nonzero modulus `N`, and a
restricted-divisor lower bound exceeding `primeTailCountThreshold`.

Claim: these data produce a seed set larger than the fixed tail-selection
threshold, together with its auxiliary prime product and Carmichael bound.

Content: this preserves the original fixed-threshold interface while the
parameterized theorem above exposes the exact seed-set size.

Proof: specialize the parameterized construction to
`T = primeTailCountThreshold` and discard the exact-cardinality field.

Role: this is the fixed-threshold interface used by the existing initial-count
bridges.
-/
theorem exists_seed_auxiliary_modulus_of_initial_uniform_count (c₀ : ℝ) (x₀ x N : ℕ)
    (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x) (hN : N ≠ 0)
    (hSquarefree : Squarefree N)
    (hlower :
      (primeTailCountThreshold : ℝ) <
        reliableProp15Coefficient c₀ 1 x *
          ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ)) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold < S.card ∧
        (∀ p ∈ S,
          Nat.Prime p ∧ p ≤ x ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * N ∧
        S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card := by
  obtain
    ⟨k, S, L, hk, hkpow, hSsize, _hScard, hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda,
      hLcard⟩ :=
    exists_seed_auxiliary_modulus_of_initial_uniform_count_with_threshold c₀ x₀ x N
      primeTailCountThreshold (Nat.le_refl _) hcount hx hN hSquarefree hlower
  exact ⟨k, S, L, hk, hkpow, hSsize, hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda, hLcard⟩

/--
Inputs: a modulus-one uniform count, a squarefree nonzero initial modulus,
and a cutoff containing its square-root divisors.

Claim: a lower bound obtained from half the full divisor count supplies the
threshold-sized seed primes and their tail product.

Content: the complementary-divisor estimate transfers the half-count bound to
the restricted divisors used by reliable, Proposition 1.5.

Role: this is the initial seed construction with the square-root divisor range
used in reliable, §2.
-/
theorem exists_seed_auxiliary_modulus_of_sqrt_divisor_count (c₀ : ℝ) (hc₀ : 0 < c₀) (x₀ x N T : ℕ)
    (hT : primeTailCountThreshold ≤ T) (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x)
    (hN : N ≠ 0) (hSquarefree : Squarefree N) (hcut : Nat.sqrt N ≤ reliableProp15DivisorCutoff x)
    (hlower :
      (T : ℝ) < reliableProp15Coefficient c₀ 1 x * (((2 ^ N.primeFactors.card : ℕ) : ℝ) / 2)) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold < S.card ∧
        S.card = T + 1 ∧
        (∀ p ∈ S,
          Nat.Prime p ∧ p ≤ x ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * N ∧
        S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card := by
  have hxTwo : 2 ≤ x := le_trans hcount.1 hx
  have hlower' :=
    initial_uniform_count_lower_bound_of_sqrt_divisors (c₀ := c₀) (N := N) (x := x) (T := T) hc₀ hN
      hSquarefree hcut hxTwo hlower
  exact
    exists_seed_auxiliary_modulus_of_initial_uniform_count_with_threshold c₀ x₀ x N T hT hcount hx
      hN hSquarefree hlower'

/--
Inputs: a squarefree nonzero modulus `N` below the divisor cutoff and a lower
bound for the uniform-count coefficient times the full divisor count.

Claim: the same strict lower bound holds with `restrictedDivisors` in place of
the full divisor count.

Content: when the cutoff covers `N`, every divisor is counted, and squarefree
`N` has exactly `2 ^ N.primeFactors.card` divisors.

Proof: rewrite the restricted divisor cardinality using
`card_restrictedDivisors_eq_two_pow_primeFactors_card`.

Role: this gives a convenient sufficient condition for the initial uniform
count needed by the seed auxiliary-modulus construction.
-/
theorem initial_uniform_count_lower_bound_of_full_divisors (c₀ : ℝ) (x N : ℕ) (hN : N ≠ 0)
    (hSquarefree : Squarefree N) (hcutoff : N ≤ reliableProp15DivisorCutoff x)
    (hlower :
      (primeTailCountThreshold : ℝ) <
        reliableProp15Coefficient c₀ 1 x * ((2 ^ N.primeFactors.card : ℕ) : ℝ)) :
    (primeTailCountThreshold : ℝ) <
      reliableProp15Coefficient c₀ 1 x *
        ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ) := by
  rw [card_restrictedDivisors_eq_two_pow_primeFactors_card hN hSquarefree hcutoff]
  exact hlower

/--
Inputs: a squarefree nonzero modulus `N`, a divisor cutoff covering `N`, and
a real lower bound at a natural threshold `T` for the full divisor count.

Claim: the same bound holds for the restricted-divisor count.

Proof: rewrite the restricted-divisor cardinality as the full divisor count.

Role: this threshold-parameterized form connects the prime-product count to
the exact-size seed construction.
-/
theorem initial_uniform_count_lower_bound_of_full_divisors_with_threshold (c₀ : ℝ) (x N T : ℕ)
    (hN : N ≠ 0) (hSquarefree : Squarefree N) (hcutoff : N ≤ reliableProp15DivisorCutoff x)
    (hlower : (T : ℝ) < reliableProp15Coefficient c₀ 1 x * ((2 ^ N.primeFactors.card : ℕ) : ℝ)) :
    (T : ℝ) <
      reliableProp15Coefficient c₀ 1 x *
        ((restrictedDivisors N (reliableProp15DivisorCutoff x)).card : ℝ) := by
  rw [card_restrictedDivisors_eq_two_pow_primeFactors_card hN hSquarefree hcutoff]
  exact hlower

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: the modulus-1 uniform count, a cutoff `z`, and bounds placing the
product of primes at most `z` below the divisor cutoff with enough divisors.

Claim: this initial prime product supplies the auxiliary modulus data produced
by `exists_seed_auxiliary_modulus_of_initial_uniform_count`.

Content: the divisor count is `2 ^ Nat.primeCounting z`, since the prime
product is squarefree and has exactly `Nat.primeCounting z` prime factors.

Proof: convert the divisor-count lower bound to the restricted-divisor bound,
then apply the existing seed construction.

Role: this is the finite arithmetic bridge from the proposed initial modulus
`N_z` to the first application of reliable, Proposition 1.5.
-/
theorem exists_seed_auxiliary_modulus_of_primeProductLE (c₀ : ℝ) (x₀ x z : ℕ)
    (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x)
    (hcut : (primeSetLE z).prod id ≤ reliableProp15DivisorCutoff x)
    (hlower :
      (primeTailCountThreshold : ℝ) <
        reliableProp15Coefficient c₀ 1 x * ((2 ^ Nat.primeCounting z : ℕ) : ℝ)) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold < S.card ∧
        (∀ p ∈ S,
          Nat.Prime p ∧
            p ≤ x ∧
            ∃ d, d ∣ (primeSetLE z).prod id ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
        S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card := by
  let N : ℕ := (primeSetLE z).prod id
  have hData := primeProductLE_data z
  have hN : N ≠ 0 := Nat.ne_of_gt (primeProductLE_pos z)
  have hFullLower :
    (primeTailCountThreshold : ℝ) <
      reliableProp15Coefficient c₀ 1 x * ((2 ^ N.primeFactors.card : ℕ) : ℝ) := by
    rw [primeProductLE_primeFactors_card]
    exact hlower
  have hRestrictedLower :=
    initial_uniform_count_lower_bound_of_full_divisors c₀ x ((primeSetLE z).prod id) hN hData.1 hcut
      hFullLower
  exact
    exists_seed_auxiliary_modulus_of_initial_uniform_count c₀ x₀ x ((primeSetLE z).prod id) hcount
      hx hN hData.1 hRestrictedLower

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: the modulus-1 uniform count, a prime-product cutoff `z`, a divisor
cutoff bound, and a count threshold at least `primeTailCountThreshold`.

Claim: the prime product through `z` supplies exactly `T + 1` seed primes and
the corresponding tail auxiliary modulus.

Content: this exposes the seed-set size needed to balance the later P2 bound
against the Carmichael and logarithmic factors.

Proof: identify the full divisor count with `2 ^ Nat.primeCounting z`, pass to
the restricted count, and apply the threshold-parameterized seed theorem.

Role: this is the threshold-aware prime-product bridge for the initial
modulus-1 application of Proposition 1.5.
-/
theorem exists_seed_auxiliary_modulus_of_primeProductLE_with_threshold (c₀ : ℝ) (x₀ x z T : ℕ)
    (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x)
    (hcut : (primeSetLE z).prod id ≤ reliableProp15DivisorCutoff x)
    (hT : primeTailCountThreshold ≤ T)
    (hlower : (T : ℝ) < reliableProp15Coefficient c₀ 1 x * ((2 ^ Nat.primeCounting z : ℕ) : ℝ)) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold < S.card ∧
        S.card = T + 1 ∧
        (∀ p ∈ S,
          Nat.Prime p ∧
            p ≤ x ∧
            ∃ d, d ∣ (primeSetLE z).prod id ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
        S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card := by
  have hData := primeProductLE_data z
  have hN : (primeSetLE z).prod id ≠ 0 := Nat.ne_of_gt (primeProductLE_pos z)
  have hFullLower :
    (T : ℝ) <
      reliableProp15Coefficient c₀ 1 x *
        ((2 ^ ((primeSetLE z).prod id).primeFactors.card : ℕ) : ℝ) := by
    rw [primeProductLE_primeFactors_card]
    exact hlower
  have hRestrictedLower :=
    initial_uniform_count_lower_bound_of_full_divisors_with_threshold c₀ x ((primeSetLE z).prod id)
      T hN hData.1 hcut hFullLower
  exact
    exists_seed_auxiliary_modulus_of_initial_uniform_count_with_threshold c₀ x₀ x
      ((primeSetLE z).prod id) T hT hcount hx hN hData.1 hRestrictedLower

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a uniform modulus-one count, a prime-product modulus, an exact seed
size threshold, and a cutoff multiplier `C > 4` with its prime-count bound.

Claim: one can select exactly `T + 1` seed primes and form their `C`-tail
modulus with reciprocal-prime sum at most `1 / C`.

Proof: use the full prime-product divisor count to select the seed primes,
then apply the general cutoff tail and squarefree-product constructions.

Role: this retains the stronger reciprocal-sum estimate needed by the
full-divisor AGP route without changing the established cutoff-60 API.
-/
theorem exists_seed_auxiliary_modulus_of_primeProductLE_with_threshold_cutoff (c₀ : ℝ)
    (x₀ x z T C : ℕ) (hC : 4 < C) (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x)
    (hcut : (primeSetLE z).prod id ≤ reliableProp15DivisorCutoff x)
    (hT : primeTailCountThreshold ≤ T) (hprimeCount : 2 * Nat.primeCounting (C * (T + 1)) ≤ T + 1)
    (hlower : (T : ℝ) < reliableProp15Coefficient c₀ 1 x * ((2 ^ Nat.primeCounting z : ℕ) : ℝ)) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold < S.card ∧
        S.card = T + 1 ∧
        (∀ p ∈ S,
          Nat.Prime p ∧
            p ≤ x ∧
            ∃ d, d ∣ (primeSetLE z).prod id ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => C * S.card < p)).prod id ∧
        Squarefree L ∧
        L.primeFactors = S.filter (fun p => C * S.card < p) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (C : ℝ)⁻¹ ∧
        ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
        S.card ≤ 2 * (S.filter (fun p => C * S.card < p)).card := by
  let N : ℕ := (primeSetLE z).prod id
  have hData := primeProductLE_data z
  have hN : N ≠ 0 := Nat.ne_of_gt (primeProductLE_pos z)
  have hFullLower :
    (T : ℝ) < reliableProp15Coefficient c₀ 1 x * ((2 ^ N.primeFactors.card : ℕ) : ℝ) := by
    rw [primeProductLE_primeFactors_card]
    exact hlower
  have hRestrictedLower :=
    initial_uniform_count_lower_bound_of_full_divisors_with_threshold c₀ x N T hN hData.1 hcut
      hFullLower
  obtain ⟨k, hk, hkpow, Sall, hSallsize, hSall⟩ :=
    exists_prime_set_of_reliable_prop15_uniform_count c₀ 1 1 x₀ N x T hcount hx hN hData.1
      (Nat.coprime_one_right _) hRestrictedLower
  obtain ⟨S, hSsub, hScard⟩ :=
    Finset.exists_subset_card_eq (s := Sall) (n := T + 1) (Nat.succ_le_of_lt hSallsize)
  have hSsize : primeTailCountThreshold < S.card := by
    rw [hScard]
    exact lt_of_le_of_lt hT (Nat.lt_succ_self _)
  have hprime : ∀ p ∈ S, Nat.Prime p := by
    intro p hp
    exact (hSall p (hSsub hp)).1
  have hseed : ∀ p ∈ S, ∃ d, d ∣ N ∧ p = d * k + 1 := by
    intro p hp
    rcases hSall p (hSsub hp) with ⟨_, _, _, d, hd, _, heq⟩
    exact ⟨d, hd, heq⟩
  have hSpos : 0 < S.card := by
    rw [hScard]
    exact Nat.succ_pos T
  have hprimeCountS : 2 * Nat.primeCounting (C * S.card) ≤ S.card := by
    rw [hScard]
    exact hprimeCount
  obtain ⟨hLsq, hLprimeFactors, hLreciprocal, hLlambda, hLcard⟩ :=
    seed_prime_tail_auxiliary_modulus_data_of_cutoff S k N C (by omega) hprime hseed hSpos
      hprimeCountS
  have hseedWithBound :
    ∀ p ∈ S,
      Nat.Prime p ∧ p ≤ x ∧ ∃ d, d ∣ N ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1 := by
    intro p hp
    rcases hSall p (hSsub hp) with ⟨hpp, hpx, hdiv, d, hd, hcutd, heq⟩
    exact ⟨hpp, hpx, d, hd, hcutd, heq⟩
  refine
    ⟨k, S, (S.filter (fun p => C * S.card < p)).prod id, hk, hkpow, hSsize, hScard, hseedWithBound,
      rfl, hLsq, hLprimeFactors, hLreciprocal, hLlambda, hLcard⟩

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a positive coefficient, a threshold for the uniform modulus-one
Proposition 1.5 count, and its lower cutoff `x₀`.

Claim: one can choose `z = 2 ^ m` and a seed size `T` so that the primorial
construction produces exactly `T + 1` seed primes, with `4 * z * m ≤ T + 1`
and `(T + 1)^4 ≤ z^15`.

Content: the explicit Chebyshev estimate for `2 ^ m` gives a count of order
`c₀ * z^2 / m`; choosing half that scale leaves enough room for the cutoff
and gives a stronger base for the fixed-factor size `s = z * m`.

Proof: select the stronger scale with `exists_primeProductLE_quadratic_seed_scale`, use
`primeProductLE_count_lower_bound_of_two_pow` for the strict count bound, and
apply the thresholded seed construction at `x = N^5`.

Role: this connects the explicit first-stage parameter scale to the seed
primes required for the reliable Proposition 1.5 construction.
-/
theorem exists_seed_auxiliary_modulus_of_primeProductLE_scale {c₀ : ℝ} (hc₀ : 0 < c₀) (x₀ : ℕ)
    (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) :
    ∃ m z T : ℕ,
      10 ≤ m ∧
        x₀ ≤ m ∧
        z = 2 ^ m ∧
        T = Nat.floor (c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2)) ∧
        primeTailCountThreshold ≤ T ∧
        primeTailCountThreshold1024 ≤ T ∧
        4 * z * m ≤ T + 1 ∧
        (T + 1) ^ 4 ≤ z ^ 15 ∧
        ∃ k : ℕ,
          ∃ S : Finset ℕ,
            ∃ L : ℕ,
              0 < k ∧
                k ^ 5 ≤ (((primeSetLE z).prod id : ℕ) ^ 5) ^ 3 ∧
                primeTailCountThreshold < S.card ∧
                S.card = T + 1 ∧
                (∀ p ∈ S,
                  Nat.Prime p ∧
                    p ≤ ((primeSetLE z).prod id : ℕ) ^ 5 ∧
                    ∃ d,
                      d ∣ (primeSetLE z).prod id ∧
                        d ≤ reliableProp15DivisorCutoff (((primeSetLE z).prod id : ℕ) ^ 5) ∧
                        p = d * k + 1) ∧
                L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
                Squarefree L ∧
                L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
                (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
                ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
                S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card ∧
                Nat.Coprime L 4 ∧
                L.primeFactors.card ^ 4 ≤ ((primeSetLE z).prod id : ℕ) ^ 5 ∧
                (∀ r, r ∣ L → Nat.Prime r → r ≤ ((primeSetLE z).prod id : ℕ) ^ 5) ∧
                2 < L ∧
                3 ≤ ArithmeticFunction.carmichael L ∧
                ReliableProp15ModFourInput L (((primeSetLE z).prod id : ℕ) ^ 5) ∧
                L ≤ (((primeSetLE z).prod id : ℕ) ^ 5) ^ (T + 1) ∧
                ArithmeticFunction.carmichael L ≤ (((primeSetLE z).prod id : ℕ) ^ 5) ^ 2 ∧
                (T + 1) / 2 ≤ L.primeFactors.card ∧
                ((T : ℝ) / (4 * ((z * m : ℕ) : ℝ))) ^ (z * m) ≤
                  ((fixedPrimeFactorProductsOf L.primeFactors (z * m)).card : ℝ) ∧
                ((c₀ * (z : ℝ) ^ 2 / (40 * (m : ℝ) * Real.log 2)) / (4 * ((z * m : ℕ) : ℝ))) ≤
                  (T : ℝ) / (4 * ((z * m : ℕ) : ℝ)) := by
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only : (1 : ℝ) < 2)
  have hden : 0 < 20 * Real.log 2 := mul_pos (by norm_num only : (0 : ℝ) < 20) hlog2
  have ha : 0 < c₀ / (20 * Real.log 2) := div_pos hc₀ hden
  obtain ⟨m, z, T, hm, hmx₀, hz, hTdef, hT, hscale, hTpow⟩ :=
    exists_primeProductLE_quadratic_seed_scale ha
      (max primeTailCountThreshold primeTailCountThreshold1024) x₀
  have hT60 : primeTailCountThreshold ≤ T := le_trans (le_max_left _ _) hT
  have hT1024 : primeTailCountThreshold1024 ≤ T := le_trans (le_max_right _ _) hT
  have hden10 : 0 < 10 * Real.log 2 := mul_pos (by norm_num only : (0 : ℝ) < 10) hlog2
  have hden20 : 0 < 20 * Real.log 2 := hden
  have hconst : c₀ / (20 * Real.log 2) < c₀ / (10 * Real.log 2) := by
    apply (div_lt_div_iff₀ hden20 hden10).2
    nlinarith only [hc₀, hlog2]
  have hzpos : 0 < z := by
    rw [hz]
    exact Nat.pow_pos (by norm_num only)
  have hmpos : 0 < m := Nat.lt_of_lt_of_le (by norm_num only : 0 < 10) hm
  have hscalePos : 0 < (z : ℝ) ^ 2 / (m : ℝ) :=
    div_pos (sq_pos_of_pos (by exact_mod_cast hzpos)) (by exact_mod_cast hmpos)
  have hTarg : 0 ≤ c₀ / (20 * Real.log 2) * (z : ℝ) ^ 2 / (m : ℝ) :=
    div_nonneg (mul_nonneg (le_of_lt ha) (sq_nonneg (z : ℝ))) (le_of_lt (by exact_mod_cast hmpos))
  have hTle : (T : ℝ) ≤ c₀ / (20 * Real.log 2) * (z : ℝ) ^ 2 / (m : ℝ) := by
    rw [hTdef]
    exact_mod_cast Nat.floor_le hTarg
  have hstrict : (T : ℝ) < c₀ * (z : ℝ) ^ 2 / (10 * (m : ℝ) * Real.log 2) := by
    calc
      (T : ℝ) ≤ c₀ / (20 * Real.log 2) * (z : ℝ) ^ 2 / (m : ℝ) := hTle
      _ = c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) := by ring
      _ < c₀ * (z : ℝ) ^ 2 / (10 * (m : ℝ) * Real.log 2) := by
        calc
          c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) =
              c₀ / (20 * Real.log 2) * ((z : ℝ) ^ 2 / (m : ℝ)) :=
            by ring
          _ < c₀ / (10 * Real.log 2) * ((z : ℝ) ^ 2 / (m : ℝ)) :=
            mul_lt_mul_of_pos_right hconst hscalePos
          _ = c₀ * (z : ℝ) ^ 2 / (10 * (m : ℝ) * Real.log 2) := by ring
  have hcountLower := primeProductLE_count_lower_bound_of_two_pow hc₀ hm
  have hcountLower' :
    c₀ * (z : ℝ) ^ 2 / (10 * (m : ℝ) * Real.log 2) ≤
      reliableProp15Coefficient c₀ 1 (((primeSetLE z).prod id : ℕ) ^ 5) *
        ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
    simpa only [hz, div_eq_mul_inv] using hcountLower
  have hTdef' : T = Nat.floor (c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2)) := by
    rw [hTdef]
    congr 1
    ring
  have hcountStrict :
    (T : ℝ) <
      reliableProp15Coefficient c₀ 1 (((primeSetLE z).prod id : ℕ) ^ 5) *
        ((2 ^ Nat.primeCounting z : ℕ) : ℝ) :=
    lt_of_lt_of_le hstrict hcountLower'
  have hpowTwo := powTwo_ge_cube hm
  have hmleZ : m ≤ z := by
    have hmleCube : m ≤ m ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) m
    exact le_trans hmleCube (by simpa only [hz] using hpowTwo)
  let N : ℕ := (primeSetLE z).prod id
  have hpi : 3 * m ≤ Nat.primeCounting z := by
    simpa only [hz] using (primeCounting_two_pow_lower hm)
  have hNlower : z ^ 3 ≤ N := by
    calc
      z ^ 3 = (2 ^ m) ^ 3 := by rw [hz]
      _ = 2 ^ (m * 3) := by rw [← pow_mul]
      _ = 2 ^ (3 * m) := by rw [Nat.mul_comm]
      _ ≤ 2 ^ Nat.primeCounting z := by exact Nat.pow_le_pow_right (by norm_num only : 0 < 2) hpi
      _ ≤ N := by
        dsimp [N]
        exact primeProductLE_ge_two_pow_primeCounting z
  have hNpos : 0 < N := primeProductLE_pos z
  have hNleX : N ≤ N ^ 5 := Nat.le_self_pow (by norm_num only : 5 ≠ 0) N
  have hx₀ : x₀ ≤ N ^ 5 := by
    have hzleCube : z ≤ z ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) z
    exact le_trans hmx₀ (le_trans hmleZ (le_trans hzleCube (le_trans hNlower hNleX)))
  have hNfiveLower : z ^ 15 ≤ N ^ 5 := by
    have hpowEq : z ^ 15 = (z ^ 3) ^ 5 := by
      calc
        z ^ 15 = z ^ (3 * 5) := by norm_num only
        _ = (z ^ 3) ^ 5 := by rw [pow_mul]
    rw [hpowEq]
    exact Nat.pow_le_pow_left hNlower 5
  have hTpowX : (T + 1) ^ 4 ≤ N ^ 5 := le_trans hTpow hNfiveLower
  have hcut := primeProductLE_le_divisorCutoff_fifth_power z
  have hseed :=
    exists_seed_auxiliary_modulus_of_primeProductLE_with_threshold c₀ x₀ (N ^ 5) z T hcount hx₀ hcut
      hT60 hcountStrict
  rcases hseed with
    ⟨k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda,
      hLcard⟩
  have hzge2 : 2 ≤ z := by
    rw [hz]
    exact Nat.le_self_pow (Nat.ne_of_gt hmpos) 2
  have hzleCube : z ≤ z ^ 3 := Nat.le_self_pow (by norm_num only : 3 ≠ 0) z
  have hxTwo : 2 ≤ N ^ 5 := le_trans hzge2 (le_trans hzleCube (le_trans hNlower hNleX))
  have hprimeCount := primeCounting_bound_of_primeTailCountThreshold (Nat.le_of_lt hSsize)
  obtain
    ⟨hLcoprimeFour, hFactorPower, hFactorBound, hLlower, hLambdaLower, hProp15Input, hLbound,
      hLambdaBound⟩ :=
    seed_auxiliary_modulus_arithmetic_bounds_of_N_le_x hxTwo hNpos hNleX hk hkpow hScard hTpowX hS
      hL hLsq hLprimeFactors hLreciprocal hLlambda hprimeCount
  have hFactorCount : (T + 1) / 2 ≤ L.primeFactors.card := by
    rw [hLprimeFactors, ← hScard]
    exact Nat.div_le_of_le_mul hLcard
  have hs : 0 < z * m := Nat.mul_pos hzpos hmpos
  have hscaleS : 4 * (z * m) ≤ T + 1 := by simpa only [Nat.mul_assoc] using hscale
  have hprimeFactor : ∀ p ∈ L.primeFactors, Nat.Prime p := by
    intro p hp
    rw [hLprimeFactors] at hp
    exact (hS p (Finset.mem_filter.mp hp).1).1
  have hfixed :=
    fixedPrimeFactorProductsOf_card_lower_bound_of_seed_factor_count L.primeFactors T (z * m)
      hprimeFactor hFactorCount hs hscaleS
  have hzm : 20 ≤ z * m := Nat.mul_le_mul hzge2 hm
  have h80 : 80 ≤ 4 * z * m := by
    calc
      80 = 4 * 20 := by norm_num only
      _ ≤ 4 * (z * m) := Nat.mul_le_mul_left 4 hzm
      _ = 4 * z * m := by rw [Nat.mul_assoc]
  have hT79 : 79 ≤ T := by omega
  have hden0 : 0 < 20 * (m : ℝ) * Real.log 2 :=
    mul_pos (mul_pos (by norm_num only : (0 : ℝ) < 20) (by exact_mod_cast Nat.zero_lt_of_lt hm))
      hlog2
  have hApos : 0 ≤ c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) :=
    div_nonneg (mul_nonneg (le_of_lt hc₀) (sq_nonneg (z : ℝ))) (le_of_lt hden0)
  have hfloorle : (T : ℝ) ≤ c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) := by
    rw [hTdef']
    exact_mod_cast Nat.floor_le hApos
  have hT79R : (79 : ℝ) ≤ (T : ℝ) := by exact_mod_cast hT79
  have hAhigh : 2 ≤ c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) :=
    le_trans (by norm_num only : (2 : ℝ) ≤ 79) (le_trans hT79R hfloorle)
  have hfloorlt : c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) < (T : ℝ) + 1 := by
    simpa only [hTdef', Nat.cast_add, Nat.cast_one] using
      Nat.lt_floor_add_one (c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2))
  have hAless : c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) - 1 < (T : ℝ) := by
    linarith only [hfloorlt]
  have hAhalf :
    (c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2)) / 2 ≤
      c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) - 1 := by
    linarith only [hAhigh]
  have hhalf : c₀ * (z : ℝ) ^ 2 / (40 * (m : ℝ) * Real.log 2) ≤ (T : ℝ) := by
    have hhalfLT : c₀ * (z : ℝ) ^ 2 / (40 * (m : ℝ) * Real.log 2) < (T : ℝ) := by
      calc
        c₀ * (z : ℝ) ^ 2 / (40 * (m : ℝ) * Real.log 2) =
            (c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2)) / 2 :=
          by ring
        _ ≤ c₀ * (z : ℝ) ^ 2 / (20 * (m : ℝ) * Real.log 2) - 1 := hAhalf
        _ < (T : ℝ) := hAless
    exact le_of_lt hhalfLT
  have hden : 0 < 4 * ((z * m : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 4 * (z * m))
  have hratio := div_le_div_of_nonneg_right hhalf (le_of_lt hden)
  exact
    ⟨m, z, T, hm, hmx₀, hz, hTdef', hT60, hT1024, hscale, hTpow, k, S, L, hk, hkpow, hSsize, hScard,
      hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda, hLcard, hLcoprimeFour, hFactorPower,
      hFactorBound, hLlower, hLambdaLower, hProp15Input, hLbound, hLambdaBound, hFactorCount,
      hfixed, hratio⟩

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a positive coefficient and the uniform modulus-1 instance of reliable,
Proposition 1.5.

Claim: one can choose the prime-product cutoff and obtain the initial seed set
and auxiliary modulus data from reliable §2, with the chosen `x` beyond `x₀`.

Content: `exists_primeProductLE_initial_count` chooses `z` so that the full
divisor count exceeds the seed threshold; setting `x = (∏_{p ≤ z} p)^5`
automatically places the modulus below the divisor cutoff.

Proof: combine that count bound and cutoff estimate with the existing finite
seed-selection construction.

Role: this closes the parameter-selection step for the initial arithmetic
stage, conditional on the uniform analytic count.
-/
theorem exists_seed_auxiliary_modulus_of_uniform_count (c₀ : ℝ) (hc₀ : 0 < c₀) (x₀ : ℕ)
    (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) :
    ∃ (z : ℕ),
      2 ≤ z ∧
        x₀ ≤ ((primeSetLE z).prod id : ℕ) ^ 5 ∧
        ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
          0 < k ∧
            k ^ 5 ≤ (((primeSetLE z).prod id : ℕ) ^ 5) ^ 3 ∧
            primeTailCountThreshold < S.card ∧
            (∀ p ∈ S,
              Nat.Prime p ∧
                p ≤ ((primeSetLE z).prod id : ℕ) ^ 5 ∧
                ∃ d,
                  d ∣ (primeSetLE z).prod id ∧
                    d ≤ reliableProp15DivisorCutoff ((primeSetLE z).prod id ^ 5) ∧ p = d * k + 1) ∧
            L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
            Squarefree L ∧
            L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
            (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
            ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
            S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card := by
  obtain ⟨z, hz, hx₀, hlower⟩ := exists_primeProductLE_initial_count hc₀ primeTailCountThreshold x₀
  have hcut := primeProductLE_le_divisorCutoff_fifth_power z
  refine ⟨z, hz, hx₀, ?_⟩
  exact
    exists_seed_auxiliary_modulus_of_primeProductLE c₀ x₀ ((primeSetLE z).prod id ^ 5) z hcount hx₀
      hcut hlower

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a positive coefficient, a uniform modulus-1 count, and a seed-size
threshold `T` at least as large as `primeTailCountThreshold`.

Claim: one can choose `z` and `x = (∏_{p ≤ z} p)^5` so that the seed set has
exactly `T + 1` elements and the auxiliary modulus satisfies
`L.primeFactors.card ^ 4 ≤ x`. Every prime factor of `L` is also at most `x`,
and the tail modulus satisfies `2 < L` and `3 ≤ ArithmeticFunction.carmichael L`.

Content: the choice of `x` also dominates `(T + 1)^4`; the exact seed size then
gives the fourth-power bound required by reliable Proposition 1.5.

Proof: enlarge the lower cutoff passed to the initial-count selection, then use
the exact-size seed bridge and monotonicity of natural fourth powers.

Role: this is the parameterized initial arithmetic construction needed before
the P2 threshold can be compared with the later progression count.
-/
theorem exists_seed_auxiliary_modulus_of_uniform_count_with_threshold (c₀ : ℝ) (hc₀ : 0 < c₀)
    (x₀ T : ℕ) (hT : primeTailCountThreshold ≤ T) (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) :
    ∃ (z : ℕ),
      2 ≤ z ∧
        x₀ ≤ ((primeSetLE z).prod id : ℕ) ^ 5 ∧
        ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
          0 < k ∧
            k ^ 5 ≤ (((primeSetLE z).prod id : ℕ) ^ 5) ^ 3 ∧
            primeTailCountThreshold < S.card ∧
            S.card = T + 1 ∧
            (∀ p ∈ S,
              Nat.Prime p ∧
                p ≤ ((primeSetLE z).prod id : ℕ) ^ 5 ∧
                ∃ d,
                  d ∣ (primeSetLE z).prod id ∧
                    d ≤ reliableProp15DivisorCutoff ((primeSetLE z).prod id ^ 5) ∧ p = d * k + 1) ∧
            L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
            Squarefree L ∧
            Nat.Coprime L 4 ∧
            L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
            L.primeFactors.card ^ 4 ≤ ((primeSetLE z).prod id : ℕ) ^ 5 ∧
            (∀ r, r ∣ L → Nat.Prime r → r ≤ ((primeSetLE z).prod id : ℕ) ^ 5) ∧
            (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
            ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
            S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card ∧
            2 < L ∧
            3 ≤ ArithmeticFunction.carmichael L ∧
            ReliableProp15ModFourInput L (((primeSetLE z).prod id : ℕ) ^ 5) ∧
            L ≤ (((primeSetLE z).prod id : ℕ) ^ 5) ^ (T + 1) ∧
            ArithmeticFunction.carmichael L ≤ (((primeSetLE z).prod id : ℕ) ^ 5) ^ 2 := by
  let xBase : ℕ := max x₀ ((T + 1) ^ 4)
  obtain ⟨z, hz, hxBase, hlower⟩ := exists_primeProductLE_initial_count hc₀ T xBase
  have hx₀ : x₀ ≤ ((primeSetLE z).prod id : ℕ) ^ 5 := le_trans (le_max_left x₀ ((T + 1) ^ 4)) hxBase
  have hTpower : (T + 1) ^ 4 ≤ ((primeSetLE z).prod id : ℕ) ^ 5 :=
    le_trans (le_max_right x₀ ((T + 1) ^ 4)) hxBase
  have hcut := primeProductLE_le_divisorCutoff_fifth_power z
  obtain
    ⟨k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda,
      hLcard⟩ :=
    exists_seed_auxiliary_modulus_of_primeProductLE_with_threshold c₀ x₀
      ((primeSetLE z).prod id ^ 5) z T hcount hx₀ hcut hT hlower
  have hprimeCount := primeCounting_bound_of_primeTailCountThreshold (Nat.le_of_lt hSsize)
  have hxTwo : 2 ≤ ((primeSetLE z).prod id : ℕ) ^ 5 := le_trans hcount.1 hx₀
  obtain
    ⟨hLcoprimeFour, hFactorPower, hFactorBound, hLlower, hLambdaLower, hProp15Input, hLbound,
      hLambdaBound⟩ :=
    seed_auxiliary_modulus_arithmetic_bounds hxTwo (primeProductLE_pos z) hcut hk hkpow hScard
      hTpower hS hL hLsq hLprimeFactors hLreciprocal hLlambda hprimeCount
  exact
    ⟨z, hz, hx₀, k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLcoprimeFour, hLprimeFactors,
      hFactorPower, hFactorBound, hLreciprocal, hLlambda, hLcard, hLlower, hLambdaLower,
      hProp15Input, hLbound, hLambdaBound⟩

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a positive coefficient, a modulus-one uniform count, and an exact seed
size above the reciprocal-tail threshold.

Claim: one can choose a primorial `N`, use the square-root divisor range at
`x = N ^ 2`, and construct the corresponding seed set and tail product.

Content: invoke the existing full-divisor parameter selection at the larger
bound `N ^ 5` with twice the target count. Since `log (N ^ 2) ≤ log (N ^ 5)`,
half of the squarefree divisor count still exceeds the target. The cutoff for
`N ^ 2` contains every divisor up to `Nat.sqrt N`.

Role: this replaces the initial `N ^ 5` all-divisor construction with the
square-root range used in reliable, §2.
-/
theorem exists_seed_auxiliary_modulus_of_uniform_count_sqrt_cutoff (c₀ : ℝ) (hc₀ : 0 < c₀)
    (x₀ T : ℕ) (hT : primeTailCountThreshold ≤ T) (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) :
    ∃ z : ℕ,
      2 ≤ z ∧
        x₀ ≤ ((primeSetLE z).prod id : ℕ) ^ 2 ∧
        (T + 1) ^ 4 ≤ ((primeSetLE z).prod id : ℕ) ^ 2 ∧
        ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
          0 < k ∧
            k ^ 5 ≤ (((primeSetLE z).prod id : ℕ) ^ 2) ^ 3 ∧
            primeTailCountThreshold < S.card ∧
            S.card = T + 1 ∧
            (∀ p ∈ S,
              Nat.Prime p ∧
                p ≤ ((primeSetLE z).prod id : ℕ) ^ 2 ∧
                ∃ d,
                  d ∣ (primeSetLE z).prod id ∧
                    d ≤ reliableProp15DivisorCutoff (((primeSetLE z).prod id : ℕ) ^ 2) ∧
                    p = d * k + 1) ∧
            L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
            Squarefree L ∧
            L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
            Nat.Coprime L 4 ∧
            L.primeFactors.card ^ 4 ≤ (((primeSetLE z).prod id : ℕ) ^ 2) ∧
            (∀ r, r ∣ L → Nat.Prime r → r ≤ ((primeSetLE z).prod id : ℕ) ^ 2) ∧
            (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
            ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
            S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card ∧
            (T + 1) / 2 ≤ L.primeFactors.card ∧
            2 < L ∧
            3 ≤ ArithmeticFunction.carmichael L ∧
            ReliableProp15ModFourInput L (((primeSetLE z).prod id : ℕ) ^ 2) ∧
            L ≤ (((primeSetLE z).prod id : ℕ) ^ 2) ^ (T + 1) ∧
            ArithmeticFunction.carmichael L ≤ (((primeSetLE z).prod id : ℕ) ^ 2) ^ 2 := by
  let xBase : ℕ := max (x₀ ^ 5) ((T + 1) ^ 10)
  obtain ⟨z, hz, hbase, hlower⟩ := exists_primeProductLE_initial_count hc₀ (2 * T) xBase
  let N : ℕ := (primeSetLE z).prod id
  have hbaseLeft : x₀ ^ 5 ≤ N ^ 5 := le_trans (le_max_left _ _) hbase
  have hx₀N : x₀ ≤ N := (Nat.pow_le_pow_iff_left (by norm_num only : 5 ≠ 0)).mp hbaseLeft
  have hbaseRight : (T + 1) ^ 10 ≤ N ^ 5 := le_trans (le_max_right _ _) hbase
  have hTbasePow : ((T + 1) ^ 2) ^ 5 ≤ N ^ 5 := by
    rw [← pow_mul]
    exact hbaseRight
  have hTbase : (T + 1) ^ 2 ≤ N := (Nat.pow_le_pow_iff_left (by norm_num only : 5 ≠ 0)).mp hTbasePow
  have hTpow : (T + 1) ^ 4 ≤ N ^ 2 := by
    calc
      (T + 1) ^ 4 = ((T + 1) ^ 2) ^ 2 := by ring
      _ ≤ N ^ 2 := Nat.pow_le_pow_left hTbase 2
  have hNpos : 0 < N := primeProductLE_pos z
  have hNge2 : 2 ≤ N := by
    have htwo : 2 ∈ primeSetLE z := by
      unfold primeSetLE
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le hz), Nat.prime_two⟩
    have htwoFactor : 2 ∈ N.primeFactors := by
      dsimp only [N]
      rw [(primeProductLE_data z).2]
      exact htwo
    exact Nat.le_of_dvd hNpos (Nat.dvd_of_mem_primeFactors htwoFactor)
  have hNle : 1 ≤ N := le_trans (by norm_num only : 1 ≤ 2) hNge2
  have hx₀ : x₀ ≤ N ^ 2 := le_trans hx₀N (Nat.le_self_pow (by norm_num only : 2 ≠ 0) N)
  have hcut := natSqrt_le_reliableProp15DivisorCutoff_square N hNle
  have hN2le5 : N ^ 2 ≤ N ^ 5 := Nat.pow_le_pow_right hNle (by norm_num only : 2 ≤ 5)
  have hlogle : Real.log (N ^ 2 : ℝ) ≤ Real.log (N ^ 5 : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.pow_pos hNpos
    · exact_mod_cast hN2le5
  have hN2gt : 1 < N ^ 2 := by
    calc
      1 < N := lt_of_lt_of_le (by norm_num only : 1 < 2) hNge2
      _ ≤ N ^ 2 := Nat.le_self_pow (by norm_num only : 2 ≠ 0) N
  have hN5gt : 1 < N ^ 5 := lt_of_lt_of_le hN2gt hN2le5
  have hlog2pos : 0 < Real.log (N ^ 2 : ℝ) := Real.log_pos (by exact_mod_cast hN2gt)
  have hlog5pos : 0 < Real.log (N ^ 5 : ℝ) := Real.log_pos (by exact_mod_cast hN5gt)
  have hcoef2 : reliableProp15Coefficient c₀ 1 (N ^ 2) = c₀ / Real.log (N ^ 2 : ℝ) := by
    simp only [reliableProp15Coefficient, Nat.totient_one, Nat.cast_one, one_mul, Nat.cast_pow]
  have hcoef5 : reliableProp15Coefficient c₀ 1 (N ^ 5) = c₀ / Real.log (N ^ 5 : ℝ) := by
    simp only [reliableProp15Coefficient, Nat.totient_one, Nat.cast_one, one_mul, Nat.cast_pow]
  have hcoefCmp :
    reliableProp15Coefficient c₀ 1 (N ^ 5) ≤ reliableProp15Coefficient c₀ 1 (N ^ 2) := by
    rw [hcoef5, hcoef2]
    apply (div_le_div_iff₀ hlog5pos hlog2pos).2
    exact mul_le_mul_of_nonneg_left hlogle (le_of_lt hc₀)
  have hfull : (0 : ℝ) ≤ ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le (2 ^ Nat.primeCounting z)
  have hscaled := mul_le_mul_of_nonneg_right hcoefCmp hfull
  have hlowerR :
    (2 : ℝ) * (T : ℝ) <
      reliableProp15Coefficient c₀ 1 (N ^ 5) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, N] using hlower
  have hstrong :
    (2 : ℝ) * (T : ℝ) <
      reliableProp15Coefficient c₀ 1 (N ^ 2) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) :=
    lt_of_lt_of_le hlowerR hscaled
  have hlowerNew :
    (T : ℝ) <
      reliableProp15Coefficient c₀ 1 (N ^ 2) * ((((2 ^ Nat.primeCounting z : ℕ) : ℝ) / 2)) := by
    have hTmul :
      (T : ℝ) * 2 <
        reliableProp15Coefficient c₀ 1 (N ^ 2) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := by
      calc
        (T : ℝ) * 2 = (2 : ℝ) * (T : ℝ) := by ring
        _ < reliableProp15Coefficient c₀ 1 (N ^ 2) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ) := hstrong
    have hhalf :
      (T : ℝ) <
        (reliableProp15Coefficient c₀ 1 (N ^ 2) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ)) / 2 :=
      (lt_div_iff₀ (by norm_num only : (0 : ℝ) < 2)).2 hTmul
    calc
      (T : ℝ) <
          (reliableProp15Coefficient c₀ 1 (N ^ 2) * ((2 ^ Nat.primeCounting z : ℕ) : ℝ)) / 2 :=
        hhalf
      _ = reliableProp15Coefficient c₀ 1 (N ^ 2) * ((((2 ^ Nat.primeCounting z : ℕ) : ℝ) / 2)) := by
        ring
  have hlowerFactors :
    (T : ℝ) <
      reliableProp15Coefficient c₀ 1 (N ^ 2) * ((((2 ^ N.primeFactors.card : ℕ) : ℝ) / 2)) := by
    rw [primeProductLE_primeFactors_card z]
    exact hlowerNew
  have hseed :=
    exists_seed_auxiliary_modulus_of_sqrt_divisor_count c₀ hc₀ x₀ (N ^ 2) N T hT hcount hx₀
      (Nat.ne_of_gt hNpos) (primeProductLE_data z).1 hcut hlowerFactors
  rcases hseed with
    ⟨k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda,
      hLcard⟩
  have hprimeCount := primeCounting_bound_of_primeTailCountThreshold (Nat.le_of_lt hSsize)
  have hxTwo : 2 ≤ N ^ 2 := le_trans hcount.1 hx₀
  have hNleX : N ≤ N ^ 2 := Nat.le_self_pow (by norm_num only : 2 ≠ 0) N
  obtain
    ⟨hLcoprimeFour, hFactorPower, hFactorBound, hLlower, hLambdaLower, hProp15Input, hLbound,
      hLambdaBound⟩ :=
    seed_auxiliary_modulus_arithmetic_bounds_of_N_le_x hxTwo hNpos hNleX hk hkpow hScard hTpow hS hL
      hLsq hLprimeFactors hLreciprocal hLlambda hprimeCount
  have hFactorCount : (T + 1) / 2 ≤ L.primeFactors.card := by
    rw [hLprimeFactors, ← hScard]
    exact Nat.div_le_of_le_mul hLcard
  exact
    ⟨z, hz, hx₀, hTpow, k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLprimeFactors,
      hLcoprimeFour, hFactorPower, hFactorBound, hLreciprocal, hLlambda, hLcard, hFactorCount,
      hLlower, hLambdaLower, hProp15Input, hLbound, hLambdaBound⟩

/--
Inputs: an exact seed-set size and the large-tail cardinality bound for its
auxiliary modulus.

Claim: at least half of the seed size, rounded down, is represented by prime
factors of the auxiliary modulus.

Proof: identify the tail with the prime-factor set, then use natural division
on the inequality that the seed size is at most twice the tail size.

Role: this transfers the parameter `T` into a lower bound for the exponent in
the divisor count of the auxiliary modulus.
-/
theorem auxiliary_modulus_primeFactors_card_lower_bound {T : ℕ} {S : Finset ℕ} {L : ℕ}
    (hScard : S.card = T + 1)
    (hLprimeFactors : L.primeFactors = S.filter (fun p => 60 * S.card < p))
    (hLcard : S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card) :
    (T + 1) / 2 ≤ L.primeFactors.card := by
  rw [hLprimeFactors]
  rw [← hScard]
  exact Nat.div_le_of_le_mul hLcard

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a modulus-one uniform count, a seed threshold, and a fixed-factor
divisor lower bound together with the fourth-power budget.

Claim: the fixed-factor construction supplies the same enriched auxiliary
modulus bounds as the all-divisor construction.

Content: the binomial family gives the initial seed count; the common finite
arithmetic completion then proves squarefree, coprimality, Carmichael, and
size bounds needed by the final Proposition 1.5 application.

Proof: apply the fixed-factor seed bridge, then pass its seed data to the
shared arithmetic-bound theorem.

Role: this is the enriched initial construction following the fixed-factor
divisor count in reliable §2.
-/
theorem exists_seed_auxiliary_modulus_of_fixedFactorCount_with_threshold (c₀ : ℝ) (hc₀ : 0 < c₀)
    (x₀ x z s T : ℕ) (hT : primeTailCountThreshold ≤ T)
    (hcount : ReliableProp15UniformCount c₀ 1 1 x₀) (hx : x₀ ≤ x)
    (hcut : (primeSetLE z).prod id ≤ reliableProp15DivisorCutoff x) (hTpower : (T + 1) ^ 4 ≤ x)
    (hlower :
      (T : ℝ) <
        reliableProp15Coefficient c₀ 1 x *
          ((((Nat.primeCounting z + 1 - s : ℕ) ^ s : ℕ) : ℝ) / (s.factorial : ℝ))) :
    ∃ (k : ℕ) (S : Finset ℕ) (L : ℕ),
      0 < k ∧
        k ^ 5 ≤ x ^ 3 ∧
        primeTailCountThreshold < S.card ∧
        S.card = T + 1 ∧
        (∀ p ∈ S,
          Nat.Prime p ∧
            p ≤ x ∧
            ∃ d, d ∣ (primeSetLE z).prod id ∧ d ≤ reliableProp15DivisorCutoff x ∧ p = d * k + 1) ∧
        L = (S.filter (fun p => 60 * S.card < p)).prod id ∧
        Squarefree L ∧
        Nat.Coprime L 4 ∧
        L.primeFactors = S.filter (fun p => 60 * S.card < p) ∧
        L.primeFactors.card ^ 4 ≤ x ∧
        (∀ r, r ∣ L → Nat.Prime r → r ≤ x) ∧
        (∑ p ∈ L.primeFactors, (p : ℝ)⁻¹) ≤ (1 / 60 : ℝ) ∧
        ArithmeticFunction.carmichael L ∣ k * (primeSetLE z).prod id ∧
        S.card ≤ 2 * (S.filter (fun p => 60 * S.card < p)).card ∧
        (T + 1) / 2 ≤ L.primeFactors.card ∧
        2 < L ∧
        3 ≤ ArithmeticFunction.carmichael L ∧
        ReliableProp15ModFourInput L x ∧
        L ≤ x ^ (T + 1) ∧ ArithmeticFunction.carmichael L ≤ x ^ 2 := by
  obtain
    ⟨k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLprimeFactors, hLreciprocal, hLlambda,
      hLcard⟩ :=
    exists_seed_auxiliary_modulus_of_fixedFactorCount c₀ hc₀ x₀ x z s T hT hcount hx hcut hlower
  have hprimeCount := primeCounting_bound_of_primeTailCountThreshold (Nat.le_of_lt hSsize)
  have hxTwo : 2 ≤ x := le_trans hcount.1 hx
  obtain
    ⟨hLcoprimeFour, hFactorPower, hFactorBound, hLlower, hLambdaLower, hProp15Input, hLbound,
      hLambdaBound⟩ :=
    seed_auxiliary_modulus_arithmetic_bounds hxTwo (primeProductLE_pos z) hcut hk hkpow hScard
      hTpower hS hL hLsq hLprimeFactors hLreciprocal hLlambda hprimeCount
  exact
    ⟨k, S, L, hk, hkpow, hSsize, hScard, hS, hL, hLsq, hLcoprimeFour, hLprimeFactors, hFactorPower,
      hFactorBound, hLreciprocal, hLlambda, hLcard,
      auxiliary_modulus_primeFactors_card_lower_bound hScard hLprimeFactors hLcard, hLlower,
      hLambdaLower, hProp15Input, hLbound, hLambdaBound⟩

end PseudoPrime.AnalyticNumberTheory.AGP
