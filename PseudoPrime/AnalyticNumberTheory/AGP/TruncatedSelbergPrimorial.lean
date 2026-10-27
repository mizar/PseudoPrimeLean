/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.AGP.BrunTitchmarshSieveReduction
public import PseudoPrime.AnalyticNumberTheory.AGP.PrimeProductBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.SquarefreeReciprocalSums
public import Mathlib.Analysis.PSeries
public import Mathlib.Algebra.Order.Antidiag.Nat
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.NumberTheory.SumPrimeReciprocals

/-! # Truncated Selberg sieve with the primorial cutoff product -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.AGP

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a natural cutoff `z`.

Claim: for the primorial consisting of all primes at most `z`, the truncated
reciprocal-totient sum dominates the reciprocal sum over positive squarefree
integers at most `z`.

Proof: apply the general divisor-sum comparison and the primorial divisibility
theorem for squarefree integers.

Role: supplies the concrete normalizer lower bound for the Selberg sieve.
-/
theorem selbergTruncatedTotientSum_primorial_ge_squarefree_reciprocal_sum (z : ℕ) :
    (∑ n ∈ (Finset.range (z + 1)).filter (fun n => 0 < n ∧ Squarefree n), 1 / (n : ℝ)) ≤
      selbergTruncatedTotientSum ((primeSetLE z).prod id) z := by
  exact
    selbergTruncatedTotientSum_ge_reciprocal_sum (P := (primeSetLE z).prod id) (z := z)
      (primeProductLE_data z).1 (fun n hn1 hnz hsq => primeProductLE_dvd_of_squarefree_le hsq hnz)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a natural cutoff `z`.

Claim: the sum of reciprocal primes at most `z` tends to infinity with `z`.

Proof: apply mathlib's nonsummability theorem for reciprocal primes to the
partial sums, then identify each partial sum with `primeSetLE`.

Role: supplies a divergent lower bound for the reciprocal sum over squarefree
integers.
-/
theorem primeSetLE_reciprocal_sum_tendsto_atTop :
    Filter.Tendsto (fun z : ℕ => ∑ p ∈ primeSetLE z, 1 / (p : ℝ)) Filter.atTop Filter.atTop := by
  let f : ℕ → ℝ := {p | Nat.Prime p}.indicator (fun n => 1 / (n : ℝ))
  have hf : ∀ n, 0 ≤ f n := by
    intro n
    apply Set.indicator_nonneg
    intro p hp
    exact div_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le p)
  have hns : ¬Summable f := by simpa only [f] using not_summable_one_div_on_primes
  have hpartial :
    Filter.Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N, f i) Filter.atTop Filter.atTop :=
    (not_summable_iff_tendsto_nat_atTop_of_nonneg hf).mp hns
  have hshift :
    Filter.Tendsto (fun z : ℕ => ∑ i ∈ Finset.range (z + 1), f i) Filter.atTop Filter.atTop := by
    apply Filter.tendsto_atTop_mono'
    · filter_upwards with z
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.range_mono (Nat.le_succ z)
      · intro i hi hnot
        exact hf i
    · exact hpartial
  have hsum : ∀ z, (∑ i ∈ Finset.range (z + 1), f i) = ∑ p ∈ primeSetLE z, 1 / (p : ℝ) := by
    intro z
    rw [primeSetLE, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    change
      ({p | Nat.Prime p}.indicator (fun n => 1 / (n : ℝ))) n =
        (if Nat.Prime n then 1 / (n : ℝ) else 0)
    by_cases hp : Nat.Prime n
    · have hmem : n ∈ {p | Nat.Prime p} := hp
      rw [Set.indicator_of_mem hmem]
      simp only [hp, ite_true]
    · have hmem : n ∉ {p | Nat.Prime p} := hp
      rw [Set.indicator_of_notMem hmem]
      simp only [hp, ite_false]
  exact hshift.congr' (Filter.Eventually.of_forall hsum)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a natural cutoff `z`.

Claim: the reciprocal sum over positive squarefree integers at most `z` tends
to infinity with `z`.

Proof: every prime at most `z` is positive and squarefree, so its reciprocal
sum is bounded above by the stated squarefree sum.

Role: gives a quantitative direction for the truncated Selberg normalizer.
-/
theorem squarefreeReciprocalSum_tendsto_atTop :
    Filter.Tendsto
      (fun z : ℕ =>
        ∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n), 1 / (n : ℝ))
      Filter.atTop Filter.atTop := by
  have hle :
    ∀ z : ℕ,
      (∑ p ∈ primeSetLE z, 1 / (p : ℝ)) ≤
        ∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n), 1 / (n : ℝ) := by
    intro z
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      have hp' := Finset.mem_filter.mp hp
      have hpos : 0 < p := hp'.2.pos
      have hsq : Squarefree p := (Nat.prime_iff.mp hp'.2).squarefree
      exact Finset.mem_filter.mpr ⟨hp'.1, ⟨hpos, hsq⟩⟩
    · intro n hn hnot
      exact div_nonneg (by norm_num only) (by exact_mod_cast Nat.zero_le n)
  exact
    Filter.tendsto_atTop_mono' Filter.atTop (Filter.Eventually.of_forall hle)
      primeSetLE_reciprocal_sum_tendsto_atTop

/--
Inputs: a cutoff `z ≥ 1`.

Claim: the reciprocal-square sum through `z` is at most `2`.

Proof: use the inverse-square integral estimate for the tail after `1`.

Role: supports the squarefree reciprocal-sum lower bound.
-/
theorem reciprocalSquareSum_Icc_le_two (z : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ Finset.Icc 1 z, ((n : ℝ) ^ 2)⁻¹) ≤ 2 :=
  Arithmetic.reciprocalSquareSum_Icc_le_two z hz

/--
Inputs: a cutoff `z ≥ 1`.

Claim: the reciprocal sum over positive squarefree integers through `z` is at
least half the logarithm of `z + 1`.

Proof: apply the arithmetic squarefree reciprocal-sum lower bound.

Role: supplies the explicit logarithmic lower bound for the Selberg normalizer.
-/
theorem squarefreeReciprocalSum_ge_log_div_two (z : ℕ) (hz : 1 ≤ z) :
    Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤
      ∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n), 1 / (n : ℝ) :=
  Arithmetic.squarefreeReciprocalSum_ge_log_div_two z hz

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z ≥ 1` and the primorial of all primes at most `z`.

Claim: the truncated reciprocal-totient normalizer is at least
`log (z + 1) / 2`.

Proof: combine the squarefree reciprocal-sum lower bound with the primorial
divisibility comparison.

Role: supplies an explicit lower bound for the main term in the finite
Selberg-sieve estimate.
-/
theorem selbergTruncatedTotientSum_primorial_ge_log_div_two (z : ℕ) (hz : 1 ≤ z) :
    Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤ selbergTruncatedTotientSum ((primeSetLE z).prod id) z := by
  exact
    le_trans (squarefreeReciprocalSum_ge_log_div_two z hz)
      (selbergTruncatedTotientSum_primorial_ge_squarefree_reciprocal_sum z)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z` and the primorial of all primes at most `z`.

Claim: its divisors at most `z` are exactly the positive squarefree integers
at most `z`.

Proof: divisors of the squarefree primorial are squarefree; conversely, each
squarefree integer through `z` divides the primorial.

Role: identifies the index set of primorial divisor-mass sums.
-/
theorem primeProductLE_divisors_filter_le_eq_squarefree_range (z : ℕ) :
    ((primeSetLE z).prod id).divisors.filter (fun k => k ≤ z) =
      (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k) := by
  let P : ℕ := (primeSetLE z).prod id
  let D : Finset ℕ := (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k)
  have hPpos : P ≠ 0 := by
    have h := primeProductLE_pos z
    simpa only [P] using Nat.ne_of_gt h
  have hset : P.divisors.filter (fun k => k ≤ z) = D := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors, D]
    constructor
    · rintro ⟨⟨hkP, hP0⟩, hkz⟩
      refine ⟨Nat.lt_succ_of_le hkz, Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hkP), ?_⟩
      exact Squarefree.squarefree_of_dvd hkP (primeProductLE_data z).1
    · rintro ⟨hklt, hkpos, hsq⟩
      have hkz : k ≤ z := Nat.le_of_lt_succ hklt
      refine ⟨⟨?_, hPpos⟩, hkz⟩
      simpa only [P] using primeProductLE_dvd_of_squarefree_le hsq hkz
  simpa only [P, D] using hset

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a primorial cutoff `z` and a real normalizer `G`.

Claim: the divisor-mass error for this primorial equals the sum of each
positive squarefree `k ≤ z` divisor sum, divided by `φ(k) G`.

Proof: rewrite the mass by its inner divisor sum, convert the cutoff to a
filtered sum, and apply the divisor-set identity above.

Role: exposes the finite arithmetic sum that remains to be bounded in the
Brun–Titchmarsh estimate.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_primorial_eq_squarefree_divisor_sum (z : ℕ)
    (G : ℝ) :
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLE z).prod id) z G =
      ∑ k ∈ (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k),
        (∑ d ∈ k.divisors, (d : ℝ)) / ((Nat.totient k : ℝ) * G) := by
  rw [selbergTruncatedOptimalWeightDivisorMass_eq_divisor_sum, ← Finset.sum_filter,
    primeProductLE_divisors_filter_le_eq_squarefree_range]

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z`, a modulus `Q`, and the primorial restricted to primes
coprime to `Q`.

Claim: its truncated reciprocal-totient sum dominates the reciprocal sum over
positive squarefree `n ≤ z` coprime to `Q`.

Proof: every such `n` divides the restricted primorial, so apply the general
Selberg normalizer comparison for coprime squarefree divisors.

Role: provides the normalizer interface for a progression sieve that omits
prime factors of its modulus.
-/
theorem selbergTruncatedTotientSum_coprime_primorial_ge_squarefree_sum (z Q : ℕ) :
    (∑ n ∈ (Finset.range (z + 1)).filter (fun n => 0 < n ∧ Squarefree n ∧ Nat.Coprime n Q),
        1 / (n : ℝ)) ≤
      selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z := by
  apply selbergTruncatedTotientSum_ge_coprime_reciprocal_sum
  · exact (primeProductLECoprime_data z Q).1
  · intro n hn1 hnz hsq hcop
    exact primeProductLECoprime_dvd_of_squarefree_le hsq hnz hcop

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z` and a progression modulus `Q`.

Claim: the divisors at most `z` of the restricted primorial are exactly the
positive squarefree integers at most `z` that are coprime to `Q`.

Proof: divisors of the squarefree product inherit squarefreeness and
coprimality; conversely, the restricted primorial divisibility lemma applies.

Role: identifies the exact summation range for the restricted Selberg
normalizer and its weight error.
-/
theorem primeProductLECoprime_divisors_filter_le_eq_squarefree_range (z Q : ℕ) :
    ((primeSetLECoprime z Q).prod id).divisors.filter (fun k => k ≤ z) =
      (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q) := by
  let P : ℕ := (primeSetLECoprime z Q).prod id
  let D : Finset ℕ :=
    (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q)
  have hPpos : P ≠ 0 := by
    have h := primeProductLECoprime_data z Q
    simpa only [P] using h.1.ne_zero
  have hset : P.divisors.filter (fun k => k ≤ z) = D := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_range, Nat.mem_divisors, D]
    constructor
    · rintro ⟨⟨hkP, hP0⟩, hkz⟩
      refine ⟨Nat.lt_succ_of_le hkz, Nat.pos_of_ne_zero (ne_zero_of_dvd_ne_zero hP0 hkP), ?_, ?_⟩
      · exact Squarefree.squarefree_of_dvd hkP (primeProductLECoprime_data z Q).1
      · exact Nat.Coprime.of_dvd_left hkP (primeProductLECoprime_coprime z Q)
    · rintro ⟨hklt, hkpos, hsq, hcop⟩
      have hkz : k ≤ z := Nat.le_of_lt_succ hklt
      refine ⟨⟨?_, hPpos⟩, hkz⟩
      · simpa only [P] using primeProductLECoprime_dvd_of_squarefree_le hsq hkz hcop
  simpa only [P, D] using hset

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z`, a modulus `Q`, and a real normalizer `G`.

Claim: the divisor-mass error for the restricted primorial is a sum over
positive squarefree `k ≤ z` coprime to `Q`, with inner divisor sum
`∑_{d ∣ k} d` divided by `φ(k) G`.

Proof: rewrite the generic divisor mass and use the restricted divisor-set
identity.

Role: expresses the weight error as an explicit arithmetic sum with the
modulus-dependent exclusions visible.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_eq_sum (z Q : ℕ) (G : ℝ) :
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G =
      ∑ k ∈ (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q),
        (∑ d ∈ k.divisors, (d : ℝ)) / ((Nat.totient k : ℝ) * G) := by
  classical
    rw [selbergTruncatedOptimalWeightDivisorMass_eq_divisor_sum, ← Finset.sum_filter,
    primeProductLECoprime_divisors_filter_le_eq_squarefree_range]

/--
Inputs: a positive integer `k`.

Claim: the divisor ratio sum `∑_{d ∣ k} d / φ(k)` is at most the number of
divisors of `k` times `2 ^ ω(k)`.

Proof: `φ(d)` divides `φ(k)` for every divisor `d`; apply the totient ratio
bound to `d` and use monotonicity of the number of distinct prime factors.

Role: supplies a uniform estimate for each inner term in the Selberg weight
mass.
-/
theorem selberg_inner_divisor_ratio_sum_le (k : ℕ) (hk : 0 < k) :
    (∑ d ∈ k.divisors, (d : ℝ) / (Nat.totient k : ℝ)) ≤
      (k.divisors.card : ℝ) * (2 : ℝ) ^ k.primeFactors.card := by
  have hphiK : 0 < (Nat.totient k : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hk
  have hterm (d : ℕ) (hd : d ∈ k.divisors) :
    (d : ℝ) / (Nat.totient k : ℝ) ≤ (2 : ℝ) ^ k.primeFactors.card := by
    have hdiv : d ∣ k := (Nat.mem_divisors.mp hd).1
    have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdiv hk
    have hphiD : 0 < (Nat.totient d : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hdpos
    have hphiDle : Nat.totient d ≤ Nat.totient k :=
      Nat.le_of_dvd (Nat.totient_pos.mpr hk) (Nat.totient_dvd_of_dvd hdiv)
    have hphiDleR : (Nat.totient d : ℝ) ≤ (Nat.totient k : ℝ) := by exact_mod_cast hphiDle
    have hratio : (d : ℝ) / (Nat.totient k : ℝ) ≤ (d : ℝ) / (Nat.totient d : ℝ) := by
      rw [div_le_div_iff₀ hphiK hphiD]
      exact mul_le_mul_of_nonneg_left hphiDleR (by exact_mod_cast (Nat.zero_le d))
    have hpowD : (2 : ℝ) ^ d.primeFactors.card ≤ (2 : ℝ) ^ k.primeFactors.card :=
      pow_le_pow_right₀ (by norm_num only) (Finset.card_le_card (Nat.primeFactors_mono hdiv hk.ne'))
    exact
      le_trans hratio
        (le_trans
          (PseudoPrime.NumberTheory.TotientProductBounds.div_totient_le_two_pow_cardFactors hdpos)
          hpowD)
  calc
    (∑ d ∈ k.divisors, (d : ℝ) / (Nat.totient k : ℝ)) ≤
        ∑ d ∈ k.divisors, (2 : ℝ) ^ k.primeFactors.card :=
      by
      apply Finset.sum_le_sum
      intro d hd
      exact hterm d hd
    _ = (k.divisors.card : ℝ) * (2 : ℝ) ^ k.primeFactors.card := by
      rw [Finset.sum_const, nsmul_eq_mul]

/--
Inputs: a positive squarefree integer `k`.

Claim: the Selberg inner divisor ratio sum is at most `4 ^ ω(k)`.

Proof: a squarefree integer has `2 ^ ω(k)` divisors; combine this count with
the preceding bound for each divisor ratio.

Role: reduces the outer optimal-weight mass estimate to a sum of the
four-divisor function over squarefree integers.
-/
theorem selberg_inner_divisor_ratio_sum_le_four_pow {k : ℕ} (hk : 0 < k) (hsq : Squarefree k) :
    (∑ d ∈ k.divisors, (d : ℝ) / (Nat.totient k : ℝ)) ≤ (4 : ℝ) ^ k.primeFactors.card := by
  have hω : k.primeFactors.card = ArithmeticFunction.cardDistinctFactors k := by
    change k.primeFactorsList.toFinset.card = _
    rw [List.card_toFinset, ArithmeticFunction.cardDistinctFactors_apply]
  have hfilter : k.divisors.filter (fun d => Squarefree d) = k.divisors := by
    ext d
    simp only [Finset.mem_filter]
    constructor
    · exact fun h => h.1
    · intro hd
      refine ⟨hd, ?_⟩
      exact Squarefree.squarefree_of_dvd (Nat.mem_divisors.mp hd).1 hsq
  have hcount := squarefree_divisor_count_eq_two_pow_cardDistinctFactors k hk
  have hdivcard : k.divisors.card = 2 ^ k.primeFactors.card := by
    calc
      k.divisors.card = (k.divisors.filter (fun d => Squarefree d)).card :=
        congrArg Finset.card hfilter.symm
      _ = 2 ^ ArithmeticFunction.cardDistinctFactors k := hcount
      _ = 2 ^ k.primeFactors.card := congrArg (fun n : ℕ => 2 ^ n) hω.symm
  have hbase := selberg_inner_divisor_ratio_sum_le k hk
  rw [hdivcard] at hbase
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hbase
  calc
    (∑ d ∈ k.divisors, (d : ℝ) / (Nat.totient k : ℝ)) ≤
        (2 : ℝ) ^ k.primeFactors.card * (2 : ℝ) ^ k.primeFactors.card :=
      hbase
    _ = (4 : ℝ) ^ k.primeFactors.card := by
      rw [← mul_pow]
      norm_num only

/--
Inputs: a squarefree integer `k`.

Claim: `4 ^ ω(k)` equals the number of ordered four-factor decompositions of
`k` into positive natural numbers.

Proof: apply the squarefree multiplicative-antidiagonal cardinality formula
and identify `ω(k)` with the cardinality of the distinct prime factors.

Role: turns the remaining outer sum into a finite count of factor tuples.
-/
theorem four_pow_primeFactorsCard_eq_finMulAntidiag_card {k : ℕ} (hsq : Squarefree k) :
    (4 : ℝ) ^ k.primeFactors.card = ((4 : ℕ).finMulAntidiag k).card := by
  have hω : k.primeFactors.card = ArithmeticFunction.cardDistinctFactors k := by
    change k.primeFactorsList.toFinset.card = _
    rw [List.card_toFinset, ArithmeticFunction.cardDistinctFactors_apply]
  rw [hω]
  exact_mod_cast (Nat.card_finMulAntidiag_of_squarefree hsq).symm

/--
Inputs: a cutoff `z` and a modulus `Q`.

Claim: the outer sum of `4 ^ ω(k)` over positive squarefree indices coprime
to `Q` equals the total cardinality of their four-factor antidiagonals.

Proof: apply the squarefree antidiagonal cardinality identity to each index.

Role: rewrites the outer weight sum as one finite set of indexed factor
tuples, ready for an injection into the unrestricted product region.
-/
theorem four_pow_primeFactorsCard_sum_eq_finMulAntidiag_card_sum (z Q : ℕ) :
    (∑ k ∈ (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q),
        (4 : ℝ) ^ k.primeFactors.card) =
      ∑ k ∈ (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q),
        (((4 : ℕ).finMulAntidiag k).card : ℝ) := by
  apply Finset.sum_congr rfl
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨_, ⟨_, hsq, _⟩⟩
  exact four_pow_primeFactorsCard_eq_finMulAntidiag_card hsq

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z`, a modulus `Q`, and a positive normalizer `G`.

Claim: the optimal-weight divisor mass for the restricted primorial is at
most the sum of `4 ^ ω(k) / G` over its positive squarefree indices.

Proof: rewrite the mass as its squarefree divisor sum, apply the preceding
inner-sum estimate termwise, and divide by the positive normalizer.

Role: isolates the remaining outer squarefree sum needed for the mass bound.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_four_pow_sum (z Q : ℕ) (G : ℝ)
    (hG : 0 < G) :
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G ≤
      ∑ k ∈ (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q),
        (4 : ℝ) ^ k.primeFactors.card / G := by
  rw [selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_eq_sum]
  apply Finset.sum_le_sum
  intro k hk
  rcases Finset.mem_filter.mp hk with ⟨_, ⟨hkpos, hsq, _⟩⟩
  have hratio : (∑ d ∈ k.divisors, (d : ℝ) / (Nat.totient k : ℝ)) ≤ (4 : ℝ) ^ k.primeFactors.card :=
    selberg_inner_divisor_ratio_sum_le_four_pow hkpos hsq
  have hterm :
    (∑ d ∈ k.divisors, (d : ℝ)) / ((Nat.totient k : ℝ) * G) =
      (∑ d ∈ k.divisors, (d : ℝ) / (Nat.totient k : ℝ)) / G := by
    rw [← Finset.sum_div]
    rw [← div_div]
  rw [hterm]
  exact (div_le_div_iff_of_pos_right hG).mpr hratio

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z`, a modulus `Q`, and a positive normalizer `G`.

Claim: the restricted optimal-weight divisor mass is at most the cardinality
of a finite set of indexed four-factor decompositions, divided by `G`.

Proof: rewrite each squarefree weight as an antidiagonal cardinality and use
the finite sigma-cardinality formula.

Role: packages the outer sum as a single finite set for the forthcoming
factor-tuple count.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_sigma_card (z Q : ℕ) (G : ℝ)
    (hG : 0 < G) :
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G ≤
      ((((Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q)).sigma
              (fun k => (4 : ℕ).finMulAntidiag k)).card :
          ℝ) /
        G := by
  let D := (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q)
  have houter :
    (∑ k ∈ D, (4 : ℝ) ^ k.primeFactors.card) =
      ((D.sigma (fun k => (4 : ℕ).finMulAntidiag k)).card : ℝ) := by
    rw [four_pow_primeFactorsCard_sum_eq_finMulAntidiag_card_sum]
    exact_mod_cast (Finset.card_sigma D (fun k => (4 : ℕ).finMulAntidiag k)).symm
  calc
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G ≤
        ∑ k ∈ D, (4 : ℝ) ^ k.primeFactors.card / G :=
      by exact selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_four_pow_sum z Q G hG
    _ = (∑ k ∈ D, (4 : ℝ) ^ k.primeFactors.card) / G := by rw [← Finset.sum_div]
    _ = ((D.sigma (fun k => (4 : ℕ).finMulAntidiag k)).card : ℝ) / G :=
      congrArg (fun x : ℝ => x / G) houter

/--
Inputs: cutoffs `z` and modulus `Q`.

Claim: the set of squarefree indices `k ≤ z` coprime to `Q`, paired with
their ordered four-factor decompositions, injects into the set of ordered
positive four-tuples with product at most `z`.

Proof: each factor in a decomposition divides `k`, so it is positive and at
most `z`; the product of the tuple recovers `k`, proving injectivity.

Role: removes the squarefree and coprimality restrictions before estimating
the finite four-tuple count.
-/
theorem four_factor_sigma_card_le_product_region_card (z Q : ℕ) :
    (((Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q)).sigma
          (fun k => (4 : ℕ).finMulAntidiag k)).card ≤
      (((((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z)).product
              (Finset.Icc 1 z)).filter
          (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)).card := by
  classical
  let D := (Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q)
  let P := Finset.Icc 1 z
  let T := (P.product P).product P
  let R : Finset (((ℕ × ℕ) × ℕ) × ℕ) :=
    (T.product P).filter (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)
  let S := D.sigma (fun k => (4 : ℕ).finMulAntidiag k)
  let e : (Sigma fun _ : ℕ => Fin 4 → ℕ) → (((ℕ × ℕ) × ℕ) × ℕ) := fun x =>
    Prod.mk (Prod.mk (Prod.mk (x.2 0) (x.2 1)) (x.2 2)) (x.2 3)
  change S.card ≤ R.card
  apply Finset.card_le_card_of_injOn (s := S) (t := R) e
  · intro x hx
    rw [Finset.mem_coe, Finset.mem_sigma] at hx
    rcases hx with ⟨hk, hf⟩
    rw [Finset.mem_coe, Finset.mem_filter]
    constructor
    · have hkpos := (Finset.mem_filter.mp hk).2.1
      have hkz := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
      have hprod := (Nat.mem_finMulAntidiag.mp hf).1
      have hdiv (i : Fin 4) : x.2 i ∣ x.1 := by
        rw [← hprod]
        exact Finset.dvd_prod_of_mem x.2 (Finset.mem_univ i)
      have hbound (i : Fin 4) : 1 ≤ x.2 i ∧ x.2 i ≤ z := by
        have hdpos := Nat.pos_of_dvd_of_pos (hdiv i) hkpos
        have hdle := Nat.le_of_dvd hkpos (hdiv i)
        exact ⟨Nat.succ_le_of_lt hdpos, le_trans hdle hkz⟩
      exact
        Finset.mem_product.mpr
          ⟨Finset.mem_product.mpr
              ⟨Finset.mem_product.mpr
                  ⟨Finset.mem_Icc.mpr (hbound 0), Finset.mem_Icc.mpr (hbound 1)⟩,
                Finset.mem_Icc.mpr (hbound 2)⟩,
            Finset.mem_Icc.mpr (hbound 3)⟩
    · have hprod := (Nat.mem_finMulAntidiag.mp hf).1
      rw [Fin.prod_univ_four] at hprod
      change x.2 3 * (x.2 0 * x.2 1 * x.2 2) ≤ z
      have hprod' : x.2 3 * (x.2 0 * x.2 1 * x.2 2) = x.2 0 * x.2 1 * x.2 2 * x.2 3 := by ac_rfl
      rw [hprod']
      rw [hprod]
      exact Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hk).1)
  · intro x hx y hy hxy
    have hxf := (Nat.mem_finMulAntidiag.mp (Finset.mem_sigma.mp hx).2).1
    have hyf := (Nat.mem_finMulAntidiag.mp (Finset.mem_sigma.mp hy).2).1
    have hfunc : x.2 = y.2 := by
      funext i
      fin_cases i
      · exact congrArg (fun q : (((ℕ × ℕ) × ℕ) × ℕ) => q.1.1.1) hxy
      · exact congrArg (fun q : (((ℕ × ℕ) × ℕ) × ℕ) => q.1.1.2) hxy
      · exact congrArg (fun q : (((ℕ × ℕ) × ℕ) × ℕ) => q.1.2) hxy
      · exact congrArg Prod.snd hxy
    have hkey : x.1 = y.1 := by
      rw [← hxf, ← hyf]
      exact congrArg (fun f : Fin 4 → ℕ => ∏ i, f i) hfunc
    apply Sigma.ext hkey
    exact hfunc ▸ HEq.rfl

/--
Inputs: a cutoff `z`.

Claim: the four-factor product region has cardinality at most the sum, over
its first three factors `a,b,c`, of `⌊z/(abc)⌋`.

Proof: partition the region by its first three coordinates. In each fiber,
the last coordinate lies in `[1, z/(abc)]`.

Role: reduces the tuple count to a triple sum of reciprocal-product bounds.
-/
theorem four_factor_product_region_card_le_divisor_sum (z : ℕ) :
    (((((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z)).product
              (Finset.Icc 1 z)).filter
          (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)).card ≤
      ∑ t ∈ ((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z),
        z / (t.1.1 * t.1.2 * t.2) := by
  classical
  let P := Finset.Icc 1 z
  let T := (P.product P).product P
  let U := (T.product P).filter (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)
  change U.card ≤ ∑ t ∈ T, z / (t.1.1 * t.1.2 * t.2)
  have hUmem : U.filter (fun q => q.1 ∈ T) = U := by
    apply Finset.filter_eq_self.mpr
    intro q hq
    exact (Finset.mem_product.mp (Finset.mem_filter.mp hq).1).1
  have hcount : (∑ t ∈ T, (U.filter (fun q => q.1 = t)).card) = U.card := by
    calc
      (∑ t ∈ T, (U.filter (fun q => q.1 = t)).card) = (U.filter (fun q => q.1 ∈ T)).card :=
        Finset.sum_card_fiberwise_eq_card_filter U T Prod.fst
      _ = U.card := congrArg Finset.card hUmem
  have hfiber (t : (ℕ × ℕ) × ℕ) (ht : t ∈ T) :
    (U.filter (fun q => q.1 = t)).card ≤ z / (t.1.1 * t.1.2 * t.2) := by
    let S := U.filter (fun q => q.1 = t)
    let R := Finset.Icc 1 (z / (t.1.1 * t.1.2 * t.2))
    rcases Finset.mem_product.mp ht with ⟨hab, hc⟩
    rcases Finset.mem_product.mp hab with ⟨ha, hb⟩
    have hta := Finset.mem_Icc.mp ha
    have htb := Finset.mem_Icc.mp hb
    have htc := Finset.mem_Icc.mp hc
    have hden : 0 < t.1.1 * t.1.2 * t.2 :=
      Nat.mul_pos
        (Nat.mul_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one hta.1)
          (Nat.lt_of_lt_of_le Nat.zero_lt_one htb.1))
        (Nat.lt_of_lt_of_le Nat.zero_lt_one htc.1)
    have hcard : S.card ≤ R.card := by
      apply Finset.card_le_card_of_injOn (s := S) (t := R) Prod.snd
      · intro q hq
        rcases Finset.mem_filter.mp hq with ⟨hqU, hfix⟩
        rcases Finset.mem_filter.mp hqU with ⟨hqProd, hbound⟩
        rcases Finset.mem_product.mp hqProd with ⟨_, hd⟩
        have hdhi : q.2 ≤ z / (t.1.1 * t.1.2 * t.2) := by
          apply (Nat.le_div_iff_mul_le hden).2
          simpa only [hfix] using hbound
        exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, hdhi⟩
      · intro q hq r hr hqr
        apply Prod.ext
        · exact (Finset.mem_filter.mp hq).2.trans (Finset.mem_filter.mp hr).2.symm
        · exact hqr
    simpa only [R, Nat.card_Icc, Nat.add_sub_cancel_right] using hcard
  calc
    U.card = ∑ t ∈ T, (U.filter (fun q => q.1 = t)).card := hcount.symm
    _ ≤ ∑ t ∈ T, z / (t.1.1 * t.1.2 * t.2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hfiber t ht

/--
Inputs: a cutoff `z`.

Claim: the four-factor product region has cardinality at most `z` times the
cube of the reciprocal sum over `[1, z]`.

Proof: bound each floor quotient by the corresponding real reciprocal product,
then factor the triple finite sum as a cube.

Role: prepares the product-region count for the harmonic bound and the sieve
error estimate.
-/
theorem four_factor_product_region_card_le_z_mul_reciprocal_sum_cube (z : ℕ) :
    (((((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z)).product
              (Finset.Icc 1 z)).filter
          (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)).card ≤
      (z : ℝ) * (∑ a ∈ Finset.Icc 1 z, (a : ℝ)⁻¹) ^ 3 := by
  classical
  let P := Finset.Icc 1 z
  let T := (P.product P).product P
  let U :=
    (((P.product P).product P).product P).filter (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)
  let f := fun n : ℕ => (n : ℝ)⁻¹
  have hnat := four_factor_product_region_card_le_divisor_sum z
  change U.card ≤ ∑ t ∈ T, z / (t.1.1 * t.1.2 * t.2) at hnat
  have hcast : (U.card : ℝ) ≤ (∑ t ∈ T, (z / (t.1.1 * t.1.2 * t.2) : ℕ) : ℝ) := by
    exact_mod_cast hnat
  have hterm (t : (ℕ × ℕ) × ℕ) (ht : t ∈ T) :
    ((z / (t.1.1 * t.1.2 * t.2) : ℕ) : ℝ) ≤ (z : ℝ) * f t.1.1 * f t.1.2 * f t.2 := by
    have hcastdiv : ((z / (t.1.1 * t.1.2 * t.2) : ℕ) : ℝ) ≤ (z : ℝ) / (t.1.1 * t.1.2 * t.2 : ℕ) :=
      Nat.cast_div_le
    rw [Nat.cast_mul, Nat.cast_mul] at hcastdiv
    calc
      _ ≤ (z : ℝ) / ((t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ)) := hcastdiv
      _ = _ := by
        rw [div_eq_mul_inv]
        have hinv : ((t.1.1 : ℝ) * (t.1.2 : ℝ) * (t.2 : ℝ))⁻¹ = f t.1.1 * f t.1.2 * f t.2 := by
          dsimp only [f]
          rw [mul_inv, mul_inv]
        rw [hinv]
        ring
  have hsum :
    (∑ t ∈ T, (z : ℝ) * f t.1.1 * f t.1.2 * f t.2) = (z : ℝ) * (∑ a ∈ P, (a : ℝ)⁻¹) ^ 3 := by
    change (∑ t ∈ (P ×ˢ P) ×ˢ P, (z : ℝ) * f t.1.1 * f t.1.2 * f t.2) = _
    rw [Finset.sum_product]
    change (∑ ab ∈ P ×ˢ P, ∑ c ∈ P, ((z : ℝ) * f ab.1 * f ab.2) * f c) = _
    have hinner (ab : ℕ × ℕ) :
      (∑ c ∈ P, ((z : ℝ) * f ab.1 * f ab.2) * f c) =
        ((z : ℝ) * f ab.1 * f ab.2) * (∑ c ∈ P, (c : ℝ)⁻¹) := by
      dsimp only [f]
      exact (Finset.mul_sum P (fun c : ℕ => (c : ℝ)⁻¹) ((z : ℝ) * f ab.1 * f ab.2)).symm
    calc
      _ = ∑ ab ∈ P ×ˢ P, (((z : ℝ) * f ab.1 * f ab.2) * (∑ c ∈ P, (c : ℝ)⁻¹)) := by
        apply Finset.sum_congr rfl
        intro ab hab
        exact hinner ab
      _ = (∑ ab ∈ P ×ˢ P, (z : ℝ) * f ab.1 * f ab.2) * (∑ c ∈ P, (c : ℝ)⁻¹) :=
        (Finset.sum_mul ..).symm
      _ = _ := by
        have hpairs :
          (∑ ab ∈ P ×ˢ P, f ab.1 * f ab.2) = (∑ a ∈ P, (a : ℝ)⁻¹) * (∑ b ∈ P, (b : ℝ)⁻¹) := by
          rw [Finset.sum_product]
          change (∑ a ∈ P, ∑ b ∈ P, f a * f b) = _
          rw [← Finset.sum_mul_sum]
        have hcoef :
          (∑ ab ∈ P ×ˢ P, (z : ℝ) * f ab.1 * f ab.2) =
            (z : ℝ) * (∑ ab ∈ P ×ˢ P, f ab.1 * f ab.2) := by
          calc
            _ = ∑ ab ∈ P ×ˢ P, (z : ℝ) * (f ab.1 * f ab.2) := by
              apply Finset.sum_congr rfl
              intro ab hab
              ring
            _ = _ := (Finset.mul_sum ..).symm
        rw [hcoef, hpairs]
        ring
  calc
    _ ≤ (∑ t ∈ T, (z / (t.1.1 * t.1.2 * t.2) : ℕ) : ℝ) := hcast
    _ ≤ ∑ t ∈ T, ((z : ℝ) * f t.1.1 * f t.1.2 * f t.2) := by
      apply Finset.sum_le_sum
      intro t ht
      exact hterm t ht
    _ = (z : ℝ) * (∑ a ∈ P, (a : ℝ)⁻¹) ^ 3 := hsum

/--
Inputs: a cutoff `z`.

Claim: the four-factor product region has cardinality at most
`z * (1 + log z)^3`.

Proof: apply the reciprocal-sum estimate and bound the harmonic sum by
`1 + log z`; monotonicity of the cube follows from nonnegativity.

Role: gives the explicit logarithmic form used in the Selberg mass estimate.
-/
theorem four_factor_product_region_card_le_z_mul_one_add_log_cube (z : ℕ) :
    (((((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z)).product
              (Finset.Icc 1 z)).filter
          (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)).card ≤
      (z : ℝ) * (1 + Real.log z) ^ 3 := by
  classical
  let P := Finset.Icc 1 z
  let S := ∑ n ∈ P, (n : ℝ)⁻¹
  have hsumCast : (harmonic z : ℝ) = S := by
    rw [harmonic_eq_sum_Icc]
    calc
      ((∑ n ∈ Finset.Icc 1 z, (n : ℚ)⁻¹ : ℚ) : ℝ) = ∑ n ∈ Finset.Icc 1 z, (((n : ℚ)⁻¹ : ℚ) : ℝ) :=
        map_sum (algebraMap ℚ ℝ) (fun n : ℕ => (n : ℚ)⁻¹) (Finset.Icc 1 z)
      _ = S := by
        dsimp only [S, P]
        apply Finset.sum_congr rfl
        intro n hn
        rw [Rat.cast_inv]
        exact congrArg (fun x : ℝ => x⁻¹) (by norm_cast)
  have hharm : S ≤ 1 + Real.log z := by
    calc
      S = (harmonic z : ℝ) := hsumCast.symm
      _ ≤ 1 + Real.log z := by exact_mod_cast harmonic_le_one_add_log z
  have hSnonneg : 0 ≤ S := by
    dsimp only [S, P]
    apply Finset.sum_nonneg
    intro n hn
    exact inv_nonneg.mpr (Nat.cast_nonneg n)
  have hRnonneg : 0 ≤ 1 + Real.log z := le_trans hSnonneg hharm
  have hSsq : S ^ 2 ≤ (1 + Real.log z) ^ 2 := by
    calc
      S ^ 2 = S * S := by ring
      _ ≤ (1 + Real.log z) * (1 + Real.log z) := mul_le_mul hharm hharm hSnonneg hRnonneg
      _ = (1 + Real.log z) ^ 2 := by ring
  have hScube : S ^ 3 ≤ (1 + Real.log z) ^ 3 := by
    calc
      S ^ 3 = S ^ 2 * S := by ring
      _ ≤ (1 + Real.log z) ^ 2 * (1 + Real.log z) :=
        mul_le_mul hSsq hharm hSnonneg (sq_nonneg (1 + Real.log z))
      _ = (1 + Real.log z) ^ 3 := by ring
  calc
    _ ≤ (z : ℝ) * S ^ 3 := four_factor_product_region_card_le_z_mul_reciprocal_sum_cube z
    _ ≤ (z : ℝ) * (1 + Real.log z) ^ 3 := mul_le_mul_of_nonneg_left hScube (Nat.cast_nonneg z)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z`, a modulus `Q`, and a positive normalizer `G`.

Claim: the restricted optimal-weight divisor mass is bounded by the number
of positive four-tuples whose product is at most `z`, divided by `G`.

Proof: apply the injection from the squarefree indexed antidiagonals into
the product region, then divide by the positive normalizer.

Role: reduces the remaining Selberg mass estimate to an unrestricted
four-tuple count.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_product_region_card (z Q : ℕ)
    (G : ℝ) (hG : 0 < G) :
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G ≤
      ((((((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z)).product
                  (Finset.Icc 1 z)).filter
              (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)).card :
          ℝ) /
        G := by
  have hcard := four_factor_sigma_card_le_product_region_card z Q
  have hcardR :
    ((((Finset.range (z + 1)).filter (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q)).sigma
            (fun k => (4 : ℕ).finMulAntidiag k)).card :
        ℝ) ≤
      ((((((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z)).product
                (Finset.Icc 1 z)).filter
            (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)).card :
        ℝ) := by
    exact_mod_cast hcard
  calc
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G ≤
        ((((Finset.range (z + 1)).filter
                    (fun k : ℕ => 0 < k ∧ Squarefree k ∧ Nat.Coprime k Q)).sigma
                (fun k => (4 : ℕ).finMulAntidiag k)).card :
            ℝ) /
          G :=
      selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_sigma_card z Q G hG
    _ ≤
        ((((((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z)).product
                    (Finset.Icc 1 z)).filter
                (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)).card :
            ℝ) /
          G :=
      (div_le_div_iff_of_pos_right hG).mpr hcardR

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z`, modulus `Q`, and positive normalizer `G`.

Claim: the coprime-primorial optimal-weight divisor mass is at most
`z * (1 + log z)^3 / G`.

Proof: combine the four-factor product-region injection with its harmonic
cardinality bound, then divide by `G > 0`.

Role: gives an explicit logarithmic upper bound for the finite sieve error.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_log_cube (z Q : ℕ) (G : ℝ)
    (hG : 0 < G) :
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G ≤
      (z : ℝ) * (1 + Real.log z) ^ 3 / G := by
  calc
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G ≤
        ((((((Finset.Icc 1 z).product (Finset.Icc 1 z)).product (Finset.Icc 1 z)).product
                    (Finset.Icc 1 z)).filter
                (fun q => q.2 * (q.1.1.1 * q.1.1.2 * q.1.2) ≤ z)).card :
            ℝ) /
          G :=
      selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_product_region_card z Q G hG
    _ ≤ (z : ℝ) * (1 + Real.log z) ^ 3 / G :=
      (div_le_div_iff_of_pos_right hG).mpr
        (four_factor_product_region_card_le_z_mul_one_add_log_cube z)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z ≥ 1` and a positive modulus `Q`.

Claim: the coprime-primorial optimal-weight divisor mass is at most
`2 Q z (1 + log z)^3 / (φ(Q) log(z + 1))`.

Proof: combine the explicit mass bound with the totient-ratio lower bound for
the normalizer.

Role: gives the squared error term a form with the modulus dependence exposed.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_totient_ratio_bound (z Q : ℕ)
    (hQ : 0 < Q) (hz : 1 ≤ z)
    (hNormLower :
      (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤
        selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z) :
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z
        (selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z) ≤
      2 * (Q : ℝ) * (z : ℝ) * (1 + Real.log z) ^ 3 /
        ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) := by
  let P : ℕ := (primeSetLECoprime z Q).prod id
  let G : ℝ := selbergTruncatedTotientSum P z
  let A : ℝ := (z : ℝ) * (1 + Real.log z) ^ 3
  have hlogpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    have hz' : 1 < z + 1 := by omega
    exact_mod_cast hz'
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hphi : 0 < (Nat.totient Q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  have hNormPos : 0 < (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) :=
    mul_pos (div_pos hphi hQR) (div_pos hlogpos (by norm_num only : (0 : ℝ) < 2))
  have hG : 0 < G := lt_of_lt_of_le hNormPos hNormLower
  have hrecip : 1 / G ≤ 2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) := by
    calc
      1 / G ≤ 1 / ((Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2)) :=
        one_div_le_one_div_of_le hNormPos hNormLower
      _ = 2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) := by
        field_simp [ne_of_gt hQR, ne_of_gt hphi, ne_of_gt hlogpos]
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz)
  have hAnonneg : 0 ≤ A := by
    dsimp only [A]
    exact
      mul_nonneg (Nat.cast_nonneg z)
        (pow_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) hlogz) 3)
  calc
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z G ≤ A / G := by
      simpa only [A, G, P] using
        selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_log_cube z Q G hG
    _ = A * (1 / G) := by ring
    _ ≤ A * (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) :=
      mul_le_mul_of_nonneg_left hrecip hAnonneg
    _ =
        2 * (Q : ℝ) * (z : ℝ) * (1 + Real.log z) ^ 3 /
          ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) :=
      by
      dsimp only [A]
      ring

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a progression modulus `Q` and a sieve cutoff `z ≥ 1`.

Claim: the progression prime count is bounded by the small-prime count, the
total-mass term divided by the restricted Selberg normalizer, and the square
of the restricted optimal-weight divisor mass.

Proof: use the finite Selberg estimate with the primorial that omits primes
sharing a factor with `Q`.

Role: extends the explicit finite sieve bound to arbitrary progression moduli.
-/
theorem progressionPrimeCount_le_coprime_primorial_divisor_mass_bound {Y Q a z : ℕ} (hQ : 0 < Q)
    (hz : 1 ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a ((primeSetLECoprime z Q).prod id)
                (primeProductLECoprime_data z Q).1).totalMass *
            (1 / selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z) +
          (selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z
              (selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z)) ^
            2) := by
  exact
    progressionPrimeCount_le_truncatedOptimal_selberg_divisor_mass_error
      (primeProductLECoprime_data z Q).1 hQ (primeProductLECoprime_coprime z Q) hz
      (selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z) rfl
      (primeProductLECoprime_small z Q)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a progression modulus coprime to the primorial through `z`, and a
cutoff `z ≥ 1`.

Claim: the finite Selberg sieve bounds the progression prime count by the
small-prime count, a total-mass term with factor `2 / log (z + 1)`, and the
explicit error `(z * (z + 1)) ^ 2`.

Proof: apply the truncated-optimal-weight sieve estimate and replace the
reciprocal normalizer by the bound from `selbergTruncatedTotientSum_primorial_ge_log_div_two`.

Role: connects the explicit normalizer lower bound to the finite progression
prime-count estimate.
-/
theorem progressionPrimeCount_le_primorial_log_bound {Y Q a z : ℕ} (hQ : 0 < Q)
    (hPQ : Nat.Coprime ((primeSetLE z).prod id) Q) (hz : 1 ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a ((primeSetLE z).prod id)
                (primeProductLE_data z).1).totalMass *
            (2 / Real.log ((z + 1 : ℕ) : ℝ)) +
          ((z : ℝ) * (z + 1 : ℕ)) ^ 2) := by
  let P : ℕ := (primeSetLE z).prod id
  let G : ℝ := selbergTruncatedTotientSum P z
  have hP : Squarefree P := by simpa only [P] using (primeProductLE_data z).1
  have hPpos : P ≠ 0 := by
    have h := primeProductLE_pos z
    simpa only [P] using Nat.ne_of_gt h
  have hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z := by
    intro p hp hpdiv
    have hpFactors : p ∈ P.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdiv, hPpos⟩
    rw [show P.primeFactors = primeSetLE z by
        simpa only [P] using (primeProductLE_data z).2] at hpFactors
    have hpRange := (Finset.mem_filter.mp hpFactors).1
    exact Nat.le_of_lt_succ (by simpa only [primeSetLE, Finset.mem_range] using hpRange)
  have hlogpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    have hz' : 1 < z + 1 := by omega
    exact_mod_cast hz'
  have hhalfpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) / 2 :=
    div_pos hlogpos (by norm_num only : (0 : ℝ) < 2)
  have hGlower : Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤ G := by
    simpa only [G, P] using selbergTruncatedTotientSum_primorial_ge_log_div_two z hz
  have hrecip : 1 / G ≤ 2 / Real.log ((z + 1 : ℕ) : ℝ) := by
    calc
      1 / G ≤ 1 / (Real.log ((z + 1 : ℕ) : ℝ) / 2) := one_div_le_one_div_of_le hhalfpos hGlower
      _ = 2 / Real.log ((z + 1 : ℕ) : ℝ) := by field_simp [ne_of_gt hlogpos]
  have hbase :=
    progressionPrimeCount_le_truncatedOptimal_selberg_explicit_error (Y := Y) (Q := Q) (a := a)
      (z := z) (P := P) hP hQ hPQ hz G (by rfl) hPsmall
  have hmass : 0 ≤ (progressionBoundingSieve Y Q a P hP).totalMass := by exact Nat.cast_nonneg _
  have hmain :
    (progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + ((z : ℝ) * (z + 1 : ℕ)) ^ 2 ≤
      (progressionBoundingSieve Y Q a P hP).totalMass * (2 / Real.log ((z + 1 : ℕ) : ℝ)) +
        ((z : ℝ) * (z + 1 : ℕ)) ^ 2 := by
    exact add_le_add_left (mul_le_mul_of_nonneg_left hrecip hmass) _
  have hbase' :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) +
          ((z : ℝ) * (z + 1 : ℕ)) ^ 2) := by
    simpa only [P] using hbase
  have hresult := le_trans hbase' (add_le_add_right hmain _)
  simpa only [P] using hresult

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a progression modulus coprime to the primorial through `z`, and a
cutoff `z ≥ 1`.

Claim: the finite Selberg sieve bounds the progression prime count by the
small-prime contribution, the explicit logarithmic main term, and the square
of the divisor-grouped optimal-weight mass.

Proof: use the divisor-mass error theorem and replace the reciprocal
normalizer by its logarithmic lower bound.

Role: exposes a refined error expression for subsequent uniform estimates.
-/
theorem progressionPrimeCount_le_primorial_log_divisor_mass_bound {Y Q a z : ℕ} (hQ : 0 < Q)
    (hPQ : Nat.Coprime ((primeSetLE z).prod id) Q) (hz : 1 ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a ((primeSetLE z).prod id)
                (primeProductLE_data z).1).totalMass *
            (2 / Real.log ((z + 1 : ℕ) : ℝ)) +
          (selbergTruncatedOptimalWeightDivisorMass ((primeSetLE z).prod id) z
              (selbergTruncatedTotientSum ((primeSetLE z).prod id) z)) ^
            2) := by
  let P : ℕ := (primeSetLE z).prod id
  let G : ℝ := selbergTruncatedTotientSum P z
  let B : ℝ := selbergTruncatedOptimalWeightDivisorMass P z G
  have hP : Squarefree P := by simpa only [P] using (primeProductLE_data z).1
  have hPpos : P ≠ 0 := by
    have h := primeProductLE_pos z
    simpa only [P] using Nat.ne_of_gt h
  have hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z := by
    intro p hp hpdiv
    have hpFactors : p ∈ P.primeFactors := Nat.mem_primeFactors.mpr ⟨hp, hpdiv, hPpos⟩
    rw [show P.primeFactors = primeSetLE z by
        simpa only [P] using (primeProductLE_data z).2] at hpFactors
    have hpRange := (Finset.mem_filter.mp hpFactors).1
    exact Nat.le_of_lt_succ (by simpa only [primeSetLE, Finset.mem_range] using hpRange)
  have hlogpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    have hz' : 1 < z + 1 := by omega
    exact_mod_cast hz'
  have hhalfpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) / 2 :=
    div_pos hlogpos (by norm_num only : (0 : ℝ) < 2)
  have hGlower : Real.log ((z + 1 : ℕ) : ℝ) / 2 ≤ G := by
    simpa only [G, P] using selbergTruncatedTotientSum_primorial_ge_log_div_two z hz
  have hrecip : 1 / G ≤ 2 / Real.log ((z + 1 : ℕ) : ℝ) := by
    calc
      1 / G ≤ 1 / (Real.log ((z + 1 : ℕ) : ℝ) / 2) := one_div_le_one_div_of_le hhalfpos hGlower
      _ = 2 / Real.log ((z + 1 : ℕ) : ℝ) := by field_simp [ne_of_gt hlogpos]
  have hbase :=
    progressionPrimeCount_le_truncatedOptimal_selberg_divisor_mass_error (Y := Y) (Q := Q) (a := a)
      (z := z) (P := P) hP hQ hPQ hz G (by rfl) hPsmall
  have hmass : 0 ≤ (progressionBoundingSieve Y Q a P hP).totalMass := by exact Nat.cast_nonneg _
  have hmain :
    (progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + B ^ 2 ≤
      (progressionBoundingSieve Y Q a P hP).totalMass * (2 / Real.log ((z + 1 : ℕ) : ℝ)) +
        B ^ 2 := by
    exact add_le_add_left (mul_le_mul_of_nonneg_left hrecip hmass) _
  have hbase' :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + B ^ 2) := by
    simpa only [P, G, B] using hbase
  have hresult := le_trans hbase' (add_le_add_right hmain _)
  simpa only [P, G, B] using hresult

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a natural cutoff `z` and the primorial of all primes at most `z`.

Claim: its truncated reciprocal-totient normalizer tends to infinity with
`z`.

Proof: the normalizer dominates the reciprocal sum over positive squarefree
integers, which in turn dominates the divergent reciprocal-prime sum.

Role: this supplies an unbounded main-term factor for the Selberg sieve
estimate.
-/
theorem selbergTruncatedTotientSum_primorial_tendsto_atTop :
    Filter.Tendsto (fun z : ℕ => selbergTruncatedTotientSum ((primeSetLE z).prod id) z) Filter.atTop
      Filter.atTop := by
  have hle :
    ∀ z : ℕ,
      (∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n), 1 / (n : ℝ)) ≤
        selbergTruncatedTotientSum ((primeSetLE z).prod id) z := by
    intro z
    exact selbergTruncatedTotientSum_primorial_ge_squarefree_reciprocal_sum z
  exact
    Filter.tendsto_atTop_mono' Filter.atTop (Filter.Eventually.of_forall hle)
      squarefreeReciprocalSum_tendsto_atTop

open PseudoPrime.AnalyticNumberTheory.Arithmetic in
open PseudoPrime.NumberTheory.TotientProductBounds in
/--
Inputs: a cutoff `z`, a positive modulus `Q`, and `z ≥ 1`.

Claim: the reciprocal sum over positive squarefree integers through `z` and
coprime to `Q` is at least `φ(Q)/Q` times `log (z + 1) / 2`.

Proof: use the arithmetic lower bound for squarefree integers coprime to `Q`.

Role: supplies the normalizer lower bound for the coprime Selberg sieve.
-/
theorem squarefree_coprime_reciprocal_sum_ge_totient_ratio_log_div_two (z Q : ℕ) (hQ : 0 < Q)
    (hz : 1 ≤ z) :
    (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤
      ∑ n ∈ (Finset.range (z + 1)).filter (fun n : ℕ => 0 < n ∧ Squarefree n ∧ Nat.Coprime n Q),
        1 / (n : ℝ) :=
  Arithmetic.squarefree_coprime_reciprocal_sum_ge_totient_ratio_log_div_two z Q hQ hz

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z`, a positive modulus `Q`, and `z ≥ 1`.

Claim: the truncated Selberg normalizer for primes at most `z` that do not
divide `Q` is at least `φ(Q)/Q * log(z + 1)/2`.

Proof: combine the coprime squarefree reciprocal-sum lower bound with the
normalizer comparison for the restricted primorial.

Role: supplies the explicit main-term denominator for the coprime sieve
estimate.
-/
theorem selbergTruncatedTotientSum_coprime_primorial_ge_totient_ratio_log_div_two (z Q : ℕ)
    (hQ : 0 < Q) (hz : 1 ≤ z) :
    (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤
      selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z := by
  exact
    le_trans (squarefree_coprime_reciprocal_sum_ge_totient_ratio_log_div_two z Q hQ hz)
      (selbergTruncatedTotientSum_coprime_primorial_ge_squarefree_sum z Q)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a cutoff `z ≥ 1` and a positive modulus `Q`.

Claim: the coprime-primorial optimal-weight divisor mass is at most
`2 Q z (1 + log z)^3 / (φ(Q) log(z + 1))`.

Proof: apply the normalizer lower bound to the general mass estimate.

Role: gives the squared sieve error an explicit modulus-dependent bound.
-/
theorem selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_totient_ratio_log_cube
    (z Q : ℕ) (hQ : 0 < Q) (hz : 1 ≤ z) :
    selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z
        (selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z) ≤
      2 * (Q : ℝ) * (z : ℝ) * (1 + Real.log z) ^ 3 /
        ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) :=
  selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_totient_ratio_bound z Q hQ hz
    (selbergTruncatedTotientSum_coprime_primorial_ge_totient_ratio_log_div_two z Q hQ hz)

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a progression bound `Y`, positive modulus `Q`, residue `a`, and
cutoff `z ≥ 1`.

Claim: the coprime-primorial sieve count has a main term with factor
`2 Q / (φ(Q) log(z + 1))` and an explicit squared logarithmic error.

Proof: use the finite sieve estimate and replace its divisor mass by the
totient-ratio logarithmic bound.

Role: makes the finite counting error explicit before its AGP-scale absorption.
-/
theorem progressionPrimeCount_le_coprime_primorial_explicit_log_cube_error {Y Q a z : ℕ}
    (hQ : 0 < Q) (hz : 1 ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a ((primeSetLECoprime z Q).prod id)
                (primeProductLECoprime_data z Q).1).totalMass *
            (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) +
          (2 * (Q : ℝ) * (z : ℝ) * (1 + Real.log z) ^ 3 /
              ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) ^
            2) := by
  let P : ℕ := (primeSetLECoprime z Q).prod id
  let G : ℝ := selbergTruncatedTotientSum P z
  let B : ℝ := selbergTruncatedOptimalWeightDivisorMass P z G
  let E : ℝ :=
    2 * (Q : ℝ) * (z : ℝ) * (1 + Real.log z) ^ 3 /
      ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))
  have hlogpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    have hz' : 1 < z + 1 := by omega
    exact_mod_cast hz'
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hphi : 0 < (Nat.totient Q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  have hNormLower : (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤ G := by
    simpa only [G, P] using
      selbergTruncatedTotientSum_coprime_primorial_ge_totient_ratio_log_div_two z Q hQ hz
  have hNormPos : 0 < (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) :=
    mul_pos (div_pos hphi hQR) (div_pos hlogpos (by norm_num only : (0 : ℝ) < 2))
  have hG : 0 < G := lt_of_lt_of_le hNormPos hNormLower
  have hBupper : B ≤ E := by
    simpa only [B, G, P, E] using
      selbergTruncatedOptimalWeightDivisorMass_coprime_primorial_le_totient_ratio_log_cube z Q hQ hz
  have hBnonneg : 0 ≤ B := by
    dsimp only [B, P, G]
    unfold selbergTruncatedOptimalWeightDivisorMass
    apply Finset.sum_nonneg
    intro k hk
    apply Finset.sum_nonneg
    intro d hd
    by_cases hcondition : d ∣ k ∧ k ≤ z
    · rw [ite_eq_left hcondition]
      exact
        div_nonneg (Nat.cast_nonneg d) (mul_nonneg (Nat.cast_nonneg (Nat.totient k)) (le_of_lt hG))
    · rw [ite_eq_right hcondition]
  have hlogz : 0 ≤ Real.log z := Real.log_nonneg (by exact_mod_cast hz)
  have hEnonneg : 0 ≤ E := by
    dsimp only [E]
    apply div_nonneg
    · exact
        mul_nonneg
          (mul_nonneg (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2) (Nat.cast_nonneg Q))
            (Nat.cast_nonneg z))
          (pow_nonneg (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) hlogz) 3)
    · exact le_of_lt (mul_pos hphi hlogpos)
  have hBsquare : B ^ 2 ≤ E ^ 2 := by
    calc
      B ^ 2 = B * B := by ring
      _ ≤ E * E := mul_le_mul hBupper hBupper hBnonneg hEnonneg
      _ = E ^ 2 := by ring
  have hrecip : 1 / G ≤ 2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) := by
    calc
      1 / G ≤ 1 / ((Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2)) :=
        one_div_le_one_div_of_le hNormPos hNormLower
      _ = 2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) := by
        field_simp [ne_of_gt hQR, ne_of_gt hphi, ne_of_gt hlogpos]
  have hmass :
    0 ≤ (progressionBoundingSieve Y Q a P (primeProductLECoprime_data z Q).1).totalMass := by
    exact Nat.cast_nonneg _
  have hmain :
    (progressionBoundingSieve Y Q a P (primeProductLECoprime_data z Q).1).totalMass * (1 / G) +
        B ^ 2 ≤
      (progressionBoundingSieve Y Q a P (primeProductLECoprime_data z Q).1).totalMass *
          (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) +
        B ^ 2 := by
    exact add_le_add_left (mul_le_mul_of_nonneg_left hrecip hmass) _
  have hbase :=
    progressionPrimeCount_le_coprime_primorial_divisor_mass_bound (Y := Y) (Q := Q) (a := a) (z :=
      z) hQ hz
  calc
    (primeCountInProgression Y Q a : ℝ) ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          ((progressionBoundingSieve Y Q a P (primeProductLECoprime_data z Q).1).totalMass *
              (1 / G) +
            B ^ 2) :=
      by simpa only [P, G, B] using hbase
    _ ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          ((progressionBoundingSieve Y Q a P (primeProductLECoprime_data z Q).1).totalMass *
              (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) +
            B ^ 2) :=
      add_le_add_right hmain _
    _ ≤
        ((Finset.range (z + 1)).filter Nat.Prime).card +
          ((progressionBoundingSieve Y Q a P (primeProductLECoprime_data z Q).1).totalMass *
              (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) +
            E ^ 2) :=
      by
      have herror :
        (progressionBoundingSieve Y Q a P (primeProductLECoprime_data z Q).1).totalMass *
              (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) +
            B ^ 2 ≤
          (progressionBoundingSieve Y Q a P (primeProductLECoprime_data z Q).1).totalMass *
              (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) +
            E ^ 2 :=
        add_le_add_right hBsquare _
      exact add_le_add_right herror _

end PseudoPrime.AnalyticNumberTheory.AGP

namespace PseudoPrime.AnalyticNumberTheory.AGP

open PseudoPrime.NumberTheory.PrimeProducts in
/--
Inputs: a progression bound `Y`, a positive modulus `Q`, residue `a`, and a
cutoff `z ≥ 1`.

Claim: the coprime-primorial Selberg sieve bounds the progression count by the
small-prime count, a total-mass term with factor
`2Q / (φ(Q) log(z + 1))`, and the squared optimal-weight divisor mass.

Proof: use the general divisor-mass sieve estimate, then replace the inverse
normalizer using the totient-ratio logarithmic lower bound.

Role: exposes the expected `Q/φ(Q)` factor for later Brun–Titchmarsh estimates.
-/
theorem progressionPrimeCount_le_coprime_primorial_totient_ratio_log_divisor_mass_bound
    {Y Q a z : ℕ} (hQ : 0 < Q) (hz : 1 ≤ z) :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a ((primeSetLECoprime z Q).prod id)
                (primeProductLECoprime_data z Q).1).totalMass *
            (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) +
          (selbergTruncatedOptimalWeightDivisorMass ((primeSetLECoprime z Q).prod id) z
              (selbergTruncatedTotientSum ((primeSetLECoprime z Q).prod id) z)) ^
            2) := by
  let P : ℕ := (primeSetLECoprime z Q).prod id
  let G : ℝ := selbergTruncatedTotientSum P z
  let B : ℝ := selbergTruncatedOptimalWeightDivisorMass P z G
  have hP : Squarefree P := by simpa only [P] using (primeProductLECoprime_data z Q).1
  have hPsmall : ∀ p : ℕ, Nat.Prime p → p ∣ P → p ≤ z := by
    intro p hp hpdiv
    exact primeProductLECoprime_small z Q p hp (by simpa only [P] using hpdiv)
  have hlogpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) := by
    apply Real.log_pos
    have hz' : 1 < z + 1 := by simpa only [Nat.add_one] using Nat.lt_succ_of_le hz
    exact_mod_cast hz'
  have hhalfpos : 0 < Real.log ((z + 1 : ℕ) : ℝ) / 2 :=
    div_pos hlogpos (by norm_num only : (0 : ℝ) < 2)
  have hQR : 0 < (Q : ℝ) := by exact_mod_cast hQ
  have hphi : 0 < (Nat.totient Q : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hQ
  have hNormLower : (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) ≤ G := by
    simpa only [G, P] using
      selbergTruncatedTotientSum_coprime_primorial_ge_totient_ratio_log_div_two z Q hQ hz
  have hNormPos : 0 < (Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2) :=
    mul_pos (div_pos hphi hQR) hhalfpos
  have hrecip : 1 / G ≤ 2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) := by
    calc
      1 / G ≤ 1 / ((Nat.totient Q : ℝ) / (Q : ℝ) * (Real.log ((z + 1 : ℕ) : ℝ) / 2)) :=
        one_div_le_one_div_of_le hNormPos hNormLower
      _ = 2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ)) := by
        field_simp [ne_of_gt hQR, ne_of_gt hphi, ne_of_gt hlogpos]
  have hbase :=
    progressionPrimeCount_le_truncatedOptimal_selberg_divisor_mass_error (Y := Y) (Q := Q) (a := a)
      (z := z) (P := P) hP hQ (primeProductLECoprime_coprime z Q) hz G (by rfl) hPsmall
  have hmass : 0 ≤ (progressionBoundingSieve Y Q a P hP).totalMass := by exact Nat.cast_nonneg _
  have hmain :
    (progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + B ^ 2 ≤
      (progressionBoundingSieve Y Q a P hP).totalMass *
          (2 * (Q : ℝ) / ((Nat.totient Q : ℝ) * Real.log ((z + 1 : ℕ) : ℝ))) +
        B ^ 2 := by
    exact add_le_add_left (mul_le_mul_of_nonneg_left hrecip hmass) _
  have hbase' :
    (primeCountInProgression Y Q a : ℝ) ≤
      ((Finset.range (z + 1)).filter Nat.Prime).card +
        ((progressionBoundingSieve Y Q a P hP).totalMass * (1 / G) + B ^ 2) := by
    simpa only [P, G, B] using hbase
  have hresult := le_trans hbase' (add_le_add_right hmain _)
  simpa only [P, G, B] using hresult

end PseudoPrime.AnalyticNumberTheory.AGP
