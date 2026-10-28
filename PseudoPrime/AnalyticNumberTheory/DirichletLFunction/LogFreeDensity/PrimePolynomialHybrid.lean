/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.PreSiftedHybrid
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.MangoldtDirichletBounds
public import PseudoPrime.Analysis.ExponentialMeanSquarePointBounds
public import PseudoPrime.Analysis.MidpointQuadrature

/-! # Prime-polynomial specializations of the hybrid large sieve -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a prime index, a derivative order, a complex coefficient twist, and a point with real and
imaginary coordinates `σ` and `t`.
Claim: the differentiated von Mangoldt L-series term at that prime is its logarithmic coefficient
times the real-decay and oscillatory factors.
Proof: expand the iterated logarithmic multiplier, use the von Mangoldt value at a prime, and
factor the complex power into its two exponential components.
Role: identifies the prime terms of the zero-detection polynomial with coefficients accepted by
the pre-sifted hybrid estimate.
-/
theorem prime_vonMangoldt_logMul_term_eq {p r : ℕ} {σ t : ℝ} (hp : Nat.Prime p) (χ : ℕ → ℂ) :
    LSeries.term (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ)))
        ((σ : ℂ) + (t : ℂ) * Complex.I) p =
      ((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ) *
        Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I) *
        χ p := by
  rw [LSeries.term_of_ne_zero hp.ne_zero,
    PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.logMul_iterate_apply,
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := by rw [← Complex.natCast_log]
  rw [hlog, Complex.cpow_def_of_ne_zero (by exact_mod_cast hp.ne_zero), div_eq_mul_inv, ←
    Complex.exp_neg, mul_add, neg_add, Complex.exp_add]
  push_cast
  ring_nf

/--
Inputs: a finite set of primes, a derivative order, a complex evaluation point, and a Dirichlet
character.
Claim: the twisted differentiated Euler sum over those primes equals the corresponding prime
polynomial with its real decay and oscillatory factors displayed.
Proof: apply `prime_vonMangoldt_logMul_term_eq` term by term in the finite sum.
Role: gives the exact finite-sum interface between the Euler detector and the prime hybrid bound.
-/
theorem finite_prime_vonMangoldt_logMul_sum_eq {q : ℕ} [NeZero q] (r : ℕ) (σ t : ℝ) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p) (χ : DirichletCharacter ℂ q) :
    (∑ p ∈ s,
        LSeries.term
          (LSeries.logMul^[r] (fun j : ℕ ↦ χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)))
          ((σ : ℂ) + (t : ℂ) * Complex.I) p) =
      ∑ p ∈ s,
        ((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ) *
          Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I) *
          χ (p : ZMod q) := by
  apply Finset.sum_congr rfl
  intro p hp
  exact prime_vonMangoldt_logMul_term_eq (hprime p hp) (fun j => χ (j : ZMod q))

/--
Inputs: a derivative order, a finite Euler-series cutoff, a complex evaluation point, and a
coefficient twist.
Claim: the finite differentiated von Mangoldt sum is the sum over primes plus the sum over
nonprime prime powers; all other indices contribute zero.
Proof: partition the finite support into prime and nonprime indices, then use the support of the
von Mangoldt function to remove nonprime integers that are not prime powers.
Role: isolates the higher-prime-power remainder that must be bounded before applying the prime
hybrid estimate to zero detection.
-/
theorem finite_vonMangoldt_logMul_sum_eq_prime_and_higher_powers (r cutoff : ℕ) (s : ℂ)
    (χ : ℕ → ℂ) :
    (∑ n ∈ Finset.range (cutoff + 1),
        LSeries.term (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ)))
          s n) =
      (∑ p ∈ (Finset.range (cutoff + 1)).filter Nat.Prime,
          LSeries.term
            (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) s p) +
        ∑ n ∈ (Finset.range (cutoff + 1)).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n),
          LSeries.term
            (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) s
            n := by
  classical
  let S : Finset ℕ := Finset.range (cutoff + 1)
  let f : ℕ → ℂ := fun n =>
    LSeries.term (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) s n
  have hzero : ∀ n, ¬IsPrimePow n → f n = 0 := by
    intro n hpow
    simp only [f]
    by_cases hn0 : n = 0
    · subst n
      simp only [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0, logMul_iterate_apply]
      have hΛ : ArithmeticFunction.vonMangoldt n = 0 :=
        (ArithmeticFunction.vonMangoldt_eq_zero_iff).2 hpow
      have hΛC : (ArithmeticFunction.vonMangoldt n : ℂ) = 0 := by exact_mod_cast hΛ
      simp only [hΛC, mul_zero, zero_div]
  have hzeroSum :
    (∑ n ∈ (S.filter (fun n => ¬Nat.Prime n)).filter (fun n => ¬IsPrimePow n), f n) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    exact hzero n (Finset.mem_filter.mp hn).2
  have hrem :
    (∑ n ∈ S.filter (fun n => ¬Nat.Prime n), f n) =
      ∑ n ∈ (S.filter (fun n => ¬Nat.Prime n)).filter IsPrimePow, f n := by
    calc
      _ =
          (∑ n ∈ (S.filter (fun n => ¬Nat.Prime n)).filter IsPrimePow, f n) +
            ∑ n ∈ (S.filter (fun n => ¬Nat.Prime n)).filter (fun n => ¬IsPrimePow n), f n :=
        (Finset.sum_filter_add_sum_filter_not (S.filter (fun n => ¬Nat.Prime n)) IsPrimePow f).symm
      _ = _ := by rw [hzeroSum, add_zero]
  have hpart := Finset.sum_filter_add_sum_filter_not S Nat.Prime f
  change
    (∑ n ∈ S, f n) =
      (∑ p ∈ S.filter Nat.Prime, f p) + ∑ n ∈ S.filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n), f n
  calc
    _ = (∑ p ∈ S.filter Nat.Prime, f p) + ∑ n ∈ S.filter (fun n => ¬Nat.Prime n), f n := hpart.symm
    _ = _ := by
      rw [hrem]
      congr 1
      congr 1
      ext n
      simp only [Finset.mem_filter, and_assoc, and_comm]

/--
Inputs: a natural number that is a prime power but is not itself prime.
Claim: it has a representation as a prime raised to an exponent at least two.
Proof: unfold the natural-number prime-power predicate and exclude exponent one using the
non-primality assumption.
Role: makes the sparse higher-prime-power support explicit for its remainder estimate.
-/
theorem isPrimePow_nonprime_has_exponent_ge_two {n : ℕ} (hpow : IsPrimePow n) (hn : ¬Nat.Prime n) :
    ∃ p k : ℕ, Nat.Prime p ∧ 2 ≤ k ∧ p ^ k = n := by
  obtain ⟨p, k, hp, hk, hnk⟩ := (isPrimePow_nat_iff n).mp hpow
  have hkne : k ≠ 1 := by
    intro hk1
    subst k
    apply hn
    rw [← hnk]
    simpa only [pow_one] using hp
  have hk2 : 2 ≤ k := by omega
  exact ⟨p, k, hp, hk2, hnk⟩

/--
Inputs: two prime bases, two positive exponents, and equality of the resulting powers.
Claim: both the bases and exponents agree.
Proof: apply the natural-number prime-power injectivity theorem.
Role: ensures that indexing a higher-prime-power remainder by its prime base and exponent does
not introduce multiplicity.
-/
theorem prime_power_representation_unique {p q k l : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hk : k ≠ 0) (hl : l ≠ 0) (h : p ^ k = q ^ l) : p = q ∧ k = l :=
  Nat.Prime.pow_inj' hp hq hk hl h

/--
Inputs: pairs consisting of a prime base and an exponent at least two.
Claim: mapping such a pair to its prime power is injective.
Proof: exponents are positive, so equality of the powers determines both entries by
`Nat.Prime.pow_inj'`.
Role: permits finite sums over higher prime powers to be reindexed by their base and exponent.
-/
theorem prime_power_pair_map_injective :
    Function.Injective
      (fun x : { p : ℕ // Nat.Prime p } × { k : ℕ // 2 ≤ k } => x.1.val ^ x.2.val) := by
  intro x y hxy
  have hexp : x.2.val ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) x.2.property)
  have heyp : y.2.val ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) y.2.property)
  have huniq := Nat.Prime.pow_inj' x.1.property y.1.property hexp heyp hxy
  rcases huniq with ⟨hp, hk⟩
  apply Prod.ext
  · exact Subtype.ext hp
  · exact Subtype.ext hk

/--
Inputs: a finite collection of pairs of prime bases and exponents at least two, and a complex
weight on natural numbers.
Claim: summing the weight over the represented prime powers equals summing it over their pairs.
Proof: reindex the image sum using injectivity of the prime-power map.
Role: provides the finite-sum interface for quantitative higher-prime-power estimates.
-/
theorem finite_prime_power_pair_sum_reindex
    (s : Finset ({ p : ℕ // Nat.Prime p } × { k : ℕ // 2 ≤ k })) (f : ℕ → ℂ) :
    (∑ n ∈ s.image (fun x => x.1.val ^ x.2.val), f n) = ∑ x ∈ s, f (x.1.val ^ x.2.val) := by
  classical
    exact
    Finset.sum_image (s := s) (g := fun x : { p : ℕ // Nat.Prime p } × { k : ℕ // 2 ≤ k } =>
      x.1.val ^ x.2.val) (f := f)
      (by
        intro x hx y hy hxy
        exact prime_power_pair_map_injective hxy)

/--
Inputs: a natural-number cutoff.
Claim: the nonprime prime powers up to the cutoff are exactly the powers `p^k` with prime `p`,
exponent `k ≥ 2`, and `p^k` within the cutoff; both the base and exponent lie in the finite range.
Proof: use the prime-power representation in one direction and prove the represented power is
composite in the other direction.
Role: supplies a finite pair domain for estimating the higher-prime-power remainder.
-/
theorem finite_nonprime_prime_powers_eq_bounded_pair_image (N : ℕ) :
    (Finset.range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n) =
      (((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
            (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ 2 ≤ x.2 ∧ x.1 ^ x.2 ≤ N)).image
        (fun x => x.1 ^ x.2) := by
  classical
  let S := (Finset.range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n)
  let P :=
    ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
      (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ 2 ≤ x.2 ∧ x.1 ^ x.2 ≤ N)
  let g : ℕ × ℕ → ℕ := fun x => x.1 ^ x.2
  change S = P.image g
  ext n
  constructor
  · intro hn
    rcases Finset.mem_filter.mp hn with ⟨hnrange, hnprops⟩
    rcases hnprops with ⟨hnpow, hnprime⟩
    have hnle : n ≤ N := by
      simp only [Finset.mem_range] at hnrange
      omega
    obtain ⟨p, k, hp, hk, hpow⟩ := isPrimePow_nonprime_has_exponent_ge_two hnpow hnprime
    have hpk : p ^ k ≤ N := by
      calc
        p ^ k = n := hpow
        _ ≤ N := hnle
    have hpPow : p ≤ p ^ k := Nat.le_self_pow (by omega : k ≠ 0) p
    have hpN : p < N + 1 := Nat.lt_succ_of_le (le_trans hpPow hpk)
    have hkPow : k < 2 ^ k := Nat.lt_two_pow_self
    have hbase : 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
    have hklt : k < p ^ k := lt_of_lt_of_le hkPow hbase
    have hkN : k < N + 1 := Nat.lt_succ_of_le (le_trans hklt.le hpk)
    apply Finset.mem_image.mpr
    refine ⟨(p, k), ?_, hpow⟩
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr hpN, Finset.mem_range.mpr hkN⟩
    · exact ⟨hp, hk, hpk⟩
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨⟨p, k⟩, hp, hnpow⟩
    rcases Finset.mem_filter.mp hp with ⟨hprod, hprops⟩
    rcases Finset.mem_product.mp hprod with ⟨hpRange, hkRange⟩
    rcases hprops with ⟨hprime, hk, hbound⟩
    have hpow : IsPrimePow (p ^ k) := (isPrimePow_nat_iff (p ^ k)).mpr ⟨p, k, hprime, by omega, rfl⟩
    have hnotprime : ¬Nat.Prime (p ^ k) := by
      intro hprimepow
      have hkpos : 0 < k := by omega
      have hdiv : p ∣ p ^ k := dvd_pow_self p hkpos.ne'
      have hlt : p < p ^ k := by
        calc
          p = p ^ 1 := by simp only [pow_one]
          _ < p ^ k := Nat.pow_lt_pow_right hprime.one_lt (by omega)
      have heq : p ^ k = p := (hprimepow.dvd_iff_eq hprime.ne_one).mp hdiv
      omega
    have hpowN : IsPrimePow n := by
      rw [← hnpow]
      exact hpow
    have hnotprimeN : ¬Nat.Prime n := by
      intro hprimeN
      rw [← hnpow] at hprimeN
      exact hnotprime hprimeN
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_range.mpr
      have hnle : p ^ k ≤ N := hbound
      rw [← hnpow]
      exact Nat.lt_succ_of_le hnle
    · exact ⟨hpowN, hnotprimeN⟩

/--
Inputs: a natural-number cutoff and a complex weight on natural numbers.
Claim: the sum over nonprime prime powers below the cutoff equals the sum over bounded prime-base
and exponent pairs.
Proof: rewrite the support as the image of the bounded pair set, then apply injective image
reindexing.
Role: exposes the higher-prime-power contribution as a finite double sum for quantitative bounds.
-/
theorem finite_nonprime_prime_powers_sum_eq_bounded_pair_sum (N : ℕ) (f : ℕ → ℂ) :
    (∑ n ∈ (Finset.range (N + 1)).filter (fun n => IsPrimePow n ∧ ¬Nat.Prime n), f n) =
      ∑
        x ∈
          (((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
            (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ 2 ≤ x.2 ∧ x.1 ^ x.2 ≤ N)),
        f (x.1 ^ x.2) := by
  classical
  let P :=
    ((Finset.range (N + 1)).product (Finset.range (N + 1))).filter
      (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ 2 ≤ x.2 ∧ x.1 ^ x.2 ≤ N)
  let g : ℕ × ℕ → ℕ := fun x => x.1 ^ x.2
  have himage := finite_nonprime_prime_powers_eq_bounded_pair_image N
  have hinj : Set.InjOn g (↑P) := by
    intro x hx y hy hxy
    rcases Finset.mem_filter.mp hx with ⟨_, hpropsx⟩
    rcases hpropsx with ⟨hpx, hkx, _⟩
    rcases Finset.mem_filter.mp hy with ⟨_, hpropsy⟩
    rcases hpropsy with ⟨hpy, hky, _⟩
    have huniq :=
      prime_power_pair_map_injective (a₁ := ⟨⟨x.1, hpx⟩, ⟨x.2, hkx⟩⟩) (a₂ :=
        ⟨⟨y.1, hpy⟩, ⟨y.2, hky⟩⟩) hxy
    apply Prod.ext
    · exact congrArg Subtype.val (congrArg Prod.fst huniq)
    · exact congrArg Subtype.val (congrArg Prod.snd huniq)
  rw [himage]
  exact Finset.sum_image (s := P) (g := g) (f := f) hinj

/--
Inputs: a derivative order, a finite Euler cutoff, a complex evaluation point, and a coefficient
twist.
Claim: the finite differentiated von Mangoldt sum is the prime sum plus a finite sum over prime
bases and exponents at least two.
Proof: combine the prime and higher-power decomposition with the bounded pair reindexing theorem.
Role: presents the Euler polynomial in the two support classes needed for separate estimates.
-/
theorem finite_vonMangoldt_logMul_sum_eq_prime_and_prime_power_pairs (r cutoff : ℕ) (s : ℂ)
    (χ : ℕ → ℂ) :
    (∑ n ∈ Finset.range (cutoff + 1),
        LSeries.term (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ)))
          s n) =
      (∑ p ∈ (Finset.range (cutoff + 1)).filter Nat.Prime,
          LSeries.term
            (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) s p) +
        ∑
          x ∈
            (((Finset.range (cutoff + 1)).product (Finset.range (cutoff + 1))).filter
              (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ 2 ≤ x.2 ∧ x.1 ^ x.2 ≤ cutoff)),
          LSeries.term
            (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) s
            (x.1 ^ x.2) := by
  rw [finite_vonMangoldt_logMul_sum_eq_prime_and_higher_powers]
  congr 1
  exact
    finite_nonprime_prime_powers_sum_eq_bounded_pair_sum cutoff
      (fun n =>
        LSeries.term (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ)))
          s n)

/--
Inputs: a derivative order, a finite Euler cutoff, a complex evaluation point, and a coefficient
twist.
Claim: subtracting the prime contribution from the finite differentiated von Mangoldt sum leaves
exactly the contribution indexed by prime bases and exponents at least two.
Proof: rewrite the established prime and prime-power decomposition and normalize the subtraction.
Role: connects the uniform higher-prime-power estimate to the full finite Euler polynomial.
-/
theorem finite_vonMangoldt_prime_power_remainder_eq (r cutoff : ℕ) (s : ℂ) (χ : ℕ → ℂ) :
    (∑ n ∈ Finset.range (cutoff + 1),
          LSeries.term
            (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) s n) -
        (∑ p ∈ (Finset.range (cutoff + 1)).filter Nat.Prime,
          LSeries.term
            (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ))) s p) =
      ∑
        x ∈
          (((Finset.range (cutoff + 1)).product (Finset.range (cutoff + 1))).filter
            (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ 2 ≤ x.2 ∧ x.1 ^ x.2 ≤ cutoff)),
        LSeries.term (LSeries.logMul^[r] (fun j : ℕ ↦ χ j * (ArithmeticFunction.vonMangoldt j : ℂ)))
          s (x.1 ^ x.2) := by
  rw [finite_vonMangoldt_logMul_sum_eq_prime_and_prime_power_pairs]
  ring

/--
Inputs: a nonnegative scale `η`, a decay exponent `σ ≥ 1`, a logarithmic order, and natural
parameters `k` and `p`.
Claim: the normalized logarithmic weight at `k log p`, with decay `exp(-σ k log p)`, is at most
`(4η)^m exp(-3 k log p / 4)`.
Proof: use the degree-`m` Taylor term bound for the exponential and the inequality `σ ≥ 1`.
Role: supplies a summable majorant for normalized higher-prime-power terms at the Euler point
`Re(s) = 1 + η`.
-/
theorem normalized_power_weight_le_exp_bound {η σ : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (m k p : ℕ) :
    (η ^ m / (m.factorial : ℝ)) * ((k : ℝ) * Real.log p) ^ m *
        Real.exp (-σ * ((k : ℝ) * Real.log p)) ≤
      (4 * η) ^ m * Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p)) := by
  let L : ℝ := (k : ℝ) * Real.log p
  change
    (η ^ m / (m.factorial : ℝ)) * L ^ m * Real.exp (-σ * L) ≤
      (4 * η) ^ m * Real.exp (-(3 / 4 : ℝ) * L)
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact mul_nonneg (Nat.cast_nonneg k) hlog
  have hfactor :
    (η ^ m / (m.factorial : ℝ)) * L ^ m = (4 * η) ^ m * ((L / 4) ^ m / (m.factorial : ℝ)) := by
    calc
      (η ^ m / (m.factorial : ℝ)) * L ^ m = (η ^ m * L ^ m) / (m.factorial : ℝ) := by ring
      _ = (η * L) ^ m / (m.factorial : ℝ) := by rw [← mul_pow]
      _ = ((4 * η) * (L / 4)) ^ m / (m.factorial : ℝ) := by
        congr 1
        ring
      _ = (4 * η) ^ m * ((L / 4) ^ m / (m.factorial : ℝ)) := by
        rw [mul_pow]
        ring
  have hTaylor := Real.pow_div_factorial_le_exp (L / 4) (by positivity) m
  have hcoeff : 0 ≤ (4 * η) ^ m := pow_nonneg (mul_nonneg (by norm_num only) hη) m
  have hTaylor' := mul_le_mul_of_nonneg_left hTaylor hcoeff
  have hTaylor'' := mul_le_mul_of_nonneg_right hTaylor' (Real.exp_pos (-σ * L)).le
  have hExp : L / 4 - σ * L ≤ -(3 / 4 : ℝ) * L := by
    have hprod : 0 ≤ (σ - 1) * L := mul_nonneg (by linarith only [hσ]) hL
    linarith only [hprod]
  calc
    (η ^ m / (m.factorial : ℝ)) * L ^ m * Real.exp (-σ * L) =
        (4 * η) ^ m * ((L / 4) ^ m / (m.factorial : ℝ)) * Real.exp (-σ * L) :=
      by rw [hfactor]
    _ ≤ (4 * η) ^ m * Real.exp (L / 4) * Real.exp (-σ * L) := hTaylor''
    _ = (4 * η) ^ m * (Real.exp (L / 4) * Real.exp (-σ * L)) := by ring
    _ = (4 * η) ^ m * Real.exp (L / 4 - σ * L) := by
      rw [← Real.exp_add]
      congr 1
      ring_nf
    _ ≤ (4 * η) ^ m * Real.exp (-(3 / 4 : ℝ) * L) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp) hcoeff

/--
Inputs: a nonnegative scale `η`, a decay exponent `σ ≥ 1`, a logarithmic order, and natural
parameters `k` and `p`.
Claim: the normalized logarithmic weight with denominator `n!` is bounded by a multiple of the
exponential majorant from `normalized_power_weight_le_exp_bound`.
Proof: convert `n!` to `(n + 1)!` and apply that pointwise estimate at order `n + 1`.
Role: matches the derivative normalization used by the higher-prime-power remainder.
-/
theorem normalized_power_weight_with_predecessor_factorial {η σ : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ)
    (n k p : ℕ) :
    (η ^ (n + 1) / (n.factorial : ℝ)) * ((k : ℝ) * Real.log p) ^ (n + 1) *
        Real.exp (-σ * ((k : ℝ) * Real.log p)) ≤
      (n + 1 : ℝ) * (4 * η) ^ (n + 1) * Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p)) := by
  have h := normalized_power_weight_le_exp_bound hη hσ (n + 1) k p
  have hfac : ((n + 1).factorial : ℝ) = (n + 1 : ℝ) * (n.factorial : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  have heq :
    (η ^ (n + 1) / (n.factorial : ℝ)) * ((k : ℝ) * Real.log p) ^ (n + 1) *
        Real.exp (-σ * ((k : ℝ) * Real.log p)) =
      (n + 1 : ℝ) *
        ((η ^ (n + 1) / ((n + 1).factorial : ℝ)) * ((k : ℝ) * Real.log p) ^ (n + 1) *
          Real.exp (-σ * ((k : ℝ) * Real.log p))) := by
    rw [hfac]
    field_simp
  have hmnonneg : 0 ≤ (n + 1 : ℝ) := by exact_mod_cast (Nat.zero_le (n + 1))
  calc
    _ =
        (n + 1 : ℝ) *
          ((η ^ (n + 1) / ((n + 1).factorial : ℝ)) * ((k : ℝ) * Real.log p) ^ (n + 1) *
            Real.exp (-σ * ((k : ℝ) * Real.log p))) :=
      heq
    _ ≤ (n + 1 : ℝ) * ((4 * η) ^ (n + 1) * Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p))) :=
      mul_le_mul_of_nonneg_left h hmnonneg
    _ = _ := by ring

/--
Inputs: a nonnegative scale `η`, a decay exponent `σ ≥ 1`, and natural indices `p`, `k`, and `n`
with `k ≥ 2`.
Claim: the normalized logarithmic term for a higher prime power is bounded by an exponential
majorant with factor `(n + 1) (4η)^(n + 1)`.
Proof: bound `log p` by `k log p`, then apply the predecessor-factorial estimate.
Role: controls each higher-prime-power term in the differentiated Euler polynomial.
-/
theorem normalized_prime_power_log_term_le_exp_bound {η σ : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (p k n : ℕ)
    (hk : 2 ≤ k) :
    (η ^ (n + 1) / (n.factorial : ℝ)) * Real.log p * ((k : ℝ) * Real.log p) ^ n *
        Real.exp (-σ * ((k : ℝ) * Real.log p)) ≤
      (n + 1 : ℝ) * (4 * η) ^ (n + 1) * Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p)) := by
  let L : ℝ := (k : ℝ) * Real.log p
  let c : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  have hlog : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  have hL : 0 ≤ L := by
    dsimp only [L]
    exact mul_nonneg (Nat.cast_nonneg k) hlog
  have hkreal : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast (le_trans (by decide : 1 ≤ 2) hk)
  have hlogL : Real.log p ≤ L := by
    dsimp only [L]
    calc
      Real.log p = 1 * Real.log p := by ring
      _ ≤ (k : ℝ) * Real.log p := mul_le_mul_of_nonneg_right hkreal hlog
  have hweight : Real.log p * L ^ n ≤ L ^ (n + 1) := by
    calc
      Real.log p * L ^ n ≤ L * L ^ n := mul_le_mul_of_nonneg_right hlogL (pow_nonneg hL n)
      _ = L ^ (n + 1) := by ring
  have hc : 0 ≤ c := div_nonneg (pow_nonneg hη _) (Nat.cast_nonneg _)
  have hweight' : c * (Real.log p * L ^ n) ≤ c * L ^ (n + 1) := mul_le_mul_of_nonneg_left hweight hc
  have hexp : 0 < Real.exp (-σ * L) := Real.exp_pos _
  have hweight'' :
    c * (Real.log p * L ^ n) * Real.exp (-σ * L) ≤ c * L ^ (n + 1) * Real.exp (-σ * L) :=
    mul_le_mul_of_nonneg_right hweight' hexp.le
  have hmain :
    c * L ^ (n + 1) * Real.exp (-σ * L) ≤
      (n + 1 : ℝ) * (4 * η) ^ (n + 1) * Real.exp (-(3 / 4 : ℝ) * L) := by
    simpa only [c, L] using normalized_power_weight_with_predecessor_factorial hη hσ n k p
  calc
    _ = c * (Real.log p * L ^ n) * Real.exp (-σ * L) := by
      dsimp only [c, L]
      ring
    _ ≤ c * L ^ (n + 1) * Real.exp (-σ * L) := hweight''
    _ ≤ (n + 1 : ℝ) * (4 * η) ^ (n + 1) * Real.exp (-(3 / 4 : ℝ) * L) := hmain
    _ = _ := by dsimp only [L]

/--
Inputs: a Dirichlet character, nonnegative normalization scale, decay exponent at least one,
derivative order, prime base, and exponent at least two.
Claim: the normalized norm of the corresponding twisted von Mangoldt Euler term is bounded by
the same exponential majorant as its real prime-power weight.
Proof: use the termwise logarithmic-weight bound, evaluate the von Mangoldt and logarithm at a
prime power, and apply the normalized real-weight estimate.
Role: transfers the finite prime-power coefficient estimate to the actual differentiated Euler
polynomial.
-/
theorem twisted_prime_power_term_normalized_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {η σ : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (n p k : ℕ) (hp : Nat.Prime p) (hk : 2 ≤ k) (s : ℂ)
    (hs : s.re = σ) :
    (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖LSeries.term
            (LSeries.logMul^[n]
              (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
            s (p ^ k)‖ ≤
      (n + 1 : ℝ) * (4 * η) ^ (n + 1) * Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p)) := by
  have hkpos : k ≠ 0 := by omega
  have hΛ : ArithmeticFunction.vonMangoldt (p ^ k) = Real.log p := by
    rw [ArithmeticFunction.vonMangoldt_apply_pow hkpos,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlog : Real.log (p ^ k : ℕ) = (k : ℝ) * Real.log p := by
    rw [show ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k by exact Nat.cast_pow p k, Real.log_pow]
  have hden : ((p ^ k : ℕ) : ℝ) ^ σ = Real.exp (σ * ((k : ℝ) * Real.log p)) := by
    rw [Real.rpow_def_of_pos (by exact_mod_cast (Nat.pow_pos hp.pos))]
    rw [show ((p ^ k : ℕ) : ℝ) = (p : ℝ) ^ k by exact Nat.cast_pow p k, Real.log_pow]
    ring_nf
  have hterm := twistedVonMangoldt_log_term_bound χ n (p ^ k) (s := s) (Nat.pow_pos hp.pos)
  rw [hs] at hterm
  have htermrewrite :
    ArithmeticFunction.vonMangoldt (p ^ k) * (Real.log (p ^ k : ℕ)) ^ n / ((p ^ k : ℕ) : ℝ) ^ σ =
      Real.log p * ((k : ℝ) * Real.log p) ^ n * Real.exp (-σ * ((k : ℝ) * Real.log p)) := by
    rw [hΛ, hlog, hden, div_eq_mul_inv, ← Real.exp_neg]
    ring_nf
  have hc : 0 ≤ η ^ (n + 1) / (n.factorial : ℝ) := div_nonneg (pow_nonneg hη _) (Nat.cast_nonneg _)
  calc
    _ ≤
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          (ArithmeticFunction.vonMangoldt (p ^ k) * (Real.log (p ^ k : ℕ)) ^ n /
            ((p ^ k : ℕ) : ℝ) ^ σ) :=
      mul_le_mul_of_nonneg_left hterm hc
    _ =
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          (Real.log p * ((k : ℝ) * Real.log p) ^ n * Real.exp (-σ * ((k : ℝ) * Real.log p))) :=
      by rw [htermrewrite]
    _ =
        (η ^ (n + 1) / (n.factorial : ℝ)) * Real.log p * ((k : ℝ) * Real.log p) ^ n *
          Real.exp (-σ * ((k : ℝ) * Real.log p)) :=
      by ring
    _ ≤ (n + 1 : ℝ) * (4 * η) ^ (n + 1) * Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p)) :=
      normalized_prime_power_log_term_le_exp_bound hη hσ p k n hk

/--
Inputs: a Dirichlet character, a finite set of prime-base/exponent pairs with exponents at least
two, a nonnegative normalization scale, and a decay exponent at least one.
Claim: the normalized norm of the finite higher-prime-power Euler sum is bounded by the sum of
the corresponding exponential majorants.
Proof: apply the triangle inequality, distribute the nonnegative normalization across the sum,
and use the termwise estimate for each pair.
Role: controls the complete finite higher-prime-power part of the differentiated Euler polynomial.
-/
theorem normalized_twisted_prime_power_sum_bound {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    {η σ : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (n : ℕ) (s : ℂ) (hs : s.re = σ) (S : Finset (ℕ × ℕ))
    (hS : ∀ x ∈ S, Nat.Prime x.1 ∧ 2 ≤ x.2) :
    (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖∑ x ∈ S,
            LSeries.term
              (LSeries.logMul^[n]
                (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
              s (x.1 ^ x.2)‖ ≤
      ∑ x ∈ S,
        ((n + 1 : ℝ) * (4 * η) ^ (n + 1) *
          Real.exp (-(3 / 4 : ℝ) * ((x.2 : ℝ) * Real.log x.1))) := by
  let c : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  have hc : 0 ≤ c := div_nonneg (pow_nonneg hη _) (Nat.cast_nonneg _)
  let f : ℕ × ℕ → ℂ := fun x =>
    LSeries.term
      (LSeries.logMul^[n] (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ))) s
      (x.1 ^ x.2)
  have htriangle : ‖∑ x ∈ S, f x‖ ≤ ∑ x ∈ S, ‖f x‖ := norm_sum_le S f
  have hscaled := mul_le_mul_of_nonneg_left htriangle hc
  have hscaled' : c * ‖∑ x ∈ S, f x‖ ≤ ∑ x ∈ S, c * ‖f x‖ := by
    calc
      _ ≤ c * ∑ x ∈ S, ‖f x‖ := hscaled
      _ = ∑ x ∈ S, c * ‖f x‖ := by rw [Finset.mul_sum]
  calc
    _ = c * ‖∑ x ∈ S, f x‖ := by dsimp only [c, f]
    _ ≤ ∑ x ∈ S, c * ‖f x‖ := hscaled'
    _ ≤
        ∑ x ∈ S,
          ((n + 1 : ℝ) * (4 * η) ^ (n + 1) *
            Real.exp (-(3 / 4 : ℝ) * ((x.2 : ℝ) * Real.log x.1))) :=
      by
      apply Finset.sum_le_sum
      intro x hx
      rcases hS x hx with ⟨hp, hk⟩
      change
        c *
            ‖LSeries.term
                (LSeries.logMul^[n]
                  (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                s (x.1 ^ x.2)‖ ≤
          _
      simpa only [c] using twisted_prime_power_term_normalized_bound χ hη hσ n x.1 x.2 hp hk s hs

/--
Inputs: a nonnegative real ratio below one and a finite set of natural exponents, all at least two.
Claim: the sum of the corresponding powers is bounded by the geometric tail beginning at exponent
two.
Proof: factor out the square, reindex the remaining powers injectively by subtracting two, and
bound the finite sum by the full geometric series.
Role: supplies a uniform exponent sum for the higher-prime-power majorant.
-/
theorem finset_sum_pow_geometric_tail {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (S : Finset ℕ)
    (hS : ∀ k ∈ S, 2 ≤ k) : (∑ k ∈ S, r ^ k) ≤ r ^ 2 * (1 - r)⁻¹ := by
  have hsum : Summable (fun j : ℕ => r ^ j) := summable_geometric_of_lt_one hr0 hr1
  have hgeom := hasSum_geometric_of_lt_one hr0 hr1
  have hinj : Set.InjOn (fun k : ℕ => k - 2) (↑S) := by
    intro a ha b hb hab
    have ha2 := hS a ha
    have hb2 := hS b hb
    change a - 2 = b - 2 at hab
    omega
  have himage := Finset.sum_image (s := S) (g := fun k : ℕ => k - 2) (f := fun j : ℕ => r ^ j) hinj
  have htail : (∑ j ∈ S.image (fun k : ℕ => k - 2), r ^ j) ≤ ∑' j : ℕ, r ^ j :=
    hsum.sum_le_tsum (S.image (fun k : ℕ => k - 2))
      (by
        intro j hj
        exact pow_nonneg hr0 j)
  have hpow : ∀ k ∈ S, r ^ k = r ^ 2 * r ^ (k - 2) := by
    intro k hk
    have hk2 := hS k hk
    calc
      r ^ k = r ^ (2 + (k - 2)) := by
        congr 1; omega
      _ = r ^ 2 * r ^ (k - 2) := by rw [pow_add]
  calc
    _ = ∑ k ∈ S, r ^ 2 * r ^ (k - 2) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hpow k hk
    _ = r ^ 2 * ∑ k ∈ S, r ^ (k - 2) := by rw [← Finset.mul_sum]
    _ = r ^ 2 * ∑ j ∈ S.image (fun k : ℕ => k - 2), r ^ j := by rw [himage]
    _ ≤ r ^ 2 * ∑' j : ℕ, r ^ j := mul_le_mul_of_nonneg_left htail (sq_nonneg r)
    _ = r ^ 2 * (1 - r)⁻¹ := by rw [hgeom.tsum_eq]

/--
Inputs: a finite set of positive natural numbers.
Claim: the sum of `exp(-3 log p / 2)` over that set is bounded by the convergent natural
`3/2`-power series.
Proof: rewrite each exponential as an inverse real power and compare the finite sum with the full
summable series.
Role: bounds the prime-base part of the higher-prime-power exponential majorant uniformly in the
cutoff.
-/
theorem finite_sum_exp_neg_three_halves_log_le_tsum (P : Finset ℕ) (hP : ∀ p ∈ P, 1 ≤ p) :
    (∑ p ∈ P, Real.exp (-(3 / 2 : ℝ) * Real.log p)) ≤ ∑' n : ℕ, (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  have hthree : (1 : ℝ) < 3 / 2 := by norm_num only
  have hsum : Summable (fun n : ℕ => (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹)) :=
    (Real.summable_nat_rpow_inv (p := (3 / 2 : ℝ))).2 hthree
  have hnonneg : ∀ n : ℕ, 0 ≤ (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    intro n
    exact inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hrewrite :
    ∀ p : ℕ, 1 ≤ p → Real.exp (-(3 / 2 : ℝ) * Real.log p) = (((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    intro p hp
    have hppos : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
    calc
      _ = Real.exp (-(Real.log p * (3 / 2 : ℝ))) := by
        congr 1
        ring
      _ = (Real.exp (Real.log p * (3 / 2 : ℝ)))⁻¹ := by rw [Real.exp_neg]
      _ = _ := by rw [← Real.rpow_def_of_pos hppos]
  calc
    _ ≤ ∑ p ∈ P, (((p : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
      apply Finset.sum_le_sum
      intro p hp
      rw [hrewrite p (hP p hp)]
    _ ≤ ∑' n : ℕ, (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
      hsum.sum_le_tsum P
        (by
          intro n hn
          exact hnonneg n)

/--
Inputs: a finite set of prime bases and a finite set of exponents at least two.
Claim: the sum of `exp(-3 k log p / 4)` over their Cartesian product is bounded by an absolute
constant times the convergent natural `3/2`-power series.
Proof: sum the geometric exponent tail for each prime, compare its ratio with the ratio at two,
and bound the remaining prime sum by the full `3/2`-power series.
Role: gives a cutoff-independent bound for the higher-prime-power remainder majorant.
-/
theorem finite_prime_power_exp_sum_le_tsum (P K : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p)
    (hK : ∀ k ∈ K, 2 ≤ k) :
    (∑ p ∈ P, ∑ k ∈ K, Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p))) ≤
      (1 - Real.exp (-(3 / 4 : ℝ) * Real.log 2))⁻¹ * ∑' n : ℕ, (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
  let r : ℕ → ℝ := fun p => Real.exp (-(3 / 4 : ℝ) * Real.log p)
  let r₀ : ℝ := Real.exp (-(3 / 4 : ℝ) * Real.log 2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num only)
  have harg₀ : -(3 / 4 : ℝ) * Real.log 2 < 0 := by nlinarith only [hlog2]
  have hr₀lt : r₀ < 1 := by
    dsimp only [r₀]
    calc
      _ < Real.exp 0 := Real.exp_lt_exp.mpr harg₀
      _ = 1 := Real.exp_zero
  have hden₀ : 0 < 1 - r₀ := by linarith only [hr₀lt]
  have hC : 0 ≤ (1 - r₀)⁻¹ := inv_nonneg.mpr hden₀.le
  have hrbase : ∀ p ∈ P, 0 ≤ r p := by
    intro p hp
    dsimp only [r]
    exact (Real.exp_pos _).le
  have hrle : ∀ p ∈ P, r p ≤ r₀ := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast (hP p hp).two_le
    have hlogcmp : Real.log 2 ≤ Real.log p := Real.log_le_log (by norm_num only) hp2
    apply Real.exp_le_exp.mpr
    nlinarith only [hlogcmp]
  have hrlt : ∀ p ∈ P, r p < 1 := by
    intro p hp
    exact lt_of_le_of_lt (hrle p hp) hr₀lt
  have hexprep : ∀ p k : ℕ, Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p)) = r p ^ k := by
    intro p k
    calc
      _ = Real.exp ((k : ℝ) * (-(3 / 4 : ℝ) * Real.log p)) := by
        congr 1
        ring
      _ = Real.exp (-(3 / 4 : ℝ) * Real.log p) ^ k := Real.exp_nat_mul _ _
      _ = r p ^ k := by rfl
  have hrpow : ∀ p ∈ P, r p ^ 2 = Real.exp (-(3 / 2 : ℝ) * Real.log p) := by
    intro p hp
    dsimp only [r]
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hinner :
    ∀ p ∈ P,
      (∑ k ∈ K, Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p))) ≤
        (1 - r₀)⁻¹ * Real.exp (-(3 / 2 : ℝ) * Real.log p) := by
    intro p hp
    have hsum : (∑ k ∈ K, Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p))) = ∑ k ∈ K, r p ^ k := by
      apply Finset.sum_congr rfl
      intro k hk
      exact hexprep p k
    have htail := finset_sum_pow_geometric_tail (hrbase p hp) (hrlt p hp) K hK
    have hdenP : 0 < 1 - r p := by
      have hle := hrle p hp
      linarith only [hle, hden₀]
    have hdenCmp : 1 - r₀ ≤ 1 - r p := by
      have hle := hrle p hp
      linarith only [hle]
    have hinv := one_div_le_one_div_of_le hden₀ hdenCmp
    have hinv' : (1 - r p)⁻¹ ≤ (1 - r₀)⁻¹ := by simpa only [one_div] using hinv
    calc
      _ = ∑ k ∈ K, r p ^ k := hsum
      _ ≤ r p ^ 2 * (1 - r p)⁻¹ := htail
      _ ≤ r p ^ 2 * (1 - r₀)⁻¹ := mul_le_mul_of_nonneg_left hinv' (sq_nonneg (r p))
      _ = (1 - r₀)⁻¹ * Real.exp (-(3 / 2 : ℝ) * Real.log p) := by
        rw [hrpow p hp]
        ring
  calc
    _ ≤ ∑ p ∈ P, ((1 - r₀)⁻¹ * Real.exp (-(3 / 2 : ℝ) * Real.log p)) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hinner p hp
    _ = (1 - r₀)⁻¹ * ∑ p ∈ P, Real.exp (-(3 / 2 : ℝ) * Real.log p) := by rw [Finset.mul_sum]
    _ ≤ (1 - r₀)⁻¹ * ∑' n : ℕ, (((n : ℝ) ^ (3 / 2 : ℝ))⁻¹) :=
      mul_le_mul_of_nonneg_left
        (finite_sum_exp_neg_three_halves_log_le_tsum P
          (by
            intro p hp
            exact (hP p hp).one_le))
        hC

/--
Inputs: a Dirichlet character, finite prime-base and exponent sets, and a finite subset of their
Cartesian product consisting of higher prime powers.
Claim: the normalized norm of the corresponding twisted Euler sum is bounded independently of
the finite subset by an absolute `3/2`-power series constant.
Proof: bound the subset sum by the full rectangular majorant and apply the cutoff-independent
exponential sum estimate.
Role: controls the higher-prime-power part of every finite differentiated Euler polynomial.
-/
theorem normalized_twisted_prime_power_sum_uniform_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {η σ : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (n : ℕ) (s : ℂ) (hs : s.re = σ)
    (P K : Finset ℕ) (hP : ∀ p ∈ P, Nat.Prime p) (hK : ∀ k ∈ K, 2 ≤ k) (S : Finset (ℕ × ℕ))
    (hS : ∀ x ∈ S, Nat.Prime x.1 ∧ 2 ≤ x.2) (hSPK : S ⊆ P.product K) :
    (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖∑ x ∈ S,
            LSeries.term
              (LSeries.logMul^[n]
                (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
              s (x.1 ^ x.2)‖ ≤
      ((n + 1 : ℝ) * (4 * η) ^ (n + 1)) *
        ((1 - Real.exp (-(3 / 4 : ℝ) * Real.log 2))⁻¹ * ∑' m : ℕ, (((m : ℝ) ^ (3 / 2 : ℝ))⁻¹)) := by
  let A : ℝ := (n + 1 : ℝ) * (4 * η) ^ (n + 1)
  have hnnonneg : 0 ≤ (n + 1 : ℝ) := by exact_mod_cast Nat.zero_le (n + 1)
  have hA : 0 ≤ A := mul_nonneg hnnonneg (pow_nonneg (mul_nonneg (by norm_num only) hη) _)
  let f : ℕ × ℕ → ℝ := fun x => Real.exp (-(3 / 4 : ℝ) * ((x.2 : ℝ) * Real.log x.1))
  have hSmajor : (∑ x ∈ S, f x) ≤ ∑ x ∈ P.product K, f x :=
    Finset.sum_le_sum_of_subset_of_nonneg hSPK
      (by
        intro x hx hxnot
        exact Real.exp_nonneg _)
  have hrectangle := finite_prime_power_exp_sum_le_tsum P K hP hK
  have hrect :
    (∑ x ∈ P.product K, f x) ≤
      (1 - Real.exp (-(3 / 4 : ℝ) * Real.log 2))⁻¹ * ∑' m : ℕ, (((m : ℝ) ^ (3 / 2 : ℝ))⁻¹) := by
    change (∑ x ∈ P ×ˢ K, f x) ≤ _
    calc
      _ = ∑ p ∈ P, ∑ k ∈ K, Real.exp (-(3 / 4 : ℝ) * ((k : ℝ) * Real.log p)) := by
        rw [Finset.sum_product]
      _ ≤ _ := hrectangle
  have hterm := normalized_twisted_prime_power_sum_bound χ hη hσ n s hs S hS
  calc
    _ ≤ ∑ x ∈ S, A * f x := by simpa only [A, f] using hterm
    _ = A * ∑ x ∈ S, f x := by rw [Finset.mul_sum]
    _ ≤ A * ∑ x ∈ P.product K, f x := mul_le_mul_of_nonneg_left hSmajor hA
    _ ≤
        A *
          ((1 - Real.exp (-(3 / 4 : ℝ) * Real.log 2))⁻¹ * ∑' m : ℕ, (((m : ℝ) ^ (3 / 2 : ℝ))⁻¹)) :=
      mul_le_mul_of_nonneg_left hrect hA

/--
Inputs: a Dirichlet character, a nonnegative normalization scale, a decay exponent at least one,
a derivative order, a complex evaluation point, and a finite Euler cutoff.
Claim: the normalized norm of the cutoff-bounded higher-prime-power Euler sum has a bound
independent of that cutoff.
Proof: expose its prime-base and exponent sets inside `range (cutoff + 1)` and apply the uniform
rectangular majorant.
Role: supplies a cutoff-independent error bound for the higher-prime-power part of the finite
differentiated Euler polynomial.
-/
theorem finite_twisted_prime_power_remainder_uniform_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {η σ : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (n : ℕ) (s : ℂ) (hs : s.re = σ)
    (cutoff : ℕ) :
    let S :=
      ((Finset.range (cutoff + 1)).product (Finset.range (cutoff + 1))).filter
        (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ 2 ≤ x.2 ∧ x.1 ^ x.2 ≤ cutoff)
    (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖∑ x ∈ S,
            LSeries.term
              (LSeries.logMul^[n]
                (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
              s (x.1 ^ x.2)‖ ≤
      ((n + 1 : ℝ) * (4 * η) ^ (n + 1)) *
        ((1 - Real.exp (-(3 / 4 : ℝ) * Real.log 2))⁻¹ * ∑' m : ℕ, (((m : ℝ) ^ (3 / 2 : ℝ))⁻¹)) := by
  dsimp only
  let P := (Finset.range (cutoff + 1)).filter Nat.Prime
  let K := (Finset.range (cutoff + 1)).filter (fun k => 2 ≤ k)
  let S :=
    ((Finset.range (cutoff + 1)).product (Finset.range (cutoff + 1))).filter
      (fun x : ℕ × ℕ => Nat.Prime x.1 ∧ 2 ≤ x.2 ∧ x.1 ^ x.2 ≤ cutoff)
  have hP : ∀ p ∈ P, Nat.Prime p := by
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hK : ∀ k ∈ K, 2 ≤ k := by
    intro k hk
    exact (Finset.mem_filter.mp hk).2
  have hS : ∀ x ∈ S, Nat.Prime x.1 ∧ 2 ≤ x.2 := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨_, ⟨hp, hk, _⟩⟩
    exact ⟨hp, hk⟩
  have hSPK : S ⊆ P.product K := by
    intro x hx
    rcases Finset.mem_filter.mp hx with ⟨hprod, ⟨hp, hk, _⟩⟩
    rcases Finset.mem_product.mp hprod with ⟨hpRange, hkRange⟩
    apply Finset.mem_product.mpr
    constructor
    · exact Finset.mem_filter.mpr ⟨hpRange, hp⟩
    · exact Finset.mem_filter.mpr ⟨hkRange, hk⟩
  exact normalized_twisted_prime_power_sum_uniform_bound χ hη hσ n s hs P K hP hK S hS hSPK

/--
Inputs: a primitive Dirichlet character, a nonnegative normalization scale, a decay exponent at
least one, a derivative order, an evaluation point, and a finite Euler cutoff.
Claim: after subtracting the prime terms, the normalized finite differentiated Euler polynomial
has a cutoff-independent bound.
Proof: identify the difference with the prime-power pair sum and apply its uniform estimate.
Role: attaches the higher-prime-power error bound to the full finite von Mangoldt polynomial.
-/
theorem finite_vonMangoldt_prime_power_remainder_uniform_bound {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {η σ : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (n : ℕ) (s : ℂ) (hs : s.re = σ)
    (cutoff : ℕ) :
    (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖(∑ j ∈ Finset.range (cutoff + 1),
              LSeries.term
                (LSeries.logMul^[n]
                  (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
                s j) -
            (∑ p ∈ (Finset.range (cutoff + 1)).filter Nat.Prime,
              LSeries.term
                (LSeries.logMul^[n]
                  (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
                s p)‖ ≤
      ((n + 1 : ℝ) * (4 * η) ^ (n + 1)) *
        ((1 - Real.exp (-(3 / 4 : ℝ) * Real.log 2))⁻¹ * ∑' m : ℕ, (((m : ℝ) ^ (3 / 2 : ℝ))⁻¹)) := by
  rw [finite_vonMangoldt_prime_power_remainder_eq]
  exact finite_twisted_prime_power_remainder_uniform_bound χ hη hσ n s hs cutoff

/--
Definition: a fixed majorant for the higher-prime-power Euler remainder, enlarged to be at least
one.

Role: gives a single constant whose growth can be absorbed by a sufficiently high derivative order.
-/
noncomputable def higherPrimePowerEulerMajorantConstant : ℝ :=
  max 1 ((1 - Real.exp (-(3 / 4 : ℝ) * Real.log 2))⁻¹ * ∑' j : ℕ, (((j : ℝ) ^ (3 / 2 : ℝ))⁻¹))

/--
Input: a derivative exponent at least the ceiling of the logarithm of the fixed prime-power
majorant.
Claim: the prime-power majorant is at most the exponential of that exponent.
Proof: compare logarithms and apply monotonicity of the exponential.
Role: absorbs the fixed majorant into the derivative-order exponential loss.
-/
theorem higherPrimePowerEulerMajorantConstant_le_exp (m : ℕ)
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ m) :
    higherPrimePowerEulerMajorantConstant ≤ Real.exp (m : ℝ) := by
  have hlogceil :
    Real.log higherPrimePowerEulerMajorantConstant ≤
      (Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) : ℝ) :=
    Nat.le_ceil _
  have hceilm : (Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hlog : Real.log higherPrimePowerEulerMajorantConstant ≤ (m : ℝ) := le_trans hlogceil hceilm
  have hpos : 0 < higherPrimePowerEulerMajorantConstant := by
    dsimp only [higherPrimePowerEulerMajorantConstant]
    exact lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  calc
    higherPrimePowerEulerMajorantConstant =
        Real.exp (Real.log higherPrimePowerEulerMajorantConstant) :=
      (Real.exp_log hpos).symm
    _ ≤ Real.exp (m : ℝ) := Real.exp_le_exp.mpr hlog

/--
Inputs: nonnegative `D` and `η`, a scale inequality for `4η`, and natural orders `K ≤ m`.
Claim: the fixed majorant times `m (4η)^m` is at most one quarter of `exp(-D K)`.
Proof: absorb the linear factor and majorant by `exp(m)`, then use the five-unit margin in the
scale inequality.
Role: makes the higher-prime-power contribution smaller than the detected finite Euler signal.
-/
theorem detector_scale_absorbs_linear_power {C D η : ℝ} {m K : ℕ} (hD : 0 ≤ D) (hη : 0 ≤ η)
    (hηratio : 4 * η ≤ Real.exp (-(D + 5))) (hm : 1 ≤ m) (hKm : K ≤ m)
    (hCexp : C ≤ Real.exp (m : ℝ)) : C * (m : ℝ) * (4 * η) ^ m ≤ Real.exp (-(D * (K : ℝ))) / 4 := by
  have hmreal : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hmexp : (m : ℝ) ≤ Real.exp (m : ℝ) := by
    calc
      (m : ℝ) ≤ (m : ℝ) + 1 := by exact le_add_of_nonneg_right (by norm_num only)
      _ ≤ Real.exp (m : ℝ) := Real.add_one_le_exp _
  have hpower : (4 * η) ^ m ≤ Real.exp (-((D + 5) * (m : ℝ))) := by
    calc
      (4 * η) ^ m ≤ (Real.exp (-(D + 5))) ^ m :=
        pow_le_pow_left₀ (mul_nonneg (by norm_num only) hη) hηratio m
      _ = Real.exp (-((D + 5) * (m : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hprod : C * (m : ℝ) ≤ Real.exp (2 * (m : ℝ)) := by
    calc
      C * (m : ℝ) ≤ Real.exp (m : ℝ) * Real.exp (m : ℝ) :=
        mul_le_mul hCexp hmexp (Nat.cast_nonneg m) (Real.exp_nonneg _)
      _ = Real.exp (2 * (m : ℝ)) := by
        rw [← Real.exp_add]; congr 1; ring
  have htotal : C * (m : ℝ) * (4 * η) ^ m ≤ Real.exp (-(D + 3) * (m : ℝ)) := by
    calc
      _ ≤ Real.exp (2 * (m : ℝ)) * Real.exp (-((D + 5) * (m : ℝ))) :=
        mul_le_mul hprod hpower (pow_nonneg (mul_nonneg (by norm_num only) hη) m)
          (Real.exp_nonneg _)
      _ = _ := by
        rw [← Real.exp_add]; congr 1; ring
  have hDkm : D * (K : ℝ) ≤ D * (m : ℝ) := mul_le_mul_of_nonneg_left (by exact_mod_cast hKm) hD
  have hm3 : 3 ≤ 3 * (m : ℝ) := by
    calc
      (3 : ℝ) = 3 * 1 := by ring
      _ ≤ 3 * (m : ℝ) := mul_le_mul_of_nonneg_left hmreal (by norm_num only)
  have harg : -(D + 3) * (m : ℝ) ≤ -(D * (K : ℝ)) - 3 := by nlinarith only [hDkm, hm3]
  have h4 : 4 ≤ Real.exp 3 := by
    calc
      (4 : ℝ) = 3 + 1 := by norm_num only
      _ ≤ Real.exp 3 := Real.add_one_le_exp 3
  have hInv : Real.exp (-3) ≤ (1 / 4 : ℝ) := by
    calc
      Real.exp (-3) = (Real.exp 3)⁻¹ := Real.exp_neg 3
      _ ≤ (4 : ℝ)⁻¹ := by
        simpa only [one_div] using (one_div_le_one_div_of_le (by norm_num only) h4)
      _ = 1 / 4 := by norm_num only [one_div]
  have htailExp : Real.exp (-(D * (K : ℝ)) - 3) ≤ Real.exp (-(D * (K : ℝ))) / 4 := by
    calc
      _ = Real.exp (-(D * (K : ℝ))) * Real.exp (-3) := by
        rw [show -(D * (K : ℝ)) - 3 = -(D * (K : ℝ)) + (-3) by ring, Real.exp_add]
      _ ≤ Real.exp (-(D * (K : ℝ))) * (1 / 4 : ℝ) :=
        mul_le_mul_of_nonneg_left hInv (Real.exp_nonneg _)
      _ = _ := by ring
  exact le_trans htotal (le_trans (Real.exp_le_exp.mpr harg) htailExp)

/--
Inputs: a primitive character, an evaluation point with real part at least one, a derivative order,
and scale parameters satisfying the exponential smallness condition.
Claim: the normalized difference between the finite Euler polynomial and its prime part is at most
one quarter of the detector signal `exp(-D K)`.
Proof: combine the cutoff-uniform remainder estimate with the scalar absorption bound.
Role: preserves at least one quarter of the finite detector signal when passing to prime terms.
-/
theorem finite_vonMangoldt_prime_power_remainder_le_detector_scale {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {η σ D : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (hD : 0 ≤ D) (n K cutoff : ℕ)
    (hKm : K ≤ n + 1) (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ n + 1) (s : ℂ)
    (hσs : s.re = σ) :
    (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖(∑ j ∈ Finset.range (cutoff + 1),
              LSeries.term
                (LSeries.logMul^[n]
                  (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
                s j) -
            (∑ p ∈ (Finset.range (cutoff + 1)).filter Nat.Prime,
              LSeries.term
                (LSeries.logMul^[n]
                  (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
                s p)‖ ≤
      Real.exp (-(D * (K : ℝ))) / 4 := by
  have hrem := finite_vonMangoldt_prime_power_remainder_uniform_bound χ hη hσ n s hσs cutoff
  have hCexp : higherPrimePowerEulerMajorantConstant ≤ Real.exp ((n + 1 : ℕ) : ℝ) :=
    higherPrimePowerEulerMajorantConstant_le_exp (n + 1) hm
  have hn : 1 ≤ n + 1 := by omega
  have hscale := detector_scale_absorbs_linear_power hD hη hηratio hn hKm hCexp
  have hCmajor :
    (1 - Real.exp (-(3 / 4 : ℝ) * Real.log 2))⁻¹ * ∑' j : ℕ, (((j : ℝ) ^ (3 / 2 : ℝ))⁻¹) ≤
      higherPrimePowerEulerMajorantConstant := by
    dsimp only [higherPrimePowerEulerMajorantConstant]
    exact le_max_right 1 _
  have hcast : ((n + 1 : ℝ)) = ((n + 1 : ℕ) : ℝ) := by norm_num only [Nat.cast_add, Nat.cast_one]
  rw [hcast] at hrem
  have hfactor : 0 ≤ ((n + 1 : ℕ) : ℝ) * (4 * η) ^ (n + 1) :=
    mul_nonneg (Nat.cast_nonneg (n + 1))
      (pow_nonneg (mul_nonneg (show (0 : ℝ) ≤ 4 by norm_num only) hη) _)
  calc
    _ ≤ ((n + 1 : ℕ) : ℝ) * (4 * η) ^ (n + 1) * higherPrimePowerEulerMajorantConstant := by
      exact le_trans hrem (mul_le_mul_of_nonneg_left hCmajor hfactor)
    _ ≤ Real.exp (-(D * (K : ℝ))) / 4 := by
      calc
        _ = higherPrimePowerEulerMajorantConstant * ((n + 1 : ℕ) : ℝ) * (4 * η) ^ (n + 1) := by ring
        _ ≤ _ := hscale

/--
Inputs: a complex finite sum, its selected prime part, a nonnegative normalization, and upper and
lower bounds for the omitted part and the full sum.
Claim: if the full sum has half the signal and the omitted part uses at most one quarter, the prime
part retains at least one quarter.
Proof: apply the triangle inequality to `F = (F - P) + P` and rearrange the scaled bounds.
Role: transfers the finite Euler detector to the prime polynomial used by the hybrid estimate.
-/
theorem norm_subtract_error_preserves_quarter_signal {F P : ℂ} {A signal : ℝ} (hA : 0 ≤ A)
    (hfull : signal / 2 ≤ A * ‖F‖) (herror : A * ‖F - P‖ ≤ signal / 4) : signal / 4 ≤ A * ‖P‖ := by
  have htriangle : ‖F‖ ≤ ‖F - P‖ + ‖P‖ := by
    calc
      _ = ‖(F - P) + P‖ := by
        congr 1; ring
      _ ≤ _ := norm_add_le _ _
  have hscaled := mul_le_mul_of_nonneg_left htriangle hA
  have hcombined : signal / 2 ≤ A * ‖F - P‖ + A * ‖P‖ := by
    calc
      _ ≤ A * ‖F‖ := hfull
      _ ≤ _ := hscaled
      _ = _ := by rw [mul_add]
  nlinarith only [hcombined, herror]

/--
Inputs: a primitive character, a finite Euler cutoff, an evaluation point, and a detector signal
whose prime-power remainder satisfies the exponential scale condition.
Claim: the finite prime part retains at least one quarter of the signal when the full Euler
polynomial has at least half the signal.
Proof: derive the prime-power error bound and apply the triangle-inequality transfer.
Role: supplies a pointwise positive input for the finite prime-polynomial hybrid estimate.
-/
theorem finite_vonMangoldt_prime_sum_norm_ge_of_detector_signal {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {η σ D : ℝ} (hη : 0 ≤ η) (hσ : 1 ≤ σ) (hD : 0 ≤ D) (n K cutoff : ℕ)
    (hKm : K ≤ n + 1) (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ n + 1) (s : ℂ)
    (hσs : s.re = σ)
    (hfull :
      Real.exp (-(D * (K : ℝ))) / 2 ≤
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          ‖∑ j ∈ Finset.range (cutoff + 1),
              LSeries.term
                (LSeries.logMul^[n]
                  (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
                s j‖) :
    Real.exp (-(D * (K : ℝ))) / 4 ≤
      (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖∑ p ∈ (Finset.range (cutoff + 1)).filter Nat.Prime,
            LSeries.term
              (LSeries.logMul^[n]
                (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
              s p‖ := by
  let A : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  let F : ℂ :=
    ∑ j ∈ Finset.range (cutoff + 1),
      LSeries.term
        (LSeries.logMul^[n] (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ))) s
        j
  let P : ℂ :=
    ∑ p ∈ (Finset.range (cutoff + 1)).filter Nat.Prime,
      LSeries.term
        (LSeries.logMul^[n] (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ))) s
        p
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact div_nonneg (pow_nonneg hη _) (Nat.cast_nonneg _)
  have hrem :=
    finite_vonMangoldt_prime_power_remainder_le_detector_scale χ hη hσ hD n K cutoff hKm hηratio hm
      s hσs
  have hfull' : Real.exp (-(D * (K : ℝ))) / 2 ≤ A * ‖F‖ := by simpa only [A, F] using hfull
  have herror : A * ‖F - P‖ ≤ Real.exp (-(D * (K : ℝ))) / 4 := by simpa only [A, F, P] using hrem
  have hprime := norm_subtract_error_preserves_quarter_signal hA hfull' herror
  simpa only [A, P] using hprime

/--
Inputs: a prime cutoff, a derivative order, and a scale `η` with `0 < η ≤ 1`.
Claim: the normalized prime logarithmic polynomial through the cutoff is bounded by four times
the `n`th exponential-series coefficient at `η log P`.
Proof: factor each prime term into its exponential-series weight and its scaled von Mangoldt mass,
then apply the finite mass estimate.
Role: controls the low-prime part before transferring detector signal to the pre-sifted support.
-/
theorem finite_low_prime_normalized_log_sum_le (P n : ℕ) (hP : 2 ≤ P) {η : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) :
    (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
        (η ^ (n + 1) / (n.factorial : ℝ)) * (Real.log p) ^ (n + 1) / (p : ℝ) ^ (1 + η)) ≤
      4 * ((η * Real.log P) ^ n / (n.factorial : ℝ)) := by
  let S := (Finset.range (P + 1)).filter Nat.Prime
  let mass : ℕ → ℝ := fun p => η * (ArithmeticFunction.vonMangoldt p / (p : ℝ) ^ (1 + η))
  let C : ℝ := (η * Real.log P) ^ n / (n.factorial : ℝ)
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact div_nonneg (pow_nonneg (mul_nonneg hη.le hlogP) _) (Nat.cast_nonneg _)
  have hpoint (p : ℕ) (hp : p ∈ S) :
    (η ^ (n + 1) / (n.factorial : ℝ)) * (Real.log p) ^ (n + 1) / (p : ℝ) ^ (1 + η) ≤
      C * mass p := by
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hple : p ≤ P := Nat.le_of_lt_succ (Finset.mem_range.mp (Finset.mem_filter.mp hp).1)
    have hppos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
    have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hprime.one_le)
    have hlogle : Real.log p ≤ Real.log P := Real.log_le_log hppos (by exact_mod_cast hple)
    have hxle : η * Real.log p ≤ η * Real.log P := mul_le_mul_of_nonneg_left hlogle hη.le
    have hpow : (η * Real.log p) ^ n ≤ (η * Real.log P) ^ n :=
      pow_le_pow_left₀ (mul_nonneg hη.le hlogp) hxle n
    have hmass : ArithmeticFunction.vonMangoldt p = Real.log p :=
      ArithmeticFunction.vonMangoldt_apply_prime hprime
    have hfrac : (η * Real.log p) ^ n / (n.factorial : ℝ) ≤ C := by
      dsimp only [C]
      exact div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
    have hnum :
      (η ^ (n + 1) / (n.factorial : ℝ)) * (Real.log p) ^ (n + 1) =
        ((η * Real.log p) ^ n / (n.factorial : ℝ)) * (η * Real.log p) := by
      rw [pow_succ]
      ring
    have hmul : 0 ≤ η * Real.log p := mul_nonneg hη.le hlogp
    have hscaled := mul_le_mul_of_nonneg_right hfrac hmul
    have hscaled' :
      (η ^ (n + 1) / (n.factorial : ℝ)) * (Real.log p) ^ (n + 1) ≤
        C * (η * ArithmeticFunction.vonMangoldt p) := by
      calc
        _ = ((η * Real.log p) ^ n / (n.factorial : ℝ)) * (η * Real.log p) := hnum
        _ ≤ C * (η * Real.log p) := hscaled
        _ = C * (η * ArithmeticFunction.vonMangoldt p) := by rw [hmass]
    have hden : 0 < (p : ℝ) ^ (1 + η) := Real.rpow_pos_of_pos hppos _
    have hdiv := div_le_div_of_nonneg_right hscaled' hden.le
    simpa only [mass, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hdiv
  have hsum :
    (∑ p ∈ S, (η ^ (n + 1) / (n.factorial : ℝ)) * (Real.log p) ^ (n + 1) / (p : ℝ) ^ (1 + η)) ≤
      C * ∑ p ∈ S, mass p := by
    calc
      _ ≤ ∑ p ∈ S, C * mass p := by
        apply Finset.sum_le_sum
        intro p hp
        exact hpoint p hp
      _ = C * ∑ p ∈ S, mass p := by rw [Finset.mul_sum]
  have hsubset : S ⊆ Finset.range (P + 1) := by
    intro p hp
    exact (Finset.mem_filter.mp hp).1
  have hmass : (∑ p ∈ S, mass p) ≤ ∑ p ∈ Finset.range (P + 1), mass p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro p hp hnot
    dsimp only [mass]
    exact
      mul_nonneg hη.le
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _))
  have hmassbound :=
    PseudoPrime.AnalyticNumberTheory.Arithmetic.eta_mul_finite_vonMangoldt_sum_le_four P hη hη1
  have hmasssum :
    (∑ p ∈ Finset.range (P + 1), mass p) =
      η * ∑ p ∈ Finset.range (P + 1), ArithmeticFunction.vonMangoldt p / (p : ℝ) ^ (1 + η) := by
    dsimp only [mass]
    rw [Finset.mul_sum]
  have hfinal := mul_le_mul_of_nonneg_left hmass hC
  calc
    _ ≤ C * ∑ p ∈ Finset.range (P + 1), mass p := le_trans hsum hfinal
    _ ≤ 4 * C := by
      rw [hmasssum]; nlinarith only [hmassbound, hC]
    _ = _ := by dsimp only [C]

/--
Inputs: a prime cutoff, derivative order, scale `η`, and a coefficient `c` bounding `η log P` by
`c n`.
Claim: the normalized low-prime sum is at most `4 c^n exp(n)`.
Proof: apply the finite mass bound and `Real.pow_div_factorial_le_exp` to the factorial quotient.
Role: makes the low-prime loss exponentially small when `c` is chosen below `exp(-1)`.
-/
theorem finite_low_prime_normalized_log_sum_le_exp (P n : ℕ) (hP : 2 ≤ P) {η c : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (hc : 0 ≤ c) (hscale : η * Real.log P ≤ c * (n : ℝ)) :
    (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
        (η ^ (n + 1) / (n.factorial : ℝ)) * (Real.log p) ^ (n + 1) / (p : ℝ) ^ (1 + η)) ≤
      4 * (c ^ n * Real.exp (n : ℝ)) := by
  have hlogP : 0 ≤ Real.log P := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ P))
  have hx : 0 ≤ η * Real.log P := mul_nonneg hη.le hlogP
  have hpow : (η * Real.log P) ^ n ≤ (c * (n : ℝ)) ^ n := pow_le_pow_left₀ hx hscale n
  have hdiv : (η * Real.log P) ^ n / (n.factorial : ℝ) ≤ (c * (n : ℝ)) ^ n / (n.factorial : ℝ) :=
    div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _)
  have hfactor :
    (c * (n : ℝ)) ^ n / (n.factorial : ℝ) = c ^ n * ((n : ℝ) ^ n / (n.factorial : ℝ)) := by ring
  have hseries : (n : ℝ) ^ n / (n.factorial : ℝ) ≤ Real.exp (n : ℝ) :=
    Real.pow_div_factorial_le_exp (n : ℝ) (Nat.cast_nonneg n) n
  have hcoeff : (η * Real.log P) ^ n / (n.factorial : ℝ) ≤ c ^ n * Real.exp (n : ℝ) := by
    calc
      _ ≤ (c * (n : ℝ)) ^ n / (n.factorial : ℝ) := hdiv
      _ = c ^ n * ((n : ℝ) ^ n / (n.factorial : ℝ)) := hfactor
      _ ≤ _ := mul_le_mul_of_nonneg_left hseries (pow_nonneg hc n)
  have hlow := finite_low_prime_normalized_log_sum_le P n hP hη hη1
  exact le_trans hlow (mul_le_mul_of_nonneg_left hcoeff (by norm_num))

/--
Inputs: a requested detector order, a derivative order, and the exponential detector constant.
Claim: if the requested order is sufficiently large and the derivative order is at least one less,
then the factorial-decay estimate has enough margin to absorb the low-prime loss.
Proof: compare the derivative order with the detector order and use the requested-order bound.
Role: aligns the $K \le n+1$ order relation from zero detection with the low-prime exponential
estimate.
-/
theorem detector_order_exponential_margin (Krequested n K : ℕ) (D : ℝ) (hD : 0 ≤ D)
    (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ)) (hn : Krequested - 1 ≤ n)
    (hKorder : K ≤ n + 1) : D * (K : ℝ) + 5 ≤ (D + 5) * (n : ℝ) := by
  have hnReal : ((Krequested - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  have hKminus : (K : ℝ) - n ≤ 1 := by
    have hKcast : (K : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hKorder
    linarith only [hKcast]
  have hDdiff : D * ((K : ℝ) - n) ≤ D := by
    calc
      D * ((K : ℝ) - n) ≤ D * 1 := mul_le_mul_of_nonneg_left hKminus hD
      _ = D := by ring
  have hN : D + 5 ≤ 5 * (n : ℝ) := by
    calc
      D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ) := hDrequested
      _ ≤ 5 * (n : ℝ) := by nlinarith only [hnReal]
  nlinarith only [hDdiff, hN]

/--
Inputs: a prime cutoff, derivative order, detector scale, and an exponential-series coefficient
bound with an explicit exponent margin.
Claim: the normalized low-prime coefficient sum is at most one eighth of the detector signal.
Proof: convert `c^n exp(n)` to `(c exp(1))^n` and apply the supplied exponent margin.
Role: reserves positive signal for primes above the pre-sifting cutoff.
-/
theorem finite_low_prime_sum_detector_scale (P n K : ℕ) (hP : 2 ≤ P) {η c D : ℝ} (hη : 0 < η)
    (hη1 : η ≤ 1) (hc : 0 ≤ c) (hmargin : D * (K : ℝ) + 5 ≤ (D + 5) * (n : ℝ))
    (hscale : η * Real.log P ≤ c * (n : ℝ)) (hcexp : c * Real.exp 1 ≤ Real.exp (-(D + 5))) :
    (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
        (η ^ (n + 1) / (n.factorial : ℝ)) * (Real.log p) ^ (n + 1) / (p : ℝ) ^ (1 + η)) ≤
      Real.exp (-(D * (K : ℝ))) / 8 := by
  have hlow := finite_low_prime_normalized_log_sum_le_exp P n hP hη hη1 hc hscale
  have hcexp_nonneg : 0 ≤ c * Real.exp 1 := mul_nonneg hc (Real.exp_nonneg _)
  have hpower : (c * Real.exp 1) ^ n ≤ Real.exp (-((D + 5) * (n : ℝ))) := by
    calc
      (c * Real.exp 1) ^ n ≤ (Real.exp (-(D + 5))) ^ n := pow_le_pow_left₀ hcexp_nonneg hcexp n
      _ = Real.exp (-((D + 5) * (n : ℝ))) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hexpn : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
    rw [show (n : ℝ) = (n : ℝ) * (1 : ℝ) by ring, ← Real.exp_nat_mul]
  have hproduct : c ^ n * Real.exp (n : ℝ) = (c * Real.exp 1) ^ n := by rw [hexpn, ← mul_pow]
  have hlow' : 4 * (c ^ n * Real.exp (n : ℝ)) ≤ 4 * Real.exp (-(D * (K : ℝ)) - 5) := by
    calc
      _ = 4 * (c * Real.exp 1) ^ n := by rw [hproduct]
      _ ≤ 4 * Real.exp (-((D + 5) * (n : ℝ))) := mul_le_mul_of_nonneg_left hpower (by norm_num)
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.exp_le_exp.mpr (by nlinarith only [hmargin])
        · norm_num
  have hexp1 : (2 : ℝ) ≤ Real.exp 1 := by
    calc
      (2 : ℝ) = 1 + 1 := by norm_num
      _ ≤ Real.exp 1 := Real.add_one_le_exp 1
  have hexp5 : 32 ≤ Real.exp 5 := by
    have hpow : (2 : ℝ) ^ 5 ≤ Real.exp 1 ^ 5 := pow_le_pow_left₀ (by norm_num) hexp1 5
    have hexp : Real.exp 1 ^ 5 = Real.exp 5 := by
      rw [show (5 : ℝ) = (5 : ℝ) * (1 : ℝ) by ring, ← Real.exp_nat_mul]
      norm_num
    rw [hexp] at hpow
    norm_num at hpow ⊢
    exact hpow
  have hinv : Real.exp (-5) ≤ (1 / 32 : ℝ) := by
    rw [Real.exp_neg]
    simpa only [one_div] using one_div_le_one_div_of_le (by norm_num) hexp5
  calc
    _ ≤ 4 * Real.exp (-(D * (K : ℝ)) - 5) := le_trans hlow hlow'
    _ = 4 * Real.exp (-(D * (K : ℝ))) * Real.exp (-5) := by
      rw [show -(D * (K : ℝ)) - 5 = -(D * (K : ℝ)) + (-5) by ring, Real.exp_add]
      ring
    _ ≤ 4 * Real.exp (-(D * (K : ℝ))) * (1 / 32) := mul_le_mul_of_nonneg_left hinv (by positivity)
    _ = Real.exp (-(D * (K : ℝ))) / 8 := by ring

/--
Inputs: a character, prime cutoff, derivative order, evaluation point, and the scale conditions for
the low-prime loss.
Claim: the normalized norm of the twisted prime sum through the cutoff is at most one eighth of
the detector signal.
Proof: apply the triangle inequality, bound each differentiated Euler term by its real prime
weight, and use the low-prime coefficient estimate.
Role: removes the low-prime part from the positive finite-prime detector before hybrid averaging.
-/
theorem finite_low_prime_twisted_sum_norm_le_detector_scale {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (P n K : ℕ) (hP : 2 ≤ P) {η c D : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    (hc : 0 ≤ c) (hmargin : D * (K : ℝ) + 5 ≤ (D + 5) * (n : ℝ))
    (hscale : η * Real.log P ≤ c * (n : ℝ)) (hcexp : c * Real.exp 1 ≤ Real.exp (-(D + 5))) (s : ℂ)
    (hs : s.re = 1 + η) :
    (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
            LSeries.term
              (LSeries.logMul^[n]
                (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
              s p‖ ≤
      Real.exp (-(D * (K : ℝ))) / 8 := by
  let S := (Finset.range (P + 1)).filter Nat.Prime
  let A : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  let f : ℕ → ℂ := fun p =>
    LSeries.term
      (LSeries.logMul^[n] (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ))) s p
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact div_nonneg (pow_nonneg hη.le _) (Nat.cast_nonneg _)
  have htriangle : ‖∑ p ∈ S, f p‖ ≤ ∑ p ∈ S, ‖f p‖ := norm_sum_le S f
  have hscaled := mul_le_mul_of_nonneg_left htriangle hA
  have hscaled' : A * ‖∑ p ∈ S, f p‖ ≤ ∑ p ∈ S, A * ‖f p‖ := by
    calc
      _ ≤ A * ∑ p ∈ S, ‖f p‖ := hscaled
      _ = _ := by rw [Finset.mul_sum]
  have hterm (p : ℕ) (hp : p ∈ S) : A * ‖f p‖ ≤ A * (Real.log p) ^ (n + 1) / (p : ℝ) ^ (1 + η) := by
    have hprime : Nat.Prime p := (Finset.mem_filter.mp hp).2
    have hlogΛ : ArithmeticFunction.vonMangoldt p = Real.log p :=
      ArithmeticFunction.vonMangoldt_apply_prime hprime
    have hbound := twistedVonMangoldt_log_term_bound χ n p (s := s) hprime.pos
    rw [hs, hlogΛ] at hbound
    have hfactor : Real.log p * (Real.log p) ^ n = (Real.log p) ^ (n + 1) := by
      rw [pow_succ]
      ring
    calc
      _ ≤ A * (Real.log p * (Real.log p) ^ n / (p : ℝ) ^ (1 + η)) := by
        dsimp only [f]
        exact mul_le_mul_of_nonneg_left hbound hA
      _ = _ := by
        rw [hfactor]; ring
  have hsum :
    (η ^ (n + 1) / (n.factorial : ℝ)) * ‖∑ p ∈ S, f p‖ ≤
      ∑ p ∈ S, (η ^ (n + 1) / (n.factorial : ℝ)) * (Real.log p) ^ (n + 1) / (p : ℝ) ^ (1 + η) := by
    calc
      _ = A * ‖∑ p ∈ S, f p‖ := by dsimp only [A]
      _ ≤ ∑ p ∈ S, A * ‖f p‖ := hscaled'
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        simpa only [A, f] using hterm p hp
  have hlow := finite_low_prime_sum_detector_scale P n K hP hη hη1 hc hmargin hscale hcexp
  calc
    _ ≤ _ := by simpa only [S] using hsum
    _ ≤ _ := hlow

/--
Inputs: a detector signal on the complete prime sum through a finite cutoff, a smaller low-prime
cutoff, and the exponential loss conditions.
Claim: the prime sum over indices above the low-prime cutoff retains at least one eighth of the
detector signal.
Proof: split the finite prime set at `P`, bound the low part by the scaled von Mangoldt mass, and
apply the triangle inequality to remove it from the complete prime sum.
Role: gives a positive input supported above the cutoff required by the hybrid large sieve.
-/
theorem finite_high_prime_sum_norm_ge_of_low_prime_removal {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (P cutoff n K : ℕ) (hP : 2 ≤ P) (hPcut : P ≤ cutoff) {η c D : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hc : 0 ≤ c) (hmargin : D * (K : ℝ) + 5 ≤ (D + 5) * (n : ℝ))
    (hscale : η * Real.log P ≤ c * (n : ℝ)) (hcexp : c * Real.exp 1 ≤ Real.exp (-(D + 5))) (s : ℂ)
    (hs : s.re = 1 + η)
    (hfull :
      Real.exp (-(D * (K : ℝ))) / 4 ≤
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          ‖∑ p ∈ (Finset.range (cutoff + 1)).filter Nat.Prime,
              LSeries.term
                (LSeries.logMul^[n]
                  (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
                s p‖) :
    Real.exp (-(D * (K : ℝ))) / 8 ≤
      (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖∑ p ∈ ((Finset.range (cutoff + 1)).filter Nat.Prime).filter (fun p => ¬p ≤ P),
            LSeries.term
              (LSeries.logMul^[n]
                (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ)))
              s p‖ := by
  classical
  let T := (Finset.range (cutoff + 1)).filter Nat.Prime
  let L := (Finset.range (P + 1)).filter Nat.Prime
  let H := T.filter (fun p => ¬p ≤ P)
  let A : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  let f : ℕ → ℂ := fun p =>
    LSeries.term
      (LSeries.logMul^[n] (fun j : ℕ ↦ χ (j : ZMod N) * (ArithmeticFunction.vonMangoldt j : ℂ))) s p
  let F : ℂ := ∑ p ∈ T, f p
  let low : ℂ := ∑ p ∈ L, f p
  let high : ℂ := ∑ p ∈ H, f p
  have hLow : L = T.filter (fun p => p ≤ P) := by
    ext p
    simp only [L, T, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hp, hprime⟩
      have hpP : p ≤ P := by omega
      exact ⟨⟨by omega, hprime⟩, hpP⟩
    · rintro ⟨⟨hp, hprime⟩, hpP⟩
      exact ⟨by omega, hprime⟩
  have hdecomp : F = low + high := by
    dsimp only [F, low, high, H]
    rw [hLow]
    simpa only [Finset.filter_filter] using
      (Finset.sum_filter_add_sum_filter_not T (fun p => p ≤ P) f).symm
  have hA : 0 ≤ A := by
    dsimp only [A]
    exact div_nonneg (pow_nonneg hη.le _) (Nat.cast_nonneg _)
  have hlow :=
    finite_low_prime_twisted_sum_norm_le_detector_scale χ P n K hP hη hη1 hc hmargin hscale hcexp s
      hs
  have hlow' : A * ‖low‖ ≤ Real.exp (-(D * (K : ℝ))) / 8 := by simpa only [A, low, L, f] using hlow
  have hfull' : (Real.exp (-(D * (K : ℝ))) / 2) / 2 ≤ A * ‖F‖ := by
    have hrewrite : Real.exp (-(D * (K : ℝ))) / 4 = (Real.exp (-(D * (K : ℝ))) / 2) / 2 := by ring
    rw [hrewrite] at hfull
    simpa only [A, F, T, f] using hfull
  have herr : A * ‖F - high‖ ≤ (Real.exp (-(D * (K : ℝ))) / 2) / 4 := by
    rw [show F - high = low by
        rw [hdecomp]; ring]
    calc
      _ ≤ Real.exp (-(D * (K : ℝ))) / 8 := hlow'
      _ = (Real.exp (-(D * (K : ℝ))) / 2) / 4 := by ring
  have hresult := norm_subtract_error_preserves_quarter_signal hA hfull' herr
  calc
    _ = (Real.exp (-(D * (K : ℝ))) / 2) / 4 := by ring
    _ ≤ A * ‖high‖ := hresult
    _ = _ := by simp only [A, high, H, T, f]

/--
Inputs: a finite Euler detector signal, a low-prime cutoff, and quantitative bounds for the
prime-power and low-prime remainders.
Claim: the normalized prime polynomial supported above the low cutoff retains one eighth of the
detector signal.
Proof: transfer the finite Euler signal to all prime terms, then remove the low-prime part using
the scaled Mangoldt estimate.
Role: provides the pointwise high-prime input for the pre-sifted hybrid mean-square bound.
-/
theorem finite_high_prime_sum_norm_ge_of_detector_signal {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (P cutoff n K : ℕ) (hP : 2 ≤ P) (hPcut : P ≤ cutoff) {η D c : ℝ}
    (hη : 0 < η) (hη1 : η ≤ 1) (hD : 0 ≤ D) (hc : 0 ≤ c) (hKorder : K ≤ n + 1)
    (hmargin : D * (K : ℝ) + 5 ≤ (D + 5) * (n : ℝ)) (hscale : η * Real.log P ≤ c * (n : ℝ))
    (hcexp : c * Real.exp 1 ≤ Real.exp (-(D + 5))) (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ n + 1) (s : ℂ)
    (hs : s.re = 1 + η)
    (hfull :
      Real.exp (-(D * (K : ℝ))) / 2 ≤
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          ‖∑ j ∈ Finset.range (cutoff + 1),
              LSeries.term
                (LSeries.logMul^[n]
                  (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
                s j‖) :
    Real.exp (-(D * (K : ℝ))) / 8 ≤
      (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖∑ p ∈ ((Finset.range (cutoff + 1)).filter Nat.Prime).filter (fun p => ¬p ≤ P),
            LSeries.term
              (LSeries.logMul^[n]
                (fun k : ℕ ↦ χ (k : ZMod N) * (ArithmeticFunction.vonMangoldt k : ℂ)))
              s p‖ := by
  have hprime :=
    finite_vonMangoldt_prime_sum_norm_ge_of_detector_signal (σ := 1 + η) χ hη.le
      (by linarith only [hη]) hD n K cutoff hKorder hηratio hm s hs hfull
  exact
    finite_high_prime_sum_norm_ge_of_low_prime_removal χ P cutoff n K hP hPcut hη hη1 hc hmargin
      hscale hcexp s hs hprime

/-- A finite prime polynomial with logarithmic coefficient power `r + 1` is differentiable in
height, and its derivative is `-I` times the polynomial with coefficient power `r + 2`. The proof
represents the polynomial as a finite exponential sum and differentiates term by term. This
identity pairs the function and derivative energies required by the mesh sampling estimate. -/
theorem finite_prime_log_power_exponential_sum_hasDerivAt {s : Finset ℕ} (r : ℕ) (σ t : ℝ)
    (χ : ℕ → ℂ) :
    HasDerivAt
      (fun v : ℝ =>
        ∑ p ∈ s,
          (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
            Complex.exp ((-(v * Real.log p) : ℝ) * Complex.I) *
            χ p)
      (-Complex.I *
        (∑ p ∈ s,
          (((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
            Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I) *
            χ p))
      t := by
  let γ : ℕ → ℝ := fun p => -Real.log p
  let a : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ) * χ p
  have hf :
    (fun v : ℝ =>
        ∑ p ∈ s,
          (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
            Complex.exp ((-(v * Real.log p) : ℝ) * Complex.I) *
            χ p) =
      PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum s γ a := by
    funext v
    unfold PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum γ a
    apply Finset.sum_congr rfl
    intro p hp
    have hphase : Complex.I * (γ p : ℂ) * (v : ℂ) = ((-(v * Real.log p) : ℝ) : ℂ) * Complex.I := by
      dsimp only [γ]
      push_cast
      ring
    rw [hphase]
    ring
  have hsum := PseudoPrime.Analysis.ExponentialMeanSquare.hasDerivAt_exponentialSum s γ a t
  have hder := hsum.congr_of_eventuallyEq (Filter.Eventually.of_forall fun v => congrFun hf v)
  apply HasDerivAt.congr_deriv hder
  unfold PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum γ a
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hn : r + 2 = (r + 1) + 1 := by omega
  rw [hn]
  simp only [Complex.ofReal_neg]
  have hphase :
    Complex.I * (-(Real.log p : ℝ) : ℂ) * (t : ℂ) = ((-(t * Real.log p) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hphase]
  simp only [Complex.ofReal_neg]
  ring_nf

/-- The primitive-character mean square of a finite prime-log polynomial sampled on an equally
spaced height mesh is bounded by its height integral and the integral for the next logarithmic
power. Apply the scalar mesh estimate character by character and use the equality between the
derivative norm and the next-order mean square. This is the finite-family interface for the hybrid
large-sieve estimate. -/
theorem primitiveCharacterPrimeLogPower_grid_mean_square_bound (q : ℕ) (hq : 1 < q) (s : Finset ℕ)
    (r : ℕ) (σ a h : ℝ) (n : ℕ) (hh : 0 < h) :
    (h / 2) *
        (∑ k ∈ Finset.range n,
          primitiveCharacterPolynomialMeanSquare q hq s
            (fun p =>
              (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                Complex.exp ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))) ≤
      (∫ t in a..(a + (n : ℝ) * h),
          primitiveCharacterPolynomialMeanSquare q hq s
            (fun p =>
              (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I))) +
        (h ^ 2 / 2) *
          (∫ t in a..(a + (n : ℝ) * h),
            primitiveCharacterPolynomialMeanSquare q hq s
              (fun p =>
                (((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                  Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I))) := by
  classical
  let P := primitiveDirichletCharacterSet q
  let A : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  let B : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  let phase (t : ℝ) (p : ℕ) : ℂ := Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)
  let F (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ := ∑ p ∈ s, A p * phase t p * χ (p : ZMod q)
  let H (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ := ∑ p ∈ s, B p * phase t p * χ (p : ZMod q)
  let G (χ : DirichletCharacter ℂ q) (t : ℝ) : ℂ := -Complex.I * H χ t
  have hD (χ : DirichletCharacter ℂ q) (t : ℝ) : HasDerivAt (F χ) (G χ t) t := by
    dsimp only [F, G, H, A, B, phase]
    exact finite_prime_log_power_exponential_sum_hasDerivAt (s := s) r σ t (fun p => χ (p : ZMod q))
  have hnext (χ : DirichletCharacter ℂ q) (t : ℝ) :
    HasDerivAt (H χ)
      (-Complex.I *
        (∑ p ∈ s,
          (((Real.log p : ℝ) ^ (r + 3) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
            phase t p *
            χ (p : ZMod q)))
      t := by
    dsimp only [H, B, phase]
    exact
      finite_prime_log_power_exponential_sum_hasDerivAt (s := s) (r + 1) σ t
        (fun p => χ (p : ZMod q))
  have hFc : ∀ χ ∈ P, Continuous (F χ) := by
    intro χ hχ
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hD χ t).continuousAt
  have hHc : ∀ χ ∈ P, Continuous (H χ) := by
    intro χ hχ
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hnext χ t).continuousAt
  have hGc : ∀ χ ∈ P, Continuous (G χ) := by
    intro χ hχ
    dsimp only [G]
    exact continuous_const.mul (hHc χ hχ)
  have hgrid :=
    PseudoPrime.Analysis.uniform_grid_sum_norm_sq_le_integrals (s := P) (a := a) (h := h) (n := n)
      hh hFc hGc (fun χ hχ t => hD χ t)
  have hmeanF (t : ℝ) :
    primitiveCharacterPolynomialMeanSquare q hq s (fun p => A p * phase t p) =
      ∑ χ ∈ P, ‖F χ t‖ ^ 2 := by
    simp only [primitiveCharacterPolynomialMeanSquare, Complex.normSq_eq_norm_sq, P, F, A, phase]
  have hmeanH (t : ℝ) :
    primitiveCharacterPolynomialMeanSquare q hq s (fun p => B p * phase t p) =
      ∑ χ ∈ P, ‖H χ t‖ ^ 2 := by
    simp only [primitiveCharacterPolynomialMeanSquare, Complex.normSq_eq_norm_sq, P, H, B, phase]
  have hsample :
    (∑ k ∈ Finset.range n, ∑ χ ∈ P, ‖F χ (a + ((k : ℝ) + 1 / 2) * h)‖ ^ 2) =
      ∑ k ∈ Finset.range n,
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun p => A p * phase (a + ((k : ℝ) + 1 / 2) * h) p) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hmeanF]
  have hintF :
    (∫ t in a..(a + (n : ℝ) * h), ∑ χ ∈ P, ‖F χ t‖ ^ 2) =
      (∫ t in a..(a + (n : ℝ) * h),
        primitiveCharacterPolynomialMeanSquare q hq s (fun p => A p * phase t p)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hmeanF t).symm
  have hEqG (t : ℝ) :
    primitiveCharacterPolynomialMeanSquare q hq s (fun p => B p * phase t p) =
      ∑ χ ∈ P, ‖G χ t‖ ^ 2 := by
    rw [hmeanH]
    simp only [G, norm_mul, norm_neg, Complex.norm_I, one_mul]
  have hintG :
    (∫ t in a..(a + (n : ℝ) * h), ∑ χ ∈ P, ‖G χ t‖ ^ 2) =
      (∫ t in a..(a + (n : ℝ) * h),
        primitiveCharacterPolynomialMeanSquare q hq s (fun p => B p * phase t p)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact (hEqG t).symm
  rw [hsample, hintF, hintG] at hgrid
  simpa only [A, B, phase] using hgrid

/-- For any finite coefficient sequence, the primitive-character mean square of its height-twisted
Dirichlet polynomial is continuous in height. Expand the mean square as a finite sum of squared
norms, and use differentiability of each finite exponential sum to establish continuity. This
justifies interval integration and subinterval comparison in the hybrid connection. -/
theorem primitiveCharacterPolynomialMeanSquare_phase_continuous {q : ℕ} (hq : 1 < q) (s : Finset ℕ)
    (a : ℕ → ℂ) :
    Continuous
      (fun t : ℝ =>
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun p => a p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I))) := by
  classical
  let P := primitiveDirichletCharacterSet q
  let γ : ℕ → ℝ := fun p => -Real.log p
  let F (χ : DirichletCharacter ℂ q) (t : ℝ) :=
    PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum s γ (fun p => a p * χ (p : ZMod q)) t
  have hD (χ : DirichletCharacter ℂ q) (t : ℝ) :
    HasDerivAt (F χ)
      (PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum s γ
        (fun p => Complex.I * γ p * (a p * χ (p : ZMod q))) t)
      t := by
    dsimp only [F]
    exact
      PseudoPrime.Analysis.ExponentialMeanSquare.hasDerivAt_exponentialSum s γ
        (fun p => a p * χ (p : ZMod q)) t
  have hFc (χ : DirichletCharacter ℂ q) : Continuous (F χ) := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (hD χ t).continuousAt
  have hphase (t : ℝ) (p : ℕ) :
    Complex.I * (γ p : ℂ) * (t : ℂ) = ((-(t * Real.log p) : ℝ) : ℂ) * Complex.I := by
    dsimp only [γ]
    push_cast
    ring
  have hpoly (χ : DirichletCharacter ℂ q) (t : ℝ) :
    (∑ p ∈ s, a p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I) * χ (p : ZMod q)) =
      F χ t := by
    dsimp only [F, PseudoPrime.Analysis.ExponentialMeanSquare.exponentialSum]
    apply Finset.sum_congr rfl
    intro p hp
    rw [hphase]
    ring
  have hmean (t : ℝ) :
    primitiveCharacterPolynomialMeanSquare q hq s
        (fun p => a p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) =
      ∑ χ ∈ P, ‖F χ t‖ ^ 2 := by
    simp only [primitiveCharacterPolynomialMeanSquare, Complex.normSq_eq_norm_sq, P]
    apply Finset.sum_congr rfl
    intro χ hχ
    rw [hpoly]
  have hsum : Continuous (fun t : ℝ => ∑ χ ∈ P, ‖F χ t‖ ^ 2) := by
    apply continuous_finsetSum
    intro χ hχ
    exact (continuous_norm.comp (hFc χ)).pow 2
  have hEq :
    (fun t : ℝ =>
        primitiveCharacterPolynomialMeanSquare q hq s
          (fun p => a p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I))) =
      (fun t => ∑ χ ∈ P, ‖F χ t‖ ^ 2) := by
    funext t
    exact hmean t
  rw [hEq]
  exact hsum

/--
Inputs: a conductor parameter `R`, a height interval with `1 ≤ T ≤ 2R`, a derivative order, a
real part `σ`, and a finite prime set supported above `R^6`.
Claim: the prime polynomial with coefficient `log(p)^(r+1) * exp(-σ log p)` has mean square at
most `4096 / log R` times its coefficient energy weighted by `p`.
Proof: apply the general pre-sifted hybrid estimate at `Z = R^2`; the support condition makes
every prime factor exceed `Z`, and `R^4 T ≤ p` absorbs the height term.
Role: supplies the higher-derivative prime-polynomial estimate needed to separate prime terms from
higher prime powers in the zero-detection polynomial.
-/
theorem primitiveCharacterPrimeLogPowerMeanSquare_preSifted_hybrid_R_squared (R : ℕ) (hR : 2 ≤ R)
    (T : ℝ) (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) (r : ℕ) (σ : ℝ) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hlower : ∀ p ∈ s, R ^ 6 ≤ p) :
    (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
        ∫ t in Set.Icc (-T) T,
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
            (fun p =>
              (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) ≤
      (4096 : ℝ) / Real.log R *
        ∑ p ∈ s,
          ‖((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^ 2 *
            p := by
  classical
  let a : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  have hRgt : 1 < R := by omega
  have hR2ltR6 : R ^ 2 < R ^ 6 := Nat.pow_lt_pow_right hRgt (by omega : 2 < 6)
  have hrough : ∀ p ∈ s, ∀ v, Nat.Prime v → v ∣ p → R ^ 2 < v := by
    intro p hp v hv hdiv
    rcases (Nat.dvd_prime (hprime p hp)).mp hdiv with hvone | hvp
    · subst v
      exact False.elim (Nat.not_prime_one hv)
    · subst v
      exact lt_of_lt_of_le hR2ltR6 (hlower p hp)
  have hpos : ∀ p ∈ s, 0 < p := by
    intro p hp
    exact (hprime p hp).pos
  have hhybrid :=
    primitiveCharacterFamilyMeanSquare_preSifted_hybrid_R_squared R hR T hT s hpos a hrough
  have hRreal : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hR4T : (R : ℝ) ^ 4 * T ≤ (R : ℝ) ^ 6 := by
    calc
      (R : ℝ) ^ 4 * T ≤ (R : ℝ) ^ 4 * (2 * R) := mul_le_mul_of_nonneg_left hTupper (by positivity)
      _ = 2 * (R : ℝ) ^ 5 := by ring
      _ ≤ R * (R : ℝ) ^ 5 := mul_le_mul_of_nonneg_right hRreal (by positivity)
      _ = (R : ℝ) ^ 6 := by ring
  have henergy : ∀ p ∈ s, ‖a p‖ ^ 2 * ((p : ℝ) + (R : ℝ) ^ 4 * T) ≤ 2 * ‖a p‖ ^ 2 * p := by
    intro p hp
    have hplarge : (R : ℝ) ^ 6 ≤ p := by exact_mod_cast hlower p hp
    have hR4Tp : (R : ℝ) ^ 4 * T ≤ p := le_trans hR4T hplarge
    have hsum : (p : ℝ) + (R : ℝ) ^ 4 * T ≤ 2 * p := by linarith only [hR4Tp]
    calc
      _ ≤ ‖a p‖ ^ 2 * (2 * p) := mul_le_mul_of_nonneg_left hsum (sq_nonneg ‖a p‖)
      _ = 2 * ‖a p‖ ^ 2 * p := by ring
  have henergySum :
    (∑ p ∈ s, ‖a p‖ ^ 2 * ((p : ℝ) + (R : ℝ) ^ 4 * T)) ≤ 2 * ∑ p ∈ s, ‖a p‖ ^ 2 * p := by
    calc
      _ ≤ ∑ p ∈ s, 2 * ‖a p‖ ^ 2 * p := by
        apply Finset.sum_le_sum
        intro p hp
        exact henergy p hp
      _ = _ := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro p hp
        ring
  change
    (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
        ∫ t in Set.Icc (-T) T,
          primitiveCharacterPolynomialMeanSquare q.val
            (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
            (fun p =>
              a p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) ≤
      (4096 : ℝ) / Real.log R * ∑ p ∈ s, ‖a p‖ ^ 2 * p
  calc
    _ ≤ (2048 : ℝ) / Real.log R * ∑ p ∈ s, ‖a p‖ ^ 2 * ((p : ℝ) + (R : ℝ) ^ 4 * T) := hhybrid
    _ ≤ (2048 : ℝ) / Real.log R * (2 * ∑ p ∈ s, ‖a p‖ ^ 2 * p) :=
      mul_le_mul_of_nonneg_left henergySum (by positivity)
    _ = (4096 : ℝ) / Real.log R * ∑ p ∈ s, ‖a p‖ ^ 2 * p := by ring

/-- Sum the finite prime-log mesh estimate over a finite family of moduli and enlarge each
subinterval integral to a common height interval. Nonnegativity and continuity justify the
interval comparison for both the polynomial and its derivative. This prepares the family sum for
the pre-sifted hybrid estimate. -/
theorem primitiveCharacterPrimeLogPower_family_grid_mean_square_bound (α : Type) (Q : Finset α)
    (qmod : α → { q : ℕ // 1 < q }) (s : Finset ℕ) (r : ℕ) (σ a h T : ℝ) (n : ℕ) (hh : 0 < h)
    (ha : -T ≤ a) (hb : a + (n : ℝ) * h ≤ T) :
    (h / 2) *
        (∑ q ∈ Q,
          ∑ k ∈ Finset.range n,
            primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
              (fun p =>
                (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                  Complex.exp
                    ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))) ≤
      (∑ q ∈ Q,
          ∫ t in Set.Icc (-T) T,
            primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
              (fun p =>
                (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                  Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) +
        (h ^ 2 / 2) *
          (∑ q ∈ Q,
            ∫ t in Set.Icc (-T) T,
              primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
                (fun p =>
                  (((Real.log p : ℝ) ^ (r + 2) : ℂ) *
                      Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                    Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) := by
  classical
  let A : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  let B : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  calc
    _ =
        ∑ q ∈ Q,
          (h / 2) *
            (∑ k ∈ Finset.range n,
              primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
                (fun p =>
                  A p *
                    Complex.exp
                      ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))) :=
      by rw [Finset.mul_sum]
    _ ≤
        ∑ q ∈ Q,
          ((∫ t in a..(a + (n : ℝ) * h),
              primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
                (fun p => A p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I))) +
            (h ^ 2 / 2) *
              (∫ t in a..(a + (n : ℝ) * h),
                primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
                  (fun p => B p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)))) :=
      by
      apply Finset.sum_le_sum
      intro q hq
      simpa only [A, B] using
        primitiveCharacterPrimeLogPower_grid_mean_square_bound (qmod q).val (qmod q).property s r σ
          a h n hh
    _ ≤
        ∑ q ∈ Q,
          ((∫ t in Set.Icc (-T) T,
              primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
                (fun p =>
                  A p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) +
            (h ^ 2 / 2) *
              (∫ t in Set.Icc (-T) T,
                primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
                  (fun p =>
                    B p *
                      Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume)) :=
      by
      apply Finset.sum_le_sum
      intro q hq
      have hAcont := primitiveCharacterPolynomialMeanSquare_phase_continuous (qmod q).property s A
      have hAnonneg :
        ∀ t : ℝ,
          0 ≤
            primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
              (fun p => A p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) :=
        fun t =>
        primitiveCharacterPolynomialMeanSquare_nonneg (qmod q).property s
          (fun p => A p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I))
      have hBcont := primitiveCharacterPolynomialMeanSquare_phase_continuous (qmod q).property s B
      have hBnonneg :
        ∀ t : ℝ,
          0 ≤
            primitiveCharacterPolynomialMeanSquare (qmod q).val (qmod q).property s
              (fun p => B p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) :=
        fun t =>
        primitiveCharacterPolynomialMeanSquare_nonneg (qmod q).property s
          (fun p => B p * Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I))
      have hnh : 0 ≤ (n : ℝ) * h := mul_nonneg (Nat.cast_nonneg _) hh.le
      have hEnd : a ≤ a + (n : ℝ) * h := le_add_of_nonneg_right hnh
      have hA :=
        PseudoPrime.Analysis.intervalIntegral_le_integral_Icc_of_nonneg ha hEnd hb hAnonneg hAcont
      have hB :=
        PseudoPrime.Analysis.intervalIntegral_le_integral_Icc_of_nonneg ha hEnd hb hBnonneg hBcont
      exact add_le_add hA (mul_le_mul_of_nonneg_left hB (by positivity))
    _ = _ := by simp only [Finset.sum_add_distrib, Finset.mul_sum, A, B]

/-- Combine the finite-family mesh estimate with the pre-sifted hybrid bounds at derivative
orders `r` and `r + 1`. The resulting second coefficient energy is explicit so the height-mesh
scale can be checked against the prime support before it is absorbed. -/
theorem primitiveCharacterPrimeLogPower_grid_hybrid_energy_bound (R : ℕ) (hR : 2 ≤ R) (T : ℝ)
    (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) (r : ℕ) (σ : ℝ) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hlower : ∀ p ∈ s, R ^ 6 ≤ p) (a h : ℝ) (n : ℕ) (hh : 0 < h)
    (ha : -T ≤ a) (hb : a + (n : ℝ) * h ≤ T) :
    (h / 2) *
        (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
          ∑ k ∈ Finset.range n,
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun p =>
                (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                  Complex.exp
                    ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))) ≤
      (4096 : ℝ) / Real.log R *
          ∑ p ∈ s,
            ‖((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^ 2 *
              p +
        (h ^ 2 / 2) *
          ((4096 : ℝ) / Real.log R *
            ∑ p ∈ s,
              ‖((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^
                  2 *
                p) := by
  classical
  let Q := (Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R
  let qmod (q : { q : ℕ // q ∈ Finset.Ioc 1 (R ^ 2) }) : { q : ℕ // 1 < q } :=
    ⟨q.val, (Finset.mem_Ioc.mp q.property).1⟩
  have hgrid :=
    primitiveCharacterPrimeLogPower_family_grid_mean_square_bound (α :=
      { q : ℕ // q ∈ Finset.Ioc 1 (R ^ 2) }) Q qmod s r σ a h T n hh ha hb
  have hhybrid :=
    primitiveCharacterPrimeLogPowerMeanSquare_preSifted_hybrid_R_squared R hR T hT hTupper r σ s
      hprime hlower
  have hhybridNext :=
    primitiveCharacterPrimeLogPowerMeanSquare_preSifted_hybrid_R_squared R hR T hT hTupper (r + 1) σ
      s hprime hlower
  calc
    _ ≤
        (∑ q ∈ Q,
            ∫ t in Set.Icc (-T) T,
              primitiveCharacterPolynomialMeanSquare q.val
                (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                (fun p =>
                  (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                      Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                    Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) +
          (h ^ 2 / 2) *
            (∑ q ∈ Q,
              ∫ t in Set.Icc (-T) T,
                primitiveCharacterPolynomialMeanSquare q.val
                  (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
                  (fun p =>
                    (((Real.log p : ℝ) ^ (r + 2) : ℂ) *
                        Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                      Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I)) ∂MeasureTheory.volume) :=
      by simpa only [qmod] using hgrid
    _ ≤
        (4096 : ℝ) / Real.log R *
            ∑ p ∈ s,
              ‖((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^
                  2 *
                p +
          (h ^ 2 / 2) *
            ((4096 : ℝ) / Real.log R *
              ∑ p ∈ s,
                ‖((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^
                    2 *
                  p) :=
      by exact add_le_add hhybrid (mul_le_mul_of_nonneg_left hhybridNext (by positivity))

/-- If the prime support is bounded by `X`, the order-`r + 1` coefficient energy is at most
`(log X)^2` times the order-`r` energy. This records the precise support dependence needed to
control the derivative term in the mesh estimate. -/
theorem primitiveCharacterPrimeLogPower_next_energy_le_sq_log_upper_bound (s : Finset ℕ) (r : ℕ)
    (σ : ℝ) (X : ℕ) (hprime : ∀ p ∈ s, Nat.Prime p) (hupper : ∀ p ∈ s, p ≤ X) :
    (∑ p ∈ s,
        ‖((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^ 2 *
          p) ≤
      (Real.log X) ^ 2 *
        ∑ p ∈ s,
          ‖((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^ 2 *
            p := by
  classical
  let A : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  let B : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  have hcoeff (p : ℕ) : B p = (Real.log p : ℂ) * A p := by
    dsimp only [A, B]
    push_cast
    ring
  have hpoint (p : ℕ) (hp : p ∈ s) : ‖B p‖ ^ 2 * p ≤ (Real.log X) ^ 2 * (‖A p‖ ^ 2 * p) := by
    have hp2 : 2 ≤ p := (hprime p hp).two_le
    have hp1 : 1 ≤ p := by omega
    have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp1)
    have hlogX : Real.log p ≤ Real.log X :=
      Real.log_le_log (by exact_mod_cast (hprime p hp).pos) (by exact_mod_cast hupper p hp)
    have hnorm : ‖B p‖ = Real.log p * ‖A p‖ := by
      rw [hcoeff p, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hlog0]
    have hprod0 : 0 ≤ Real.log p * ‖A p‖ := mul_nonneg hlog0 (norm_nonneg _)
    have hprod : Real.log p * ‖A p‖ ≤ Real.log X * ‖A p‖ :=
      mul_le_mul_of_nonneg_right hlogX (norm_nonneg _)
    have hsq : (Real.log p * ‖A p‖) ^ 2 ≤ (Real.log X * ‖A p‖) ^ 2 := by
      simpa only [pow_two] using mul_self_le_mul_self hprod0 hprod
    rw [hnorm]
    calc
      (Real.log p * ‖A p‖) ^ 2 * p ≤ (Real.log X * ‖A p‖) ^ 2 * p :=
        mul_le_mul_of_nonneg_right hsq (Nat.cast_nonneg _)
      _ = (Real.log X) ^ 2 * (‖A p‖ ^ 2 * p) := by ring
  calc
    _ = ∑ p ∈ s, ‖B p‖ ^ 2 * p := by simp only [B]
    _ ≤ ∑ p ∈ s, (Real.log X) ^ 2 * (‖A p‖ ^ 2 * p) := by
      apply Finset.sum_le_sum
      intro p hp
      exact hpoint p hp
    _ = _ := by rw [Finset.mul_sum]

/-- Under a prime upper cutoff `X`, absorb the higher-order hybrid energy into the lower-order
energy. The mesh loss is the explicit factor `1 + (h^2 / 2) * (log X)^2`. -/
theorem primitiveCharacterPrimeLogPower_grid_hybrid_cutoff_bound (R : ℕ) (hR : 2 ≤ R) (T : ℝ)
    (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) (r : ℕ) (σ : ℝ) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hlower : ∀ p ∈ s, R ^ 6 ≤ p) (X : ℕ) (hupper : ∀ p ∈ s, p ≤ X)
    (a h : ℝ) (n : ℕ) (hh : 0 < h) (ha : -T ≤ a) (hb : a + (n : ℝ) * h ≤ T) :
    (h / 2) *
        (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
          ∑ k ∈ Finset.range n,
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun p =>
                (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                  Complex.exp
                    ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))) ≤
      (4096 : ℝ) / Real.log R * (1 + (h ^ 2 / 2) * (Real.log X) ^ 2) *
        ∑ p ∈ s,
          ‖((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^ 2 *
            p := by
  classical
  let A : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  let B : ℕ → ℂ := fun p =>
    ((Real.log p : ℝ) ^ (r + 2) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)
  have hgrid :=
    primitiveCharacterPrimeLogPower_grid_hybrid_energy_bound R hR T hT hTupper r σ s hprime hlower a
      h n hh ha hb
  have henergy :=
    primitiveCharacterPrimeLogPower_next_energy_le_sq_log_upper_bound s r σ X hprime hupper
  have hC : 0 ≤ (4096 : ℝ) / Real.log R := by
    have hRgt : 1 < R := by omega
    positivity
  have hh2 : 0 ≤ h ^ 2 / 2 := by positivity
  calc
    _ ≤
        (4096 : ℝ) / Real.log R * ∑ p ∈ s, ‖A p‖ ^ 2 * p +
          (h ^ 2 / 2) * ((4096 : ℝ) / Real.log R * ∑ p ∈ s, ‖B p‖ ^ 2 * p) :=
      by simpa only [A, B] using hgrid
    _ ≤
        (4096 : ℝ) / Real.log R * ∑ p ∈ s, ‖A p‖ ^ 2 * p +
          (h ^ 2 / 2) * ((4096 : ℝ) / Real.log R * ((Real.log X) ^ 2 * ∑ p ∈ s, ‖A p‖ ^ 2 * p)) :=
      by
      apply add_le_add le_rfl
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left henergy hC) hh2
    _ = _ := by ring

/-- If the height mesh is at most `η / 8` and the prime cutoff satisfies
`log X ≤ c₁ K / η`, the derivative-energy loss is bounded by a quadratic polynomial in `K`.
This is the scale needed to absorb the mesh loss into the exponential factor in the zero-density
estimate. -/
theorem mesh_cutoff_loss_le_quadratic_detector_order (η c₁ h : ℝ) (K X : ℕ) (hη : 0 < η)
    (hc₁ : 0 ≤ c₁) (hh : 0 ≤ h) (hhη : h ≤ η / 8) (hX : 1 ≤ X) (hlogX : Real.log X ≤ c₁ * K / η) :
    1 + (h ^ 2 / 2) * (Real.log X) ^ 2 ≤ 1 + (c₁ * K / 8) ^ 2 / 2 := by
  have hlog0 : 0 ≤ Real.log X := Real.log_nonneg (by exact_mod_cast hX)
  have hscale : h * Real.log X ≤ c₁ * K / 8 := by
    calc
      h * Real.log X ≤ (η / 8) * Real.log X := mul_le_mul_of_nonneg_right hhη hlog0
      _ ≤ (η / 8) * (c₁ * K / η) := mul_le_mul_of_nonneg_left hlogX (by positivity)
      _ = c₁ * K / 8 := by field_simp [ne_of_gt hη]
  have hsq : (h * Real.log X) ^ 2 ≤ (c₁ * K / 8) ^ 2 :=
    (sq_le_sq₀ (mul_nonneg hh hlog0)
          (div_nonneg (mul_nonneg hc₁ (Nat.cast_nonneg _)) (by norm_num))).2
      hscale
  have hfactor : (h ^ 2 / 2) * (Real.log X) ^ 2 = (h * Real.log X) ^ 2 / 2 := by ring
  rw [hfactor]
  have hdiv : (h * Real.log X) ^ 2 / 2 ≤ (c₁ * K / 8) ^ 2 / 2 :=
    div_le_div_of_nonneg_right hsq (by norm_num)
  calc
    1 + (h * Real.log X) ^ 2 / 2 = (h * Real.log X) ^ 2 / 2 + 1 := by ring
    _ ≤ (c₁ * K / 8) ^ 2 / 2 + 1 := add_le_add_left hdiv 1
    _ = 1 + (c₁ * K / 8) ^ 2 / 2 := by ring

/-- For a prime-supported hybrid grid with `η log X ≤ c₁ K` and mesh width at most
`η / 8`, replace the support-dependent derivative loss by a quadratic polynomial
in `K`. Combine the cutoff hybrid bound with the mesh loss estimate and nonnegative
coefficient energy. This consumes the logarithmic cutoff supplied by the zero detector. -/
theorem primitiveCharacterPrimeLogPower_grid_hybrid_detector_order_bound (R : ℕ) (hR : 2 ≤ R)
    (T : ℝ) (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) (r : ℕ) (σ : ℝ) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hlower : ∀ p ∈ s, R ^ 6 ≤ p) (X : ℕ) (hupper : ∀ p ∈ s, p ≤ X)
    (a h : ℝ) (n : ℕ) (hh : 0 < h) (ha : -T ≤ a) (hb : a + (n : ℝ) * h ≤ T) (η c₁ : ℝ) (K : ℕ)
    (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hhη : h ≤ η / 8) (hX : 1 ≤ X) (hlogX : η * Real.log X ≤ c₁ * K) :
    (h / 2) *
        (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
          ∑ k ∈ Finset.range n,
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun p =>
                (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
                  Complex.exp
                    ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))) ≤
      (4096 : ℝ) / Real.log R * (1 + (c₁ * K / 8) ^ 2 / 2) *
        ∑ p ∈ s,
          ‖((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^ 2 *
            p := by
  have hgrid :=
    primitiveCharacterPrimeLogPower_grid_hybrid_cutoff_bound R hR T hT hTupper r σ s hprime hlower X
      hupper a h n hh ha hb
  have hlog : Real.log X ≤ c₁ * K / η := (le_div_iff₀ hη).mpr (by simpa only [mul_comm] using hlogX)
  have hfactor := mesh_cutoff_loss_le_quadratic_detector_order η c₁ h K X hη hc₁ hh.le hhη hX hlog
  have hC : 0 ≤ (4096 : ℝ) / Real.log R :=
    div_nonneg (by norm_num only)
      (Real.log_nonneg (by exact_mod_cast ((by norm_num only : 1 ≤ 2).trans hR)))
  have henergy :
    0 ≤
      ∑ p ∈ s,
        ‖((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ ^ 2 *
          p :=
    Finset.sum_nonneg (fun p hp ↦ mul_nonneg (sq_nonneg _) (Nat.cast_nonneg p))
  exact hgrid.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hfactor hC) henergy)

/-- For a positive rate with `2η ≤ 1` and a cutoff in the decreasing range, the
rate-`2η` von Mangoldt moment normalized by `η^(m+1)/m!` is bounded by
`3(log 4 + 4) exp(-η log N)/2`. Cancel the powers of two in the Chernoff bound.
This is the moment normalization used by squared prime coefficients. -/
theorem normalized_doubled_rate_vonMangoldt_tail_le (η : ℝ) (m N : ℕ) (hη : 0 < η)
    (hηsmall : 2 * η ≤ 1) (hN : 1 ≤ N) (hm : (m : ℝ) ≤ (1 + 2 * η) * Real.log N) :
    η ^ (m + 1) / (m.factorial : ℝ) *
        (∑' k : { k // k ∉ Finset.range (N + 1) },
          ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ m / (k.val : ℝ) ^ (1 + 2 * η)) ≤
      (3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log N)) := by
  have hbase :=
    normalized_vonMangoldt_log_weight_tail_le_chernoff (2 * η) m N (mul_pos (by norm_num only) hη)
      hηsmall hN hm
  rw [mul_pow, show -((2 * η) * Real.log N) / 2 = -(η * Real.log N) by ring] at hbase
  apply (mul_le_mul_iff_left₀ (pow_pos (by norm_num only : (0 : ℝ) < 2) (m + 1))).mp
  calc
    _ =
        (2 : ℝ) ^ (m + 1) * η ^ (m + 1) / (m.factorial : ℝ) *
          (∑' k : { k // k ∉ Finset.range (N + 1) },
            ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ m /
              (k.val : ℝ) ^ (1 + 2 * η)) :=
      by ring
    _ ≤ _ := hbase
    _ = _ := by
      rw [pow_succ (2 : ℝ)]
      ring

/-- For a finite prime support above `N` and positive damping, dominate its
logarithmic moment by the von Mangoldt tail. Replace `Λ(p)` by `log p` and embed
the finite sum into the summable nonnegative tail. This transfers the Abel bound to primes. -/
theorem finite_prime_log_moment_le_vonMangoldt_tail (η : ℝ) (m N : ℕ) (s : Finset ℕ) (hη : 0 < η)
    (hprime : ∀ p ∈ s, Nat.Prime p) (habove : ∀ p ∈ s, N < p) :
    (∑ p ∈ s, (Real.log p) ^ (m + 1) / (p : ℝ) ^ (1 + 2 * η)) ≤
      ∑' k : { k // k ∉ Finset.range (N + 1) },
        ArithmeticFunction.vonMangoldt k.val * (Real.log k.val) ^ m /
          (k.val : ℝ) ^ (1 + 2 * η) := by
  classical
  let f : ℕ → ℝ := fun k ↦
    ArithmeticFunction.vonMangoldt k * (Real.log k) ^ m / (k : ℝ) ^ (1 + 2 * η)
  have hsum :=
    (summable_vonMangoldt_log_weight (show 1 < 1 + 2 * η by linarith only [hη]) m).subtype
      (fun k ↦ k ∉ Finset.range (N + 1))
  have hsub : ∀ p ∈ s, p ∉ Finset.range (N + 1) := by
    intro p hp
    simpa only [Finset.mem_range, not_lt, Nat.succ_le_iff] using habove p hp
  have hfinite : (∑ p ∈ s, (Real.log p) ^ (m + 1) / (p : ℝ) ^ (1 + 2 * η)) = ∑ p ∈ s, f p := by
    apply Finset.sum_congr rfl
    intro p hp
    dsimp only [f]
    rw [ArithmeticFunction.vonMangoldt_apply_prime (hprime p hp), ← pow_succ']
  rw [hfinite, ← Finset.sum_subtype_of_mem f hsub]
  exact
    hsum.sum_le_tsum _
      (fun k hk ↦
        div_nonneg
          (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
            (pow_nonneg (Real.log_natCast_nonneg k.val) m))
          (Real.rpow_nonneg (Nat.cast_nonneg k.val) _))

/-- For finite prime support above a decreasing-range cutoff, normalize its
logarithmic moment by `η^(m+1)/m!` and apply the doubled-rate von Mangoldt estimate.
The resulting bound contains no inverse-rate factor and controls the prime energy moment. -/
theorem normalized_finite_prime_log_moment_le (η : ℝ) (m N : ℕ) (s : Finset ℕ) (hη : 0 < η)
    (hηsmall : 2 * η ≤ 1) (hN : 1 ≤ N) (hm : (m : ℝ) ≤ (1 + 2 * η) * Real.log N)
    (hprime : ∀ p ∈ s, Nat.Prime p) (habove : ∀ p ∈ s, N < p) :
    η ^ (m + 1) / (m.factorial : ℝ) * (∑ p ∈ s, (Real.log p) ^ (m + 1) / (p : ℝ) ^ (1 + 2 * η)) ≤
      (3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log N)) := by
  have hfinite :=
    mul_le_mul_of_nonneg_left (finite_prime_log_moment_le_vonMangoldt_tail η m N s hη hprime habove)
      (div_nonneg (pow_nonneg hη.le (m + 1)) (Nat.cast_nonneg m.factorial))
  exact hfinite.trans (normalized_doubled_rate_vonMangoldt_tail_le η m N hη hηsmall hN hm)

/-- For a positive prime index, rewrite the weighted square of its complex
logarithmic coefficient as a real damped moment. Evaluate the exponential norm and
combine the real powers. This identifies the exact coefficient energy in the hybrid bound. -/
theorem prime_log_power_energy_term_eq (η : ℝ) (n p : ℕ) (hp : 0 < p) :
    ‖(((Real.log p) ^ (n + 1) : ℝ) : ℂ) * Complex.exp (-((Real.log p * (1 + η) : ℝ) : ℂ))‖ ^ 2 * p =
      (Real.log p) ^ (2 * n + 2) / (p : ℝ) ^ (1 + 2 * η) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (Real.log_natCast_nonneg p) (n + 1)), Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [mul_pow, ← pow_mul, ← Real.exp_nat_mul]
  have hpow : (n + 1) * 2 = 2 * n + 2 := by ring
  rw [hpow, Real.rpow_def_of_pos hpR, div_eq_mul_inv, ← Real.exp_neg]
  have he :
    Real.exp ((2 : ℝ) * -(Real.log p * (1 + η))) * (p : ℝ) =
      Real.exp (-(Real.log p * (1 + 2 * η))) := by
    calc
      _ = Real.exp ((2 : ℝ) * -(Real.log p * (1 + η))) * Real.exp (Real.log p) := by
        rw [Real.exp_log hpR]
      _ = _ := by
        rw [← Real.exp_add]
        congr 1
        ring_nf
  calc
    _ = (Real.log p) ^ (2 * n + 2) * (Real.exp ((2 : ℝ) * -(Real.log p * (1 + η))) * (p : ℝ)) := by
      norm_num only [Nat.cast_ofNat]
      ring
    _ = _ := by rw [he]

/-- For any rate and natural order, the squared detector normalization equals
the moment normalization times the factorial ratio `(2n+1)!/(n!)²`. Cancel the nonzero
factorial and identify the natural exponents. This preserves factorial gains in the energy. -/
theorem factorial_normalization_square_eq (η : ℝ) (n : ℕ) :
    ((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2 *
        (η ^ ((2 * n + 1) + 1) / ((2 * n + 1).factorial : ℝ)) =
      (η ^ (n + 1) / (n.factorial : ℝ)) ^ 2 := by
  have hf : ((2 * n + 1).factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  rw [div_mul_div_comm, mul_comm ((2 * n + 1).factorial : ℝ), mul_div_mul_right _ _ hf, div_pow, ←
    pow_mul]
  congr 2
  ring

/-- For finite prime support above a decreasing-range cutoff and `0 < 2η ≤ 1`,
bound its squared-normalized coefficient energy by the factorial ratio times the
exponentially damped Abel constant. Rewrite each coefficient and use the prime moment bound.
This connects Euler-detector normalization to the hybrid coefficient energy. -/
theorem normalized_prime_coefficient_energy_le_factorial_ratio (η : ℝ) (n N : ℕ) (s : Finset ℕ)
    (hη : 0 < η) (hηsmall : 2 * η ≤ 1) (hN : 1 ≤ N)
    (hn : ((2 * n + 1 : ℕ) : ℝ) ≤ (1 + 2 * η) * Real.log N) (hprime : ∀ p ∈ s, Nat.Prime p)
    (habove : ∀ p ∈ s, N < p) :
    (η ^ (n + 1) / (n.factorial : ℝ)) ^ 2 *
        (∑ p ∈ s,
          ‖(((Real.log p) ^ (n + 1) : ℝ) : ℂ) * Complex.exp (-((Real.log p * (1 + η) : ℝ) : ℂ))‖ ^
              2 *
            p) ≤
      (((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2) *
        ((3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log N))) := by
  have heq :
    (∑ p ∈ s,
        ‖(((Real.log p) ^ (n + 1) : ℝ) : ℂ) * Complex.exp (-((Real.log p * (1 + η) : ℝ) : ℂ))‖ ^ 2 *
          p) =
      ∑ p ∈ s, (Real.log p) ^ ((2 * n + 1) + 1) / (p : ℝ) ^ (1 + 2 * η) := by
    apply Finset.sum_congr rfl
    intro p hp
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      prime_log_power_energy_term_eq η n p (hprime p hp).pos
  rw [heq, ← factorial_normalization_square_eq η n, mul_assoc]
  exact
    mul_le_mul_of_nonneg_left
      (normalized_finite_prime_log_moment_le η (2 * n + 1) N s hη hηsmall hN hn hprime habove)
      (div_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

/-- For natural `n`, bound `(2n+1)!/(n!)²` by `(n+1) 2^(2n+1)`.
Express the ratio using a binomial coefficient and apply the complete binomial sum bound.
This makes the coefficient energy at most exponential in the detector order. -/
theorem factorial_ratio_le_order_exponential (n : ℕ) :
    ((2 * n + 1).factorial : ℝ) / (n.factorial : ℝ) ^ 2 ≤ (n + 1 : ℝ) * (2 : ℝ) ^ (2 * n + 1) := by
  have hn : n ≤ 2 * n + 1 := by
    calc
      n ≤ n + (n + 1) := Nat.le_add_right n (n + 1)
      _ = _ := by ring
  have hid := Nat.choose_mul_factorial_mul_factorial hn
  have hsub : 2 * n + 1 - n = n + 1 := by
    rw [show 2 * n + 1 = n + (n + 1) by ring, Nat.add_sub_cancel_left]
  rw [hsub, Nat.factorial_succ] at hid
  have hreal :
    ((2 * n + 1).factorial : ℝ) =
      (((2 * n + 1).choose n : ℕ) : ℝ) * (n + 1) * (n.factorial : ℝ) ^ 2 := by
    have hcast :
      (((2 * n + 1).choose n : ℕ) : ℝ) * (n.factorial : ℝ) * ((n + 1) * (n.factorial : ℝ)) =
        ((2 * n + 1).factorial : ℝ) := by
      exact_mod_cast hid
    rw [← hcast]
    ring
  rw [hreal,
    mul_div_cancel_right₀ _ (pow_ne_zero _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))]
  have hchoose : (((2 * n + 1).choose n : ℕ) : ℝ) ≤ (2 : ℝ) ^ (2 * n + 1) := by
    exact_mod_cast Nat.choose_le_two_pow (2 * n + 1) n
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hchoose (add_nonneg (Nat.cast_nonneg n) zero_le_one)

/-- Under the finite-prime moment hypotheses, bound normalized coefficient
energy by `(n+1) 2^(2n+1)` times the damped Abel constant. Combine the factorial-ratio
estimate and its binomial bound. This supplies an explicit order loss without `1/η`. -/
theorem normalized_prime_coefficient_energy_le_exponential (η : ℝ) (n N : ℕ) (s : Finset ℕ)
    (hη : 0 < η) (hηsmall : 2 * η ≤ 1) (hN : 1 ≤ N)
    (hn : ((2 * n + 1 : ℕ) : ℝ) ≤ (1 + 2 * η) * Real.log N) (hprime : ∀ p ∈ s, Nat.Prime p)
    (habove : ∀ p ∈ s, N < p) :
    (η ^ (n + 1) / (n.factorial : ℝ)) ^ 2 *
        (∑ p ∈ s,
          ‖(((Real.log p) ^ (n + 1) : ℝ) : ℂ) * Complex.exp (-((Real.log p * (1 + η) : ℝ) : ℂ))‖ ^
              2 *
            p) ≤
      ((n + 1 : ℝ) * (2 : ℝ) ^ (2 * n + 1)) *
        ((3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log N))) := by
  have hbase :=
    normalized_prime_coefficient_energy_le_factorial_ratio η n N s hη hηsmall hN hn hprime habove
  have hnonneg : 0 ≤ (3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log N)) :=
    mul_nonneg
      (mul_nonneg (by norm_num only)
        (add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)))
      (Real.exp_pos _).le
  exact hbase.trans (mul_le_mul_of_nonneg_right (factorial_ratio_le_order_exponential n) hnonneg)

/-- For a prime-supported height grid at abscissa `1+η`, combine the scaled
logarithmic cutoff and a decreasing-range lower cutoff with squared detector normalization.
The resulting hybrid grid bound has an explicit polynomial mesh loss and exponential order
loss, and no inverse-rate prefactor. Apply the grid bound and normalized coefficient energy.
This supplies the mean-square side of the normalized zero-incidence estimate. -/
theorem primitiveCharacterPrimeLogPower_grid_hybrid_normalized_detector_order_bound (R : ℕ)
    (hR : 2 ≤ R) (T : ℝ) (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) (r : ℕ) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, Nat.Prime p) (hlower : ∀ p ∈ s, R ^ 6 ≤ p) (X : ℕ) (hupper : ∀ p ∈ s, p ≤ X)
    (a h : ℝ) (n : ℕ) (hh : 0 < h) (ha : -T ≤ a) (hb : a + (n : ℝ) * h ≤ T) (η c₁ : ℝ) (K : ℕ)
    (hη : 0 < η) (hc₁ : 0 ≤ c₁) (hhη : h ≤ η / 8) (hX : 1 ≤ X) (hlogX : η * Real.log X ≤ c₁ * K)
    (N : ℕ) (hN : 1 ≤ N) (hηsmall : 2 * η ≤ 1)
    (hmoment : ((2 * r + 1 : ℕ) : ℝ) ≤ (1 + 2 * η) * Real.log N) (habove : ∀ p ∈ s, N < p) :
    (η ^ (r + 1) / (r.factorial : ℝ)) ^ 2 * (h / 2) *
        (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q => q.val ≤ R),
          ∑ k ∈ Finset.range n,
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1) s
              (fun p =>
                (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                    Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                  Complex.exp
                    ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))) ≤
      (4096 : ℝ) / Real.log R * (1 + (c₁ * K / 8) ^ 2 / 2) *
        (((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) *
          ((3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log N)))) := by
  have hgrid :=
    primitiveCharacterPrimeLogPower_grid_hybrid_detector_order_bound R hR T hT hTupper r (1 + η) s
      hprime hlower X hupper a h n hh ha hb η c₁ K hη hc₁ hhη hX hlogX
  have henergy :=
    normalized_prime_coefficient_energy_le_exponential η r N s hη hηsmall hN hmoment hprime habove
  simp only [Complex.ofReal_pow] at henergy
  have hA : 0 ≤ (η ^ (r + 1) / (r.factorial : ℝ)) ^ 2 := sq_nonneg _
  have hscaled := mul_le_mul_of_nonneg_left hgrid hA
  have hC : 0 ≤ (4096 : ℝ) / Real.log R * (1 + (c₁ * K / 8) ^ 2 / 2) :=
    mul_nonneg
      (div_nonneg (by norm_num only)
        (Real.log_nonneg (by exact_mod_cast ((by norm_num only : 1 ≤ 2).trans hR))))
      (add_nonneg zero_le_one (div_nonneg (sq_nonneg _) (by norm_num only)))
  have hfinal := mul_le_mul_of_nonneg_left henergy hC
  nlinarith only [hscaled, hfinal]

/-- A requested-order budget and `η log R ≤ 3` control the low-prime scale at
`R^6` for every larger derivative order. Rewrite the logarithm and compare orders.
This supplies one scale inequality uniformly across a detector family. -/
theorem requested_order_R_six_log_scale (η D : ℝ) (Krequested n R : ℕ) (hn : Krequested - 1 ≤ n)
    (hRscale : η * Real.log (R : ℝ) ≤ 3)
    (hRorder : 18 ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ)) :
    η * Real.log ((R ^ 6 : ℕ) : ℝ) ≤ Real.exp (-(D + 6)) * n := by
  have hnreal : ((Krequested - 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast hn
  have hc := mul_le_mul_of_nonneg_left hnreal (Real.exp_pos (-(D + 6))).le
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_ofNat]
  nlinarith only [hRscale, hRorder, hc]

/-- The exponential coefficient chosen for low-prime removal has the required
unit-shift margin. Combine exponentials and simplify their exponents.
This makes the removal budget independent of the character and height. -/
theorem low_prime_exponential_budget (D : ℝ) :
    Real.exp (-(D + 6)) * Real.exp 1 ≤ Real.exp (-(D + 5)) := by
  rw [← Real.exp_add]
  apply le_of_eq
  congr 1
  ring

/-- Under the requested-order, scale, and prime-power budgets, any finite Euler
signal above the shared cutoff retains one eighth of its local detector signal on
primes above `R^6`. Derive the removal margins from the requested order and apply
the established low-prime and prime-power estimates.
This transfers a common finite support to the high-prime hybrid interface. -/
theorem finite_high_prime_signal_of_requested_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (η D : ℝ) (Krequested R n K cutoff : ℕ) (hη : 0 < η) (hηsmall : η ≤ 1) (hD : 0 ≤ D) (hR : 2 ≤ R)
    (hKrequested : Krequested ≤ K) (hKorder : K ≤ n + 1) (hcutoff : R ^ 6 ≤ cutoff)
    (hDrequested : D + 5 ≤ 5 * ((Krequested - 1 : ℕ) : ℝ)) (hRscale : η * Real.log (R : ℝ) ≤ 3)
    (hRorder : 18 ≤ Real.exp (-(D + 6)) * ((Krequested - 1 : ℕ) : ℝ))
    (hηratio : 4 * η ≤ Real.exp (-(D + 5)))
    (hm : Nat.ceil (Real.log higherPrimePowerEulerMajorantConstant) ≤ Krequested) {s : ℂ}
    (hs : s.re = 1 + η)
    (hfull :
      Real.exp (-(D * (K : ℝ))) / 2 ≤
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          ‖∑ j ∈ Finset.range (cutoff + 1),
              LSeries.term
                (LSeries.logMul^[n]
                  (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
                s j‖) :
    Real.exp (-(D * (K : ℝ))) / 8 ≤
      (η ^ (n + 1) / (n.factorial : ℝ)) *
        ‖∑ p ∈ ((Finset.range (cutoff + 1)).filter Nat.Prime).filter (fun p ↦ ¬p ≤ R ^ 6),
            LSeries.term
              (LSeries.logMul^[n]
                (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
              s p‖ := by
  have hn : Krequested - 1 ≤ n := Nat.sub_le_iff_le_add.mpr (hKrequested.trans hKorder)
  exact
    finite_high_prime_sum_norm_ge_of_detector_signal χ (R ^ 6) cutoff n K
      (hR.trans (Nat.le_self_pow (by decide) R)) hcutoff hη hηsmall hD (Real.exp_pos _).le hKorder
      (detector_order_exponential_margin Krequested n K D hD hDrequested hn hKorder)
      (requested_order_R_six_log_scale η D Krequested n R hn hRscale hRorder)
      (low_prime_exponential_budget D) hηratio (hm.trans (hKrequested.trans hKorder)) s hs hfull

/-- For a nonnegative rate, a bounded derivative order, and a sufficiently large
conductor scale, the weight decreases above `R^6`. Compare orders and expand the
cutoff logarithm. This derives the moment hypothesis of the normalized hybrid energy. -/
theorem prime_energy_decreasing_range_of_order_envelope (η : ℝ) (n nmax R : ℕ) (hη : 0 ≤ η)
    (hn : n ≤ nmax) (hR : 1 ≤ R) (hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ)) :
    ((2 * n + 1 : ℕ) : ℝ) ≤ (1 + 2 * η) * Real.log ((R ^ 6 : ℕ) : ℝ) := by
  have hnreal : (n : ℝ) ≤ nmax := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (R : ℝ) := Real.log_nonneg (by exact_mod_cast hR)
  rw [Nat.cast_pow, Real.log_pow]
  norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hlarge ⊢
  nlinarith only [hnreal, hlarge, mul_nonneg hη hlog]

/-- For each fixed derivative-order envelope, all sufficiently large natural
scales satisfy the prime-energy decreasing condition, uniformly in nonnegative rates.
Use logarithmic divergence and the explicit order-envelope criterion.
This discharges the lower-cutoff condition in the asymptotic AGP range. -/
theorem eventually_prime_energy_decreasing_range (nmax : ℕ) :
    ∃ R₀ : ℕ,
      2 ≤ R₀ ∧
        ∀ R : ℕ,
          R₀ ≤ R →
            ∀ η : ℝ,
              0 ≤ η →
                ∀ n ≤ nmax, ((2 * n + 1 : ℕ) : ℝ) ≤ (1 + 2 * η) * Real.log ((R ^ 6 : ℕ) : ℝ) := by
  have hlog : Filter.Tendsto (fun R : ℕ ↦ Real.log (R : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨R₀, hR₀⟩ :=
    Filter.eventually_atTop.mp
      (hlog.eventually (Filter.eventually_ge_atTop (((2 * nmax + 1 : ℕ) : ℝ) / 6)))
  refine ⟨max 2 R₀, le_max_left _ _, ?_⟩
  intro R hR η hη n hn
  have hlarge := hR₀ R ((le_max_right 2 R₀).trans hR)
  exact
    prime_energy_decreasing_range_of_order_envelope η n nmax R hη hn
      (((by norm_num only : 1 ≤ 2).trans (le_max_left 2 R₀)).trans hR) (by linarith only [hlarge])

/-- For a scale `R` and Euler cutoff, define the finite prime support between
`R^6` and the cutoff, excluding the lower endpoint. This is exactly the support of
the common high-prime detector and is used in the hybrid mean-square bound. -/
def highPrimeEulerSupport (R cutoff : ℕ) : Finset ℕ :=
  ((Finset.range (cutoff + 1)).filter Nat.Prime).filter (fun p ↦ ¬p ≤ R ^ 6)

/-- Membership in the high-prime Euler support means primality and the explicit
lower and upper bounds. Expand the filters and natural interval conditions.
This supplies the support hypotheses for the hybrid sieve and coefficient energy. -/
theorem mem_highPrimeEulerSupport {R cutoff p : ℕ} :
    p ∈ highPrimeEulerSupport R cutoff ↔ p ≤ cutoff ∧ Nat.Prime p ∧ R ^ 6 < p := by
  simp only [highPrimeEulerSupport, Finset.mem_filter, Finset.mem_range, Nat.lt_succ_iff, not_le,
    and_assoc]

/-- For the actual high-prime Euler support and an order envelope below the
logarithmic scale, apply the normalized hybrid grid estimate with lower cutoff `R^6`.
Use support membership and the order-envelope decreasing condition. The upper support
enters only through the scaled logarithmic cutoff, so its loss is quadratic in `K`.
This is the common-support mean-square interface for the zero-incidence count. -/
theorem highPrimeEulerSupport_grid_hybrid_normalized_bound (R cutoff nmax r : ℕ) (hR : 2 ≤ R)
    (T : ℝ) (hT : 1 ≤ T) (hTupper : T ≤ 2 * R) (a h : ℝ) (gridSize : ℕ) (hh : 0 < h) (ha : -T ≤ a)
    (hb : a + (gridSize : ℝ) * h ≤ T) (η c₁ : ℝ) (K : ℕ) (hη : 0 < η) (hηsmall : 2 * η ≤ 1)
    (hc₁ : 0 ≤ c₁) (hhη : h ≤ η / 8) (hlogX : η * Real.log ((cutoff : ℝ) + 1) ≤ c₁ * K)
    (hr : r ≤ nmax) (hlarge : ((2 * nmax + 1 : ℕ) : ℝ) ≤ 6 * Real.log (R : ℝ)) :
    (η ^ (r + 1) / (r.factorial : ℝ)) ^ 2 * (h / 2) *
        (∑ q ∈ ((Finset.Ioc 1 (R ^ 2)).attach.filter fun q ↦ q.val ≤ R),
          ∑ k ∈ Finset.range gridSize,
            primitiveCharacterPolynomialMeanSquare q.val
              (show 1 < q.val from (Finset.mem_Ioc.mp q.property).1)
              (highPrimeEulerSupport R cutoff)
              (fun p ↦
                (((Real.log p : ℝ) ^ (r + 1) : ℂ) *
                    Complex.exp (-((Real.log p : ℝ) * (1 + η) : ℝ) : ℂ)) *
                  Complex.exp
                    ((-((a + ((k : ℝ) + 1 / 2) * h) * Real.log p : ℝ) : ℝ) * Complex.I))) ≤
      (4096 : ℝ) / Real.log R * (1 + (c₁ * K / 8) ^ 2 / 2) *
        (((r + 1 : ℝ) * (2 : ℝ) ^ (2 * r + 1)) *
          ((3 / 2 : ℝ) * (Real.log 4 + 4) * Real.exp (-(η * Real.log ((R ^ 6 : ℕ) : ℝ))))) := by
  have hRone : 1 ≤ R := (by norm_num only : 1 ≤ 2).trans hR
  have hmoment := prime_energy_decreasing_range_of_order_envelope η r nmax R hη.le hr hRone hlarge
  have hlog : η * Real.log ((cutoff + 1 : ℕ) : ℝ) ≤ c₁ * K := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlogX
  exact
    primitiveCharacterPrimeLogPower_grid_hybrid_normalized_detector_order_bound R hR T hT hTupper r
      (highPrimeEulerSupport R cutoff) (fun p hp ↦ (mem_highPrimeEulerSupport.mp hp).2.1)
      (fun p hp ↦ (mem_highPrimeEulerSupport.mp hp).2.2.le) (cutoff + 1)
      (fun p hp ↦ (mem_highPrimeEulerSupport.mp hp).1.trans (Nat.le_succ cutoff)) a h gridSize hh ha
      hb η c₁ K hη hc₁ hhη (Nat.succ_pos cutoff) hlog (R ^ 6) (Nat.one_le_pow 6 R hRone) hηsmall
      hmoment (fun p hp ↦ (mem_highPrimeEulerSupport.mp hp).2.2)

/-- For a positive rate at most one and prime support above a decreasing-range
cutoff, bound the factorial-normalized logarithmic moment by the Chernoff tail.
Compare the prime sum with the von Mangoldt series. This supplies the first derivative energy. -/
theorem normalized_finite_prime_log_moment_le_chernoff (η : ℝ) (m N : ℕ) (s : Finset ℕ) (hη : 0 < η)
    (hηsmall : η ≤ 1) (hN : 1 ≤ N) (hm : (m : ℝ) ≤ (1 + η) * Real.log N)
    (hprime : ∀ p ∈ s, Nat.Prime p) (habove : ∀ p ∈ s, N < p) :
    η ^ (m + 1) / (m.factorial : ℝ) * (∑ p ∈ s, (Real.log p) ^ (m + 1) / (p : ℝ) ^ (1 + η)) ≤
      3 * (Real.log 4 + 4) * (2 : ℝ) ^ m * Real.exp (-(η * Real.log N) / 2) := by
  have hcompare :=
    finite_prime_log_moment_le_vonMangoldt_tail (η / 2) m N s (half_pos hη) hprime habove
  rw [show 2 * (η / 2) = η by ring] at hcompare
  exact
    (mul_le_mul_of_nonneg_left hcompare
          (div_nonneg (pow_nonneg hη.le (m + 1)) (Nat.cast_nonneg m.factorial))).trans
      (normalized_vonMangoldt_log_weight_tail_le_chernoff η m N hη hηsmall hN hm)

/-- For a rate and order, multiplying the detector normalization by the rate
equals the next-order normalization times `r+1`. Expand the successor factorial and
cancel its positive factor. This identifies the rate in the height-variation estimate. -/
theorem factorial_normalization_successor_scale (η : ℝ) (r : ℕ) :
    η * (η ^ (r + 1) / (r.factorial : ℝ)) =
      (r + 1 : ℝ) * (η ^ ((r + 1) + 1) / ((r + 1).factorial : ℝ)) := by
  have hr : (r + 1 : ℝ) ≠ 0 := ne_of_gt (add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) zero_lt_one)
  rw [Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  rw [div_mul_eq_div_mul_one_div, ← mul_assoc, mul_div_cancel₀ _ hr]
  ring

/-- Under the prime moment hypotheses, multiplying the normalized next-order
absolute moment by `η` leaves an explicit order-dependent bound. Combine the Chernoff
moment and the successor-factorial identity, discarding a decaying exponential.
This yields variation of size an absolute order factor divided by `η`. -/
theorem scaled_prime_log_derivative_moment_le (η : ℝ) (r N : ℕ) (s : Finset ℕ) (hη : 0 < η)
    (hηsmall : η ≤ 1) (hN : 1 ≤ N) (hr : ((r + 1 : ℕ) : ℝ) ≤ (1 + η) * Real.log N)
    (hprime : ∀ p ∈ s, Nat.Prime p) (habove : ∀ p ∈ s, N < p) :
    η * (η ^ (r + 1) / (r.factorial : ℝ)) * (∑ p ∈ s, (Real.log p) ^ (r + 2) / (p : ℝ) ^ (1 + η)) ≤
      3 * (Real.log 4 + 4) * (r + 1) * (2 : ℝ) ^ (r + 1) := by
  have hmoment :=
    normalized_finite_prime_log_moment_le_chernoff η (r + 1) N s hη hηsmall hN hr hprime habove
  have hexp : Real.exp (-(η * Real.log N) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (div_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr (mul_nonneg hη.le (Real.log_nonneg (by exact_mod_cast hN))))
        (by norm_num only))
  have hC : 0 ≤ 3 * (Real.log 4 + 4) * (2 : ℝ) ^ (r + 1) :=
    mul_nonneg
      (mul_nonneg (by norm_num only)
        (add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)))
      (pow_nonneg (by norm_num only) _)
  have hbound := hmoment.trans (by simpa only [mul_one] using (mul_le_mul_of_nonneg_left hexp hC))
  have hscaled :=
    mul_le_mul_of_nonneg_left hbound (add_nonneg (Nat.cast_nonneg r : (0 : ℝ) ≤ r) zero_le_one)
  rw [factorial_normalization_successor_scale, mul_assoc]
  simpa only [Nat.add_assoc, Nat.reduceAdd, mul_assoc, mul_left_comm, mul_comm] using hscaled

/-- For finite support, logarithmic order, real abscissa, coefficient twist,
and height, define the twisted prime-log exponential sum. The coefficient has real decay
and a unit oscillatory factor. This represents the high-prime detector on height windows. -/
noncomputable def primeLogPowerPolynomial (s : Finset ℕ) (r : ℕ) (σ : ℝ) (χ : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ p ∈ s,
    (((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)) *
      Complex.exp ((-(t * Real.log p) : ℝ) * Complex.I) *
      χ p

/--
Inputs: finite prime support, a derivative order, a real abscissa, and a coefficient twist.
Claim: the associated prime-log polynomial is continuous in its height variable.
Proof: each summand is a constant multiple of a complex exponential of a continuous linear map.
Role: supplies interval integrability for energy estimates on physical detection windows.
-/
theorem primePoly_cont (s : Finset ℕ) (r : ℕ) (σ : ℝ) (χ : ℕ → ℂ) :
    Continuous (primeLogPowerPolynomial s r σ χ) := by
  unfold primeLogPowerPolynomial
  apply continuous_finsetSum
  intro p hp
  have hreal : Continuous (fun t : ℝ => -(t * Real.log (p : ℝ))) := (continuous_id.mul_const _).neg
  have harg : Continuous (fun t : ℝ => ((-(t * Real.log (p : ℝ)) : ℝ) : ℂ) * Complex.I) :=
    (Complex.continuous_ofReal.comp hreal).mul continuous_const
  have hphase : Continuous (fun t : ℝ => Complex.exp ((-(t * Real.log (p : ℝ)) : ℝ) * Complex.I)) :=
    Complex.continuous_exp.comp harg
  exact ((continuous_const.mul hphase).mul continuous_const)

/-- For a positive index, identify the complex coefficient norm with its real
logarithmic weight. Evaluate the exponential norm and positive-base real power.
This converts polynomial derivative bounds into nonnegative prime moments. -/
theorem norm_prime_log_power_coefficient_eq (p r : ℕ) (σ : ℝ) (hp : 0 < p) :
    ‖((Real.log p : ℝ) ^ (r + 1) : ℂ) * Complex.exp (-((Real.log p : ℝ) * σ : ℝ) : ℂ)‖ =
      (Real.log p) ^ (r + 1) / (p : ℝ) ^ σ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_natCast_nonneg p), Complex.norm_exp]
  simp only [Complex.neg_re, Complex.ofReal_re]
  rw [Real.rpow_def_of_pos hpR, div_eq_mul_inv, Real.exp_neg]

/-- The finite prime-log polynomial is differentiable in height, with derivative
`-I` times the next-order polynomial. Apply the existing finite exponential-sum derivative.
This supplies the height derivative for the mean-value estimate. -/
theorem primeLogPowerPolynomial_hasDerivAt (s : Finset ℕ) (r : ℕ) (σ t : ℝ) (χ : ℕ → ℂ) :
    HasDerivAt (primeLogPowerPolynomial s r σ χ)
      (-Complex.I * primeLogPowerPolynomial s (r + 1) σ χ t) t := by
  unfold primeLogPowerPolynomial
  simpa only [Nat.add_assoc, Nat.reduceAdd] using
    (finite_prime_log_power_exponential_sum_hasDerivAt (s := s) r σ t χ)

/-- For positive support and twists of norm at most one, bound the polynomial
norm by its untwisted logarithmic moment. Apply the norm triangle inequality and the unit
phase norm. This is the absolute derivative majorant for height-window transfer. -/
theorem norm_primeLogPowerPolynomial_le_log_moment (s : Finset ℕ) (r : ℕ) (σ t : ℝ) (χ : ℕ → ℂ)
    (hpos : ∀ p ∈ s, 0 < p) (hχ : ∀ p ∈ s, ‖χ p‖ ≤ 1) :
    ‖primeLogPowerPolynomial s r σ χ t‖ ≤ ∑ p ∈ s, (Real.log p) ^ (r + 1) / (p : ℝ) ^ σ := by
  apply (norm_sum_le s _).trans
  apply Finset.sum_le_sum
  intro p hp
  rw [norm_mul, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    norm_prime_log_power_coefficient_eq p r σ (hpos p hp)]
  exact
    (mul_le_mul_of_nonneg_left (hχ p hp)
          (div_nonneg (pow_nonneg (Real.log_natCast_nonneg p) _)
            (Real.rpow_nonneg (Nat.cast_nonneg p) _))).trans_eq
      (mul_one _)

/-- For positive finite support and bounded twists, polynomial variation is at
most the height distance times the next logarithmic moment. Bound the derivative on the
whole real line and apply the convex mean-value theorem.
This gives a height-independent Lipschitz bound on the common support. -/
theorem primeLogPowerPolynomial_vertical_variation (s : Finset ℕ) (r : ℕ) (σ t u : ℝ) (χ : ℕ → ℂ)
    (hpos : ∀ p ∈ s, 0 < p) (hχ : ∀ p ∈ s, ‖χ p‖ ≤ 1) :
    ‖primeLogPowerPolynomial s r σ χ u - primeLogPowerPolynomial s r σ χ t‖ ≤
      |u - t| * ∑ p ∈ s, (Real.log p) ^ (r + 2) / (p : ℝ) ^ σ := by
  have hder v := primeLogPowerPolynomial_hasDerivAt s r σ v χ
  have hbound v :
    ‖deriv (primeLogPowerPolynomial s r σ χ) v‖ ≤
      ∑ p ∈ s, (Real.log p) ^ (r + 2) / (p : ℝ) ^ σ := by
    rw [(hder v).deriv, norm_mul, norm_neg, Complex.norm_I, one_mul]
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      norm_primeLogPowerPolynomial_le_log_moment s (r + 1) σ v χ hpos hχ
  have hvar :=
    Convex.norm_image_sub_le_of_norm_deriv_le (fun v (_ : v ∈ Set.univ) ↦ (hder v).differentiableAt)
      (fun v (_ : v ∈ Set.univ) ↦ hbound v) (convex_univ : Convex ℝ (Set.univ : Set ℝ))
      (Set.mem_univ t) (Set.mem_univ u)
  simpa only [Real.norm_eq_abs, mul_comm] using hvar

/-- For a natural derivative order, define the absolute variation coefficient
`3(log 4+4)(r+1)2^(r+1)`. Together with the inverse near-one rate, it controls the
normalized high-prime polynomial slope and the physical detection-window radius. -/
noncomputable def primeLogPowerVariationBound (r : ℕ) : ℝ :=
  3 * (Real.log 4 + 4) * (r + 1) * (2 : ℝ) ^ (r + 1)

/-- The absolute variation coefficient is positive at every natural order.
Each defining factor is positive. This permits division when choosing detection windows. -/
theorem primeLogPowerVariationBound_pos (r : ℕ) : 0 < primeLogPowerVariationBound r := by
  exact
    mul_pos
      (mul_pos
        (mul_pos (by norm_num only)
          (add_pos_of_nonneg_of_pos (Real.log_nonneg (by norm_num only)) (by norm_num only)))
        (add_pos_of_nonneg_of_pos (Nat.cast_nonneg r) zero_lt_one))
      (pow_pos (by norm_num only) _)

/-- The absolute variation coefficient increases with the natural order.
Compare the linear and exponential factors. This provides one slope bound for an order family. -/
theorem primeLogPowerVariationBound_mono {r nmax : ℕ} (hr : r ≤ nmax) :
    primeLogPowerVariationBound r ≤ primeLogPowerVariationBound nmax := by
  have horder : (r : ℝ) + 1 ≤ (nmax : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hr 1
  exact
    mul_le_mul
      (mul_le_mul_of_nonneg_left horder
        (mul_nonneg (by norm_num only)
          (add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only))))
      (pow_le_pow_right₀ (by norm_num only : (1 : ℝ) ≤ 2) (Nat.add_le_add_right hr 1))
      (pow_nonneg (by norm_num only) _)
      (by
        exact
          mul_nonneg
            (mul_nonneg (by norm_num only)
              (add_nonneg (Real.log_nonneg (by norm_num only)) (by norm_num only)))
            (add_nonneg (Nat.cast_nonneg nmax) zero_le_one))

/-- For the decreasing prime support, multiply normalized polynomial variation
by `η` and bound it by the height distance times the absolute order coefficient.
Combine the mean-value estimate and the sharp prime moment bound.
This avoids an extra inverse-rate loss in the physical detection window. -/
theorem scaled_primeLogPowerPolynomial_vertical_variation (η : ℝ) (r N : ℕ) (s : Finset ℕ) (t u : ℝ)
    (χ : ℕ → ℂ) (hη : 0 < η) (hηsmall : η ≤ 1) (hN : 1 ≤ N)
    (hr : ((r + 1 : ℕ) : ℝ) ≤ (1 + η) * Real.log N) (hprime : ∀ p ∈ s, Nat.Prime p)
    (habove : ∀ p ∈ s, N < p) (hχ : ∀ p ∈ s, ‖χ p‖ ≤ 1) :
    η * (η ^ (r + 1) / (r.factorial : ℝ)) *
        ‖primeLogPowerPolynomial s r (1 + η) χ u - primeLogPowerPolynomial s r (1 + η) χ t‖ ≤
      |u - t| * primeLogPowerVariationBound r := by
  dsimp only [primeLogPowerVariationBound]
  have hvar :=
    primeLogPowerPolynomial_vertical_variation s r (1 + η) t u χ (fun p hp ↦ (hprime p hp).pos) hχ
  have hscaled :=
    mul_le_mul_of_nonneg_left hvar
      (mul_nonneg hη.le (div_nonneg (pow_nonneg hη.le (r + 1)) (Nat.cast_nonneg r.factorial)))
  have hmoment :=
    mul_le_mul_of_nonneg_left
      (scaled_prime_log_derivative_moment_le η r N s hη hηsmall hN hr hprime habove)
      (abs_nonneg (u - t))
  nlinarith only [hscaled, hmoment]

/-- For a normalized polynomial signal, a shared order envelope, and decreasing
prime support, retain half the signal whenever the height distance is at most
`η B / (2 C(nmax))`. Use the uniform normalized variation bound and the norm triangle
inequality. This gives a physical window proportional to `η`, rather than to the mesh step. -/
theorem normalized_primeLogPowerPolynomial_window (η B : ℝ) (r nmax N : ℕ) (s : Finset ℕ) (t u : ℝ)
    (χ : ℕ → ℂ) (hη : 0 < η) (hηsmall : η ≤ 1) (hN : 1 ≤ N) (hrmax : r ≤ nmax)
    (hr : ((r + 1 : ℕ) : ℝ) ≤ (1 + η) * Real.log N) (hprime : ∀ p ∈ s, Nat.Prime p)
    (habove : ∀ p ∈ s, N < p) (hχ : ∀ p ∈ s, ‖χ p‖ ≤ 1)
    (hdet : B ≤ (η ^ (r + 1) / (r.factorial : ℝ)) * ‖primeLogPowerPolynomial s r (1 + η) χ t‖)
    (hdist : |u - t| ≤ η * B / (2 * primeLogPowerVariationBound nmax)) :
    B / 2 ≤ (η ^ (r + 1) / (r.factorial : ℝ)) * ‖primeLogPowerPolynomial s r (1 + η) χ u‖ := by
  have hC := primeLogPowerVariationBound_pos nmax
  have hvar :=
    scaled_primeLogPowerPolynomial_vertical_variation η r N s t u χ hη hηsmall hN hr hprime habove
      hχ
  have hCm :=
    mul_le_mul_of_nonneg_left (primeLogPowerVariationBound_mono hrmax) (abs_nonneg (u - t))
  have hdistC := mul_le_mul_of_nonneg_right hdist hC.le
  rw [div_mul_eq_mul_div, mul_div_mul_right _ _ (ne_of_gt hC)] at hdistC
  have ht :=
    norm_sub_le (primeLogPowerPolynomial s r (1 + η) χ u)
      (primeLogPowerPolynomial s r (1 + η) χ u - primeLogPowerPolynomial s r (1 + η) χ t)
  rw [sub_sub_cancel] at ht
  have hA : 0 ≤ η * (η ^ (r + 1) / (r.factorial : ℝ)) :=
    mul_nonneg hη.le (div_nonneg (pow_nonneg hη.le _) (Nat.cast_nonneg _))
  have htriangle := mul_le_mul_of_nonneg_left ht hA
  have hsignal := mul_le_mul_of_nonneg_left hdet hη.le
  apply (mul_le_mul_iff_left₀ hη).mp
  nlinarith only [hvar, hCm, hdistC, htriangle, hsignal]

/-- The finite Euler sum on the actual high-prime support equals the height
polynomial with character twist. Apply the prime-term identity on that support.
This joins the common high-prime detector to the physical-window and hybrid estimates. -/
theorem finite_highPrimeEuler_sum_eq_primeLogPowerPolynomial {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (R cutoff r : ℕ) (σ t : ℝ) :
    (∑ p ∈ highPrimeEulerSupport R cutoff,
        LSeries.term
          (LSeries.logMul^[r] (fun k : ℕ ↦ χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)))
          ((σ : ℂ) + (t : ℂ) * Complex.I) p) =
      primeLogPowerPolynomial (highPrimeEulerSupport R cutoff) r σ (fun k ↦ χ (k : ZMod q)) t := by
  exact
    finite_prime_vonMangoldt_logMul_sum_eq r σ t (highPrimeEulerSupport R cutoff)
      (fun p hp ↦ (mem_highPrimeEulerSupport.mp hp).2.1) χ

/-- The absolute variation coefficient is at least one. Bound its constant, linear,
and exponential factors from below. This controls the physical window by `η/8`. -/
theorem one_le_primeLogPowerVariationBound (r : ℕ) : 1 ≤ primeLogPowerVariationBound r := by
  have hlog : (4 : ℝ) ≤ Real.log 4 + 4 := le_add_of_nonneg_left (Real.log_nonneg (by norm_num only))
  have hC : (1 : ℝ) ≤ 3 * (Real.log 4 + 4) := by linarith only [hlog]
  have hr : (1 : ℝ) ≤ r + 1 := le_add_of_nonneg_left (Nat.cast_nonneg r)
  have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ (r + 1) := one_le_pow₀ (by norm_num only)
  exact
    hC.trans
      ((le_mul_of_one_le_right (le_trans zero_le_one hC) hr).trans
        (le_mul_of_one_le_right (mul_nonneg (le_trans zero_le_one hC) (le_trans zero_le_one hr))
          hpow))

/-- The coefficient of the physical high-prime window is positive for every real
exponent and natural order envelope. This permits choosing a finite incidence mesh. -/
theorem uniform_high_prime_window_factor_pos (D : ℝ) (K nmax : ℕ) :
    0 < Real.exp (-(D * (K : ℝ))) / (16 * primeLogPowerVariationBound nmax) :=
  div_pos (Real.exp_pos _) (mul_pos (by norm_num only) (primeLogPowerVariationBound_pos _))

/-- For a nonnegative detector exponent, the physical window coefficient is at
most one eighth. Bound the exponential by one and the variation coefficient from below.
This keeps every detection window inside the local zero-counting scale. -/
theorem uniform_high_prime_window_factor_le (D : ℝ) (K nmax : ℕ) (hD : 0 ≤ D) :
    Real.exp (-(D * (K : ℝ))) / (16 * primeLogPowerVariationBound nmax) ≤ 1 / 8 := by
  have he : Real.exp (-(D * (K : ℝ))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg hD (Nat.cast_nonneg K)))
  apply
    (div_le_iff₀
        (mul_pos (by norm_num only : (0 : ℝ) < 16) (primeLogPowerVariationBound_pos nmax))).mpr
  nlinarith only [he, one_le_primeLogPowerVariationBound nmax]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
