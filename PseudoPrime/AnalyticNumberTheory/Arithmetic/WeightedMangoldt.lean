/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.LSeries.Dirichlet
import PseudoPrime.AnalyticNumberTheory.Arithmetic.PrimeFactors

/-!
# Weighted von Mangoldt sums

Generic finite weighted sums built from the von Mangoldt function and Dirichlet characters,
together with the elementary reindexing and estimation lemmas for finite sums over prime powers
that these weighted sums reduce to.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The logarithmically weighted von Mangoldt summand `Λ(n) log(x / n)`. -/
noncomputable def logWeightedMangoldtTerm (x : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * Real.log (x / n)

/-- The real weighted von Mangoldt sum occurring in the Riemann explicit formula. -/
noncomputable def logWeightedMangoldtSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, logWeightedMangoldtTerm x n

/-- The part of the logarithmically weighted sum with `(n, m) > 1`. -/
noncomputable def commonFactorLogWeightedSum (x : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n m, logWeightedMangoldtTerm x n

/-- The reciprocal weight `Λ(n) / n * (1 - n / x)`. -/
noncomputable def reciprocalWeightedMangoldtTerm (x : ℝ) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n / n * (1 - n / x)

/-- The real reciprocal weighted sum occurring in the Riemann explicit formula. -/
noncomputable def reciprocalWeightedMangoldtSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, reciprocalWeightedMangoldtTerm x n

/-- The part of the reciprocal weighted sum with `(n, m) > 1`. -/
noncomputable def commonFactorReciprocalWeightedSum (x : ℝ) (m : ℕ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n m, reciprocalWeightedMangoldtTerm x n

/-- The reciprocal weighted sum splits into its coprime part and the common-factor part. -/
theorem reciprocalWeightedMangoldtSum_eq_coprime_add_common (x : ℝ) (q : ℕ) :
    reciprocalWeightedMangoldtSum x =
      ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ Nat.Coprime n q, reciprocalWeightedMangoldtTerm x n +
        commonFactorReciprocalWeightedSum x q := by
  rw [reciprocalWeightedMangoldtSum, commonFactorReciprocalWeightedSum]
  exact
    (Finset.sum_filter_add_sum_filter_not (s := Finset.Ioc 0 ⌊x⌋₊) (f :=
        reciprocalWeightedMangoldtTerm x) (p := fun n ↦ Nat.Coprime n q)).symm

/-- The complex logarithmically weighted von Mangoldt summand attached to a character. -/
noncomputable def characterLogWeightedTerm {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ℂ :=
  (logWeightedMangoldtTerm x n : ℂ) * χ n

/-- The finite character sum `Σ_{0 < n ≤ x} Λ(n) * log(x/n) * χ(n)`. -/
noncomputable def characterLogWeightedSum {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, characterLogWeightedTerm x χ n

/-- The complex reciprocal weighted Mangoldt summand attached to a character. -/
noncomputable def characterReciprocalWeightedTerm {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q)
    (n : ℕ) : ℂ :=
  (reciprocalWeightedMangoldtTerm x n : ℂ) * χ n

/-- The finite character sum `Σ_{0 < n ≤ x} Λ(n)/n * (1 - n/x) * χ(n)`. -/
noncomputable def characterReciprocalWeightedSum {q : ℕ} (x : ℝ) (χ : DirichletCharacter ℂ q) : ℂ :=
  ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, characterReciprocalWeightedTerm x χ n

/-- Outside the prime powers, the logarithmically weighted summand vanishes. -/
theorem logWeightedMangoldtTerm_eq_zero_of_not_primePow {x : ℝ} {n : ℕ} (hn : ¬IsPrimePow n) :
    logWeightedMangoldtTerm x n = 0 := by
  rw [logWeightedMangoldtTerm, ArithmeticFunction.vonMangoldt_apply]
  simp only [hn, ↓reduceIte, zero_mul]

/-- Outside the prime powers, the reciprocal weighted summand vanishes. -/
theorem reciprocalWeightedMangoldtTerm_eq_zero_of_not_primePow {x : ℝ} {n : ℕ}
    (hn : ¬IsPrimePow n) : reciprocalWeightedMangoldtTerm x n = 0 := by
  rw [reciprocalWeightedMangoldtTerm, ArithmeticFunction.vonMangoldt_apply]
  simp only [hn, ↓reduceIte, zero_div, zero_mul]

/-- The finite reciprocal prime-power tail is bounded by its infinite geometric sum. -/
theorem sum_log_div_prime_pow_le {p N : ℕ} (hp : p.Prime) :
    ∑ k ∈ Finset.Icc 1 N, Real.log p / (p : ℝ) ^ k ≤ Real.log p / (p - 1) := by
  have hpcast : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hinv0 : 0 ≤ (p : ℝ)⁻¹ := inv_nonneg.mpr (zero_le_one.trans hpcast.le)
  have hinv1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hpcast
  calc
    _ = Real.log p * ∑ k ∈ Finset.Icc 1 N, ((p : ℝ)⁻¹) ^ k := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [inv_pow, div_eq_mul_inv]
    _ ≤ Real.log p * ((p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)) := by
      apply mul_le_mul_of_nonneg_left
      · rw [← Finset.Ico_add_one_right_eq_Icc]
        simpa only [pow_one] using
          (geom_sum_Ico_le_of_lt_one (x := (p : ℝ)⁻¹) (m := 1) (n := N + 1) hinv0 hinv1)
      · exact Real.log_nonneg hpcast.le
    _ = Real.log p / (p - 1) := by
      have hp0 : (p : ℝ) ≠ 0 := ne_of_gt (zero_lt_one.trans hpcast)
      have hp1 : (p : ℝ) - 1 ≠ 0 := sub_ne_zero.mpr hpcast.ne'
      field_simp

/-- Closed form for the finite arithmetic sum occurring in the logarithmic estimate. -/
theorem two_mul_sum_log_weight (a L : ℝ) (K : ℕ) :
    2 * ∑ k ∈ Finset.Icc 1 K, a * (L - k * a) = K * a * (2 * L - (K + 1) * a) := by
  induction K with
  | zero =>
    have h : Finset.Icc 1 0 = ∅ := by decide
    rw [h]
    simp only [Finset.sum_empty, Nat.cast_zero, zero_mul, mul_zero]
  | succ K ih =>
    rw [Finset.sum_Icc_succ_top (by omega), mul_add, ih]
    push_cast
    ring

/-- Every initial arithmetic log-weight sum is at most half the square of its endpoint log. -/
theorem sum_log_weight_le_half_sq (a L : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.Icc 1 K, a * (L - k * a) ≤ L ^ 2 / 2 := by
  have hidentity := two_mul_sum_log_weight a L K
  have hnonneg : 0 ≤ (L - K * a) ^ 2 + K * a ^ 2 := by positivity
  nlinarith

/-- A finite sum over prime powers can be reindexed with the prime as its outer variable. -/
theorem sum_primePow_eq_sum_primesLE (f : ℕ → ℝ) (n : ℕ) :
    ∑ q ∈ Finset.Icc 1 n with IsPrimePow q, f q =
      ∑ p ∈ Nat.primesLE n, ∑ k ∈ Finset.Icc 1 (p.log n), f (p ^ k) := by
  calc
    _ =
        ∑
          q ∈
            ((Finset.Icc 1 n).filter Nat.Prime).biUnion fun p ↦
              (Finset.Icc 1 (p.log n)).image fun k ↦ p ^ k,
          f q :=
      by
      refine (Finset.sum_subset (fun q hq ↦ ?_) fun q hq hqnot ↦ ?_).symm
      · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image] at hq ⊢
        obtain ⟨p, ⟨⟨hp1, hpn⟩, hp⟩, k, ⟨hk1, hklog⟩, rfl⟩ := hq
        exact
          ⟨⟨Nat.one_le_of_lt (Nat.pow_pos (Nat.zero_lt_one.trans_le hp1)),
              Nat.pow_le_of_le_log (by omega) hklog⟩,
            hp.prime.isPrimePow.pow (by omega)⟩
      · exfalso
        apply hqnot
        simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, Finset.mem_image]
        simp only [Finset.mem_filter, Finset.mem_Icc] at hq
        have hqdata := hq
        obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff (n := q)).mp hqdata.2
        have hpn : p ≤ n := (Nat.le_self_pow hk.ne' p).trans hqdata.1.2
        exact ⟨p, ⟨⟨hp.one_le, hpn⟩, hp⟩, k, ⟨hk, Nat.le_log_of_pow_le hp.one_lt hqdata.1.2⟩, rfl⟩
    _ =
        ∑ p ∈ Finset.Icc 1 n with p.Prime,
          ∑ q ∈ (Finset.Icc 1 (p.log n)).image fun k ↦ p ^ k, f q :=
      by
      rw [Finset.sum_biUnion]
      rw [Finset.pairwiseDisjoint_iff]
      grind [Nat.Prime.pow_inj']
    _ = ∑ p ∈ Nat.primesLE n, ∑ k ∈ Finset.Icc 1 (p.log n), f (p ^ k) := by
      refine Finset.sum_congr (Nat.primesLE_eq_filter_Icc_one n).symm fun p hp ↦ ?_
      exact
        Finset.sum_image fun a ha b hb hab ↦
          Nat.pow_right_injective (Nat.two_le_of_mem_primesLE hp) hab

/--
A finite sum supported on prime powers can be reindexed by exponent and prime while retaining
the condition that its index is not coprime to `m`.
-/
theorem sum_not_coprime_eq_sum_prime_powers (f : ℕ → ℝ) (m : ℕ) {x : ℝ} (hx : 0 ≤ x)
    (hf : ∀ n : ℕ, ¬IsPrimePow n → f n = 0) :
    ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter fun n ↦ ¬Nat.Coprime n m, f n =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ∣ m, f (p ^ k) := by
  calc
    _ = ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter IsPrimePow, if ¬Nat.Coprime n m then f n else 0 := by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro n hn
      by_cases hpow : IsPrimePow n
      · simp only [hpow, ↓reduceIte]
      · rw [hf n hpow]
        simp only [ite_self]
    _ =
        ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
          ∑ p ∈ Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊ with p.Prime,
            if ¬Nat.Coprime (p ^ k) m then f (p ^ k) else 0 :=
      by exact Chebyshev.sum_PrimePow_eq_sum_sum (fun n ↦ if ¬Nat.Coprime n m then f n else 0) hx
    _ = _ := by
      apply Finset.sum_congr rfl
      intro k hk
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      have hkpos : 0 < k := (Finset.mem_Icc.mp hk).1
      simp only [Nat.coprime_pow_left_iff hkpos]
      by_cases hprime : p.Prime
      · by_cases hdvd : p ∣ m
        · simp only [hprime, ↓reduceIte, hprime.coprime_iff_not_dvd, hdvd, not_true_eq_false,
            not_false_eq_true, and_self]
        · simp only [hprime, ↓reduceIte, hprime.coprime_iff_not_dvd, hdvd, not_false_eq_true,
            not_true_eq_false, and_false]
      · simp only [hprime, false_and, ↓reduceIte]

/-- On a nontrivial power of a prime, the logarithmic summand has an explicit affine form. -/
theorem logWeightedMangoldtTerm_prime_pow {x : ℝ} {p k : ℕ} (hx : x ≠ 0) (hp : p.Prime)
    (hk : k ≠ 0) :
    logWeightedMangoldtTerm x (p ^ k) = Real.log p * (Real.log x - k * Real.log p) := by
  have hpk0 : ((p ^ k : ℕ) : ℝ) ≠ 0 := by exact_mod_cast pow_ne_zero k hp.ne_zero
  rw [logWeightedMangoldtTerm, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp, Real.log_div hx hpk0, Nat.cast_pow, Real.log_pow]

/-- On a nontrivial power of a prime, the reciprocal summand has its geometric-series form. -/
theorem reciprocalWeightedMangoldtTerm_prime_pow {x : ℝ} {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) :
    reciprocalWeightedMangoldtTerm x (p ^ k) =
      Real.log p / (p : ℝ) ^ k * (1 - (p : ℝ) ^ k / x) := by
  rw [reciprocalWeightedMangoldtTerm, ArithmeticFunction.vonMangoldt_apply_pow hk,
    ArithmeticFunction.vonMangoldt_apply_prime hp, Nat.cast_pow]

/-- A reciprocal prime-power summand is bounded by the corresponding geometric term. -/
theorem reciprocalWeightedMangoldtTerm_prime_pow_le {x : ℝ} {p k : ℕ} (hx : 0 < x) (hp : p.Prime)
    (hk : k ≠ 0) : reciprocalWeightedMangoldtTerm x (p ^ k) ≤ Real.log p / (p : ℝ) ^ k := by
  rw [reciprocalWeightedMangoldtTerm_prime_pow hp hk]
  have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
  have hcoeff : 0 ≤ Real.log p / (p : ℝ) ^ k := div_nonneg hlog (by positivity)
  exact mul_le_of_le_one_right hcoeff (sub_le_self 1 (by positivity))

/-- The complete initial logarithmic prime-power contribution is at most half `log(x) ^ 2`. -/
theorem sum_logWeightedMangoldtTerm_prime_pow_le {x : ℝ} {p K : ℕ} (hx : x ≠ 0) (hp : p.Prime) :
    ∑ k ∈ Finset.Icc 1 K, logWeightedMangoldtTerm x (p ^ k) ≤ (Real.log x) ^ 2 / 2 := by
  calc
    _ = ∑ k ∈ Finset.Icc 1 K, Real.log p * (Real.log x - k * Real.log p) := by
      apply Finset.sum_congr rfl
      intro k hk
      exact
        logWeightedMangoldtTerm_prime_pow hx hp
          (Nat.ne_of_gt (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1))
    _ ≤ (Real.log x) ^ 2 / 2 := sum_log_weight_le_half_sq _ _ _

/--
The logarithmic common-factor sum can be reindexed with prime divisors of `m` outside and their
admissible positive exponents inside.
-/
theorem commonFactorLogWeightedSum_eq_sum_prime_divisors (m : ℕ) (x : ℝ) :
    commonFactorLogWeightedSum x m =
      ∑ p ∈ (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ m,
        ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), logWeightedMangoldtTerm x (p ^ k) := by
  calc
    _ =
        ∑ q ∈ Finset.Icc 1 ⌊x⌋₊ with IsPrimePow q,
          if ¬Nat.Coprime q m then logWeightedMangoldtTerm x q else 0 :=
      by
      rw [commonFactorLogWeightedSum, ← Finset.Icc_add_one_left_eq_Ioc]
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      by_cases hpow : IsPrimePow q
      · simp only [hpow, ↓reduceIte]
      · rw [logWeightedMangoldtTerm_eq_zero_of_not_primePow hpow]
        simp only [ite_self]
    _ =
        ∑ p ∈ Nat.primesLE ⌊x⌋₊,
          ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊),
            if ¬Nat.Coprime (p ^ k) m then logWeightedMangoldtTerm x (p ^ k) else 0 :=
      by
      exact
        sum_primePow_eq_sum_primesLE
          (fun q ↦ if ¬Nat.Coprime q m then logWeightedMangoldtTerm x q else 0) ⌊x⌋₊
    _ = _ := by
      simp_rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p hp
      have hpprime : p.Prime := Nat.prime_of_mem_primesLE hp
      by_cases hdvd : p ∣ m
      · simp only [hdvd, ↓reduceIte]
        apply Finset.sum_congr rfl
        intro k hk
        have hkpos : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
        have hcop : ¬Nat.Coprime (p ^ k) m := by
          rw [Nat.coprime_pow_left_iff hkpos, hpprime.coprime_iff_not_dvd]
          exact not_not_intro hdvd
        simp only [hcop, not_false_eq_true, ↓reduceIte]
      · simp only [hdvd, ↓reduceIte]
        apply Finset.sum_eq_zero
        intro k hk
        have hkpos : 0 < k := Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1
        have hcop : Nat.Coprime (p ^ k) m := by
          rw [Nat.coprime_pow_left_iff hkpos]
          exact hpprime.coprime_iff_not_dvd.mpr hdvd
        rw [ite_eq_right (not_not_intro hcop)]

/--
For `m ≠ 0` and `x > 0`, the logarithmic common-factor weighted sum is at most
`ω(m) * log(x) ^ 2 / 2`, by the arithmetic-sum bound for each prime divisor of `m`.
-/
theorem commonFactorLogWeightedSum_le {m : ℕ} (hm0 : m ≠ 0) {x : ℝ} (hx : 0 < x) :
    commonFactorLogWeightedSum x m ≤ (1 / 2 : ℝ) * m.primeFactors.card * (Real.log x) ^ 2 := by
  rw [commonFactorLogWeightedSum_eq_sum_prime_divisors m x]
  let source := (Nat.primesLE ⌊x⌋₊).filter fun p ↦ p ∣ m
  calc
    ∑ p ∈ source, ∑ k ∈ Finset.Icc 1 (p.log ⌊x⌋₊), logWeightedMangoldtTerm x (p ^ k) ≤
        ∑ p ∈ source, (Real.log x) ^ 2 / 2 :=
      by
      apply Finset.sum_le_sum
      intro p hp
      exact
        sum_logWeightedMangoldtTerm_prime_pow_le hx.ne'
          (Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1)
    _ ≤ ∑ p ∈ m.primeFactors, (Real.log x) ^ 2 / 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        have hpdata := Finset.mem_filter.mp hp
        exact Nat.mem_primeFactors.mpr ⟨Nat.prime_of_mem_primesLE hpdata.1, hpdata.2, hm0⟩
      · intro p hp hpmissing
        positivity
    _ = (1 / 2 : ℝ) * m.primeFactors.card * (Real.log x) ^ 2 := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/--
The common-factor reciprocal weighted sum is a double sum over powers of primes not coprime
to the modulus.
-/
theorem commonFactorReciprocalWeightedSum_eq_sum_prime_powers (m : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    commonFactorReciprocalWeightedSum x m =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ∣ m,
          reciprocalWeightedMangoldtTerm x (p ^ k) := by
  exact
    sum_not_coprime_eq_sum_prime_powers (reciprocalWeightedMangoldtTerm x) m hx fun _ ↦
      reciprocalWeightedMangoldtTerm_eq_zero_of_not_primePow

/--
The reciprocal common-factor sum is bounded by complete finite geometric tails for all prime
divisors of the modulus.
-/
theorem commonFactorReciprocalWeightedSum_le_primeFactors {m : ℕ} (hm0 : m ≠ 0) {x : ℝ}
    (hx : 0 < x) :
    commonFactorReciprocalWeightedSum x m ≤
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ m.primeFactors, Real.log p / (p : ℝ) ^ k := by
  rw [commonFactorReciprocalWeightedSum_eq_sum_prime_powers m hx.le]
  apply Finset.sum_le_sum
  intro k hk
  let source := (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter fun p ↦ p.Prime ∧ p ∣ m
  calc
    ∑ p ∈ source, reciprocalWeightedMangoldtTerm x (p ^ k) ≤
        ∑ p ∈ source, Real.log p / (p : ℝ) ^ k :=
      by
      apply Finset.sum_le_sum
      intro p hp
      have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.zero_lt_one.trans_le (Finset.mem_Icc.mp hk).1)
      exact reciprocalWeightedMangoldtTerm_prime_pow_le hx (Finset.mem_filter.mp hp).2.1 hk0
    _ ≤ ∑ p ∈ m.primeFactors, Real.log p / (p : ℝ) ^ k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact
          Nat.mem_primeFactors.mpr
            ⟨(Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2, hm0⟩
      · intro p hp hpmissing
        have hpprime : p.Prime := (Nat.mem_primeFactors.mp hp).1
        exact div_nonneg (Real.log_nonneg (by exact_mod_cast hpprime.one_le)) (by positivity)

/--
For `m ≠ 0` and `x > 0`, the reciprocal common-factor weighted sum is at most
`Σ_{p ∣ m} log p / (p - 1)`, by summing the geometric bound for each prime divisor.
-/
theorem commonFactorReciprocalWeightedSum_le {m : ℕ} (hm0 : m ≠ 0) {x : ℝ} (hx : 0 < x) :
    commonFactorReciprocalWeightedSum x m ≤ primeFactorLogSum m := by
  calc
    _ ≤
        ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
          ∑ p ∈ m.primeFactors, Real.log p / (p : ℝ) ^ k :=
      commonFactorReciprocalWeightedSum_le_primeFactors hm0 hx
    _ =
        ∑ p ∈ m.primeFactors,
          ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊, Real.log p / (p : ℝ) ^ k :=
      by rw [Finset.sum_comm]
    _ ≤ ∑ p ∈ m.primeFactors, Real.log p / (p - 1) := by
      apply Finset.sum_le_sum
      intro p hp
      exact sum_log_div_prime_pow_le (Nat.prime_of_mem_primeFactors hp)
    _ = primeFactorLogSum m := by rw [primeFactorLogSum]

end PseudoPrime.AnalyticNumberTheory.Arithmetic
