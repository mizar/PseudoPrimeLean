/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.IdealNormCount

/-!
# Prime-power ideal counts from quadratic prime splitting

Count the ideals of prime-power norm in the ramified, inert, and split cases.
Match these counts with character divisor sums and extend to all positive integers
by multiplicativity. Identifying a field's splitting with its discriminant character
is a separate arithmetic input.
-/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- If `(p) = P^e` for a prime ideal `P` of norm `p^f`, every ideal of norm `p^k`
is `P^j` with `f * j = k`. The ideal contains its norm, so it divides a power of `P`;
prime-power divisibility identifies it, and norms determine the exponent equation.
This classifies the norm fiber for ramified and inert primes. -/
theorem singlePrime_norm_exponents (K : Type) [Field K] [NumberField K] {p e f k : ℕ} (hp : p.Prime)
    (P : Ideal (NumberField.RingOfIntegers K)) (hP : Prime P)
    (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P ^ e) (hN : Ideal.absNorm P = p ^ f)
    (I : Ideal (NumberField.RingOfIntegers K)) (hI : Ideal.absNorm I = p ^ k) :
    ∃ j : ℕ, I = P ^ j ∧ f * j = k := by
  have hle := Ideal.span_singleton_absNorm_le I
  rw [hI, Nat.cast_pow, ← Ideal.span_singleton_pow, hs, ← pow_mul] at hle
  obtain ⟨j, _hj, hassoc⟩ := (dvd_prime_pow hP (e * k)).mp (Ideal.dvd_iff_le.mpr hle)
  have heq := associated_iff_eq.mp hassoc
  have hn := congrArg Ideal.absNorm heq
  rw [map_pow, hN, ← pow_mul, hI] at hn
  exact ⟨j, heq, (Nat.pow_right_inj hp.one_lt).mp hn.symm⟩

/-- For prime `p`, a positive residue degree `f`, and `(p) = P^e` with prime `P`
of norm `p^f`, powers of `P` identify the exponent solutions `f * j = k` with the
integral ideals of norm `p^k`. Norms prove injectivity and prime-power divisibility
proves surjectivity. This provides the local counting equivalence for a single prime. -/
noncomputable def idealNormFiberPrimePowEquiv (K : Type) [Field K] [NumberField K] {p e f : ℕ}
    (hp : p.Prime) (hf : 0 < f) (P : Ideal (NumberField.RingOfIntegers K)) (hP : Prime P)
    (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P ^ e) (hN : Ideal.absNorm P = p ^ f)
    (k : ℕ) :
    { j : ℕ // f * j = k } ≃
      { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } := by
  let g :
    { j : ℕ // f * j = k } →
      { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } :=
    fun j ↦ ⟨P ^ j.val, by rw [map_pow, hN, ← pow_mul, j.property]⟩
  apply Equiv.ofBijective g
  constructor
  · intro j l he
    apply Subtype.ext
    have heq := congrArg (fun I ↦ Ideal.absNorm I.val) he
    change Ideal.absNorm (P ^ j.val) = Ideal.absNorm (P ^ l.val) at heq
    rw [map_pow, map_pow, hN, ← pow_mul, ← pow_mul] at heq
    exact Nat.eq_of_mul_eq_mul_left hf ((Nat.pow_right_inj hp.one_lt).mp heq)
  · intro I
    obtain ⟨j, hj, hk⟩ := singlePrime_norm_exponents K hp P hP hs hN I.val I.property
    exact ⟨⟨j, hk⟩, Subtype.ext hj.symm⟩

/-- For positive `f`, the equation `f * j = k` has exactly one natural solution
when `f` divides `k`, and none otherwise. Cancel multiplication by `f` for uniqueness.
This evaluates the exponent count for a single prime ideal above a rational prime. -/
private theorem normCount_exponent_card {f k : ℕ} (hf : 0 < f) :
    Nat.card { j : ℕ // f * j = k } = if f ∣ k then 1 else 0 := by
  by_cases hk : f ∣ k
  · rw [ite_eq_left hk]
    apply Nat.card_eq_one_iff_unique.mpr
    obtain ⟨j, hj⟩ := hk
    refine ⟨⟨?_⟩, ⟨⟨j, hj.symm⟩⟩⟩
    intro a b
    exact Subtype.ext (Nat.eq_of_mul_eq_mul_left hf (a.property.trans b.property.symm))
  · rw [ite_eq_right hk]
    apply Nat.card_eq_zero.mpr
    exact Or.inl ⟨fun j ↦ hk ⟨j.val, j.property.symm⟩⟩

/-- Suppose `(p) = P^e` for prime `p` and prime ideal `P` of norm `p^f`, with `f > 0`.
There is one ideal of norm `p^k` if `f` divides `k`, and none otherwise.
Take cardinalities of the prime-power norm equivalence and count exponent solutions.
This handles both ramified and inert quadratic primes. -/
theorem card_ideal_absNorm_prime_pow_of_single_prime (K : Type) [Field K] [NumberField K]
    {p e f : ℕ} (hp : p.Prime) (hf : 0 < f) (P : Ideal (NumberField.RingOfIntegers K))
    (hP : Prime P) (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P ^ e)
    (hN : Ideal.absNorm P = p ^ f) (k : ℕ) :
    Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } =
      if f ∣ k then 1 else 0 := by
  rw [← Nat.card_congr (idealNormFiberPrimePowEquiv K hp hf P hP hs hN k)]
  exact normCount_exponent_card hf

/-- For a prime `p`, the divisor sum of a character at `p^k` is the finite geometric
sum of powers of `χ(p)`. Replace divisor pairs by divisors, list the prime-power
divisors, and use multiplicativity of the character. This matches local ideal counts. -/
theorem character_divisor_sum_prime_pow {q p : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime)
    (k : ℕ) :
    (∑ d ∈ (p ^ k).divisorsAntidiagonal, χ (d.2 : ℕ)) =
      ∑ j ∈ Finset.range (k + 1), χ (p : ℕ) ^ j := by
  rw [Nat.sum_divisorsAntidiagonal' (fun _ j ↦ χ j), Nat.sum_divisors_prime_pow hp]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [Nat.cast_pow, map_pow]

/-- The geometric sum of powers of zero from exponent zero through `k` is one.
Apply the finite geometric-sum identity and use `k + 1 > 0` for the terminal power.
This is the character contribution at a ramified prime. -/
private theorem normCount_geometric_zero (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (0 : ℂ) ^ j) = 1 := by
  have h := geom_sum_mul_neg (0 : ℂ) (k + 1)
  simpa only [zero_pow (Nat.add_one_ne_zero k), sub_zero, sub_zero, mul_one] using h

/-- The geometric sum of powers of minus one through exponent `k` is one for even
`k` and zero for odd `k`. Use the alternating finite sum and the parity of `k + 1`.
This is the character contribution at an inert prime. -/
private theorem normCount_geometric_neg_one (k : ℕ) :
    (∑ j ∈ Finset.range (k + 1), (-1 : ℂ) ^ j) = if 2 ∣ k then 1 else 0 := by
  rw [← Fin.sum_univ_eq_sum_range, Fin.sum_neg_one_pow]
  simp only [Nat.even_add_one, ite_not]
  simp only [even_iff_two_dvd]

/-- If `(p) = P^2`, `P` is prime of norm `p`, and `χ(p) = 0`, the number of ideals
of norm `p^k` equals the character divisor sum. Both sides are one: the ideal is
`P^k`, and the character geometric sum has only its constant term.
This proves the coefficient identity in the ramified quadratic case. -/
theorem ideal_prime_power_count_eq_divisor_sum_of_ramified (K : Type) [Field K] [NumberField K]
    {p q : ℕ} (hp : p.Prime) (P : Ideal (NumberField.RingOfIntegers K)) (hP : Prime P)
    (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P ^ 2) (hN : Ideal.absNorm P = p)
    (χ : DirichletCharacter ℂ q) (hχ : χ (p : ℕ) = 0) (k : ℕ) :
    (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } : ℂ) =
      ∑ d ∈ (p ^ k).divisorsAntidiagonal, χ (d.2 : ℕ) := by
  have hN' : Ideal.absNorm P = p ^ 1 := hN.trans (pow_one p).symm
  rw [card_ideal_absNorm_prime_pow_of_single_prime K hp Nat.zero_lt_one P hP hs hN' k,
    ite_eq_left (one_dvd k), Nat.cast_one, character_divisor_sum_prime_pow χ hp, hχ,
    normCount_geometric_zero]

/-- If `(p)` is prime of norm `p^2` and `χ(p) = -1`, the ideal count at `p^k`
equals the character divisor sum. Both sides are one for even `k` and zero for odd
`k`, by the norm-exponent classification and the alternating geometric sum.
This proves the coefficient identity in the inert quadratic case. -/
theorem ideal_prime_power_count_eq_divisor_sum_of_inert (K : Type) [Field K] [NumberField K]
    {p q : ℕ} (hp : p.Prime) (P : Ideal (NumberField.RingOfIntegers K)) (hP : Prime P)
    (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P) (hN : Ideal.absNorm P = p ^ 2)
    (χ : DirichletCharacter ℂ q) (hχ : χ (p : ℕ) = -1) (k : ℕ) :
    (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } : ℂ) =
      ∑ d ∈ (p ^ k).divisorsAntidiagonal, χ (d.2 : ℕ) := by
  have hs' : Ideal.span {(p : NumberField.RingOfIntegers K)} = P ^ 1 := hs.trans (pow_one P).symm
  rw [card_ideal_absNorm_prime_pow_of_single_prime K hp (by norm_num only : 0 < (2 : ℕ)) P hP hs' hN
      k,
    character_divisor_sum_prime_pow χ hp, hχ, normCount_geometric_neg_one]
  split_ifs
  · exact Nat.cast_one
  · exact Nat.cast_zero

/-- If `(p) = P * Q` for prime ideals of norm `p`, every ideal of norm `p^k`
is `P^i * Q^j` with `i + j = k`. It divides `(p)^k`; split this divisibility into
the two prime powers and compare norms. This proves surjectivity for split-prime counting. -/
theorem splitPrime_norm_exponents (K : Type) [Field K] [NumberField K] {p k : ℕ} (hp : p.Prime)
    (P Q : Ideal (NumberField.RingOfIntegers K)) (hP : Prime P) (hQ : Prime Q)
    (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P * Q) (hNP : Ideal.absNorm P = p)
    (hNQ : Ideal.absNorm Q = p) (I : Ideal (NumberField.RingOfIntegers K))
    (hI : Ideal.absNorm I = p ^ k) : ∃ i j : ℕ, I = P ^ i * Q ^ j ∧ i + j = k := by
  have hle := Ideal.span_singleton_absNorm_le I
  rw [hI, Nat.cast_pow, ← Ideal.span_singleton_pow, hs, mul_pow] at hle
  obtain ⟨A, B, hA, hB, he⟩ := exists_dvd_and_dvd_of_dvd_mul (Ideal.dvd_iff_le.mpr hle)
  obtain ⟨i, _hi, ha⟩ := (dvd_prime_pow hP k).mp hA
  obtain ⟨j, _hj, hb⟩ := (dvd_prime_pow hQ k).mp hB
  rw [associated_iff_eq.mp ha, associated_iff_eq.mp hb] at he
  have hn := congrArg Ideal.absNorm he
  rw [map_mul, map_pow, map_pow, hNP, hNQ, ← pow_add, hI] at hn
  exact ⟨i, j, he, (Nat.pow_right_inj hp.one_lt).mp hn.symm⟩

/-- For coprime prime ideals `P` and `Q`, equality of two products of their powers
forces the exponent of `P` on the left to be at most that on the right.
Coprimality removes the power of `Q` from divisibility, and prime-power divisibility
compares exponents. Applying this in both directions proves uniqueness. -/
theorem splitPrime_exponent_le {R : Type} [CommRing R] [IsDedekindDomain R] (P Q : Ideal R)
    (hP : Prime P) (hc : IsCoprime P Q) {i j a b : ℕ} (h : P ^ i * Q ^ a = P ^ j * Q ^ b) :
    i ≤ j := by
  have hd : P ^ i ∣ P ^ j * Q ^ b := h ▸ dvd_mul_right (P ^ i) (Q ^ a)
  exact (pow_dvd_pow_iff hP.ne_zero hP.not_isUnit).mp (hc.pow.dvd_of_dvd_mul_right hd)

/-- For `(p) = P * Q` with coprime prime ideals of norm `p`, the exponents
`0, ..., k` parametrize all ideals of norm `p^k` by `P^j * Q^(k - j)`.
Prime-power divisibility gives surjectivity, and coprimality gives uniqueness.
This is the finite equivalence used to count split quadratic primes. -/
noncomputable def idealNormFiberSplitPrimePowEquiv (K : Type) [Field K] [NumberField K] {p : ℕ}
    (hp : p.Prime) (P Q : Ideal (NumberField.RingOfIntegers K)) (hP : Prime P) (hQ : Prime Q)
    (hc : IsCoprime P Q) (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P * Q)
    (hNP : Ideal.absNorm P = p) (hNQ : Ideal.absNorm Q = p) (k : ℕ) :
    Fin (k + 1) ≃ { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } := by
  let g : Fin (k + 1) → { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } :=
    fun j ↦
    ⟨P ^ j.val * Q ^ (k - j.val), by
      rw [map_mul, map_pow, map_pow, hNP, hNQ, ← pow_add,
        Nat.add_sub_of_le (Nat.le_of_lt_succ j.isLt)]⟩
  apply Equiv.ofBijective g
  constructor
  · intro i j he
    apply Fin.ext
    have h : P ^ i.val * Q ^ (k - i.val) = P ^ j.val * Q ^ (k - j.val) := congrArg Subtype.val he
    exact
      Nat.le_antisymm (splitPrime_exponent_le P Q hP hc h) (splitPrime_exponent_le P Q hP hc h.symm)
  · intro I
    obtain ⟨i, j, hi, hk⟩ := splitPrime_norm_exponents K hp P Q hP hQ hs hNP hNQ I.val I.property
    have hil : i ≤ k := hk ▸ Nat.le_add_right i j
    refine ⟨⟨i, Nat.lt_succ_of_le hil⟩, ?_⟩
    apply Subtype.ext
    change P ^ i * Q ^ (k - i) = I.val
    have hsub : k - i = j := hk ▸ Nat.add_sub_cancel_left i j
    rw [hsub]
    exact hi.symm

/-- If `(p) = P * Q` with coprime prime ideals of norm `p`, exactly `k + 1`
integral ideals have norm `p^k`. Take cardinalities of the equivalence with `Fin (k + 1)`.
This is the local ideal count in the split quadratic case. -/
theorem card_ideal_absNorm_prime_pow_of_split (K : Type) [Field K] [NumberField K] {p : ℕ}
    (hp : p.Prime) (P Q : Ideal (NumberField.RingOfIntegers K)) (hP : Prime P) (hQ : Prime Q)
    (hc : IsCoprime P Q) (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P * Q)
    (hNP : Ideal.absNorm P = p) (hNQ : Ideal.absNorm Q = p) (k : ℕ) :
    Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } = k + 1 := by
  rw [← Nat.card_congr (idealNormFiberSplitPrimePowEquiv K hp P Q hP hQ hc hs hNP hNQ k),
    Nat.card_fin]

/-- If `(p) = P * Q` with coprime prime ideals of norm `p` and `χ(p) = 1`, the
ideal count at `p^k` equals the character divisor sum. There are `k + 1` ideals,
and the character geometric sum has `k + 1` terms equal to one.
This proves the coefficient identity in the split quadratic case. -/
theorem ideal_prime_power_count_eq_divisor_sum_of_split (K : Type) [Field K] [NumberField K]
    {p q : ℕ} (hp : p.Prime) (P Q : Ideal (NumberField.RingOfIntegers K)) (hP : Prime P)
    (hQ : Prime Q) (hc : IsCoprime P Q)
    (hs : Ideal.span {(p : NumberField.RingOfIntegers K)} = P * Q) (hNP : Ideal.absNorm P = p)
    (hNQ : Ideal.absNorm Q = p) (χ : DirichletCharacter ℂ q) (hχ : χ (p : ℕ) = 1) (k : ℕ) :
    (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } : ℂ) =
      ∑ d ∈ (p ^ k).divisorsAntidiagonal, χ (d.2 : ℕ) := by
  rw [card_ideal_absNorm_prime_pow_of_split K hp P Q hP hQ hc hs hNP hNQ k,
    character_divisor_sum_prime_pow χ hp, hχ]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/-- The ideal factorization at a natural number `p` agrees with the quadratic
splitting pattern specified by `χ(p)`; primality of `p` is assumed by users of this predicate.
Value zero requires `(p) = P^2` with norm `p`; value minus one requires `(p)` prime
of norm `p^2`; value one requires two coprime prime factors, each of norm `p`.
The condition records actual ideal equalities and norms, including ramified primes.
It is the local arithmetic input to the quadratic Dedekind coefficient identity. -/
def quadraticPrimeSplittingAt (K : Type) [Field K] [NumberField K] {q : ℕ}
    (χ : DirichletCharacter ℂ q) (p : ℕ) : Prop :=
  (χ (p : ℕ) = 0 ∧
      ∃ P : Ideal (NumberField.RingOfIntegers K),
        Prime P ∧ Ideal.span {(p : NumberField.RingOfIntegers K)} = P ^ 2 ∧ Ideal.absNorm P = p) ∨
    (χ (p : ℕ) = -1 ∧
      ∃ P : Ideal (NumberField.RingOfIntegers K),
        Prime P ∧ Ideal.span {(p : NumberField.RingOfIntegers K)} = P ∧ Ideal.absNorm P = p ^ 2) ∨
    (χ (p : ℕ) = 1 ∧
      ∃ P Q : Ideal (NumberField.RingOfIntegers K),
        Prime P ∧
          Prime Q ∧
          IsCoprime P Q ∧
          Ideal.span {(p : NumberField.RingOfIntegers K)} = P * Q ∧
          Ideal.absNorm P = p ∧ Ideal.absNorm Q = p)

/-- If the splitting of a prime `p` agrees with `χ(p)`, the ideal count at every
power of `p` equals the character divisor sum. Apply the ramified, inert, or split
count according to the splitting condition. This supplies the prime-power comparison. -/
theorem ideal_prime_power_count_eq_divisor_sum_of_splitting (K : Type) [Field K] [NumberField K]
    {p q : ℕ} (χ : DirichletCharacter ℂ q) (hp : p.Prime) (hsplit : quadraticPrimeSplittingAt K χ p)
    (k : ℕ) :
    (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = p ^ k } : ℂ) =
      ∑ d ∈ (p ^ k).divisorsAntidiagonal, χ (d.2 : ℕ) := by
  rcases hsplit with ⟨hχ, P, hP, hs, hN⟩ | ⟨hχ, P, hP, hs, hN⟩ |
    ⟨hχ, P, Q, hP, hQ, hc, hs, hNP, hNQ⟩
  · exact ideal_prime_power_count_eq_divisor_sum_of_ramified K hp P hP hs hN χ hχ k
  · exact ideal_prime_power_count_eq_divisor_sum_of_inert K hp P hP hs hN χ hχ k
  · exact ideal_prime_power_count_eq_divisor_sum_of_split K hp P Q hP hQ hc hs hNP hNQ χ hχ k

/-- If every rational prime splits according to the same character `χ`, the
integral-ideal count equals its divisor sum at every positive integer.
Prove the local identity in each splitting case, then use multiplicativity to extend
from prime powers. This is the arithmetic coefficient premise needed for Dedekind
factorization and the class-number bounds. -/
theorem ideal_count_eq_divisor_sum_of_splitting (K : Type) [Field K] [NumberField K] {q : ℕ}
    (χ : DirichletCharacter ℂ q) (hsplit : ∀ p : ℕ, p.Prime → quadraticPrimeSplittingAt K χ p)
    (n : ℕ) (hn : n ≠ 0) :
    (Nat.card { I : Ideal (NumberField.RingOfIntegers K) // Ideal.absNorm I = n } : ℂ) =
      ∑ d ∈ n.divisorsAntidiagonal, χ (d.2 : ℕ) := by
  apply ideal_count_eq_divisor_sum_of_prime_power_count K χ ?_ n hn
  intro p k hp
  exact ideal_prime_power_count_eq_divisor_sum_of_splitting K χ hp (hsplit p hp) k

end PseudoPrime.NumberTheory
