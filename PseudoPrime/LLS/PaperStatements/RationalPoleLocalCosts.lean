/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleFullPrincipal
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-! # Exact finite local costs for the fourth-pole kernel -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The exact local discrepancy `(1-re χ(n)) Λ(n) f_x(n)` at a natural index.
It is supported on prime powers and keeps the character value explicit. -/
noncomputable def fourPoleLocalTerm {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (n : ℕ) : ℝ :=
  (1 - (χ n).re) * ArithmeticFunction.vonMangoldt n * fourScaledWeight x n

/-- Sum the local discrepancy through the cutoff only on nonunits of the ambient
integer `a`. The character conductor and ambient exclusions remain separate inputs. -/
noncomputable def fourPoleLocalCost {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ ¬Nat.Coprime n a), fourPoleLocalTerm χ x n

/-- The local cost term vanishes off prime powers because the Mangoldt coefficient vanishes. -/
theorem fourPoleLocalTerm_zero_not_primePow {q n : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hn : ¬IsPrimePow n) : fourPoleLocalTerm χ x n = 0 := by
  rw [fourPoleLocalTerm, ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hn, mul_zero, zero_mul]

/-- Reindex the exact finite local cost by positive powers of primes dividing the ambient
integer. This preserves the ambient support without a global enumeration. -/
theorem fourPoleLocalCost_prime_powers {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ) {x : ℝ}
    (hx : 0 ≤ x) :
    fourPoleLocalCost χ a x =
      ∑ k ∈ Finset.Icc 1 ⌊Real.log x / Real.log 2⌋₊,
        ∑ p ∈ (Finset.Ioc 0 ⌊x ^ ((1 : ℝ) / k)⌋₊).filter (fun p ↦ p.Prime ∧ p ∣ a),
          fourPoleLocalTerm χ x (p ^ k) := by
  exact
    AnalyticNumberTheory.Arithmetic.sum_not_coprime_eq_sum_prime_powers (fourPoleLocalTerm χ x) a hx
      (fun n hn ↦ fourPoleLocalTerm_zero_not_primePow χ x hn)

/-- A prime of character value one has zero local cost at every exponent. -/
theorem fourPoleLocalTerm_of_one {q p k : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (hp : χ p = 1) :
    fourPoleLocalTerm χ x (p ^ k) = 0 := by
  simp only [fourPoleLocalTerm, Nat.cast_pow, map_pow, hp, one_pow, Complex.one_re, sub_self,
    zero_mul]

/-- At a ramified prime and positive exponent, the local cost is log(p) times the weight. -/
theorem fourPoleLocalTerm_of_zero {q p k : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) (hp : p.Prime)
    (hk : 0 < k) (hz : χ p = 0) :
    fourPoleLocalTerm χ x (p ^ k) = Real.log p * fourScaledWeight x (p ^ k) := by
  simp only [fourPoleLocalTerm, Nat.cast_pow, map_pow, hz, zero_pow hk.ne', Complex.zero_re,
    sub_zero, one_mul, ArithmeticFunction.vonMangoldt_apply_pow hk.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp]

/-- At a prime of character value minus one, every even power has zero local cost. -/
theorem fourPoleLocalTerm_negative_even {q p k : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hp : χ p = -1) (hk : Even k) : fourPoleLocalTerm χ x (p ^ k) = 0 := by
  simp only [fourPoleLocalTerm, Nat.cast_pow, map_pow, hp, hk.neg_one_pow, Complex.one_re, sub_self,
    zero_mul]

/-- At a prime of character value minus one, an odd power costs twice log(p) times its weight. -/
theorem fourPoleLocalTerm_negative_odd {q p k : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ)
    (hp : p.Prime) (hk : Odd k) (hz : χ p = -1) :
    fourPoleLocalTerm χ x (p ^ k) = 2 * Real.log p * fourScaledWeight x (p ^ k) := by
  simp only [fourPoleLocalTerm, Nat.cast_pow, map_pow, hz, hk.neg_one_pow, Complex.neg_re,
    Complex.one_re, ArithmeticFunction.vonMangoldt_apply_pow hk.pos.ne',
    ArithmeticFunction.vonMangoldt_apply_prime hp]
  ring

end PseudoPrime.LLS.PaperStatements
