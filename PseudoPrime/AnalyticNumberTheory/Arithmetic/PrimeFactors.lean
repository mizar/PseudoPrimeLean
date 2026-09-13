/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ConductorPrimeFactors

/-!
# Distinct prime factors and their logarithmic weight

This file provides finite-`primeFactors` interfaces for two generic arithmetic quantities: the
number of distinct prime divisors and the sum `Σ_{p ∣ q} log p / (p - 1)`.  Neither is specific to
downstream correction terms that consume them.
-/

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- The number of distinct prime factors of `q`. -/
def distinctPrimeFactorCount (q : ℕ) : ℕ :=
  ArithmeticFunction.cardDistinctFactors q

/-- The finite sum `Σ_{p ∈ q.primeFactors} log p / (p - 1)`.
In particular, it is `0` at `q = 0`, following the `Nat.primeFactors` convention. -/
noncomputable def primeFactorLogSum (q : ℕ) : ℝ :=
  ∑ p ∈ q.primeFactors, Real.log p / (p - 1)

/-- The project count agrees with mathlib's arithmetic function `cardDistinctFactors`. -/
theorem distinctPrimeFactorCount_eq_cardDistinctFactors (q : ℕ) :
    distinctPrimeFactorCount q =
      ArithmeticFunction.cardDistinctFactors q :=
  rfl

/--
Input/assumptions: a positive natural number `n`.
Conclusion: the sum of `log p` over the distinct prime divisors of `n` is at most `log n`.
Content: the distinct prime divisors of `n` multiply to a divisor of `n`, hence to a natural
number at most `n`; take logs and use `Real.log_prod` to turn the product into the sum.
Role: with `n = q / conductor`, bounds the quotient-support sum `Σ_{p ∈ S} log p` by
`log(q / conductor)`, replacing the per-prime alternating bounds' `log p` summands by a single
`log(q / conductor)` term without any Mertens-type or `ω(q / conductor)` estimate.
-/
theorem sum_log_primeFactors_le_log {n : ℕ} (hn : n ≠ 0) :
    ∑ p ∈ n.primeFactors, Real.log p ≤ Real.log n := by
  have hdvd : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have hprodpos : 0 < ∏ p ∈ n.primeFactors, p := by
    apply Finset.prod_pos
    intro p hp
    exact (Nat.prime_of_mem_primeFactors hp).pos
  have hle : (∏ p ∈ n.primeFactors, p : ℕ) ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hlogle : Real.log (∏ p ∈ n.primeFactors, p : ℕ) ≤ Real.log n :=
    Real.log_le_log (by exact_mod_cast hprodpos) (by exact_mod_cast hle)
  rw [Nat.cast_prod,
    Real.log_prod (s := n.primeFactors) (f := fun p : ℕ ↦ (p : ℝ)) fun p hp ↦
      (by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos.ne' : (p : ℝ) ≠ 0)] at hlogle
  exact hlogle

/- For natural `n ≥ 4`, `π ≤ n` implies `0 ≤ log(n/π)`. -/
theorem log_conductor_div_pi_nonneg_of_four_le {n : ℕ} (hn : 4 ≤ n) :
    0 ≤ Real.log ((n : ℝ) / Real.pi) := by
  apply Real.log_nonneg
  apply (le_div_iff₀ Real.pi_pos).2
  have hn' : (4 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [one_mul] using Real.pi_le_four.trans hn'

/- Each summand `log p / (p - 1)` is at most `log 2`. -/
theorem primeFactorLogSum_le_card_mul_log_two {n : ℕ} :
    primeFactorLogSum n ≤
      (n.primeFactors.card : ℝ) * Real.log 2 := by
  have hpow : ∀ k : ℕ, k + 1 ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => norm_num only
    | succ k ih =>
      rw [pow_succ]
      have hk : 1 ≤ 2 ^ k := Nat.one_le_pow k 2 (by norm_num only)
      calc
        k + 1 + 1 ≤ 2 ^ k + 1 := Nat.add_le_add_right ih 1
        _ ≤ 2 ^ k + 2 ^ k := Nat.add_le_add_left hk _
        _ = 2 ^ k * 2 := by rw [Nat.mul_two]
  unfold primeFactorLogSum
  calc
    ∑ p ∈ n.primeFactors, Real.log p / (p - 1) ≤ ∑ p ∈ n.primeFactors, Real.log 2 := by
      apply Finset.sum_le_sum
      intro p hp
      have hpprime := Nat.prime_of_mem_primeFactors hp
      have hpone : 1 ≤ p := hpprime.one_le
      have hpowp : p ≤ 2 ^ (p - 1) := by simpa only [Nat.sub_add_cancel hpone] using hpow (p - 1)
      have hpowp' : (p : ℝ) ≤ (2 : ℝ) ^ (p - 1) := by exact_mod_cast hpowp
      have hlogp : Real.log (p : ℝ) ≤ Real.log ((2 : ℝ) ^ (p - 1)) := by
        exact
          Real.strictMonoOn_log.monotoneOn
            (by
              change 0 < (p : ℝ)
              exact_mod_cast hpprime.pos)
            (by
              change 0 < (2 : ℝ) ^ (p - 1)
              positivity)
            hpowp'
      rw [Real.log_pow] at hlogp
      rw [Nat.cast_sub hpone] at hlogp
      have hpdenNat : 0 < p - 1 := Nat.sub_pos_of_lt hpprime.one_lt
      have hpden : (0 : ℝ) < p - 1 := by exact_mod_cast hpdenNat
      apply (div_le_iff₀ hpden).2
      simpa only [mul_comm, Nat.cast_one] using hlogp
    _ = (n.primeFactors.card : ℝ) * Real.log 2 := by simp only [Finset.sum_const, nsmul_eq_mul]

/- The complementary level quotient inherits the preceding logarithmic bound. -/
theorem primeFactorLogSum_quotient_le_log {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    primeFactorLogSum (q / χ.conductor) ≤
      Real.log (q / χ.conductor : ℕ) := by
  have hsum :=
    primeFactorLogSum_le_card_mul_log_two (n := q / χ.conductor)
  have hcard :=
    DirichletLFunction.card_primeFactors_quotient_le_log_div_log_two χ
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    primeFactorLogSum (q / χ.conductor) ≤ ((q / χ.conductor).primeFactors.card : ℝ) * Real.log 2 :=
      hsum
    _ ≤ (Real.log (q / χ.conductor : ℕ) / Real.log 2) * Real.log 2 :=
      mul_le_mul_of_nonneg_right hcard hlog2.le
    _ = Real.log (q / χ.conductor : ℕ) := by exact div_mul_cancel₀ _ hlog2.ne'

end PseudoPrime.AnalyticNumberTheory.Arithmetic
