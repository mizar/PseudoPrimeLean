/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.JacobiCharacterArithmetic
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.SquareFactorPrimeBudget

/-! # Conductor and exclusion budgets retaining the Jacobi square factor -/

@[expose] public section

namespace PseudoPrime.NumberTheory

/-- The square factor in an odd nonsquare arithmetic bridge is positive.
A zero factor would force n=0 by the exact decomposition. This supplies the
nonzero assumptions for logarithmic and prime-support budgets. -/
theorem JacobiCharacterArithmeticData.squareFactor_pos {n : ℕ} {hn : Odd n} {hns : ¬IsSquare n}
    (bridge : JacobiCharacterArithmeticData n hn hns) : 0 < bridge.squareFactor := by
  apply Nat.pos_of_ne_zero
  intro hz
  have h := bridge.squarefreePart_sq_mul
  rw [hz, zero_pow (by norm_num only : (2 : ℕ) ≠ 0), zero_mul] at h
  exact hn.pos.ne' h.symm

/-- For a prime divisor p of odd n, p divides the canonical conductor exactly
when it divides the squarefree part d. The conductor is d or 4d, and odd n is
coprime to four. This identifies ramified and square-factor-only prime costs. -/
theorem JacobiCharacterArithmeticData.prime_dvd_conductor_iff {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) {p : ℕ} (hp : p.Prime)
    (hpn : p ∣ n) : p ∣ (complexQuadraticCharacter n hn).conductor ↔ p ∣ bridge.squarefreePart := by
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  rw [complexQuadraticCharacter_conductor_eq_discriminant bridge hdvd, bridge.discriminant_eq]
  by_cases hd4 : bridge.squarefreePart % 4 = 1
  · rw [positiveFundamentalDiscriminant_eq_self hd4]
  · rw [positiveFundamentalDiscriminant_eq_four_mul hd4]
    have hn4 : Nat.Coprime n 4 := hn.coprime_two_right.mul_right hn.coprime_two_right
    have hnot4 : ¬p ∣ 4 := hp.coprime_iff_not_dvd.mp (hn4.of_dvd_left hpn)
    constructor
    · intro h
      exact (hp.dvd_mul.mp h).resolve_left hnot4
    · intro h
      exact dvd_mul_of_dvd_right h 4

/-- The conductor logarithm plus twice the square-factor logarithm is at
most log n+log 4. Combine the exact input decomposition with conductor<=4d.
This retains the same square-factor saving in the analytic level and cost budgets. -/
theorem JacobiCharacterArithmeticData.log_conductor_add_square_factor_le {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) :
    Real.log (complexQuadraticCharacter n hn).conductor + 2 * Real.log bridge.squareFactor ≤
      Real.log n + Real.log 4 := by
  have hdvd : bridge.squarefreePart ∣ n :=
    ⟨bridge.squareFactor ^ 2, by simpa only [Nat.mul_comm] using bridge.squarefreePart_sq_mul.symm⟩
  rw [complexQuadraticCharacter_conductor_eq_discriminant bridge hdvd]
  have hlog := bridge.log_discriminant_le_y_add_log_four
  dsimp only [JacobiCharacterArithmeticData.y] at hlog
  have he :=
    AnalyticNumberTheory.Arithmetic.log_square_factor_decomposition bridge.squarefreePart_pos.ne'
      bridge.squareFactor_pos.ne' bridge.squarefreePart_sq_mul
  linarith only [hlog, he]

/-- For nonnegative ramified and unramified half-rates a,b and finite
nonnegative excesses, local costs at conductor primes and other input primes
sum to at most b log n+(a-b)log d plus the excesses. Identify the conductor
support before applying the square-factor budget. This supplies arithmetic input
to actual negative Jacobi witness bounds. -/
theorem JacobiCharacterArithmeticData.sum_prime_cost_le_conductor_square_budget {n : ℕ} {hn : Odd n}
    {hns : ¬IsSquare n} (bridge : JacobiCharacterArithmeticData n hn hns) (F : ℕ → ℝ) {a b : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (T : Finset ℕ) (e : ℕ → ℝ) (he : ∀ p ∈ T, 0 ≤ e p)
    (hR :
      ∀ p ∈ n.primeFactors,
        p ∣ (complexQuadraticCharacter n hn).conductor →
          F p ≤ a * Real.log p + if p ∈ T then e p else 0)
    (hE :
      ∀ p ∈ n.primeFactors,
        ¬p ∣ (complexQuadraticCharacter n hn).conductor →
          F p ≤ 2 * b * Real.log p + if p ∈ T then e p else 0) :
    (∑ p ∈ n.primeFactors, F p) ≤
      b * Real.log n + (a - b) * Real.log bridge.squarefreePart + ∑ p ∈ T, e p := by
  apply
    AnalyticNumberTheory.Arithmetic.sum_prime_cost_le_square_factor_budget_add_excess
      bridge.squarefreePart_pos.ne' bridge.squareFactor_pos.ne' bridge.squarefreePart_sq_mul F ha hb
      T e he
  · intro p hp hd
    have hpr := (Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp
    exact hR p hp ((bridge.prime_dvd_conductor_iff hpr.1 hpr.2).mpr hd)
  · intro p hp hd
    have hpr := (Nat.mem_primeFactors_of_ne_zero hn.pos.ne').mp hp
    exact hE p hp (fun hf ↦ hd ((bridge.prime_dvd_conductor_iff hpr.1 hpr.2).mp hf))

end PseudoPrime.NumberTheory
