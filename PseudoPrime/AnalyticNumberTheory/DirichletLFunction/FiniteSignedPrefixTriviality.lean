/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.FiniteSignedResolvent

/-! # Prime triviality cancels finite signed resolvent defects -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- Input: arbitrary signed resolvent coefficients, a finite set of indices at most `b`,
and a character equal to one on every prime at most `b`.
Claim: the character defect of the whole finite Mangoldt-weighted sum vanishes.
Proof: nonzero Mangoldt terms are prime powers; their base prime lies below the same bound.
Role: preserve exact prime-power savings for every signed resolvent candidate. -/
theorem finiteSigned_prefix_defect_eq_zero_of_prime_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    (l : List (ℚ × ℚ)) (B : Finset ℕ) {b : ℝ} (hB : ∀ k ∈ B, (k : ℝ) ≤ b)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → χ p = 1) :
    (∑ k ∈ B, (1 - (χ k).re) * Analysis.finiteSignedMangoldtWeight l k) = 0 := by
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hΛ : ArithmeticFunction.vonMangoldt k = 0
  · simp only [Analysis.finiteSignedMangoldtWeight, hΛ, zero_mul, mul_zero]
  · obtain ⟨p, r, hp, hr, rfl⟩ :=
      (isPrimePow_nat_iff (n := k)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
    have hpb : (p : ℝ) ≤ b :=
      (show (p : ℝ) ≤ (p ^ r : ℕ) by exact_mod_cast Nat.le_pow hr).trans (hB _ hk)
    simp only [Nat.cast_pow, map_pow, hsmall p hp hpb, one_pow, Complex.one_re, sub_self, zero_mul]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
