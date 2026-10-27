/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.NumberTheory.Heilbronn.TripleDiagonalSplit

/-! # Explicit real budgets for weighted Heilbronn triple amplification -/

@[expose] public section

namespace PseudoPrime.NumberTheory.Heilbronn

/-- Explicit upper budget for the squared off-diagonal triple sum at
support S and height Δ. The factors are the height cost, the proved
third-energy bound, and the proved mixed third-energy bound. This retains
both Fourier main and error terms for the final energy comparison. -/
noncomputable def heilbronnOffDiagonalBudget (p : ℕ) [Fact p.Prime] (S : Finset (ZMod (p ^ 2)))
    (Δ : ℕ) : ℝ :=
  (Δ : ℝ) ^ 4 * (786433 * (p : ℝ) ^ 3 * (1 + Real.log p)) *
    ((Nat.log2 p + 1 : ℕ) *
      (4 * (S.card : ℝ) ^ 2 * heilbronnEnergy p / (p : ℝ) ^ 2 +
        4096 * S.card * p * Real.sqrt (heilbronnEnergy p)))

/-- Replace the third and mixed energy factors in a proved natural square
bound by their explicit estimates. Cast the inequality and multiply the
two bounds with verified nonnegative factors. This is shared by all
selected levels and does not introduce a new analytic assumption. -/
theorem square_le_heilbronnOffDiagonalBudget {p R : ℕ} [Fact p.Prime] (hodd : Odd p)
    (S : Finset (ZMod (p ^ 2))) (Δ : ℕ)
    (hR : R ^ 2 ≤ Δ ^ 4 * heilbronnThirdEnergy p * mixedHeilbronnThirdEnergy p S) :
    (R : ℝ) ^ 2 ≤ heilbronnOffDiagonalBudget p S Δ := by
  have hr : (R : ℝ) ^ 2 ≤ (Δ : ℝ) ^ 4 * heilbronnThirdEnergy p * mixedHeilbronnThirdEnergy p S := by
    exact_mod_cast hR
  have ht := heilbronnThirdEnergy_le_log hodd
  have hm := mixedHeilbronnThirdEnergy_le_explicit hodd S
  have hΔ : (0 : ℝ) ≤ (Δ : ℝ) ^ 4 := pow_nonneg (Nat.cast_nonneg _) _
  exact
    hr.trans
      (mul_le_mul (mul_le_mul_of_nonneg_left ht hΔ) hm (Nat.cast_nonneg _)
        (mul_nonneg hΔ
          ((Nat.cast_nonneg (heilbronnThirdEnergy p) : (0 : ℝ) ≤ heilbronnThirdEnergy p).trans ht)))

/-- A selected level of height at most Δ has full triple sum bounded by
(p-1)ΔB plus the square root of the explicit mixed-energy budget. Use the
proved diagonal split and off-diagonal square bound. All correlation and
moment estimates are discharged under the single odd-prime premise. -/
theorem level_weight_triple_le_explicit {p : ℕ} [Fact p.Prime] (hodd : Odd p) (P : ℕ → Prop) (Δ : ℕ)
    (hP : ∀ v, P v → v ≤ Δ) :
    (weightedHeilbronnTriple p (heilbronnLevelWeight p P) : ℝ) ≤
      ((p - 1 : ℕ) : ℝ) * Δ * heilbronnLevelEnergy p P +
        Real.sqrt (heilbronnOffDiagonalBudget p (heilbronnCorrelationLevel p P) Δ) := by
  have hd :
    (weightedHeilbronnTriple p (heilbronnLevelWeight p P) : ℝ) ≤
      ((p - 1 : ℕ) : ℝ) * Δ * heilbronnLevelEnergy p P +
        weightedHeilbronnOffDiagonal p (heilbronnLevelWeight p P) := by
    exact_mod_cast level_weight_triple_le_diagonal_add_offDiagonal (p := p) P Δ hP
  have hs :=
    square_le_heilbronnOffDiagonalBudget hodd (heilbronnCorrelationLevel p P) Δ
      (level_weight_offDiagonal_square_le P Δ hP)
  exact hd.trans (add_le_add (le_refl _) (Real.le_sqrt_of_sq_le hs))

/-- The retained level energy satisfies a completely explicit amplified
comparison in terms of p, E, B, its support size and height. Combine B²E
amplification with the proved full triple upper bound. This is the
quantitative input for truncation and the final E¹³ comparison. -/
theorem level_energy_amplification_le_explicit {p : ℕ} [Fact p.Prime] (hodd : Odd p) (P : ℕ → Prop)
    (Δ : ℕ) (hP : ∀ v, P v → v ≤ Δ) :
    (heilbronnLevelEnergy p P : ℝ) ^ 2 * heilbronnEnergy p ≤
      ((p - 1 : ℕ) : ℝ) ^ 3 *
        (((p - 1 : ℕ) : ℝ) * Δ * heilbronnLevelEnergy p P +
          Real.sqrt (heilbronnOffDiagonalBudget p (heilbronnCorrelationLevel p P) Δ)) := by
  have ha :
    (heilbronnLevelEnergy p P : ℝ) ^ 2 * heilbronnEnergy p ≤
      ((p - 1 : ℕ) : ℝ) ^ 3 * weightedHeilbronnTriple p (heilbronnLevelWeight p P) := by
    exact_mod_cast heilbronn_level_energy_amplification (p := p) P
  exact
    ha.trans
      (mul_le_mul_of_nonneg_left (level_weight_triple_le_explicit hodd P Δ hP)
        (pow_nonneg (Nat.cast_nonneg _) _))

end PseudoPrime.NumberTheory.Heilbronn
