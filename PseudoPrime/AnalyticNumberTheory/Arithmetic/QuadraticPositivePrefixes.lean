/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.QuadraticAmbientSquares

/-! # Restored quadratic squares in positive-character prefixes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If q divides N, every natural input belongs to exactly one of three classes:
coprime to N, noncoprime to q, or coprime to q but noncoprime to N. The identity holds
for any real weight without sign restrictions. This transfers main-term comparisons
to positive-character prefix comparisons. -/
theorem ambient_coprimality_partition {q N n : ℕ} (hqN : q ∣ N) (v : ℝ) :
    (if Nat.Coprime n N then v else 0) + (if ¬Nat.Coprime n q then v else 0) +
        (if Nat.Coprime n q ∧ ¬Nat.Coprime n N then v else 0) =
      v := by
  by_cases hq : Nat.Coprime n q
  · by_cases hN : Nat.Coprime n N
    · rw [ite_eq_left hN, ite_eq_right (not_not_intro hq),
        ite_eq_right (show ¬(Nat.Coprime n q ∧ ¬Nat.Coprime n N) from fun h ↦ h.2 hN)]
      simp only [add_zero]
    · rw [ite_eq_right hN, ite_eq_right (not_not_intro hq), ite_eq_left ⟨hq, hN⟩]
      simp only [zero_add, add_zero]
  · have hN : ¬Nat.Coprime n N := fun h ↦ hq (h.of_dvd_right hqN)
    rw [ite_eq_right hN, ite_eq_left hq,
      ite_eq_right (show ¬(Nat.Coprime n q ∧ ¬Nat.Coprime n N) from fun h ↦ hq h.1)]
    simp only [zero_add, add_zero]

/-- For q dividing N, quadratic character data, a nonnegative finite support through b
and triviality at N-coprime primes through b, add twice the excluded square prefix to
the old positive-prefix lower bound. Combine the restored main-term inequality with
the exact coprimality partition. This strengthens both the zero and pole comparisons. -/
theorem quadratic_ambientPositiveMangoldtPrefix_le_character {q N : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ n ∈ S, (n : ℝ) ≤ b) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    ambientPositiveMangoldtPrefix q N S w + 2 * additionalSquareMangoldtPrefix q N S w ≤
      ∑ n ∈ S, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n * w n := by
  unfold ambientPositiveMangoldtPrefix additionalSquareMangoldtPrefix
  simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun n hn ↦ ?_)
  have ht := quadratic_allowed_term_le_character_add_loss hqN χ hquad (hw n hn) hsmall (hS n hn)
  have he := ambient_coprimality_partition (n := n) hqN (ArithmeticFunction.vonMangoldt n * w n)
  nlinarith only [ht, he]

/-- A selected subset of additional excluded squares with certified term lower
bounds gives a lower bound on the full square prefix. Other weights are nonnegative.
No character, divisibility or analytic hypothesis is needed. This supplies sparse
inputs for the zero and pole positive-prefix savings. -/
theorem selected_additionalSquareMangoldtPrefix_lower_le (q N : ℕ) (S C : Finset ℕ) (w lo : ℕ → ℝ)
    (hC : C ⊆ S) (hcop : ∀ n ∈ C, Nat.Coprime n q ∧ ¬Nat.Coprime n N ∧ IsSquare n)
    (hw : ∀ n ∈ S, 0 ≤ w n) (hlo : ∀ n ∈ C, lo n ≤ ArithmeticFunction.vonMangoldt n * w n) :
    ∑ n ∈ C, lo n ≤ additionalSquareMangoldtPrefix q N S w := by
  have hl := Finset.sum_le_sum (fun n hn ↦ hlo n hn)
  have hs : C ⊆ S.filter (fun n ↦ Nat.Coprime n q ∧ ¬Nat.Coprime n N ∧ IsSquare n) := fun n hn ↦
    Finset.mem_filter.mpr ⟨hC hn, hcop n hn⟩
  have hb :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * w n)
      hs
      (fun n hn _ ↦
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n (Finset.mem_filter.mp hn).1))
  exact hl.trans hb

end PseudoPrime.AnalyticNumberTheory.Arithmetic
