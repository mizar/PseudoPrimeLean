/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterAmbientTriviality

/-! # Restoring square terms in quadratic ambient-exclusion bounds -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- For any quadratic complex character, a square natural input coprime to the level
has value one. Factor the square and exclude the zero quadratic value by coprimality.
No primitivity, GRH, positivity or prime-power assumption is required. This restores
positive contributions from squares excluded only by the ambient modulus. -/
theorem quadratic_character_apply_one_of_coprime_square {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hc : Nat.Coprime n q) (hs : IsSquare n) : χ n = 1 := by
  obtain ⟨m, rfl⟩ := hs
  have hm : Nat.Coprime m q := hc.of_dvd_left (dvd_mul_right m m)
  have hz : χ m ≠ 0 := MulChar.apply_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime m q).mpr hm)
  rw [Nat.cast_mul, map_mul]
  rcases hquad (m : ZMod q) with h0 | h1 | hn
  · exact False.elim (hz h0)
  · rw [h1, one_mul]
  · rw [hn, neg_mul_neg, one_mul]

/-- The weighted Mangoldt prefix on indices coprime to q, noncoprime to N and square.
The finite support and weights are arbitrary. These terms have quadratic character
value one and were previously charged as possible value minus one. Their doubled
weight is the exact restoration in the strengthened main-term lower bound. -/
noncomputable def additionalSquareMangoldtPrefix (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S.filter (fun n ↦ Nat.Coprime n q ∧ ¬Nat.Coprime n N ∧ IsSquare n),
    ArithmeticFunction.vonMangoldt n * w n

/-- Under ambient prime triviality through b and q dividing N, restore twice the
weight of an additional excluded square in the pointwise main-term comparison.
Use the exact quadratic value one on that square; elsewhere reuse the generic bound.
Weights are nonnegative and the Mangoldt factor may vanish. -/
theorem quadratic_allowed_term_le_character_add_loss {q N n : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) {b w : ℝ} (hw : 0 ≤ w)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) (hn : (n : ℝ) ≤ b) :
    (if Nat.Coprime n N then ArithmeticFunction.vonMangoldt n * w else 0) +
        2 *
          (if Nat.Coprime n q ∧ ¬Nat.Coprime n N ∧ IsSquare n then
            ArithmeticFunction.vonMangoldt n * w
          else 0) ≤
      (χ n).re * ArithmeticFunction.vonMangoldt n * w +
        if Nat.Coprime n q ∧ ¬Nat.Coprime n N then ArithmeticFunction.vonMangoldt n * w else 0 := by
  by_cases hs : Nat.Coprime n q ∧ ¬Nat.Coprime n N ∧ IsSquare n
  · rw [ite_eq_left hs, ite_eq_right hs.2.1, ite_eq_left ⟨hs.1, hs.2.1⟩,
      quadratic_character_apply_one_of_coprime_square χ hquad hs.1 hs.2.2]
    simp only [Complex.one_re, one_mul, zero_add]
    nlinarith only []
  · rw [ite_eq_right hs, mul_zero, add_zero]
    exact allowed_mangoldt_term_le_character_add_loss hqN χ hw hsmall hn

/-- Sum the quadratic square restoration over a finite nonnegative support through b.
Assume q divides N and prime triviality only for N-coprime primes through b.
This retains excluded unit squares positively without enumerating individual primes. -/
theorem quadratic_allowed_sum_le_character_add_loss {q N : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ)
    (hS : ∀ n ∈ S, (n : ℝ) ≤ b) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ S.filter (fun n ↦ Nat.Coprime n N), ArithmeticFunction.vonMangoldt n * w n) +
        2 * additionalSquareMangoldtPrefix q N S w ≤
      (∑ n ∈ S, (χ n).re * ArithmeticFunction.vonMangoldt n * w n) +
        additionalNonunitMangoldtPrefix q N S w := by
  unfold additionalSquareMangoldtPrefix additionalNonunitMangoldtPrefix
  simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact
    Finset.sum_le_sum
      (fun n hn ↦
        quadratic_allowed_term_le_character_add_loss hqN χ hquad (hw n hn) hsmall (hS n hn))

/-- For any selected N-coprime subset of a nonnegative finite support through b,
subtract the additional exclusion loss and restore twice the excluded square prefix.
Use prime triviality on N-coprime primes, sum the pointwise quadratic comparison, and
discard unselected allowed terms. This supplies the principal-sum analytic interface. -/
theorem quadratic_selected_sub_loss_le_character {q N : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic) {b : ℝ} (S B : Finset ℕ) (w : ℕ → ℝ)
    (hB : B ⊆ S) (hcop : ∀ n ∈ B, Nat.Coprime n N) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, 0 ≤ w n) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ B, ArithmeticFunction.vonMangoldt n * w n) - additionalNonunitMangoldtPrefix q N S w +
        2 * additionalSquareMangoldtPrefix q N S w ≤
      ∑ n ∈ S, (χ n).re * ArithmeticFunction.vonMangoldt n * w n := by
  have hs := quadratic_allowed_sum_le_character_add_loss hqN χ hquad S w hS hw hsmall
  have hsub : B ⊆ S.filter (fun n ↦ Nat.Coprime n N) := fun n hn ↦
    Finset.mem_filter.mpr ⟨hB hn, hcop n hn⟩
  have hb :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * w n)
      hsub
      (fun n hn _ ↦
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n (Finset.mem_filter.mp hn).1))
  linarith only [hs, hb]

/-- For arbitrary q,N and nonnegative finite weights, the additional excluded square
prefix is nonnegative. Each Mangoldt factor is nonnegative. This proves that restoring
the square prefix can only improve an existing analytic witness separation. -/
theorem additionalSquareMangoldtPrefix_nonneg (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n) : 0 ≤ additionalSquareMangoldtPrefix q N S w := by
  exact
    Finset.sum_nonneg
      (fun n hn ↦
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n (Finset.mem_filter.mp hn).1))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
