/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterCoprimeTriviality

/-! # Extra nonunit losses under triviality outside an ambient modulus -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If a character is one at primes coprime to an ambient N through b, it is one
at any n<=b coprime to N with nonzero Mangoldt value. The character level q is independent.
Reduce to a positive prime power. This transfers restricted witness nonexistence. -/
theorem character_apply_one_of_ambient_mangoldt_ne_zero {q N n : ℕ} (χ : DirichletCharacter ℂ q)
    {b : ℝ} (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) (hn : (n : ℝ) ≤ b)
    (hcop : Nat.Coprime n N) (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 := by
  obtain ⟨p, r, hp, hr, rfl⟩ :=
    (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hpb : (p : ℝ) ≤ b := (show (p : ℝ) ≤ (p ^ r : ℕ) by exact_mod_cast Nat.le_pow hr).trans hn
  have hpc := hcop.of_dvd_left (dvd_pow_self p hr.ne')
  simp only [Nat.cast_pow, map_pow, hsmall p hp hpb hpc, one_pow]

/-- The weighted Mangoldt prefix on indices coprime to the character level q
but not to the ambient exclusion modulus N. Inputs S,w specify a finite support and weights.
This retains exactly the additional nonunit contribution when q divides N. -/
noncomputable def additionalNonunitMangoldtPrefix (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ n ∈ S.filter (fun n ↦ Nat.Coprime n q ∧ ¬Nat.Coprime n N),
    ArithmeticFunction.vonMangoldt n * w n

/-- Twice the prefix coprime to N plus the prefix noncoprime to q.
The character level q and ambient modulus N are independent inputs; later comparisons
assume q divides N. This is a lower positive-character prefix under ambient prime triviality. -/
noncomputable def ambientPositiveMangoldtPrefix (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  2 * (∑ n ∈ S.filter (fun n ↦ Nat.Coprime n N), ArithmeticFunction.vonMangoldt n * w n) +
    ∑ n ∈ S.filter (fun n ↦ ¬Nat.Coprime n q), ArithmeticFunction.vonMangoldt n * w n

/-- If q divides N, the ambient positive prefix equals the coprime positive
prefix at q minus twice the additional nonunit prefix. Partition the finite support
by both coprimality conditions. Real weights may have either sign. -/
theorem ambientPositiveMangoldtPrefix_eq_sub {q N : ℕ} (hqN : q ∣ N) (S : Finset ℕ) (w : ℕ → ℝ) :
    ambientPositiveMangoldtPrefix q N S w =
      coprimePositiveMangoldtPrefix q S w - 2 * additionalNonunitMangoldtPrefix q N S w := by
  have he :
    ambientPositiveMangoldtPrefix q N S w + 2 * additionalNonunitMangoldtPrefix q N S w =
      coprimePositiveMangoldtPrefix q S w := by
    unfold ambientPositiveMangoldtPrefix additionalNonunitMangoldtPrefix
      coprimePositiveMangoldtPrefix
    simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    by_cases hq : Nat.Coprime n q
    · by_cases hN : Nat.Coprime n N
      · rw [ite_eq_left hN, ite_eq_right (not_not_intro hq),
          ite_eq_right (show ¬(Nat.Coprime n q ∧ ¬Nat.Coprime n N) from fun h ↦ h.2 hN),
          ite_eq_left hq]
        ring
      · rw [ite_eq_right hN, ite_eq_right (not_not_intro hq), ite_eq_left (And.intro hq hN),
          ite_eq_left hq]
        ring
    · have hN : ¬Nat.Coprime n N := fun h ↦ hq (h.of_dvd_right hqN)
      rw [ite_eq_right hN, ite_eq_left hq,
        ite_eq_right (show ¬(Nat.Coprime n q ∧ ¬Nat.Coprime n N) from fun h ↦ hq h.1),
        ite_eq_right hq]
      ring
  linarith only [he]

/-- If q divides N and primes coprime to N through b have character value one,
nonnegative weights on a support through b give an ambient prefix below the positive
character prefix. Use exact values on allowed indices and Re chi>=-1 on extra exclusions. -/
theorem ambientPositiveMangoldtPrefix_le_character {q N : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, 0 ≤ w n) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    ambientPositiveMangoldtPrefix q N S w ≤
      ∑ n ∈ S, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n * w n := by
  unfold ambientPositiveMangoldtPrefix
  simp only [Finset.sum_filter, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum (fun n hn ↦ ?_)
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, mul_zero, zero_mul, ite_self, add_zero, le_refl]
  · by_cases hq : Nat.Coprime n q
    · by_cases hN : Nat.Coprime n N
      · rw [character_apply_one_of_ambient_mangoldt_ne_zero χ hsmall (hS n hn) hN hΛ]
        simp only [ite_eq_left hN, ite_eq_right (not_not_intro hq), Complex.one_re]
        nlinarith only []
      · have hr := (abs_le.mp ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))).1
        have hm :=
          mul_nonneg (show 0 ≤ 1 + (χ n).re by linarith only [hr])
            (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) (hw n hn))
        simp only [ite_eq_right hN, ite_eq_right (not_not_intro hq), mul_zero, add_zero]
        simpa only [mul_assoc] using hm
    · have hN : ¬Nat.Coprime n N := fun h ↦ hq (h.of_dvd_right hqN)
      have hz : χ n = 0 := χ.map_nonunit (fun hu ↦ hq ((ZMod.isUnit_iff_coprime n q).mp hu))
      simp only [ite_eq_right hN, ite_eq_left hq, hz, Complex.zero_re, add_zero, one_mul, mul_zero,
        zero_add, le_refl]

/-- Under ambient prime triviality through b and q dividing N, an allowed Mangoldt
term with nonnegative weight is at most its character term plus the additional exclusion
term. Split zero Mangoldt values, allowed inputs, extra exclusions and character nonunits. -/
theorem allowed_mangoldt_term_le_character_add_loss {q N n : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) {b w : ℝ} (hw : 0 ≤ w)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) (hn : (n : ℝ) ≤ b) :
    (if Nat.Coprime n N then ArithmeticFunction.vonMangoldt n * w else 0) ≤
      (χ n).re * ArithmeticFunction.vonMangoldt n * w +
        if Nat.Coprime n q ∧ ¬Nat.Coprime n N then ArithmeticFunction.vonMangoldt n * w else 0 := by
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, mul_zero, zero_mul, ite_self, add_zero, le_refl]
  · by_cases hN : Nat.Coprime n N
    · have hq := hN.of_dvd_right hqN
      have hbad : ¬(Nat.Coprime n q ∧ ¬Nat.Coprime n N) := fun h ↦ h.2 hN
      rw [ite_eq_left hN, ite_eq_right hbad,
        character_apply_one_of_ambient_mangoldt_ne_zero χ hsmall hn hN hΛ]
      simp only [Complex.one_re, one_mul, add_zero, le_refl]
    · by_cases hq : Nat.Coprime n q
      · have hr := (abs_le.mp ((Complex.abs_re_le_norm (χ n)).trans (χ.norm_le_one n))).1
        have hm :=
          mul_nonneg (show 0 ≤ 1 + (χ n).re by linarith only [hr])
            (mul_nonneg (ArithmeticFunction.vonMangoldt_nonneg (n := n)) hw)
        rw [ite_eq_right hN, ite_eq_left (And.intro hq hN)]
        nlinarith only [hm]
      · have hz : χ n = 0 := χ.map_nonunit (fun hu ↦ hq ((ZMod.isUnit_iff_coprime n q).mp hu))
        rw [ite_eq_right hN,
          ite_eq_right (show ¬(Nat.Coprime n q ∧ ¬Nat.Coprime n N) from fun h ↦ hq h.1), hz]
        simp only [Complex.zero_re, zero_mul, add_zero, le_refl]

/-- For a finite nonnegative prefix through b under ambient prime triviality,
the allowed sum is at most the real character sum plus the extra nonunit contribution.
Assume q divides N and sum the pointwise term inequality. -/
theorem allowed_mangoldt_sum_le_character_add_loss {q N : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) {b : ℝ} (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hw : ∀ n ∈ S, 0 ≤ w n) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ S.filter (fun n ↦ Nat.Coprime n N), ArithmeticFunction.vonMangoldt n * w n) ≤
      (∑ n ∈ S, (χ n).re * ArithmeticFunction.vonMangoldt n * w n) +
        additionalNonunitMangoldtPrefix q N S w := by
  unfold additionalNonunitMangoldtPrefix
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  exact
    Finset.sum_le_sum
      (fun n hn ↦ allowed_mangoldt_term_le_character_add_loss hqN χ (hw n hn) hsmall (hS n hn))

/-- For nonnegative weights on a support through b, a selected N-coprime subset
minus the extra nonunit contribution bounds the character sum from below.
Assume q divides N and ambient prime triviality; discard unselected nonnegative terms. -/
theorem selected_mangoldt_sub_loss_le_character {q N : ℕ} (hqN : q ∣ N) (χ : DirichletCharacter ℂ q)
    {b : ℝ} (S B : Finset ℕ) (w : ℕ → ℝ) (hB : B ⊆ S) (hcop : ∀ n ∈ B, Nat.Coprime n N)
    (hS : ∀ n ∈ S, (n : ℝ) ≤ b) (hw : ∀ n ∈ S, 0 ≤ w n)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ B, ArithmeticFunction.vonMangoldt n * w n) - additionalNonunitMangoldtPrefix q N S w ≤
      ∑ n ∈ S, (χ n).re * ArithmeticFunction.vonMangoldt n * w n := by
  have hs := allowed_mangoldt_sum_le_character_add_loss hqN χ S w hS hw hsmall
  have hsub : B ⊆ S.filter (fun n ↦ Nat.Coprime n N) := fun n hn ↦
    Finset.mem_filter.mpr ⟨hB hn, hcop n hn⟩
  have hb :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * w n)
      hsub
      (fun n hn _ ↦
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n (Finset.mem_filter.mp hn).1))
  linarith only [hs, hb]

/-- Nonnegative weights on a finite support make the ambient positive prefix
nonnegative for any two moduli q,N. Both filtered sums have nonnegative terms.
No divisibility, character or analytic assumptions are needed. -/
theorem ambientPositiveMangoldtPrefix_nonneg (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n) : 0 ≤ ambientPositiveMangoldtPrefix q N S w := by
  exact
    add_nonneg
      (mul_nonneg (by norm_num only : (0 : ℝ) ≤ 2)
        (Finset.sum_nonneg
          (fun n hn ↦
            mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n (Finset.mem_filter.mp hn).1))))
      (Finset.sum_nonneg
        (fun n hn ↦
          mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n (Finset.mem_filter.mp hn).1)))

/-- Nonnegative finite weights make the additional nonunit prefix nonnegative.
Each term is the product of a nonnegative Mangoldt value and weight.
This supplies sign data for explicit exclusion budgets. -/
theorem additionalNonunitMangoldtPrefix_nonneg (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n) : 0 ≤ additionalNonunitMangoldtPrefix q N S w := by
  exact
    Finset.sum_nonneg
      (fun n hn ↦
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n (Finset.mem_filter.mp hn).1))

/-- For nonnegative finite weights, the additional nonunit prefix is at most the
entire prefix noncoprime to N. Compare the nested filters and discarded nonnegative terms.
This connects the precise loss to coarser common-factor bounds. -/
theorem additionalNonunitMangoldtPrefix_le_common (q N : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hw : ∀ n ∈ S, 0 ≤ w n) :
    additionalNonunitMangoldtPrefix q N S w ≤
      ∑ n ∈ S.filter (fun n ↦ ¬Nat.Coprime n N), ArithmeticFunction.vonMangoldt n * w n := by
  exact
    Finset.sum_le_sum_of_subset_of_nonneg
      (fun n hn ↦
        Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2.2⟩)
      (fun n hn _ ↦
        mul_nonneg ArithmeticFunction.vonMangoldt_nonneg (hw n (Finset.mem_filter.mp hn).1))

end PseudoPrime.AnalyticNumberTheory.Arithmetic
