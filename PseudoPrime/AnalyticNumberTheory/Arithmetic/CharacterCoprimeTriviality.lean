/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality

/-! # Exact Mangoldt prefixes under triviality at coprime primes -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- If a character is one at all coprime primes through b, its value is one at
every coprime n<=b with nonzero Mangoldt value. Reduce to a positive prime power.
This transfers unit-prime witness nonexistence to selected Mangoldt supports. -/
theorem character_apply_one_of_coprime_mangoldt_ne_zero {q n : ℕ} (χ : DirichletCharacter ℂ q)
    {b : ℝ} (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1) (hn : (n : ℝ) ≤ b)
    (hcop : Nat.Coprime n q) (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = 1 := by
  obtain ⟨p, r, hp, hr, rfl⟩ :=
    (isPrimePow_nat_iff (n := n)).mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ)
  have hpb : (p : ℝ) ≤ b := (show (p : ℝ) ≤ (p ^ r : ℕ) by exact_mod_cast Nat.le_pow hr).trans hn
  have hpc := hcop.of_dvd_left (dvd_pow_self p hr.ne')
  simp only [Nat.cast_pow, map_pow, hsmall p hp hpb hpc, one_pow]

/-- Under coprime prime triviality through b, every n<=b with nonzero Mangoldt value
has character value one if coprime to q and zero otherwise. Use prime powers and
vanishing on nonunits. This retains ramified zeros instead of excluding them silently. -/
theorem character_apply_ite_of_coprime_trivial {q n : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1) (hn : (n : ℝ) ≤ b)
    (hΛ : ArithmeticFunction.vonMangoldt n ≠ 0) : χ n = if Nat.Coprime n q then 1 else 0 := by
  by_cases hc : Nat.Coprime n q
  · rw [ite_eq_left hc]
    exact character_apply_one_of_coprime_mangoldt_ne_zero χ hsmall hn hc hΛ
  · rw [ite_eq_right hc]
    exact χ.map_nonunit (fun hu ↦ hc ((ZMod.isUnit_iff_coprime n q).mp hu))

/-- The untwisted Mangoldt prefix plus a second copy on indices coprime to q.
Inputs are modulus q, finite support S and arbitrary real weights w.
Under coprime prime triviality this equals the positive character prefix exactly. -/
noncomputable def coprimePositiveMangoldtPrefix (q : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) : ℝ :=
  (∑ n ∈ S, ArithmeticFunction.vonMangoldt n * w n) +
    ∑ n ∈ S.filter (fun n ↦ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n * w n

/-- For a finite support through b and arbitrary real weights, coprime prime
triviality identifies the positive character prefix with one full copy plus one
coprime copy. Split zero Mangoldt terms and use the exact zero-or-one values. -/
theorem character_positive_mangoldt_prefix_eq_coprime {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1) :
    (∑ n ∈ S, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n * w n) =
      coprimePositiveMangoldtPrefix q S w := by
  unfold coprimePositiveMangoldtPrefix
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, mul_zero, zero_mul, ite_self, add_zero]
  · rw [character_apply_ite_of_coprime_trivial χ hsmall (hS n hn) hΛ]
    by_cases hc : Nat.Coprime n q
    · simp only [ite_eq_left hc, Complex.one_re]
      ring
    · simp only [ite_eq_right hc, Complex.zero_re, add_zero, one_mul]

/-- For a finite support through b and arbitrary real weights, coprime prime
triviality identifies the real character prefix with the coprime filtered prefix.
Reduce nonzero Mangoldt terms to their exact zero-or-one character values. -/
theorem character_mangoldt_prefix_re_eq_coprime {q : ℕ} (χ : DirichletCharacter ℂ q) {b : ℝ}
    (S : Finset ℕ) (w : ℕ → ℝ) (hS : ∀ n ∈ S, (n : ℝ) ≤ b)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ b → Nat.Coprime p q → χ p = 1) :
    (∑ n ∈ S, (χ n).re * ArithmeticFunction.vonMangoldt n * w n) =
      ∑ n ∈ S.filter (fun n ↦ Nat.Coprime n q), ArithmeticFunction.vonMangoldt n * w n := by
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hΛ : ArithmeticFunction.vonMangoldt n = 0
  · simp only [hΛ, mul_zero, zero_mul, ite_self]
  · rw [character_apply_ite_of_coprime_trivial χ hsmall (hS n hn) hΛ]
    by_cases hc : Nat.Coprime n q
    · simp only [ite_eq_left hc, Complex.one_re, one_mul]
    · simp only [ite_eq_right hc, Complex.zero_re, zero_mul]

/-- For arbitrary real weights, the full-plus-coprime prefix equals twice the
full prefix minus the noncoprime contribution. Partition the support by coprimality.
This exposes the exact common-factor loss for later quantitative estimates. -/
theorem coprimePositiveMangoldtPrefix_eq_twice_sub (q : ℕ) (S : Finset ℕ) (w : ℕ → ℝ) :
    coprimePositiveMangoldtPrefix q S w =
      2 * (∑ n ∈ S, ArithmeticFunction.vonMangoldt n * w n) -
        ∑ n ∈ S.filter (fun n ↦ ¬Nat.Coprime n q), ArithmeticFunction.vonMangoldt n * w n := by
  have hs :=
    Finset.sum_filter_add_sum_filter_not (s := S) (p := fun n ↦ Nat.Coprime n q) (f := fun n ↦
      ArithmeticFunction.vonMangoldt n * w n)
  unfold coprimePositiveMangoldtPrefix
  linarith only [hs]

/-- On a support coprime to q, the full-plus-coprime prefix is twice the full prefix.
The coprime filter is the entire support. This recovers the no-loss comparison interface. -/
theorem coprimePositiveMangoldtPrefix_eq_twice_of_coprime (q : ℕ) (S : Finset ℕ) (w : ℕ → ℝ)
    (hc : ∀ n ∈ S, Nat.Coprime n q) :
    coprimePositiveMangoldtPrefix q S w = 2 * ∑ n ∈ S, ArithmeticFunction.vonMangoldt n * w n := by
  unfold coprimePositiveMangoldtPrefix
  rw [Finset.filter_eq_self.mpr hc]
  ring

/-- For a quadratic complex character and any natural input coprime to its level,
a value different from one is minus one. Exclude zero by the unit condition and
split the three quadratic values. No primitivity, GRH or primality is needed. -/
theorem quadratic_character_apply_neg_one_of_coprime_ne_one {q n : ℕ} (χ : DirichletCharacter ℂ q)
    (hquad : χ.IsQuadratic) (hcop : Nat.Coprime n q) (hne : χ n ≠ 1) : χ n = -1 := by
  have hz : χ n ≠ 0 := MulChar.apply_ne_zero_iff.mpr ((ZMod.isUnit_iff_coprime n q).mpr hcop)
  rcases hquad (n : ZMod q) with h0 | h1 | hm
  · exact False.elim (hz h0)
  · exact False.elim (hne h1)
  · exact hm

end PseudoPrime.AnalyticNumberTheory.Arithmetic
