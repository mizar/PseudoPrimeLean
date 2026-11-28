/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPolePrefixComparison

public import PseudoPrime.PrimeTestBounds.MillerRabin.RefinedSixPoleDoubleAbel
import Mathlib.Analysis.Complex.ExponentialBounds

/-! # Six-pole principal comparison with squares above the cutoff -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Extend the principal prefix at X by the squares of roots in S. The roots
lie below X, so their Mangoldt-supported squares have trace three whenever the
three characters are one on primes up to X. The squares exceed X, so their
fourfold principal contribution is disjoint from the prefix. -/
theorem refined_prefix_add_squares {p q r : ℕ} [NeZero p] [NeZero q] [NeZero r]
    (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ r) {X : ℝ}
    (hX : 0 < X) (S : Finset ℕ) (hs : ∀ k ∈ S, (k : ℝ) ≤ X ∧ X < (k : ℝ) ^ 2)
    (ht : ∀ k : ℕ, -1 ≤ (a k).re + (b k).re + (c k).re)
    (hA : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → a l = 1) (hB : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → b l = 1)
    (hC : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → c l = 1) :
    let f := fun k : ℕ ↦ (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re
    4 * (∑ k ∈ Finset.Ioc 0 ⌊X⌋₊, f k) + 4 * (∑ k ∈ S, f (k ^ 2)) -
        (∑' k : ℕ, refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) X k).re ≤
      (∑' k : ℕ, refinedSixPoleKernel.summand a X k).re +
        (∑' k : ℕ, refinedSixPoleKernel.summand b X k).re +
        (∑' k : ℕ, refinedSixPoleKernel.summand c X k).re := by
  intro f
  let P := Finset.Ioc 0 ⌊X⌋₊
  let T := S.image (fun k ↦ k ^ 2)
  have hd : Disjoint P T := by
    apply Finset.disjoint_left.mpr
    intro m hm ht'
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ht'
    exact
      (not_lt_of_ge ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hm).2))
        (by exact_mod_cast (hs k hk).2)
  have oneAt {d : ℕ} (χ : DirichletCharacter ℂ d) (hχ : ∀ l : ℕ, l.Prime → (l : ℝ) ≤ X → χ l = 1)
    {m : ℕ} (hm : m ∈ P ∪ T) (hΛ : ArithmeticFunction.vonMangoldt m ≠ 0) : χ m = 1 := by
    have base {k : ℕ} (hk : (k : ℝ) ≤ X) (hv : ArithmeticFunction.vonMangoldt k ≠ 0) :=
      AnalyticNumberTheory.Arithmetic.character_eq_one_of_ambient_mangoldt (N := 1) χ
        (fun l hl hlX _ ↦ hχ l hl hlX) hk (Nat.coprime_one_right k) hv
    rcases Finset.mem_union.mp hm with hm | hm
    · exact base ((Nat.le_floor_iff hX.le).mp (Finset.mem_Ioc.mp hm).2) hΛ
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hm
    rw [ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0)] at hΛ
    rw [Nat.cast_pow, map_pow, base (hs k hk).1 hΛ, one_pow]
  have hc :=
    refined_three_principal_prefix a b c hX (P ∪ T) ht
      (by
        intro k hk hv
        rw [oneAt a hA hk hv, oneAt b hB hk hv, oneAt c hC hk hv, Complex.one_re]
        norm_num only)
  rw [Finset.sum_union hd,
    Finset.sum_image (fun _ _ _ _ h ↦ Nat.pow_left_injective (by decide : 2 ≠ 0) h)] at hc
  dsimp only [f]
  linarith only [hc]

/-- For r at least 465/2, the root window of the six-pole kernel lies below
the cutoff r squared, and each square from that window exceeds the cutoff. -/
theorem refined_square_window {r : ℝ} (hr : 465 / 2 ≤ r) {k : ℕ}
    (hk : k ∈ Finset.Ioc ⌊r⌋₊ ⌊Real.exp (21 / 16) * r⌋₊) :
    (k : ℝ) ≤ r ^ 2 ∧ r ^ 2 < (k : ℝ) ^ 2 := by
  have hr0 : 0 ≤ r := le_trans (by norm_num only : (0 : ℝ) ≤ 465 / 2) hr
  obtain ⟨ha, hb⟩ := Finset.mem_Ioc.mp hk
  have hlo := Nat.lt_of_floor_lt ha
  have hhi := (Nat.le_floor_iff (mul_nonneg (Real.exp_pos _).le hr0)).mp hb
  have he : Real.exp (21 / 16) ≤ 9 := by
    have ht := Real.exp_le_exp.mpr (by norm_num only : (21 / 16 : ℝ) ≤ 1 + 1)
    rw [Real.exp_add] at ht
    exact
      ht.trans
        (by
          nlinarith only [Real.exp_one_lt_three, Real.exp_pos 1,
            mul_self_lt_mul_self (Real.exp_pos 1).le Real.exp_one_lt_three])
  exact
    ⟨hhi.trans
        (le_trans (mul_le_mul_of_nonneg_right he hr0)
          (by nlinarith only [mul_le_mul_of_nonneg_right hr hr0, hr0])),
      pow_lt_pow_left₀ hlo hr0 (by decide)⟩

/-- At square indices the actual principal recovery term is the Mangoldt
weight of the root times the six-pole scaled weight at its square. -/
theorem refined_square_principal_eq {x : ℝ} (hx : 0 < x) {k : ℕ} (hk : 0 < k) :
    (refinedSixPoleKernel.summand (1 : DirichletCharacter ℂ 1) x (k ^ 2)).re =
      ArithmeticFunction.vonMangoldt k * refinedScaledWeight x ((k : ℝ) ^ 2) := by
  rw [refined_principal_summand_eq hx (pow_ne_zero _ hk.ne'),
    ArithmeticFunction.vonMangoldt_apply_pow (by decide : 2 ≠ 0), Nat.cast_pow]

end PseudoPrime.PrimeTestBounds.MillerRabin
