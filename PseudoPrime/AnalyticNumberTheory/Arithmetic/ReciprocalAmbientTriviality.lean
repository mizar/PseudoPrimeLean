/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterAmbientTriviality
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt

/-! # Reciprocal weighted sums with exact additional nonunit losses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Arithmetic

/-- Mangoldt-free reciprocal weight n^(-1)(1-n/Y), with totalized real division.
It is nonnegative for 0<=n<=Y and Y>0. Multiplication by Lambda gives the standard
reciprocal summand; this permits ambient-exclusion arithmetic comparisons. -/
noncomputable def reciprocalMangoldtFactor (Y : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)⁻¹ * (1 - n / Y)

/-- At positive Y and n<=Y the reciprocal factor is nonnegative.
Both factors are nonnegative. Used for selected reciprocal prefixes. -/
theorem reciprocalMangoldtFactor_nonneg {Y : ℝ} (hY : 0 < Y) (n : ℕ) (hn : (n : ℝ) ≤ Y) :
    0 ≤ reciprocalMangoldtFactor Y n := by
  exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n)) (sub_nonneg.mpr ((div_le_one hY).mpr hn))

/-- For all real Y and natural n, multiplying the reciprocal factor by Lambda(n)
gives the standard reciprocal term. Rearrange totalized division without cancellation.
This identifies the generic weighted arithmetic sum with the explicit formula sum. -/
theorem mangoldt_mul_reciprocalMangoldtFactor (Y : ℝ) (n : ℕ) :
    ArithmeticFunction.vonMangoldt n * reciprocalMangoldtFactor Y n =
      reciprocalWeightedMangoldtTerm Y n := by
  unfold reciprocalMangoldtFactor reciprocalWeightedMangoldtTerm
  simp only [div_eq_mul_inv]
  ring

/-- If q divides N, Y>0, C is an N-coprime selected subset through Y, and the
character is one on N-coprime primes through Y, the selected reciprocal sum minus
its exact additional-nonunit loss bounds the real character reciprocal sum below.
Apply the generic nonnegative weighted comparison and identify its summands.
This retains conductor/exclusion distinctions in endpoint zero-mass bounds. -/
theorem selected_reciprocal_sub_loss_le_character {q N : ℕ} (hqN : q ∣ N)
    (χ : DirichletCharacter ℂ q) {Y : ℝ} (hY : 0 < Y) (C : Finset ℕ) (hC : C ⊆ Finset.Ioc 0 ⌊Y⌋₊)
    (hcop : ∀ n ∈ C, Nat.Coprime n N)
    (ht : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ Y → Nat.Coprime p N → χ p = 1) :
    (∑ n ∈ C, reciprocalWeightedMangoldtTerm Y n) -
        additionalNonunitMangoldtPrefix q N (Finset.Ioc 0 ⌊Y⌋₊) (reciprocalMangoldtFactor Y) ≤
      (characterReciprocalWeightedSum Y χ).re := by
  have hw : ∀ n ∈ Finset.Ioc 0 ⌊Y⌋₊, 0 ≤ reciprocalMangoldtFactor Y n := by
    intro n hn
    exact
      mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg n))
        (sub_nonneg.mpr
          ((div_le_one hY).mpr
            ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hY.le))))
  have hs :=
    selected_mangoldt_sub_loss_le_character hqN χ (Finset.Ioc 0 ⌊Y⌋₊) C (reciprocalMangoldtFactor Y)
      hC hcop (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hY.le)) hw
      ht
  have he :
    (characterReciprocalWeightedSum Y χ).re =
      ∑ n ∈ Finset.Ioc 0 ⌊Y⌋₊,
        (χ n).re * ArithmeticFunction.vonMangoldt n * reciprocalMangoldtFactor Y n := by
    unfold characterReciprocalWeightedSum characterReciprocalWeightedTerm
    simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
      sub_zero]
    apply Finset.sum_congr rfl
    intro n _
    unfold reciprocalWeightedMangoldtTerm reciprocalMangoldtFactor
    ring
  rw [he]
  simpa only [mangoldt_mul_reciprocalMangoldtFactor] using hs

end PseudoPrime.AnalyticNumberTheory.Arithmetic
