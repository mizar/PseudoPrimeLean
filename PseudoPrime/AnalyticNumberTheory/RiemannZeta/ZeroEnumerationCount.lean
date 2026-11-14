/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCriticalEnumeration
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCountConjugation

/-! # Completeness and simplicity from a zero-count bound -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- A subset with `n` elements exhausts a finite set whose positive integer
weights sum to at most `n`. Equality also forces every weight to be one. -/
private theorem finite_weights_eq_one {α : Type*} (s t : Finset α) (w : α → ℕ) {n : ℕ} (hs : s ⊆ t)
    (hcard : s.card = n) (hw : ∀ x ∈ t, 1 ≤ w x) (hcount : (∑ x ∈ t, (w x : ℝ)) ≤ n) :
    s = t ∧ ∀ x ∈ t, w x = 1 := by
  classical
  have hle : (t.card : ℝ) ≤ ∑ x ∈ t, (w x : ℝ) := by
    calc
      (t.card : ℝ) = ∑ x ∈ t, (1 : ℝ) := by simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ∑ x ∈ t, (w x : ℝ) := Finset.sum_le_sum (fun x hx ↦ by exact_mod_cast hw x hx)
  have hct : t.card ≤ n := by exact_mod_cast hle.trans hcount
  have heq : s = t := Finset.eq_of_subset_of_card_le hs (hcard ▸ hct)
  have hsum : (∑ x ∈ t, (1 : ℝ)) = ∑ x ∈ t, (w x : ℝ) := by
    have hc : t.card = n := by rw [← heq, hcard]
    simp only [Finset.sum_const, nsmul_eq_mul, mul_one, hc]
    exact le_antisymm (by simpa only [hc] using hle) hcount
  refine ⟨heq, ?_⟩
  have hpoint := (Finset.sum_eq_sum_iff_of_le (fun x hx ↦ by exact_mod_cast hw x hx)).mp hsum
  intro x hx
  exact_mod_cast (hpoint x hx).symm

/-- Under RH, `n` distinct positive-height ledger zeros and a two-sided
multiplicity count of at most `2n` exhaust the positive ledger and are all
simple. Conjugation halves the count and every zero has positive multiplicity. -/
theorem positive_ledger_of_count {T : ℝ} (hT : 0 ≤ T) (hRH : RiemannHypothesis) {n : ℕ}
    (z : Fin n → ℂ) (hinj : Function.Injective z)
    (hz : ∀ i, z i ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im)) (hcount : zeroCount T ≤ 2 * n) :
    (Finset.univ.image z = (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im)) ∧
      ∀ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im), riemannZetaZeroMultiplicity ρ = 1 := by
  classical
  have hs : Finset.univ.image z ⊆ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im) := by
    intro ρ hρ
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hρ
    exact hz i
  have hc : (Finset.univ.image z).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hw : ∀ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im), 1 ≤ riemannZetaZeroMultiplicity ρ := by
    intro ρ hρ
    have hh := Finset.mem_filter.mp hρ
    have hne : ρ ≠ 1 := by
      intro he
      rw [he, Complex.one_im] at hh
      exact (lt_irrefl 0) hh.2
    exact riemannZetaZeroMultiplicity_pos hne ((mem_zerosUpTo hT).mp hh.1).1
  have hbound :
    (∑ ρ ∈ (zerosUpTo T).filter (fun ρ ↦ 0 < ρ.im), (riemannZetaZeroMultiplicity ρ : ℝ)) ≤ n := by
    have h := zeroCount_eq_two_positive hRH hT
    rw [positiveZeroCount] at h
    linarith only [h, hcount]
  exact finite_weights_eq_one _ _ _ hs hc hw hbound

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
