/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyExceptionalWeightedGap

/-! # Weighted character families and their multiplicity occurrence ledgers -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a nonprincipal character and a closed rectangle, summing any real weight
over multiplicity occurrences equals the divisor-weighted sum over distinct zeros.
Expand the finite sigma and identify divisor and analytic order. This preserves
multiplicity in weighted analytic family estimates. -/
theorem sum_zeroOccurrences_eq_divisor {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (z w : ℂ) (f : ℂ → ℝ) :
    ∑ o ∈ completedZeroMultiplicityOccurrences χ hne z w, f o.1 =
      ∑ ρ ∈ completedZerosInRectangle χ hne z w,
        (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * f ρ := by
  rw [completedZeroMultiplicityOccurrences, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro ρ _
  rw [completed_divisor_eq_orderNat hne, Int.cast_natCast]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

namespace LogFreeDensity

/-- Retain a successor-indexed conductor and its complex character at a bounded
scale. This is the character part of a family zero occurrence and matches the
bounded primitive labels used for arithmetic error transfer. -/
abbrev FamilyCharacterLabel (Q : ℕ) :=
  Σ q : Fin Q, DirichletCharacter ℂ (q.val + 1)

/-- Project a family zero occurrence to its conductor-character label, retaining
both labels while dropping only the zero and multiplicity index. This selects
exactly the characters contributing to a finite arithmetic family. -/
def occurrenceLabel {Q : ℕ} (o : FamilyZeroOccurrence Q) : FamilyCharacterLabel Q :=
  ⟨o.1, o.2.1⟩

open Classical in
/-- For a finite set of conductor-character labels, the weighted sum of the
corresponding ledger occurrences equals the sum of actual divisor-weighted zero
sums over those labels. Nonprimitive and principal labels contribute zero.
Expand the finite sigma sums and use the individual occurrence identity. This
connects global weighted density to finite character families without a family factor. -/
theorem occurrence_labels_sum (Q H : ℕ) (σ : ℝ) (S : Finset (FamilyCharacterLabel Q)) (f : ℂ → ℝ) :
    ∑ o ∈ (occurrenceLedger Q σ H).filter (fun o ↦ occurrenceLabel o ∈ S), f (occurrenceValue o) =
      ∑ p ∈ S,
        if hne : p.2 ≠ 1 then
          if _hp : p.2.IsPrimitive then
            ∑
              ρ ∈
                completedZerosInRectangle p.2 hne ((σ : ℂ) - (H : ℝ) * Complex.I)
                  ((1 : ℂ) + (H : ℝ) * Complex.I),
              (MeromorphicOn.divisor p.2.completedLFunction Set.univ ρ : ℝ) * f ρ
          else 0
        else 0 := by
  let F : FamilyCharacterLabel Q → ℝ := fun p ↦
    if hne : p.2 ≠ 1 then
      if _hp : p.2.IsPrimitive then
        ∑
          ρ ∈
            completedZerosInRectangle p.2 hne ((σ : ℂ) - (H : ℝ) * Complex.I)
              ((1 : ℂ) + (H : ℝ) * Complex.I),
          (MeromorphicOn.divisor p.2.completedLFunction Set.univ ρ : ℝ) * f ρ
      else 0
    else 0
  change _ = ∑ p ∈ S, F p
  have hs : (∑ p ∈ S, F p) = ∑ p : FamilyCharacterLabel Q, if p ∈ S then F p else 0 := by
    rw [← Finset.sum_filter]
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hs, Fintype.sum_sigma, Finset.sum_filter, occurrenceLedger, Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro q _
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro χ _
  dsimp only [F, occurrenceLabel, occurrenceValue]
  by_cases hn : χ ≠ 1
  · rw [dite_eq_left hn, dite_eq_left hn]
    by_cases hp : χ.IsPrimitive
    · rw [dite_eq_left hp, dite_eq_left hp]
      by_cases hm : (⟨q, χ⟩ : FamilyCharacterLabel Q) ∈ S
      · simp only [hm, ite_true]
        exact sum_zeroOccurrences_eq_divisor χ hn _ _ f
      · simp only [hm, ite_false, Finset.sum_const_zero]
    · simp only [dite_eq_right hp, Finset.sum_empty, ite_self]
  · simp only [dite_eq_right hn, Finset.sum_empty, ite_self]

/-- An occurrence in a family ledger with threshold at most one has real part
between that threshold and one. Extract the actual zero and its rectangle
coordinates. These bounds permit changing the lower threshold of a family packet. -/
theorem occurrence_re_bounds {Q H : ℕ} {σ : ℝ} (hσ : σ ≤ 1) {o : FamilyZeroOccurrence Q}
    (ho : o ∈ occurrenceLedger Q σ H) :
    σ ≤ (occurrenceValue o).re ∧ (occurrenceValue o).re ≤ 1 := by
  obtain ⟨q, χ, ρ, i, hne, rfl, hp, hρ⟩ := ledger_mem_extract ho
  have hb := (mem_completedZerosInRectangle_iff.mp hρ).1
  rw [completedRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm] at hb
  have hre := hb.1
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
    mul_zero, zero_mul, sub_zero, Complex.add_re, add_zero, Complex.one_re] at hre
  rw [Set.uIcc_of_le hσ] at hre
  exact hre

/-- Lowering a ledger's real-part threshold preserves every occurrence, provided
the original threshold is at most one. Reconstruct membership from the actual
zero coordinates while retaining its multiplicity index. This embeds near-one
packets in the half-strip ledger used by the proved density estimate. -/
theorem ledger_antitone_re {Q H : ℕ} {σ τ : ℝ} (hστ : σ ≤ τ) (hτ : τ ≤ 1) :
    occurrenceLedger Q τ H ⊆ occurrenceLedger Q σ H := by
  intro o ho
  have hre := occurrence_re_bounds hτ ho
  have hh := occurrence_height_le ho
  obtain ⟨q, χ, ρ, i, hne, rfl, hp, hρ⟩ := ledger_mem_extract ho
  exact
    ledger_mem_of_coords i hne hp (mem_completedZerosInRectangle_iff.mp hρ).2 (hστ.trans hre.1)
      hre.2 hh

end LogFreeDensity

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
