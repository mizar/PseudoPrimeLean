/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteQuadraticHeightWeights
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.FamilyDensity

/-! # Inverse quadratic weights in unconditional primitive-family density -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/-- For a conductor cutoff, retain the conductor index, primitive-family character,
complex zero, and an index below its analytic order. This is the ambient dependent
type of the existing occurrence ledger. It preserves multiplicity and character
identity in weighted density sums. -/
abbrev FamilyZeroOccurrence (Q : ℕ) :=
  Σ q : Fin Q,
    Σ χ : DirichletCharacter ℂ (q.val + 1),
      Σ ρ : ℂ, Fin (analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ)

/-- Project a family occurrence to its complex zero value. Conductor, character,
and multiplicity labels remain in the occurrence even when projected values agree.
This projection supplies real-part and ordinate weights in finite family sums. -/
def familyZeroOccurrenceValue {Q : ℕ} (o : FamilyZeroOccurrence Q) : ℂ :=
  o.2.2.1

/-- A primitive nonprincipal completed zero with real part in the specified strip
and ordinate below the natural cutoff belongs to the family occurrence ledger
with each valid analytic-order index. Construct the rectangle membership from its
coordinates and retain the original conductor and character labels. -/
theorem familyZeroOccurrence_mem_of_coordinates {Q n : ℕ} {q : Fin Q}
    {χ : DirichletCharacter ℂ (q.val + 1)} {ρ : ℂ}
    (i : Fin (analyticOrderNatAt χ.completedLFunction ρ)) (hne : χ ≠ 1) (hp : χ.IsPrimitive)
    (hz : χ.completedLFunction ρ = 0) {σ : ℝ} (hlo : σ ≤ ρ.re) (hhi : ρ.re ≤ 1) (hh : |ρ.im| ≤ n) :
    (⟨q, χ, ρ, i⟩ : FamilyZeroOccurrence Q) ∈
      primitiveCharacterFamilyZeroOccurrenceLedger Q σ n := by
  classical
  have hbox :
    ρ ∈
      dirichletCompletedLFunctionRectangleBox ((σ : ℂ) - (n : ℝ) * Complex.I)
        ((1 : ℂ) + (n : ℝ) * Complex.I) := by
    rw [dirichletCompletedLFunctionRectangleBox, Rectangle.rectangleClosedBox, Complex.mem_reProdIm]
    simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, sub_zero, Complex.add_re, add_zero, Complex.sub_im, Complex.mul_im, Complex.I_im,
      mul_one, zero_sub, Complex.add_im, zero_add, Complex.one_re, Complex.one_im]
    exact ⟨Set.Icc_subset_uIcc ⟨hlo, hhi⟩, Set.Icc_subset_uIcc (abs_le.mp hh)⟩
  have hzero := (mem_completedZerosInRectangle_iff (hχ := hne)).mpr ⟨hbox, hz⟩
  simp only [primitiveCharacterFamilyZeroOccurrenceLedger, Finset.mem_sigma, Finset.mem_univ,
    dite_eq_left hne, dite_eq_left hp, true_and, completedZeroMultiplicityOccurrences]
  exact ⟨hzero, True.intro⟩

/-- Filtering any existing finite family packet by a new real-part threshold and
height places it in the corresponding occurrence ledger. Extract primitivity and
nonprincipality from the original ledger and use the unconditional zero-free right
half-plane. This permits comparison with the actual analytic-multiplicity count. -/
theorem filter_familyZeroOccurrence_subset_height_ledger {Q H n : ℕ} {σ₀ σ : ℝ}
    (S : Finset (FamilyZeroOccurrence Q))
    (hS : S ⊆ primitiveCharacterFamilyZeroOccurrenceLedger Q σ₀ H) :
    S.filter
        (fun o ↦ σ ≤ (familyZeroOccurrenceValue o).re ∧ |(familyZeroOccurrenceValue o).im| ≤ n) ⊆
      primitiveCharacterFamilyZeroOccurrenceLedger Q σ n := by
  intro o ho
  have hs := (Finset.mem_filter.mp ho).1
  have hc := (Finset.mem_filter.mp ho).2
  obtain ⟨q, χ, ρ, i, hne, heq, hp, hρ⟩ :=
    primitiveCharacterFamilyZeroOccurrenceLedger_mem_extract (hS hs)
  subst o
  have hz := (mem_completedZerosInRectangle_iff.mp hρ).2
  exact
    familyZeroOccurrence_mem_of_coordinates i hne hp hz hc.1
      (completedLFunction_zero_re_lt_one hne hz).le hc.2

/-- There are positive absolute density constants bounding inverse quadratic
ordinate weights in every finite primitive-family packet, uniformly in its height.
For real-part thresholds in `[1/2,1]` with density exponent at most one half, the
bound is `C * (Q+1)^(A*(1-σ))`. Derive a linear cumulative height count from the
proved log-free density and apply the finite quadratic-weight lemma. No density
hypothesis or RH remains in the public interface; all occurrence labels are retained. -/
theorem exists_family_inverse_quadratic_weighted_density :
    ∃ A C : ℝ,
      0 < A ∧
        0 < C ∧
        ∀ (Q H : ℕ) (σ : ℝ),
          (1 / 2 : ℝ) ≤ σ →
            σ ≤ 1 →
            A * (1 - σ) ≤ 1 / 2 →
            ∀ S : Finset (FamilyZeroOccurrence Q),
              S ⊆ primitiveCharacterFamilyZeroOccurrenceLedger Q (1 / 2) H →
                ∑ o ∈ S.filter (fun o ↦ σ ≤ (familyZeroOccurrenceValue o).re),
                    1 / (1 + (familyZeroOccurrenceValue o).im ^ 2) ≤
                  C * Real.rpow ((Q + 1 : ℕ) : ℝ) (A * (1 - σ)) := by
  obtain ⟨A, C, hA, hC, hcounts⟩ :=
    exists_primitiveCharacterFamily_log_free_density_height_sum_bounds
  refine ⟨A, 16 * C, hA, mul_pos (by norm_num only) hC, ?_⟩
  intro Q H σ hσlo hσhi hδ S hS
  let B := C * Real.rpow ((Q + 1 : ℕ) : ℝ) (A * (1 - σ))
  let U := S.filter (fun o ↦ σ ≤ (familyZeroOccurrenceValue o).re)
  have hB : 0 ≤ B := mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hc (n : ℕ) (hn : 2 ≤ n) :
    ∑ o ∈ U.filter (fun o ↦ |(familyZeroOccurrenceValue o).im| ≤ n), (1 : ℝ) ≤ B * n := by
    have hsub :
      U.filter (fun o ↦ |(familyZeroOccurrenceValue o).im| ≤ n) ⊆
        primitiveCharacterFamilyZeroOccurrenceLedger Q σ n := by
      intro o ho
      have hU := (Finset.mem_filter.mp ho).1
      have hSσ := Finset.mem_filter.mp hU
      apply filter_familyZeroOccurrence_subset_height_ledger S hS
      exact Finset.mem_filter.mpr ⟨hSσ.1, hSσ.2, (Finset.mem_filter.mp ho).2⟩
    have hcard := Finset.card_le_card hsub
    have hcount := (hcounts Q σ hσlo hσhi hδ).1 n hn
    have hnreal : (1 : ℝ) ≤ n := by
      have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith only [hnr]
    have hpow : Real.rpow (n : ℝ) (A * (1 - σ)) ≤ n := by
      have hb := Real.rpow_le_rpow_of_exponent_le hnreal (by linarith only [hδ] : A * (1 - σ) ≤ 1)
      simpa only [Real.rpow_one, Real.rpow_eq_pow] using hb
    calc
      _ = ((U.filter (fun o ↦ |(familyZeroOccurrenceValue o).im| ≤ n)).card : ℝ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
      _ ≤ ((primitiveCharacterFamilyZeroOccurrenceLedger Q σ n).card : ℝ) := by exact_mod_cast hcard
      _ = primitiveCharacterFamilyZeroCountAtNatHeight Q σ n :=
        (primitiveCharacterFamilyZeroCountAtNatHeight_eq_occurrenceLedger_card Q σ n).symm
      _ ≤ B * Real.rpow (n : ℝ) (A * (1 - σ)) := hcount
      _ ≤ B * n := mul_le_mul_of_nonneg_left hpow hB
  have hw :=
    Analysis.sum_inverse_quadratic_of_linear_height_count U
      (fun o ↦ (familyZeroOccurrenceValue o).im) (fun _ ↦ (1 : ℝ)) hB (fun _ _ ↦ zero_le_one) hc
  change (∑ o ∈ U, 1 / (1 + (familyZeroOccurrenceValue o).im ^ 2)) ≤ _
  exact
    hw.trans_eq
      (by
        dsimp only [B]; ring)

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
