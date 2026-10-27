/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.QuadraticAmbientSquares
public import PseudoPrime.LLS.ReciprocalGapAmbientArithmetic

/-! # Principal-weight restoration for excluded quadratic squares -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Principal-weight sum on positive indices below x that are squares, coprime to q
and noncoprime to N. The parameters are totalized. Twice this sum is restored when
a quadratic character replaces the generic bound Re chi>=-1 by its exact value one. -/
noncomputable def reciprocalGapAdditionalSquareWeight (h : ℝ) (q N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ Nat.Coprime n q ∧ ¬Nat.Coprime n N ∧ IsSquare n),
    reciprocalGapPrincipalWeight h x n

/-- For h>=0,x>0, quadratic character data and ambient prime triviality through x,
restore twice the exact additional square weight in the selected principal-sum bound.
Pass the generic arithmetic square restoration to the principal factor and identify
the real character sum. This retains squared excluded-prime contributions positively. -/
theorem quadratic_selected_reciprocalGap_sum_sub_loss_le_character {q N : ℕ} (hqN : q ∣ N) {h x : ℝ}
    (hh : 0 ≤ h) (hx : 0 < x) (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) :
    (∑ n ∈ B, reciprocalGapPrincipalWeight h x n) - reciprocalGapAdditionalNonunitWeight h q N x +
        2 * reciprocalGapAdditionalSquareWeight h q N x ≤
      (reciprocalGapCharacterSum h χ x).re := by
  have hs :=
    AnalyticNumberTheory.Arithmetic.quadratic_selected_sub_loss_le_character hqN χ hquad
      (Finset.Ioc 0 ⌊x⌋₊) B (reciprocalGapPrincipalFactor h x) hB hcop
      (fun n hn ↦ (Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx.le))
      (fun n hn ↦
        reciprocalGapPrincipalFactor_nonneg hh hx n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp hn).2).trans (Nat.floor_le hx.le)))
      hsmall
  simp only [AnalyticNumberTheory.Arithmetic.additionalNonunitMangoldtPrefix,
    AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix, mul_assoc,
    mangoldt_mul_reciprocalGapPrincipalFactor] at hs
  rw [reciprocalGapCharacterSum_re_eq_weighted]
  exact hs

/-- Under quadratic ambient triviality, finite Mangoldt lower and power upper endpoints
give a selected lower certificate minus exclusion cost plus twice the square restoration.
Combine the generic selected-weight bound with the restored exact principal sum.
This is the input for improved odd negative witness separation. -/
theorem quadratic_selected_reciprocalGap_lower_sub_loss_le_character {q N : ℕ} (hqN : q ∣ N)
    {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) (χ : DirichletCharacter ℂ q) (hquad : χ.IsQuadratic)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1) (B : Finset ℕ)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ B, u n ≤ 1) :
    (∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / h)) -
          reciprocalGapAdditionalNonunitWeight h q N x +
        2 * reciprocalGapAdditionalSquareWeight h q N x ≤
      (reciprocalGapCharacterSum h χ x).re := by
  have hl := sum_lower_le_reciprocalGap_selectedWeight hh B lo u hlo hu hu1
  have hs :=
    quadratic_selected_reciprocalGap_sum_sub_loss_le_character hqN hh hx χ hquad hsmall B hB hcop
  linarith only [hl, hs]

/-- For h>=0,x>0, the additional excluded square principal weight is nonnegative.
Every index lies below x. This proves that the square restoration weakens the
sufficient witness inequality without adding a hypothesis on the modulus. -/
theorem reciprocalGapAdditionalSquareWeight_nonneg {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) (q N : ℕ) :
    0 ≤ reciprocalGapAdditionalSquareWeight h q N x := by
  exact
    Finset.sum_nonneg
      (fun n hn ↦
        reciprocalGapPrincipalWeight_nonneg hh hx n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2).trans
            (Nat.floor_le hx.le)))

/-- For h>=0,x>0, a selected subset of additional excluded squares and certified
Mangoldt lower/power upper endpoints give a lower bound on the full square restoration.
Discard other nonnegative square weights. This permits sparse certificates for the
improvement without enumerating every square below the radius. -/
theorem selected_reciprocalGap_square_lower_le {q N : ℕ} {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x)
    (C : Finset ℕ) (hC : C ⊆ Finset.Ioc 0 ⌊x⌋₊)
    (hcop : ∀ n ∈ C, Nat.Coprime n q ∧ ¬Nat.Coprime n N ∧ IsSquare n) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ C, lo n ≤ ArithmeticFunction.vonMangoldt n) (hu : ∀ n ∈ C, ((n : ℝ) / x) ^ h ≤ u n)
    (hu1 : ∀ n ∈ C, u n ≤ 1) :
    (∑ n ∈ C, (lo n / Real.sqrt x) * ((1 - u n) / h)) ≤
      reciprocalGapAdditionalSquareWeight h q N x := by
  have hl := sum_lower_le_reciprocalGap_selectedWeight hh C lo u hlo hu hu1
  have hs :
    C ⊆ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n ↦ Nat.Coprime n q ∧ ¬Nat.Coprime n N ∧ IsSquare n) :=
    fun n hn ↦ Finset.mem_filter.mpr ⟨hC hn, hcop n hn⟩
  have hb :=
    Finset.sum_le_sum_of_subset_of_nonneg (f := reciprocalGapPrincipalWeight h x) hs
      (fun n hn _ ↦
        reciprocalGapPrincipalWeight_nonneg hh hx n
          ((Nat.cast_le.mpr (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).2).trans
            (Nat.floor_le hx.le)))
  exact hl.trans hb

end PseudoPrime.LLS.PaperStatements
