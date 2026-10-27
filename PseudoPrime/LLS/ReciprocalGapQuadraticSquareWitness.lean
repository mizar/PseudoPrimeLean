/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapQuadraticSquares
public import PseudoPrime.LLS.ReciprocalGapEvenAmbientWitness

/-! # Quadratic witnesses with restored excluded-square contributions -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Even ambient separation with twice the exact additional excluded-square
principal weight subtracted. Inputs are the character level, ambient exclusion modulus,
radius and two positive-prefix supports. Under quadraticity these restored terms have
value one, yielding a smaller sufficient witness budget. -/
noncomputable def reciprocalGapQuadraticSquareSeparation (q N : ℕ) (x : ℝ) (B₀ B₁ : Finset ℕ) : ℝ :=
  reciprocalGapEvenAmbientRationalSeparation q N x B₀ B₁ -
    2 * reciprocalGapAdditionalSquareWeight (7 / 10) q N x

/-- For primitive even nonprincipal quadratic GRH data with q dividing N and x>=1,
square-restored separation yields an N-coprime non-one prime below x. Under witness
nonexistence combine the even scalar upper bound with the strengthened principal lower
bound. No excluded square term is charged as a possible negative character value. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_quadratic_squares {q N : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hqN : q ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (he : χ.Even)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapQuadraticSquareSeparation q N x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have hK₀ :=
    AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix_le_character hqN χ B₀
      (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹) hB₀
      (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsmall
  have hK₁ :=
    AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix_le_character hqN χ B₁
      (fun n ↦ ((n : ℝ) ^ (6 / 5 : ℝ))⁻¹) hB₁
      (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsmall
  simp only [← div_eq_mul_inv] at hK₀ hK₁
  have hU :=
    reciprocalGapCharacterSum_re_le_even_scalar_rational hq hGRH he hp hne hinv hx B₀ B₁ hK₀ hK₁
  have hL :=
    quadratic_selected_reciprocalGap_lower_sub_loss_le_character hqN
      (by norm_num only : (0 : ℝ) ≤ 7 / 10) (zero_lt_one.trans_le hx) χ hquad hsmall B hB hcop lo u
      hlo hu hu1
  unfold reciprocalGapQuadraticSquareSeparation reciprocalGapEvenAmbientRationalSeparation at hgap
  linarith only [hL, hU, hgap]

/-- For a primitive even nonprincipal quadratic character under GRH, assume q divides N
and two divides N. Ambient separation against the selected lower certificate yields
an odd N-coprime prime p<=x with chi(p)=-1. Coprimality excludes two and zero character
values. The exact extra-exclusion budget is retained in the separation premise. -/
theorem exists_odd_prime_neg_one_of_reciprocalGap_quadratic_squares {q N : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (he : χ.Even)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapQuadraticSquareSeparation q N x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hinv : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_quadratic_squares hq hqN hGRH he hp hne hinv hquad
      hx B₀ B₁ B hB₀ hB₁ hB hcop lo u hlo hu hu1 hgap
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      AnalyticNumberTheory.Arithmetic.quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad
        (hpc.of_dvd_right hqN) hv⟩

/-- For x>0, restoring the additional square weight can only decrease the even
ambient separation budget. The restored weight is nonnegative. This verifies that
every previously certified gap remains sufficient for the quadratic refinement. -/
theorem reciprocalGapQuadraticSquareSeparation_le_even {x : ℝ} (hx : 0 < x) (q N : ℕ)
    (B₀ B₁ : Finset ℕ) :
    reciprocalGapQuadraticSquareSeparation q N x B₀ B₁ ≤
      reciprocalGapEvenAmbientRationalSeparation q N x B₀ B₁ := by
  have hs := reciprocalGapAdditionalSquareWeight_nonneg (by norm_num only : (0 : ℝ) ≤ 7 / 10) hx q N
  unfold reciprocalGapQuadraticSquareSeparation
  linarith only [hs]

/-- Any certified real lower bound R on the additional square weight may replace
the exact weight in a sufficient quadratic witness budget. Multiply the lower bound
by two and reverse it on subtraction. Together with the selected-square certificate
this avoids expanding the full square sum in a numerical separation certificate. -/
theorem reciprocalGapQuadraticSquareSeparation_le_of_square_lower (q N : ℕ) (x R : ℝ)
    (B₀ B₁ : Finset ℕ) (hR : R ≤ reciprocalGapAdditionalSquareWeight (7 / 10) q N x) :
    reciprocalGapQuadraticSquareSeparation q N x B₀ B₁ ≤
      reciprocalGapEvenAmbientRationalSeparation q N x B₀ B₁ - 2 * R := by
  unfold reciprocalGapQuadraticSquareSeparation
  linarith only [hR]

end PseudoPrime.LLS.PaperStatements
