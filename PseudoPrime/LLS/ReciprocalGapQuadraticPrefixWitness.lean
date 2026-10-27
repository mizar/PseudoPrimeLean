/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.QuadraticPositivePrefixes
public import PseudoPrime.LLS.ReciprocalGapQuadraticSquareWitness

/-! # Restoring quadratic squares in both positive prefixes and the main term -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For x>0 and arbitrary real prefix inputs, adding twice J0,J1 to the lower
scalars decreases the even scalar budget by (200/77)*J0+(4/sqrt(x))*J1. Expand the
linear budget and normalize rational coefficients. This generic identity quantifies
positive-prefix improvements independently of any character or arithmetic support. -/
theorem reciprocalGapEvenScalarRationalSeparation_add_prefix (q : ℕ) {x : ℝ} (hx : 0 < x)
    (K₀ K₁ J₀ J₁ : ℝ) :
    reciprocalGapEvenScalarRationalSeparation q x (K₀ + 2 * J₀) (K₁ + 2 * J₁) =
      reciprocalGapEvenScalarRationalSeparation q x K₀ K₁ - (200 / 77) * J₀ -
        (4 / Real.sqrt x) * J₁ := by
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.mpr hx).ne'
  unfold reciprocalGapEvenScalarRationalSeparation reciprocalGapScalarPoleBudget
  field_simp [hs]
  ring

/-- Fixed even quadratic separation budget with restored squares in both
positive-prefix inputs and in the principal lower sum. Inputs are q,N,x and two finite
prefix supports. Divisibility, primitive quadratic data and finite certificates enter
the witness theorem; all defining real operations are totalized. -/
noncomputable def reciprocalGapQuadraticPrefixSeparation (q N : ℕ) (x : ℝ) (B₀ B₁ : Finset ℕ) : ℝ :=
  reciprocalGapEvenScalarRationalSeparation q x
        (AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix q N B₀
            (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹) +
          2 *
            AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix q N B₀
              (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹))
        (AnalyticNumberTheory.Arithmetic.ambientPositiveMangoldtPrefix q N B₁
            (fun n ↦ ((n : ℝ) ^ (6 / 5 : ℝ))⁻¹) +
          2 *
            AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix q N B₁
              (fun n ↦ ((n : ℝ) ^ (6 / 5 : ℝ))⁻¹)) +
      reciprocalGapAdditionalNonunitWeight (7 / 10) q N x -
    2 * reciprocalGapAdditionalSquareWeight (7 / 10) q N x

/-- For primitive even nonprincipal quadratic GRH data with q dividing N and x>=1,
restore excluded square contributions in the main term and both positive prefixes.
The strengthened finite separation yields an N-coprime non-one prime below x.
Use the quadratic prefix comparison and the existing restored main-term lower bound. -/
theorem exists_prime_coprime_not_one_of_reciprocalGap_quadratic_prefixes {q N : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hqN : q ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (he : χ.Even)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapQuadraticPrefixSeparation q N x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p ≠ 1 := by
  by_contra hn
  have hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → Nat.Coprime p N → χ p = 1 := by
    intro p hprime hpx hpc
    by_contra hv
    exact hn ⟨p, hprime, hpx, hpc, hv⟩
  have hK₀ :=
    AnalyticNumberTheory.Arithmetic.quadratic_ambientPositiveMangoldtPrefix_le_character hqN χ hquad
      B₀ (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹) hB₀
      (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsmall
  have hK₁ :=
    AnalyticNumberTheory.Arithmetic.quadratic_ambientPositiveMangoldtPrefix_le_character hqN χ hquad
      B₁ (fun n ↦ ((n : ℝ) ^ (6 / 5 : ℝ))⁻¹) hB₁
      (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hsmall
  simp only [← div_eq_mul_inv] at hK₀ hK₁
  have hU :=
    reciprocalGapCharacterSum_re_le_even_scalar_rational hq hGRH he hp hne hinv hx B₀ B₁ hK₀ hK₁
  have hL :=
    quadratic_selected_reciprocalGap_lower_sub_loss_le_character hqN
      (by norm_num only : (0 : ℝ) ≤ 7 / 10) (zero_lt_one.trans_le hx) χ hquad hsmall B hB hcop lo u
      hlo hu hu1
  unfold reciprocalGapQuadraticPrefixSeparation at hgap
  linarith only [hL, hU, hgap]

/-- For a primitive even nonprincipal quadratic character under GRH, assume q divides N
and two divides N. Ambient separation against the selected lower certificate yields
an odd N-coprime prime p<=x with chi(p)=-1. Coprimality excludes two and zero character
values. The exact extra-exclusion budget is retained in the separation premise. -/
theorem exists_odd_prime_neg_one_of_reciprocalGap_quadratic_prefixes {q N : ℕ} [NeZero q]
    (hq : 2 ≤ q) (hqN : q ∣ N) (hN2 : 2 ∣ N) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (he : χ.Even)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hquad : χ.IsQuadratic) {x : ℝ} (hx : 1 ≤ x)
    (B₀ B₁ B : Finset ℕ) (hB₀ : ∀ n ∈ B₀, (n : ℝ) ≤ x) (hB₁ : ∀ n ∈ B₁, (n : ℝ) ≤ x)
    (hB : B ⊆ Finset.Ioc 0 ⌊x⌋₊) (hcop : ∀ n ∈ B, Nat.Coprime n N) (lo u : ℕ → ℝ)
    (hlo : ∀ n ∈ B, lo n ≤ ArithmeticFunction.vonMangoldt n)
    (hu : ∀ n ∈ B, ((n : ℝ) / x) ^ (7 / 10 : ℝ) ≤ u n) (hu1 : ∀ n ∈ B, u n ≤ 1)
    (hgap :
      reciprocalGapQuadraticPrefixSeparation q N x B₀ B₁ <
        ∑ n ∈ B, (lo n / Real.sqrt x) * ((1 - u n) / (7 / 10 : ℝ))) :
    ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) ≤ x ∧ Nat.Coprime p N ∧ χ p = -1 := by
  have hinv : χ⁻¹ ≠ 1 := by
    rw [hquad.inv]
    exact hne
  obtain ⟨p, hprime, hpx, hpc, hv⟩ :=
    exists_prime_coprime_not_one_of_reciprocalGap_quadratic_prefixes hq hqN hGRH he hp hne hinv
      hquad hx B₀ B₁ B hB₀ hB₁ hB hcop lo u hlo hu hu1 hgap
  have hne2 : p ≠ 2 := by
    intro he
    subst p
    exact (Nat.prime_two.coprime_iff_not_dvd.mp hpc) hN2
  exact
    ⟨p, hprime, hprime.odd_of_ne_two hne2, hpx, hpc,
      AnalyticNumberTheory.Arithmetic.quadratic_character_apply_neg_one_of_coprime_ne_one χ hquad
        (hpc.of_dvd_right hqN) hv⟩

/-- For x>0, the strengthened quadratic budget equals the previous square-restored
budget minus (200/77) times the excluded square prefix at 127/100 and (4/sqrt(x))
times the excluded square prefix at 6/5. The exact principal-loss terms are unchanged.
This separates the two positive-prefix savings from the previously restored main term. -/
theorem reciprocalGapQuadraticPrefixSeparation_eq_saving (q N : ℕ) {x : ℝ} (hx : 0 < x)
    (B₀ B₁ : Finset ℕ) :
    reciprocalGapQuadraticPrefixSeparation q N x B₀ B₁ =
      reciprocalGapQuadraticSquareSeparation q N x B₀ B₁ -
        (200 / 77) *
          AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix q N B₀
            (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹) -
        (4 / Real.sqrt x) *
          AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix q N B₁
            (fun n ↦ ((n : ℝ) ^ (6 / 5 : ℝ))⁻¹) := by
  unfold reciprocalGapQuadraticPrefixSeparation reciprocalGapQuadraticSquareSeparation
    reciprocalGapEvenAmbientRationalSeparation
  rw [reciprocalGapEvenScalarRationalSeparation_add_prefix q hx]
  ring

/-- For x>0, arbitrary certified lower bounds on the two excluded square prefixes
may replace their exact sums in an upper bound for the new separation budget.
The coefficients are nonnegative. This supplies sparse finite-certificate inputs
without enumerating all square contributions in either positive prefix. -/
theorem reciprocalGapQuadraticPrefixSeparation_le_of_square_lower (q N : ℕ) {x : ℝ} (hx : 0 < x)
    (B₀ B₁ : Finset ℕ) (R₀ R₁ : ℝ)
    (hR₀ :
      R₀ ≤
        AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix q N B₀
          (fun n ↦ ((n : ℝ) ^ (127 / 100 : ℝ))⁻¹))
    (hR₁ :
      R₁ ≤
        AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix q N B₁
          (fun n ↦ ((n : ℝ) ^ (6 / 5 : ℝ))⁻¹)) :
    reciprocalGapQuadraticPrefixSeparation q N x B₀ B₁ ≤
      reciprocalGapQuadraticSquareSeparation q N x B₀ B₁ - (200 / 77) * R₀ -
        (4 / Real.sqrt x) * R₁ := by
  rw [reciprocalGapQuadraticPrefixSeparation_eq_saving q N hx]
  have h₀ := mul_le_mul_of_nonneg_left hR₀ (by norm_num only : (0 : ℝ) ≤ 200 / 77)
  have h₁ :=
    mul_le_mul_of_nonneg_left hR₁ (div_nonneg (by norm_num only : (0 : ℝ) ≤ 4) (Real.sqrt_nonneg x))
  linarith only [h₀, h₁]

/-- For x>0, restoring both positive square prefixes can only decrease the previous
quadratic main-square separation budget. Both excluded square prefixes have
nonnegative inverse-power weights. Thus all previously certified quadratic gaps
remain sufficient after the positive-prefix refinement. -/
theorem reciprocalGapQuadraticPrefixSeparation_le_square (q N : ℕ) {x : ℝ} (hx : 0 < x)
    (B₀ B₁ : Finset ℕ) :
    reciprocalGapQuadraticPrefixSeparation q N x B₀ B₁ ≤
      reciprocalGapQuadraticSquareSeparation q N x B₀ B₁ := by
  have h :=
    reciprocalGapQuadraticPrefixSeparation_le_of_square_lower q N hx B₀ B₁ 0 0
      (AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix_nonneg q N B₀ _
        (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
      (AnalyticNumberTheory.Arithmetic.additionalSquareMangoldtPrefix_nonneg q N B₁ _
        (fun n _ ↦ inv_nonneg.mpr (Real.rpow_nonneg (Nat.cast_nonneg n) _)))
  simpa only [mul_zero, sub_zero] using h

end PseudoPrime.LLS.PaperStatements
