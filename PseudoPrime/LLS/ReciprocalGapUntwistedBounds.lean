/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapNumericalBounds
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.CharacterPrimeTriviality

/-! # Character-free Euler-prefix criteria for adjustable reciprocal witnesses -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data at level at least eight and 1/2<c<=7, a strict
separation using the untwisted finite Euler prefix and Gamma cap 8/5 yields a non-one
prime witness up to the scale. Assume the prefix indices are at most that scale.
Under witness nonexistence every weighted character value equals one; apply the generic
prime-triviality identity and the numerical contour criterion. The premise is character-free. -/
theorem exists_prime_not_one_of_reciprocalGap_untwisted_separation {h c : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hcu : c ≤ 7)
    (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ} (hx : 1 ≤ x) (B : Finset ℕ) (hB : ∀ n ∈ B, (n : ℝ) ≤ x)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + 8 / 5 +
                (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
              2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
            reciprocalGapNumericLeftBudget h hh q x +
            176) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  classical
  by_contra hn
  have hs : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ x → χ p = 1 := by
    intro p hp hpx
    by_contra hχ
    exact hn ⟨p, hp, hpx, hχ⟩
  have hpref :
    (∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) =
      2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c) := by
    have he :=
      AnalyticNumberTheory.Arithmetic.character_positive_mangoldt_prefix_eq_twice χ B
        (fun n ↦ ((n : ℝ) ^ (1 / 2 + c))⁻¹) hB hs
    simpa only [div_eq_mul_inv] using he
  have hg :=
    AnalyticNumberTheory.DirichletLFunction.abs_re_logDeriv_gammaFactor_le_eight_fifths χ (σ :=
      1 / 2 + c) (by linarith only [hc]) (by linarith only [hcu])
  have hγ := (abs_le.mp hg).2
  rw [Complex.ofReal_add] at hγ
  have hc0 : 0 < c := lt_trans (by norm_num only : (0 : ℝ) < 1 / 2) hc
  have hW :=
    exists_prime_not_one_of_reciprocalGap_numeric_separation hh hq hGRH hp hne hinv hc hbound hx B
  apply hn
  apply hW
  rw [hpref]
  have hE :
    (1 / c) *
        (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
            (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
          2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤
      (1 / c) *
        (Real.log q / 2 + 8 / 5 +
            (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
          2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hγ]) (div_nonneg zero_le_one hc0.le)
  exact (add_le_add hE (le_refl _)).trans_lt hgap

/-- The untwisted reciprocal-gap criterion remains valid with any certified real upper cap M
for the untwisted Mangoldt Dirichlet series. The finite prefix retains its subtraction.
Monotonicity in M reduces the claim to the exact Euler-series criterion.
This permits elementary bounds or sharper certified Euler evaluations without changing
character hypotheses or generating input-range certificates. -/
theorem exists_prime_not_one_of_reciprocalGap_euler_cap_separation {h c : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hcu : c ≤ 7)
    (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ} (hx : 1 ≤ x) (B : Finset ℕ) (hB : ∀ n ∈ B, (n : ℝ) ≤ x)
    (M : ℝ) (hM : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤ M)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + 8 / 5 + M -
              2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
            reciprocalGapNumericLeftBudget h hh q x +
            176) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply
    exists_prime_not_one_of_reciprocalGap_untwisted_separation hh hq hGRH hp hne hinv hc hcu hbound
      hx B hB
  have hc0 : 0 < c := lt_trans (by norm_num only : (0 : ℝ) < 1 / 2) hc
  have hE :
    (1 / c) *
        (Real.log q / 2 + 8 / 5 +
            (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
          2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤
      (1 / c) *
        (Real.log q / 2 + 8 / 5 + M -
          2 * ∑ n ∈ B, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) :=
    mul_le_mul_of_nonneg_left (by linarith only [hM]) (div_nonneg zero_le_one hc0.le)
  exact (add_le_add hE (le_refl _)).trans_lt hgap

end PseudoPrime.LLS.PaperStatements
