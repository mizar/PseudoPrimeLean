/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapRealAxisBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ShiftedPoissonEulerBounds

/-! # Character-independent Euler and Gamma bounds for the reflected left contour -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- The real even-character Gamma logarithmic derivative at positive real input r,
written as (-log(pi)+Re digamma(r/2))/2. The expression is totalized for all real r.
For positive r it is a lower bound valid for both character parities. -/
noncomputable def reciprocalGapEvenGammaLower (r : ℝ) : ℝ :=
  (-Real.log Real.pi + (Complex.digamma ((r / 2 : ℝ) : ℂ)).re) / 2

/-- For any character and positive real r, the even Gamma value bounds the Gamma
logarithmic derivative's real part below. Use a fixed nonnegative parity shift and
real digamma monotonicity. This supplies a character-independent left-contour input. -/
theorem reciprocalGapEvenGammaLower_le {r : ℝ} (hr : 0 < r) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    reciprocalGapEvenGammaLower r ≤ (logDeriv χ.gammaFactor (r : ℂ)).re := by
  obtain ⟨κ, hk, _, he⟩ := gammaFactor_logDeriv_eq_affine_digamma χ
  have hm :=
    AnalyticNumberTheory.Gamma.re_digamma_mono_of_pos (show 0 < r / 2 by linarith only [hr])
      (le_add_of_nonneg_right hk)
  have ha : (r : ℂ) / 2 + (κ : ℂ) = ((r / 2 + κ : ℝ) : ℂ) := by
    push_cast; rfl
  rw [he (by simpa only [Complex.ofReal_re] using hr), ha, ← Complex.ofReal_log Real.pi_pos.le]
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  unfold reciprocalGapEvenGammaLower
  linarith only [hm]

/-- The explicit signed left budget using the uniform Euler-ratio upper bound at 1+h
and the even Gamma lower bound. Inputs are h,q,x with totalized real operations.
Later lemmas require positive h and x and a nonprincipal inverse character.
This removes character-dependent analytic values from the adjustable left budget. -/
noncomputable def reciprocalGapUniformRealAxisBudget (h : ℝ) (q : ℕ) (x : ℝ) : ℝ :=
  reciprocalGapRealAxisBudget h q x ((h⁻¹ ^ 2 + (h + 1)⁻¹) / (1 + (2 : ℝ) ^ (-h) / h))
    (reciprocalGapEvenGammaLower (1 + h))

/-- For positive h,x, nonzero modulus and nonprincipal inverse character, the exact
left real-axis value is at most the character-independent explicit budget.
Apply the proved Euler-ratio cap and uniform even Gamma lower bound to the scalar
budget interface. No GRH or primitivity is needed for this comparison. -/
theorem reciprocalGapRealAxisLeftValue_le_uniform_budget {h x : ℝ} (hh : 0 < h) (hx : 0 < x) {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hinv : χ⁻¹ ≠ 1) :
    reciprocalGapRealAxisLeftValue h χ x ≤ reciprocalGapUniformRealAxisBudget h q x := by
  exact
    reciprocalGapRealAxisLeftValue_le_budget hh hx hinv
      (AnalyticNumberTheory.Arithmetic.tsum_vonMangoldt_le_euler_ratio hh)
      (reciprocalGapEvenGammaLower_le (by linarith only [hh]) χ⁻¹)

/-- For primitive nonprincipal GRH data at level at least eight, positive gap,
admissible zero comparison and x>=1, separation with the uniform real-axis budget
produces a non-one prime witness. Bound the exact left value and reuse the signed
real-axis criterion. The zero-prefix term still retains its exact character values. -/
theorem exists_prime_not_one_of_reciprocalGap_uniform_realAxis_separation {h c : ℝ} (hh : 0 < h)
    {q : ℕ} [NeZero q] (hq : 8 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B : Finset ℕ)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
              ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (((7 / 6 : ℝ) * Real.log q + 4) / (h * Real.sqrt x) +
            reciprocalGapUniformRealAxisBudget h q x +
            reciprocalGapSignedGammaBudget h x) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply
    exists_prime_not_one_of_reciprocalGap_realAxis_separation hh hq hGRH hp hne hinv hc hbound hx B
  have hV := reciprocalGapRealAxisLeftValue_le_uniform_budget hh (zero_lt_one.trans_le hx) hinv
  linarith only [hV, hgap]

/-- The real odd-character Gamma logarithmic derivative at positive real input r,
written as (-log(pi)+Re digamma((r+1)/2))/2. The expression is totalized.
For positive r this is an upper bound valid for both character parities. -/
noncomputable def reciprocalGapOddGammaUpper (r : ℝ) : ℝ :=
  (-Real.log Real.pi + (Complex.digamma (((r + 1) / 2 : ℝ) : ℂ)).re) / 2

/-- For every character and positive real input r, the odd Gamma value bounds
the Gamma logarithmic derivative's real part above. Bound the fixed parity shift
by one half and apply real digamma monotonicity. This supplies a uniform pole input. -/
theorem reciprocalGapGamma_re_le_odd {r : ℝ} (hr : 0 < r) {q : ℕ} (χ : DirichletCharacter ℂ q) :
    (logDeriv χ.gammaFactor (r : ℂ)).re ≤ reciprocalGapOddGammaUpper r := by
  obtain ⟨κ, hk, hku, he⟩ := gammaFactor_logDeriv_eq_affine_digamma χ
  have hm :=
    AnalyticNumberTheory.Gamma.re_digamma_mono_of_pos (show 0 < r / 2 + κ by linarith only [hr, hk])
      (show r / 2 + κ ≤ (r + 1) / 2 by linarith only [hku])
  have ha : (r : ℂ) / 2 + (κ : ℂ) = ((r / 2 + κ : ℝ) : ℂ) := by
    push_cast; rfl
  rw [he (by simpa only [Complex.ofReal_re] using hr), ha, ← Complex.ofReal_log Real.pi_pos.le]
  simp only [Complex.div_ofNat_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
  unfold reciprocalGapOddGammaUpper
  linarith only [hm]

end PseudoPrime.LLS.PaperStatements
