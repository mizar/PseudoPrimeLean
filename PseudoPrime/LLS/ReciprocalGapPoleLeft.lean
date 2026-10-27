/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapUniformRealAxis

/-! # Exact joint real-axis values for the first residue and adjustable left contour -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive gap and scale and nonprincipal character, the complex first-pole residue
is -logDeriv(completed L)(0)/(h*sqrt(x)). Evaluate the regularized kernel and inverse
square-root power before taking any norms. This retains its sign for joint contour bounds. -/
theorem reciprocalGap_poleResidue_eq_endpoint {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hne : χ ≠ 1) {x : ℝ} (hx : 0 < x) :
    MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
        (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) =
      ((1 / (h * Real.sqrt x) : ℝ) : ℂ) * (-logDeriv χ.completedLFunction 0) := by
  simp only [MellinKernel.weightedResidue, ite_true]
  rw [AnalyticNumberTheory.DirichletLFunction.logDeriv_shifted_completed hne]
  have he : (-1 / 2 : ℂ) + 1 / 2 = 0 := by ring
  rw [he]
  dsimp only [reciprocalGapMellinKernel]
  simp only [neg_div]
  change
    -logDeriv χ.completedLFunction 0 *
        (1 / ((-(1 / 2) : ℂ) + ((1 / 2 + h : ℝ) : ℂ)) * (x : ℂ) ^ (-(1 / 2) : ℂ)) =
      _
  have hs : (-(1 / 2) : ℂ) + ((1 / 2 + h : ℝ) : ℂ) = (h : ℂ) := by
    push_cast; ring
  have hp : (x : ℂ) ^ (-(1 / 2) : ℂ) = ((1 / Real.sqrt x : ℝ) : ℂ) := by
    have hr : x ^ (-(1 / 2) : ℝ) = 1 / Real.sqrt x := by
      rw [Real.rpow_neg hx.le, ← Real.sqrt_eq_rpow, one_div]
    rw [← hr, Complex.ofReal_cpow hx.le]
    congr 1
    push_cast
    ring
  rw [hs, hp]
  push_cast
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal data with nonprincipal inverse and positive gap and scale,
the first-pole residue equals (log(q)+logDeriv(completed inverse L)(1))/(h*sqrt(x)).
Apply the endpoint functional equation and right nonvanishing. No GRH is required. -/
theorem reciprocalGap_poleResidue_eq_realAxis {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 0 < x) :
    MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
        (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) =
      ((1 / (h * Real.sqrt x) : ℝ) : ℂ) * (Complex.log q + logDeriv χ⁻¹.completedLFunction 1) := by
  rw [reciprocalGap_poleResidue_eq_endpoint hh hne hx]
  have he :=
    completedLFunction_logDeriv_functionalEquation_at hp hne (s := 1)
      (completedLFunction_ne_zero_of_one_le_re hinv (by norm_num only [Complex.one_re]))
  rw [sub_self] at he
  rw [he]

/-- For primitive nonprincipal data with nonprincipal inverse, h>0 and x>=1, the first
residue plus left integral is the exact signed combination of the inverse completed
derivative at 1 and 1+h. The conductor is multiplied by 1-x^(-h).
Combine the two exact formulas and real-power identities without taking separate norms. -/
theorem reciprocalGap_pole_add_left_eq_realAxis {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
          (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) +
        reciprocalGapLeftIntegral h hh χ x =
      ((1 / (h * Real.sqrt x) : ℝ) : ℂ) *
        ((1 - ((x ^ (-h) : ℝ) : ℂ)) * Complex.log q + logDeriv χ⁻¹.completedLFunction 1 -
          ((x ^ (-h) : ℝ) : ℂ) * logDeriv χ⁻¹.completedLFunction ((1 + h : ℝ) : ℂ)) := by
  have hx0 := zero_lt_one.trans_le hx
  have hf : -x ^ (-1 / 2 - h) / h = -(1 / (h * Real.sqrt x)) * x ^ (-h) := by
    have he : (-1 / 2 - h : ℝ) = -(1 / 2) + (-h) := by ring
    rw [he, Real.rpow_add hx0, Real.rpow_neg hx0.le (1 / 2), ← Real.sqrt_eq_rpow]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [reciprocalGap_poleResidue_eq_realAxis hh hp hne hinv hx0,
    reciprocalGap_leftIntegral_eq_realAxis hh hp hne hinv hx, hf]
  simp only [Complex.ofReal_mul, Complex.ofReal_neg]
  ring

/-- The real joint value of the first-pole residue and left contour. It equals
((1-x^(-h))*log(q)+Re D(1)-x^(-h)*Re D(1+h))/(h*sqrt(x)), with D the inverse
character's completed logarithmic derivative. Operations are totalized; later lemmas
impose primitivity, nontriviality, positive gap and scale at least one. -/
noncomputable def reciprocalGapPoleLeftValue {q : ℕ} [NeZero q] (h : ℝ) (χ : DirichletCharacter ℂ q)
    (x : ℝ) : ℝ :=
  (1 / (h * Real.sqrt x)) *
    ((1 - x ^ (-h)) * Real.log q + (logDeriv χ⁻¹.completedLFunction 1).re -
      x ^ (-h) * (logDeriv χ⁻¹.completedLFunction ((1 + h : ℝ) : ℂ)).re)

/-- For primitive nonprincipal data with nonprincipal inverse, positive gap and x>=1,
the sum of the residue and left integral has real part equal to the joint real-axis value.
Take real parts of the exact complex identity. This exposes conductor cancellation. -/
theorem reciprocalGap_pole_add_left_re_eq_realAxis {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    (MellinKernel.weightedResidue (reciprocalGapMellinKernel h hh)
            (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) +
          reciprocalGapLeftIntegral h hh χ x).re =
      reciprocalGapPoleLeftValue h χ x := by
  rw [reciprocalGap_pole_add_left_eq_realAxis hh hp hne hinv hx, ← Complex.natCast_log]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re, Complex.sub_re,
    Complex.one_re, zero_mul, mul_zero, sub_zero]
  rfl

/-- For primitive nonprincipal data with nonprincipal inverse, h>0 and x>=1, the completed
remainder is at most the exact joint pole-and-left value plus the signed Gamma budget.
Combine the contour decomposition with exact real parts. Unlike a separate endpoint
norm estimate, this step requires neither GRH nor modulus at least eight. -/
theorem reciprocalGap_remainder_re_le_pole_left_value {h : ℝ} (hh : 0 < h) {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ}
    (hx : 1 ≤ x) :
    (reciprocalGapCompletedRemainder h hh χ x).re ≤
      reciprocalGapPoleLeftValue h χ x + reciprocalGapSignedGammaBudget h x := by
  have hΓ := reciprocalGap_remainder_gamma_re_le_signed_budget hh hx χ
  have hP := reciprocalGap_pole_add_left_re_eq_realAxis hh hp hne hinv hx
  simp only [Complex.sub_re] at hΓ
  simp only [Complex.add_re] at hP
  linarith only [hΓ, hP]

/-- For primitive nonprincipal GRH data at modulus at least two, positive gap, admissible
zero-test coordinate and x>=1, separation with the exact joint pole-and-left value
produces a non-one prime witness. Use the signed remainder bound in the existing exact
zero comparison. Concrete uniform cutoffs still require quantitative endpoint estimates. -/
theorem exists_prime_not_one_of_reciprocalGap_pole_left_separation {h c : ℝ} (hh : 0 < h) {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2) {x : ℝ}
    (hx : 1 ≤ x) (B : Finset ℕ)
    (hgap :
      (1 / c) *
            (Real.log q / 2 + (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re +
                (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) -
              ∑ n ∈ B, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) +
          (reciprocalGapPoleLeftValue h χ x + reciprocalGapSignedGammaBudget h x) <
        (reciprocalGapCharacterSum h (1 : DirichletCharacter ℂ 1) x).re) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ χ p ≠ 1 := by
  apply exists_prime_not_one_of_reciprocalGap_separation hh hq hGRH hp hne hinv hc hbound hx B
  have hR := reciprocalGap_remainder_re_le_pole_left_value hh hp hne hinv hx
  exact (add_le_add (le_refl _) hR).trans_lt hgap

end PseudoPrime.LLS.PaperStatements
