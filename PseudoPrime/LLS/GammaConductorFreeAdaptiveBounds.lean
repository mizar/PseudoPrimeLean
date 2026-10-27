/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaAdaptiveCharacterBounds
public import PseudoPrime.LLS.GammaSignedConductorRemainder
public import PseudoPrime.LLS.GammaVariablePrefixCharacterBounds

/-! # Adaptive character bounds with conductor-free completed left cost -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal conductor 3 ≤ m ≤ q, ambient q ≥ 20000,
GRH and scale x ≥ 2, the real Gamma sum is bounded by M log m + 211/10,
the ambient pole allowance and 43 x^(-9/16). Combine the adaptive zero sum
with the signed completed remainder. No positive archimedean or left
log-conductor cost is added. This is usable for character witness comparisons. -/
theorem gamma_primitive_sum_re_le_conductor_free_adaptive {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log m + 211 / 10 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hz :=
    norm_gamma_oscillatingZeroSum_lt_adaptive (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm) hGRH hp
      hne hinv (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hz.le, hr, hn]

/-- For any nonprincipal character of level q ≥ 20000 under GRH and x ≥ 2,
the primitive Gamma sum satisfies the conductor-free adaptive bound.
Primitivization supplies conductor at least three and a nonprincipal inverse.
The actual conductor remains in the leading term, with no separate size gate. -/
theorem gamma_primitiveCharacter_sum_re_le_conductor_free_adaptive {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 211 / 10 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gamma_primitive_sum_re_le_conductor_free_adaptive hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hx

/-- For nonprincipal level q ≥ 20000 under GRH and x ≥ 2, any certified
finite zero-error prefix below C gives the primitive arithmetic upper bound
M log(conductor)+C plus the ambient pole and conductor-free left costs.
Pass to the primitive character and combine its actual zero sum with the signed
remainder. Prefix length and allowance remain parameters for later improvements. -/
theorem gamma_primitiveCharacter_sum_re_le_conductor_free_prefix {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x)
    (prefixLen : ℕ) {C : ℝ} (hC : Analysis.gammaResolventPrefixErrorSum prefixLen < C) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re ≤
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + C +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  have hp := DirichletCharacter.primitiveCharacter_isPrimitive χ
  have hz :=
    norm_gamma_oscillatingZeroSum_lt_variable_prefix (le_trans (by norm_num only : (2 : ℕ) ≤ 3) hm)
      hGRH hp hnp (inv_ne_one.mpr hnp) (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
      prefixLen hC
  have hr :=
    re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hnp (inv_ne_one.mpr hnp) hGRH hx
  have hn :=
    Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ.primitiveCharacter x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hz.le, hr, hn]

end PseudoPrime.LLS.PaperStatements
