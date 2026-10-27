/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaConductorFreeAdaptiveBounds
public import PseudoPrime.LLS.GammaResolventCharacterComparison
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GammaPrincipalEulerBudget

/-! # Conductor-retaining character bounds from principal Euler positivity -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Input: GRH, primitive nonprincipal conductor 3 <= m <= q, q >= 20000 and x >= 2.
Claim: the primitive Gamma arithmetic sum is below mu log m + 117/10 plus pole and left costs.
Proof: combine the actual signed resolvent bound with the conductor-free remainder.
Role: use the improved zero budget in character witness comparisons. -/
theorem gamma_primitive_sum_re_le_principal_euler {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re <
      (11783423 / 25000000 : ℝ) * Real.log m + 117 / 10 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hm2 : 2 ≤ m := le_trans (by norm_num only) hm
  have hz :=
    AnalyticNumberTheory.DirichletLFunction.gammaResolvent_zeroMass_lt_principal_uniform hm2
      (hGRH m χ hp) hGRH.riemann hp hne hinv
  have hn :=
    norm_gamma_oscillatingZeroSum_le_resolvent hm2 (hGRH m χ hp) hp hne hinv
      (lt_of_lt_of_le (by norm_num only : (0 : ℝ) < 2) hx)
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  have he := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at he
  simp only [Complex.add_re] at hr
  linarith only [hz, hn, hr, he]

/-- Input: GRH, a nonprincipal character at level q >= 20000 and x >= 2.
Claim: the primitive-character Gamma sum retains its conductor with fixed cost 117/10.
Proof: primitivize and apply the signed principal Euler arithmetic bound.
Role: supply the improved upper input to quadratic and subgroup comparisons. -/
theorem gamma_primitiveCharacter_sum_re_lt_principal_euler {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 2 ≤ x) :
    (∑' k : ℕ, gammaMellinKernel.summand χ.primitiveCharacter x k).re <
      (11783423 / 25000000 : ℝ) * Real.log χ.conductor + 117 / 10 +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gamma_primitive_sum_re_le_principal_euler hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hx

end PseudoPrime.LLS.PaperStatements
