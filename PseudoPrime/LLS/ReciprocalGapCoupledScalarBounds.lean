/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.ReciprocalGapCoupledBudgets

/-! # Character-sum bounds with coupled variable-gap conductor terms -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Scalar character-sum budget with the pole and left conductor terms coupled.
Parameters h,r,c,kappa and Euler/Gamma endpoints are independent inputs; K0,K1
are positive-prefix lower scalars. The formula retains all inverse-gap residuals.
Analytic theorems supply the real-axis, GRH and comparison hypotheses. -/
noncomputable def reciprocalGapCoupledScalarSeparation (h r c κ : ℝ) (q : ℕ)
    (x M₀ G₀ M₁ G₁ M₂ G₂ K₀ K₁ : ℝ) : ℝ :=
  (1 / c) * (Real.log q / 2 + G₀ + M₀ - K₀) +
    (reciprocalGapCoupledPoleLeftBudget h r κ q x M₁ G₁ K₁ M₂ G₂ +
      reciprocalGapSignedGammaBudget h x)

/-- For primitive nonprincipal GRH data at q>=2,x>=1 and positive h,r, assume
the existing zero-comparison condition and r<=kappa*h. Any two finite positive-prefix
lower scalars yield the coupled upper bound on the real character sum. Combine the
previous generic comparison with the signed pole-left conductor estimate.
The Euler/Gamma inputs are not replaced by fixed numerical endpoints. -/
theorem reciprocalGapCharacterSum_re_le_coupled_scalar {h r c κ : ℝ} (hh : 0 < h) (hr : 0 < r)
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hc : (1 / 2 : ℝ) < c) (hbound : c ^ 2 ≤ 1 / 4 + h / 2)
    (hκ : r ≤ κ * h) {x : ℝ} (hx : 1 ≤ x) (B₀ B₁ : Finset ℕ) (M₀ G₀ M₁ G₁ M₂ G₂ K₀ K₁ : ℝ)
    (hM₀ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c)) ≤ M₀)
    (hG₀ : (logDeriv χ.gammaFactor (((1 / 2 : ℝ) + c) : ℂ)).re ≤ G₀)
    (hM₁ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) ≤ M₁)
    (hG₁ : (logDeriv χ⁻¹.gammaFactor ((1 + r : ℝ) : ℂ)).re ≤ G₁)
    (hM₂ : (∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + h)) ≤ M₂)
    (hG₂ : G₂ ≤ (logDeriv χ⁻¹.gammaFactor ((1 + h : ℝ) : ℂ)).re)
    (hK₀ : K₀ ≤ ∑ n ∈ B₀, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 / 2 + c))
    (hK₁ : K₁ ≤ ∑ n ∈ B₁, (1 + (χ n).re) * ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (1 + r)) :
    (reciprocalGapCharacterSum h χ x).re ≤
      reciprocalGapCoupledScalarSeparation h r c κ q x M₀ G₀ M₁ G₁ M₂ G₂ K₀ K₁ := by
  have hU :=
    reciprocalGapCharacterSum_re_le_scalar_prefix hh hr hq hGRH hp hne hinv hc hbound hx B₀ B₁ M₀ G₀
      M₁ G₁ M₂ G₂ K₀ K₁ hM₀ hG₀ hM₁ hG₁ hM₂ hG₂ hK₀ hK₁
  have hB :=
    reciprocalGap_pole_add_left_le_coupled hh hx hκ (le_trans (by norm_num only : 1 ≤ 2) hq) M₁ G₁
      K₁ M₂ G₂
  unfold reciprocalGapCoupledScalarSeparation
  linarith only [hU, hB]

end PseudoPrime.LLS.PaperStatements
