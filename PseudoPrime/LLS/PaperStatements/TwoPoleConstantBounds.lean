/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TwoPoleSignedSharpBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.TwoPoleGammaSignedConstant

/-! # Signed Gamma caps in parameterized two-pole witness bounds -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under primitive GRH and a scalar Gamma-constant cap, retain both finite Euler savings in the
norm bound. The proof uses the triangle inequality and the two-pole zero-mass estimate; this
transfers signed Gamma bounds to oscillating zero sums. -/
theorem norm_gammaZeroSum_twoPole_bound_GRH {m : ℕ} [NeZero m] (hm : 2 ≤ m)
    {χ : DirichletCharacter ℂ m} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) {C : ℝ}
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ ≤ C) (A B : Finset ℕ) :
    ‖∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ‖ ≤
      Real.log m / 2 + C -
        (∑ n ∈ A, AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (5 / 4) n) -
        (3 / 4 : ℝ) *
          (∑ n ∈ B,
            Real.log n *
              AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (11 / 4) n) := by
  have hs := MellinKernel.summable_oscillatingZeroTerm gammaMellinKernel hm hGRH hp hne hinv hx
  have hn := norm_tsum_le_tsum_norm hs.norm
  have he (ρ : ℂ) :=
    (MellinKernel.norm_oscillatingZeroTerm gammaMellinKernel χ hx ρ).trans
      (norm_gamma_kernelZeroTerm_eq_twoPole hGRH hp hne hinv ρ)
  rw [tsum_congr he] at hn
  exact
    hn.trans
      (AnalyticNumberTheory.DirichletLFunction.gamma_zeroMass_le_twoPole_of_RH hm (hGRH m χ hp) hp
          hne hinv hC A B).2

/-- For a primitive nonprincipal character of conductor at most the ambient level, bound the
real smoothed sum using a scalar Gamma cap. Combine the zero-sum norm with the conductor-free
remainder; both finite Euler savings are retained for subsequent comparisons. -/
theorem gamma_primitive_sum_re_le_twoPole_constant {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) {C : ℝ}
    (hC : AnalyticNumberTheory.DirichletLFunction.twoPoleGammaConstant χ ≤ C) (A B : Finset ℕ) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log m / 2 + C -
          (∑ n ∈ A, AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (5 / 4) n) -
          (3 / 4 : ℝ) *
            (∑ n ∈ B,
              Real.log n *
                AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (11 / 4) n) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hz :=
    norm_gammaZeroSum_twoPole_bound_GRH (by linarith only [hm] : 2 ≤ m) hGRH hp hne hinv
      (by linarith only [hx] : 0 < x) hC A B
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hz, hr, hn]

end PseudoPrime.LLS.PaperStatements
