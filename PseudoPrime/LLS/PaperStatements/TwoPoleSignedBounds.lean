/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaNonOneComparison
public import PseudoPrime.LLS.TwoPoleNegativeLogBounds
public import PseudoPrime.LLS.PaperStatements.GammaSignedConductorRemainder

/-! # Two-pole arithmetic bounds retaining signed archimedean and conductor terms -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under primitive nonprincipal GRH with conductor between three and an ambient
level at least 20000 and scale at least two, the two-pole Gamma arithmetic sum has
an upper real bound retaining Euler prefixes. The signed archimedean contribution
is nonpositive and the left allowance is conductor free. No 64/9 norm cost is added. -/
theorem gamma_primitive_sum_re_le_twoPole_signed {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (A B : Finset ℕ) :
    (∑' n : ℕ, gammaMellinKernel.summand χ x n).re ≤
      Real.log m / 2 + 419 / 50 -
          (∑ n ∈ A, AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (5 / 4) n) -
          (3 / 4 : ℝ) *
            (∑ n ∈ B,
              Real.log n *
                AnalyticNumberTheory.DirichletLFunction.realPairedEulerTerm χ (11 / 4) n) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hz :=
    norm_gamma_oscillatingZeroSum_le_twoPole (by linarith only [hm] : 2 ≤ m) hGRH hp hne hinv
      (by linarith only [hx] : 0 < x) A B
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  have hn := Complex.re_le_norm (-(∑' ρ : ℂ, gammaMellinKernel.oscillatingZeroTerm χ x ρ))
  simp only [Complex.neg_re, norm_neg] at hn
  simp only [Complex.add_re] at hr
  linarith only [hz, hr, hn]

end PseudoPrime.LLS.PaperStatements
