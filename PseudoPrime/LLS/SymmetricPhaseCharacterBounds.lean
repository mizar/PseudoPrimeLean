/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.SymmetricGammaPhaseInterpolation
public import PseudoPrime.LLS.LogarithmicPhaseCharacterBounds

/-! # Actual character sums with quadratic symmetric-anchor cost -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, primitive nonprincipal conductor data, admissible anchor nodes
and nonnegative Euler weights, two symmetric phase bounds give the actual Gamma
character sum below the original arithmetic prefix budget plus
(5*d^2/4)*(log(m)+76/5) and the existing contour remainder. The same prefix and
local arithmetic data are retained; the extra zero-mass cost is quadratic in d. -/
theorem gamma_primitive_sum_re_le_symmetric_anchor_prefix {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (d : ℚ)
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u) (B : Finset ℕ)
    (hminus :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (Real.log x - d) : ℝ) : ℂ))).re ≤
          Analysis.finiteSignedResolvent l t)
    (hplus :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (Complex.I * ((t * (Real.log x + d) : ℝ) : ℂ))).re ≤
          Analysis.finiteSignedResolvent l t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B +
        ((5 / 4 : ℚ) * d ^ 2 : ℝ) * (Real.log m + 76 / 5) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hm2 : 2 ≤ m := (by norm_num only : 2 ≤ 3).trans hm
  have hd0 : 0 ≤ (5 / 4 : ℚ) * d ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg d)
  have hpos : ∀ ab ∈ l, (0 : ℚ) < ab.1 := fun ab hab ↦
    (by norm_num only : (0 : ℚ) < 1 / 2).trans (hl ab hab)
  have hz :=
    gammaMellinKernel.neg_re_oscillatingZeroSum_le_finiteResolvent hm2 hGRH hp hne hinv
      (by linarith only [hx]) (Analysis.logarithmicPhaseExtension l ((5 / 4) * d ^ 2))
      (fun ab hab ↦
        (by norm_num only : (0 : ℚ) < 1 / 2).trans
          (Analysis.logarithmicPhaseExtension_admissible hl _ ab hab))
      (fun t ↦ by
        change -(Complex.Gamma (Complex.I * t + 1 / 2) * (x : ℂ) ^ (Complex.I * t)).re ≤ _
        rw [add_comm (Complex.I * (t : ℂ)) (1 / 2)]
        exact
          Analysis.gammaHalf_phase_majorant_of_symmetric_anchors (by linarith only [hx]) l d hminus
            hplus t)
  have hmz :=
    AnalyticNumberTheory.DirichletLFunction.logarithmicPhaseExtension_zeroMass_le hm2 (hGRH m χ hp)
      hp hne hinv l hpos hd0
  have hb :=
    AnalyticNumberTheory.DirichletLFunction.finiteSignedResolvent_zeroMass_le_prefix hm2
      (hGRH m χ hp) hp hne hinv l hl (Analysis.finiteSignedMangoldtWeight_nonneg l hW) B
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  simp only [Complex.add_re] at hr
  dsimp only [AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget]
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hmz ⊢
  linarith only [hz, hmz, hb, hr]

end PseudoPrime.LLS.PaperStatements
