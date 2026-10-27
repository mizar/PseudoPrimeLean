/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaPhaseLogInterval
public import PseudoPrime.LLS.LogarithmicPhaseCharacterBounds

/-! # Original arithmetic budgets on a continuously covered log-scale interval -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, primitive nonprincipal conductor data, admissible nodes and
nonnegative Euler weights, two rational-log endpoint majorants bound the actual
Gamma sum throughout their closed log interval. Retain the original prefix budget
and add (5*(r1-r0)^2/16)*(log(m)+76/5) and the existing contour allowance.
This gives continuous scale coverage without interior spectral certificates. -/
theorem gamma_primitive_sum_re_le_log_interval_prefix {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 2 ≤ x) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (r0 r1 : ℚ) (hlo : (r0 : ℝ) ≤ Real.log x)
    (hhi : Real.log x ≤ (r1 : ℝ)) (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u)
    (B : Finset ℕ)
    (ha :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * r0 : ℝ) : ℂ) * Complex.I)).re ≤
          Analysis.finiteSignedResolvent l t)
    (hbphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) *
                Complex.exp (((t * r1 : ℝ) : ℂ) * Complex.I)).re ≤
          Analysis.finiteSignedResolvent l t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B +
        ((5 / 16 : ℚ) * (r1 - r0) ^ 2 : ℝ) * (Real.log m + 76 / 5) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hm2 : 2 ≤ m := (by norm_num only : 2 ≤ 3).trans hm
  have hd0 : 0 ≤ (5 / 16 : ℚ) * (r1 - r0) ^ 2 := mul_nonneg (by norm_num only) (sq_nonneg (r1 - r0))
  have hpos : ∀ ab ∈ l, (0 : ℚ) < ab.1 := fun ab hab ↦
    (by norm_num only : (0 : ℚ) < 1 / 2).trans (hl ab hab)
  have hz :=
    gammaMellinKernel.neg_re_oscillatingZeroSum_le_finiteResolvent hm2 hGRH hp hne hinv
      (by linarith only [hx]) (Analysis.logarithmicPhaseExtension l ((5 / 16) * (r1 - r0) ^ 2))
      (fun ab hab ↦
        (by norm_num only : (0 : ℚ) < 1 / 2).trans
          (Analysis.logarithmicPhaseExtension_admissible hl _ ab hab))
      (fun t ↦ by
        change -(Complex.Gamma (Complex.I * t + 1 / 2) * (x : ℂ) ^ (Complex.I * t)).re ≤ _
        rw [add_comm (Complex.I * (t : ℂ)) (1 / 2)]
        exact
          Analysis.gammaHalf_phase_majorant_on_log_interval (by linarith only [hx]) l r0 r1 hlo hhi
            ha hbphase t)
  have hmz :=
    AnalyticNumberTheory.DirichletLFunction.logarithmicPhaseExtension_zeroMass_le hm2 (hGRH m χ hp)
      hp hne hinv l hpos hd0
  have hb :=
    AnalyticNumberTheory.DirichletLFunction.finiteSignedResolvent_zeroMass_le_prefix hm2
      (hGRH m χ hp) hp hne hinv l hl (Analysis.finiteSignedMangoldtWeight_nonneg l hW) B
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  simp only [Complex.add_re] at hr
  dsimp only [AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget]
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_pow, Rat.cast_sub, Rat.cast_ofNat] at hmz ⊢
  linarith only [hz, hmz, hb, hr]

end PseudoPrime.LLS.PaperStatements
