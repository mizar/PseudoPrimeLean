/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.FiniteSignedPhaseTransport
public import PseudoPrime.LLS.MellinPhaseResolventBounds
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogarithmicPhaseZeroMass

/-! # Actual character bounds transported from a logarithmic-scale anchor -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- At positive scales, an anchor Gamma phase majorant and a rational
logarithmic-distance cap give the actual Mellin-kernel phase majorant for the extended
node list. Unfold the kernel and apply the proved logarithmic phase transport. -/
theorem gamma_majorant_at_log_distance {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (l : List (ℚ × ℚ))
    (δ : ℚ) (hd : |Real.log x - Real.log y| ≤ (δ : ℝ))
    (hyphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t)
    (t : ℝ) :
    -(gammaMellinKernel.function (Complex.I * t) * (x : ℂ) ^ (Complex.I * t)).re ≤
      Analysis.finiteSignedResolvent (Analysis.logarithmicPhaseExtension l δ) t := by
  change -(Complex.Gamma (Complex.I * t + 1 / 2) * (x : ℂ) ^ (Complex.I * t)).re ≤ _
  rw [add_comm (Complex.I * (t : ℂ)) (1 / 2)]
  exact Analysis.gammaHalf_phase_majorant_of_log_distance hx hy l δ hd hyphase t

/-- Under GRH and the primitive conductor hypotheses, a valid anchor
majorant transports to a nearby scale with the exact paired Euler tail retained.
Append the one admissible node and apply the existing full explicit formula. No new
spectral grid is needed at the target scale. -/
theorem gamma_primitive_sum_re_le_logarithmic_phase_prefix_tail {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x y : ℝ} (hx : 2 ≤ x) (hy : 0 < y) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (δ : ℚ) (hd : |Real.log x - Real.log y| ≤ (δ : ℝ))
    (B : Finset ℕ)
    (hyphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
            (Analysis.logarithmicPhaseExtension l δ) B -
          Analysis.pairedWeightTail
            (Analysis.finiteSignedMangoldtWeight (Analysis.logarithmicPhaseExtension l δ))
            (fun n ↦ (χ n).re) B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        Analysis.gammaNegativeConductorTerm (Real.log m) x +
        43 * x ^ (-9 / 16 : ℝ) := by
  exact
    gamma_primitive_sum_re_le_phase_prefix_tail hq hm hmq hGRH hp hne hinv hx
      (Analysis.logarithmicPhaseExtension l δ) (Analysis.logarithmicPhaseExtension_admissible hl δ)
      B (gamma_majorant_at_log_distance (by linarith only [hx]) hy l δ hd hyphase)

/-- Under the transported-phase hypotheses and original Euler nonnegativity,
the actual primitive Gamma sum obeys the extended prefix budget with certified
remainder. Infer delta>=0 and preserve nonnegative Mangoldt weights. -/
theorem gamma_primitive_sum_re_le_logarithmic_phase_prefix {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x y : ℝ} (hx : 2 ≤ x) (hy : 0 < y) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (δ : ℚ) (hd : |Real.log x - Real.log y| ≤ (δ : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u) (B : Finset ℕ)
    (hyphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ
          (Analysis.logarithmicPhaseExtension l δ) B +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hd0 : 0 ≤ δ :=
    (Rat.cast_nonneg (K := ℝ)).mp ((abs_nonneg (Real.log x - Real.log y)).trans hd)
  exact
    gamma_primitive_sum_re_le_phase_prefix hq hm hmq hGRH hp hne hinv hx
      (Analysis.logarithmicPhaseExtension l δ) (Analysis.logarithmicPhaseExtension_admissible hl δ)
      (Analysis.logarithmicPhaseExtension_mangoldt_nonneg hd0 hW) B
      (gamma_majorant_at_log_distance (by linarith only [hx]) hy l δ hd hyphase)

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under the anchor transport hypotheses, the actual primitive Gamma sum
is bounded by the original prefix budget plus delta*(log(m)+76/5) and the certified
remainder. Bound only the added zero mass, preserving the original Euler and local
data. This avoids a new finite arithmetic certificate at each nearby scale. -/
theorem gamma_primitive_sum_re_le_anchor_prefix {q m : ℕ} [NeZero m] (hq : 20000 ≤ q) (hm : 3 ≤ m)
    (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x y : ℝ} (hx : 2 ≤ x) (hy : 0 < y) (l : List (ℚ × ℚ))
    (hl : ∀ ab ∈ l, (1 / 2 : ℚ) < ab.1) (δ : ℚ) (hd : |Real.log x - Real.log y| ≤ (δ : ℝ))
    (hW : ∀ u : ℝ, 1 ≤ u → 0 ≤ Analysis.finiteSignedEulerWeight l u) (B : Finset ℕ)
    (hyphase :
      ∀ t : ℝ,
        -(Complex.Gamma ((1 / 2 : ℂ) + Complex.I * t) * (y : ℂ) ^ (Complex.I * t)).re ≤
          Analysis.finiteSignedResolvent l t) :
    (∑' k : ℕ, gammaMellinKernel.summand χ x k).re ≤
      AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget χ l B +
        (δ : ℝ) * (Real.log m + 76 / 5) +
        ((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x +
        43 * x ^ (-9 / 16 : ℝ) := by
  have hm2 : 2 ≤ m := (by norm_num only : 2 ≤ 3).trans hm
  have hd0 : 0 ≤ δ :=
    (Rat.cast_nonneg (K := ℝ)).mp ((abs_nonneg (Real.log x - Real.log y)).trans hd)
  have hpos : ∀ ab ∈ l, (0 : ℚ) < ab.1 := fun ab hab ↦
    (by norm_num only : (0 : ℚ) < 1 / 2).trans (hl ab hab)
  have hz :=
    gammaMellinKernel.neg_re_oscillatingZeroSum_le_finiteResolvent hm2 hGRH hp hne hinv
      (by linarith only [hx]) (Analysis.logarithmicPhaseExtension l δ)
      (fun ab hab ↦
        (by norm_num only : (0 : ℚ) < 1 / 2).trans
          (Analysis.logarithmicPhaseExtension_admissible hl δ ab hab))
      (gamma_majorant_at_log_distance (by linarith only [hx]) hy l δ hd hyphase)
  have hmz :=
    AnalyticNumberTheory.DirichletLFunction.logarithmicPhaseExtension_zeroMass_le hm2 (hGRH m χ hp)
      hp hne hinv l hpos hd0
  have hb :=
    AnalyticNumberTheory.DirichletLFunction.finiteSignedResolvent_zeroMass_le_prefix hm2
      (hGRH m χ hp) hp hne hinv l hl (Analysis.finiteSignedMangoldtWeight_nonneg l hW) B
  have hr := re_gamma_primitive_remainder_le_conductor_free hq hm hmq hp hne hinv hGRH hx
  simp only [Complex.add_re] at hr
  dsimp only [AnalyticNumberTheory.DirichletLFunction.finiteSignedPrefixBudget]
  linarith only [hz, hmz, hb, hr]

end PseudoPrime.LLS.PaperStatements
