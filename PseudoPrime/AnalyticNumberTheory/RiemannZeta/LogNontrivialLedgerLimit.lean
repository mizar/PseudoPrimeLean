/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.WeightedExplicitBounds

/-! # Exact logarithmic zero-ledger limit

Extract the nontrivial-zero contribution before taking an absolute value.
-/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `x > 1`, the real part of the finite nontrivial-zero ledger converges
to the logarithmically weighted Mangoldt sum minus its pole terms plus the
trivial-zero series. Subtract the trivial-zero ledger from the exact contour
limit; this retains the signs needed by the integrated explicit formula. -/
theorem tendsto_logNontrivialLedger {x : ℝ} (hx : 1 < x) :
    Filter.Tendsto
      (fun m : ℕ ↦
        (∑
            ρ ∈
              (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m)
                    (unifiedTauRectangleUpper 2 m)).filter
                (fun ρ ↦ ¬ρ.re < 0),
            riemannZetaLogZeroContribution x ρ).re)
      Filter.atTop
      (nhds
        (Arithmetic.logWeightedMangoldtSum x -
            (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
                Real.log (2 * Real.pi) * Real.log x +
              x) +
          riemannZetaLogTrivialZeroSeries x)) := by
  classical
  have hxpos : 0 < x := zero_lt_one.trans hx
  have h2 : (1 : ℝ) < 2 := by norm_num only
  have hR :=
    Analysis.tendsto_residueLedger_of_normalized
      (tendsto_zetaLogContourResidueLedger_atTop hx h2 le_rfl)
  rw [← logWeightedMangoldtSum_eq_integral hxpos h2] at hR
  have hRe := (Complex.continuous_re.tendsto _).comp hR
  simp only [Complex.ofReal_re] at hRe
  have ht := tendsto_logTrivialSum_unified hx h2
  have hlim :=
    (hRe.sub_const
          (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
              Real.log (2 * Real.pi) * Real.log x +
            x)).sub
      ht
  simp only [sub_neg_eq_add] at hlim
  apply hlim.congr'
  filter_upwards with m
  let S := riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper 2 m)
  have hsplit :=
    Finset.sum_filter_add_sum_filter_not S (fun ρ : ℂ ↦ ρ.re < 0) (riemannZetaLogZeroContribution x)
  have hre0 :
    (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero -
          Complex.log (2 * Real.pi) * Complex.log x).re =
      -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
        Real.log (2 * Real.pi) * Real.log x := by
    rw [← Complex.ofReal_ofNat 2, ← Complex.ofReal_mul, ←
      Complex.ofReal_log (mul_nonneg (by norm_num only) Real.pi_pos.le), ←
      Complex.ofReal_log hxpos.le, ← Complex.ofReal_mul, Complex.sub_re, Complex.neg_re,
      Complex.ofReal_re]
  dsimp only [Function.comp_apply]
  rw [zetaLogContourResidueLedger_unifiedTau_eq h2, riemannZetaLogResidueAtZero_eq hxpos,
    riemannZetaLogResidueAtOne_eq, Complex.add_re, Complex.add_re, hre0, Complex.ofReal_re]
  change
    (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re - Real.log (2 * Real.pi) * Real.log x +
          x +
          (∑ ρ ∈ S, riemannZetaLogZeroContribution x ρ).re) -
        _ -
        _ =
      _
  rw [← hsplit, Complex.add_re]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
