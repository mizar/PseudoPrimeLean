/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.FiniteZeroSums
public import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMass
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroClassification
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ReciprocalTrivialZeroSeries
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LogResidueAtZeroClosedForm
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ContourKernelConjugation

/-! General RH bounds for smoothed zeta zero sums and contour integrals. -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- Under RH, combine the Mellin-pole residues at zero and one with the
finite zero-contribution bound to obtain the logarithmic residue-ledger lower bound. -/
theorem logResidueLedger_unified_re_lower_RH (hRH : RiemannHypothesis) {x τ : ℝ} (hx : 1 < x)
    (hτ : 1 < τ) (m : ℕ) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 -
        2 * RiemannXi.riemannZeroMass * (Real.sqrt x + 1) ≤
      (riemannZetaLogContourResidueLedger x (unifiedRectangleLower m)
          (unifiedTauRectangleUpper τ m)).re := by
  have hxpos : 0 < x := by linarith only [hx]
  rw [zetaLogContourResidueLedger_unifiedTau_eq hτ, Complex.add_re, Complex.add_re,
    riemannZetaLogResidueAtZero_eq hxpos, riemannZetaLogResidueAtOne_eq]
  have hre0 :
    (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero -
          Complex.log (2 * Real.pi) * Complex.log x).re =
      -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero.re -
        Real.log (2 * Real.pi) * Real.log x := by
    rw [Complex.sub_re, Complex.neg_re]
    congr 1
    rw [show (2 : ℂ) * (Real.pi : ℂ) = ((2 * Real.pi : ℝ) : ℂ) from by
        push_cast
        ring,
      ← Complex.ofReal_log (mul_nonneg (by norm_num only) Real.pi_pos.le), ←
      Complex.ofReal_log hxpos.le, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hre1 : (x : ℂ).re = x := Complex.ofReal_re x
  rw [hre0, hre1]
  unfold riemannZetaLogContourZeroLedger
  have hzero_ledger :=
    logZeroSum_re_lower_RH hRH hx
      (riemannZetaZerosInAnyRectangle (unifiedRectangleLower m) (unifiedTauRectangleUpper τ m))
      (fun ρ hρ => (mem_riemannZetaZerosInAnyRectangle_iff.mp hρ).2)
  have hq := RiemannXi.re_qMinusOne_add_logTrivialZeroSeries_le hRH hx
  linarith only [hzero_ledger, hq]

/-- **The `τ = 2` case of the vertical-integral lower bound (logarithmic kernel), under RH.**
Combines the finite ledger bound with
`RiemannZeta.tendsto_zetaLogContourResidueLedger_atTop` via
`ge_of_tendsto`, after cancelling the leading `I` factor. -/
theorem logKernel_integral_two_re_lower_RH (hRH : RiemannHypothesis) {x : ℝ} (hx : 1 < x) :
    x - Real.log (2 * Real.pi) * Real.log x - 1 -
        2 * RiemannXi.riemannZeroMass * (Real.sqrt x + 1) ≤
      ((2 * Real.pi : ℝ)⁻¹ •
          ∫ y : ℝ, riemannZetaLogContourKernel x ((2 : ℂ) + (y : ℂ) * Complex.I)).re := by
  apply General.re_inv_two_pi_smul_ge_of_tendsto_residueLedger
  · simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat, smul_eq_mul] using
      tendsto_zetaLogContourResidueLedger_atTop hx (by norm_num only) le_rfl
  · intro m
    exact logResidueLedger_unified_re_lower_RH hRH hx (by norm_num only) m

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
