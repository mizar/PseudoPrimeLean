/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SmoothedContour
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HadamardLimit

/-!
# Logarithmic-kernel residue at zero

For positive `x`, differentiate `-(logDeriv ζ s)*x^s` at zero by the product
rule. The value is `-deriv (logDeriv ζ) 0 - log(2π)*log x`.
The second logarithmic derivative is retained as the named constant supplied by
`PseudoPrime.AnalyticNumberTheory.RiemannXi.HadamardLimit`.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/-- For `x > 0`, the logarithmic-kernel residue at zero equals minus the
named second logarithmic derivative of zeta minus `log(2π)*log x`. -/
theorem riemannZetaLogResidueAtZero_eq {x : ℝ} (hx : 0 < x) :
    riemannZetaLogResidueAtZero x =
      -RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero -
        Complex.log (2 * Real.pi) * Complex.log x := by
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hf :
    HasDerivAt (fun s : ℂ => -logDeriv riemannZeta s)
      (-RiemannXi.qMinusOneRiemannZetaSecondLogDerivAtZero) 0 :=
    RiemannXi.differentiableAt_logDeriv_riemannZeta_zero.hasDerivAt.neg
  have hg : HasDerivAt (fun s : ℂ => (x : ℂ) ^ s) (Complex.log x) 0 := by
    have h1 := (hasDerivAt_id (0 : ℂ)).const_cpow (c := (x : ℂ)) (Or.inl hxne)
    simpa only [id_eq, Complex.cpow_zero, one_mul, mul_one] using h1
  have hprod := hf.mul hg
  have heq :
    riemannZetaLogZeroRegularization x =
      (fun s : ℂ => -logDeriv riemannZeta s) * fun s : ℂ => (x : ℂ) ^ s := by
    funext s
    unfold riemannZetaLogZeroRegularization logDeriv
    rfl
  unfold riemannZetaLogResidueAtZero
  rw [heq, hprod.deriv]
  simp only [Complex.cpow_zero, mul_one, RiemannXi.logDeriv_riemannZeta_zero]
  ring

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
