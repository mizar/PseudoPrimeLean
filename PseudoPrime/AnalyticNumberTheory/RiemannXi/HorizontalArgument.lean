/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.UpperRectangle
public import PseudoPrime.Analysis.ContinuousLogDerivative

/-! # Xi arguments on a good horizontal line -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- At a good height, any continuous polar argument of xi on a closed
horizontal interval has derivative equal to the imaginary part of xi's
logarithmic derivative. The good-height condition supplies nonvanishing. -/
theorem xi_horizontal_arg_deriv {t a b : ℝ}
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hpolar :
      ∀ x : ℝ,
        x ∈ Set.Icc a b →
          riemannXi ((x : ℂ) + (t : ℂ) * Complex.I) =
            (‖riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) * Complex.exp ((φ x : ℂ) * Complex.I))
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    HasDerivWithinAt φ (logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im (Set.Icc a b) x := by
  let f : ℝ → ℂ := fun y ↦ riemannXi ((y : ℂ) + (t : ℂ) * Complex.I)
  have hne : ∀ y ∈ Set.Icc a b, f y ≠ 0 := by
    intro y hy
    exact riemannXi_good_height_ne_zero hgood y
  have hd :=
    (differentiable_riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).hasDerivAt.comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const ((t : ℂ) * Complex.I))
  have hf :
    HasDerivWithinAt f (deriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)) (Set.Icc a b) x := by
    have hh := hd.comp_ofReal
    simpa only [Function.comp_def, id_eq, mul_one, f] using hh.hasDerivWithinAt
  have h := Analysis.hasDerivWithinAt_continuous_arg hx (hcont x hx) hf hne hpolar
  simpa only [logDeriv_apply, f] using h

/-- At a good height, the integral of the imaginary logarithmic derivative
over an ordered horizontal interval equals the change of any continuous xi
polar argument. Continuity of the zero-free logarithmic derivative supplies
the integrability required by the fundamental theorem of calculus. -/
theorem xi_horizontal_arg_integral {t a b : ℝ} (hab : a ≤ b)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hpolar :
      ∀ x : ℝ,
        x ∈ Set.Icc a b →
          riemannXi ((x : ℂ) + (t : ℂ) * Complex.I) =
            (‖riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I)) :
    (∫ x in a..b, (logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im) = φ b - φ a := by
  have hf : Continuous (fun x : ℝ ↦ logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    let z : ℂ := (x : ℂ) + (t : ℂ) * Complex.I
    have hz := riemannXi_good_height_ne_zero hgood x
    have hd :=
      (((differentiable_riemannXi.analyticAt z).deriv).div (differentiable_riemannXi.analyticAt z)
          hz).continuousAt
    change ContinuousAt (logDeriv riemannXi) z at hd
    have hc : ContinuousAt (fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) x :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    exact ContinuousAt.comp (f := fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) hd hc
  have hint :
    IntervalIntegrable (fun x : ℝ ↦ (logDeriv riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im)
      MeasureTheory.volume a b :=
    (Complex.continuous_im.comp hf).intervalIntegrable a b
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab hcont
  · intro x hx
    have hd := xi_horizontal_arg_deriv hgood hcont hpolar ⟨hx.1.le, hx.2.le⟩
    exact (hd.hasDerivAt (Icc_mem_nhds hx.1 hx.2)).hasDerivWithinAt
  · exact hint

end PseudoPrime.AnalyticNumberTheory.RiemannXi
