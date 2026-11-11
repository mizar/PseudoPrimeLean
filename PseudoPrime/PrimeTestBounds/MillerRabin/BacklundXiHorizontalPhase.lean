/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundRealPhase
import PseudoPrime.AnalyticNumberTheory.RiemannXi.HorizontalArgument

/-! # Xi argument on the right half of the upper edge -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At a positive height, any continuous polar argument of zeta on the
Backlund segment induces a continuous polar argument of xi on its right
half. Add the imaginary part of the xi factor logarithm, which is
differentiable there because both principal-log arguments avoid their cuts. -/
theorem xi_horizontal_polar {t : ℝ} (ht : 0 < t) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hp :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I)) :
    ContinuousOn
        (fun x : ℝ ↦
          (AnalyticNumberTheory.RiemannXi.xiLogFactor ((x : ℂ) + (t : ℂ) * Complex.I)).im + φ x)
        (Set.Icc (1 / 2) (3 / 2)) ∧
      ∀ x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2),
        AnalyticNumberTheory.RiemannXi.riemannXi ((x : ℂ) + (t : ℂ) * Complex.I) =
          (‖AnalyticNumberTheory.RiemannXi.riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
            Complex.exp
              ((((AnalyticNumberTheory.RiemannXi.xiLogFactor ((x : ℂ) + (t : ℂ) * Complex.I)).im +
                      φ x :
                    ℝ) :
                  ℂ) *
                Complex.I) := by
  have hsub : Set.Icc (1 / 2 : ℝ) (3 / 2) ⊆ Set.Icc (-(1 / 2)) (3 / 2) := by
    intro x hx
    exact ⟨by linarith only [hx.1], hx.2⟩
  have hdata (x : ℝ) (hx : x ∈ Set.Icc (1 / 2 : ℝ) (3 / 2)) :
    0 < (((x : ℂ) + (t : ℂ) * Complex.I)).re ∧
      ((x : ℂ) + (t : ℂ) * Complex.I) - 1 ∈ Complex.slitPlane := by
    constructor
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
        Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
      linarith only [hx.1]
    · apply Complex.mem_slitPlane_iff.mpr
      right
      simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_im, Complex.I_re, mul_one, mul_zero, add_zero, zero_add,
        Complex.one_im, sub_zero]
      exact ne_of_gt ht
  have hf :
    ContinuousOn
      (fun x : ℝ ↦ AnalyticNumberTheory.RiemannXi.xiLogFactor ((x : ℂ) + (t : ℂ) * Complex.I))
      (Set.Icc (1 / 2) (3 / 2)) := by
    intro x hx
    have hd :=
      AnalyticNumberTheory.RiemannXi.differentiableAt_xiLogFactor (hdata x hx).1 (hdata x hx).2
    have hp' : ContinuousAt (fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) x :=
      (Complex.continuous_ofReal.add continuous_const).continuousAt
    exact
      (ContinuousAt.comp (f := fun y : ℝ ↦ (y : ℂ) + (t : ℂ) * Complex.I) hd.continuousAt
          hp').continuousWithinAt
  constructor
  · exact (Complex.continuous_im.comp_continuousOn hf).add (hc.mono hsub)
  · intro x hx
    have hs1 : ((x : ℂ) + (t : ℂ) * Complex.I) ≠ 1 := by
      intro he
      have hi := congrArg Complex.im he
      simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, mul_one, mul_zero, add_zero, zero_add, Complex.one_im] at hi
      linarith only [ht, hi]
    exact xi_polar_of_zeta (hdata x hx).1 hs1 (φ x) (hp x (hsub hx))

/-- At a positive good height, the right-half top-edge integral of xi's
logarithmic derivative is the change of the xi factor phase plus the given
zeta argument. Apply the continuous-argument derivative theorem and the
fundamental theorem of calculus to the induced xi polar argument. -/
theorem xi_upper_arg_integral {t : ℝ} (ht : 0 < t)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ t) (φ : ℝ → ℝ)
    (hc : ContinuousOn φ (Set.Icc (-(1 / 2)) (3 / 2)))
    (hp :
      ∀ x : ℝ,
        x ∈ Set.Icc (-(1 / 2)) (3 / 2) →
          riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (t : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I)) :
    (∫ x in (1 / 2 : ℝ)..(3 / 2),
        (logDeriv AnalyticNumberTheory.RiemannXi.riemannXi ((x : ℂ) + (t : ℂ) * Complex.I)).im) =
      ((AnalyticNumberTheory.RiemannXi.xiLogFactor (((3 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im +
          φ (3 / 2)) -
        ((AnalyticNumberTheory.RiemannXi.xiLogFactor (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).im +
          φ (1 / 2)) := by
  obtain ⟨hcont, hpolar⟩ := xi_horizontal_polar ht φ hc hp
  exact
    AnalyticNumberTheory.RiemannXi.xi_horizontal_arg_integral (by norm_num only) hgood hcont hpolar

end PseudoPrime.PrimeTestBounds.MillerRabin
