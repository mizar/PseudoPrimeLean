/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.BacklundPhase
public import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.Complex.RealDeriv
import PseudoPrime.Analysis.ContinuousLogDerivative
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GoodHeight

/-! # Derivative of the horizontal zeta argument -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- At a positive good height, zeta does not vanish at any point of the
horizontal line. Every zero at nonzero height has nonnegative real part, so
the good-height condition applies without a restriction on the abscissa. -/
theorem zeta_horizontal_ne_zero {T x : ℝ} (hT : 0 < T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) :
    riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) ≠ 0 := by
  intro hz
  have hi : ((x : ℂ) + (T : ℂ) * Complex.I).im = T := by
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, zero_mul, mul_one, add_zero, zero_add]
  have hre :=
    AnalyticNumberTheory.RiemannZeta.riemannZeta_zero_re_nonneg_of_im_ne_zero hz
      (by
        rw [hi]; exact hT.ne')
  exact hgood _ hz hre hi

/-- At a positive good height, a continuous polar argument for zeta on a
closed horizontal interval has derivative equal to the imaginary part of
zeta's logarithmic derivative. The good-height condition excludes zeros;
the general continuous-logarithm derivative theorem then applies. -/
theorem zeta_horizontal_arg_deriv {T a b : ℝ} (hT : 0 < T)
    (hgood : ∀ ρ : ℂ, riemannZeta ρ = 0 → 0 ≤ ρ.re → ρ.im ≠ T) {φ : ℝ → ℝ}
    (hcont : ContinuousOn φ (Set.Icc a b))
    (hpolar :
      ∀ x : ℝ,
        x ∈ Set.Icc a b →
          riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I) =
            (‖riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)‖ : ℂ) *
              Complex.exp ((φ x : ℂ) * Complex.I))
    {x : ℝ} (hx : x ∈ Set.Icc a b) :
    HasDerivWithinAt φ (logDeriv riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)).im (Set.Icc a b)
      x := by
  let f : ℝ → ℂ := fun y => riemannZeta ((y : ℂ) + (T : ℂ) * Complex.I)
  have hne : ∀ y ∈ Set.Icc a b, f y ≠ 0 := by
    intro y hy hz
    exact zeta_horizontal_ne_zero hT hgood hz
  have h1 : (x : ℂ) + (T : ℂ) * Complex.I ≠ 1 := by
    intro h
    have hi := congrArg Complex.im h
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
      Complex.I_im, zero_mul, mul_one, add_zero, zero_add, Complex.one_im] at hi
    linarith only [hT, hi]
  have hd :=
    (differentiableAt_riemannZeta h1).hasDerivAt.comp (x : ℂ)
      ((hasDerivAt_id (x : ℂ)).add_const ((T : ℂ) * Complex.I))
  have hf :
    HasDerivWithinAt f (deriv riemannZeta ((x : ℂ) + (T : ℂ) * Complex.I)) (Set.Icc a b) x := by
    have hh := hd.comp_ofReal
    simpa only [Function.comp_def, id_eq, mul_one, f] using hh.hasDerivWithinAt
  have h := Analysis.hasDerivWithinAt_continuous_arg hx (hcont x hx) hf hne hpolar
  simpa only [logDeriv_apply, f] using h

/-- If a real argument has derivative `d` throughout the Backlund segment,
the sum of its right and left variations has derivative equal to the
difference of `d` at the reflected points. Apply the chain rule on `[0,1]`. -/
theorem reflected_arg_deriv {φ d : ℝ → ℝ}
    (hφ :
      ∀ x ∈ Set.Icc (-(1 / 2) : ℝ) (3 / 2), HasDerivWithinAt φ (d x) (Set.Icc (-(1 / 2)) (3 / 2)) x)
    {u : ℝ} (hu : u ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (fun v : ℝ => (φ (1 / 2 + v) - φ (1 / 2)) + (φ (1 / 2 - v) - φ (1 / 2)))
      (d (1 / 2 + u) - d (1 / 2 - u)) (Set.Icc 0 1) u := by
  have hplus : Set.MapsTo (fun v : ℝ => 1 / 2 + v) (Set.Icc 0 1) (Set.Icc (-(1 / 2)) (3 / 2)) := by
    intro v hv
    constructor <;> linarith only [hv.1, hv.2]
  have hminus : Set.MapsTo (fun v : ℝ => 1 / 2 - v) (Set.Icc 0 1) (Set.Icc (-(1 / 2)) (3 / 2)) := by
    intro v hv
    constructor <;> linarith only [hv.1, hv.2]
  have hp := (hφ _ (hplus hu)).comp u ((hasDerivAt_id u).const_add (1 / 2)).hasDerivWithinAt hplus
  have hm := (hφ _ (hminus hu)).comp u ((hasDerivAt_id u).const_sub (1 / 2)).hasDerivWithinAt hminus
  have hcomb := (hp.sub_const (φ (1 / 2))).add (hm.sub_const (φ (1 / 2)))
  simpa only [Function.comp_def, id_eq, mul_one, mul_neg, ← sub_eq_add_neg, Pi.add_def] using hcomb

end PseudoPrime.PrimeTestBounds.MillerRabin
