/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.General.MellinTestStripDecay
public import PseudoPrime.AnalyticNumberTheory.General.MellinTestAnalytic
public import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
public import Mathlib.Analysis.MellinInversion

/-!
# Mellin inversion for compact logarithmic tests

Endpoint vanishing and Mellin decay discharge both convergence premises of
inversion, preparing the arithmetic evaluation of the explicit formula.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- A continuous compactly supported logarithmic test has a convergent
Mellin transform at every complex point. Its multiplicative weight vanishes
near both endpoints and is locally integrable on the positive half-line.
Arbitrary endpoint power bounds place any point in a convergence strip.
This supplies the forward-transform premise for Mellin inversion. -/
theorem mellinConvergent_logarithmicTestWeight (g : ℝ → ℂ) (hc : HasCompactSupport g)
    (hg : Continuous g) (s : ℂ) : MellinConvergent (logarithmicTestWeight g) s := by
  obtain ⟨ht, hb⟩ := logarithmicTestWeight_eventually_zero g hc
  apply
    mellinConvergent_of_isBigO_rpow (logarithmicTestWeight_locallyIntegrable g hg)
      ((Asymptotics.isBigO_zero (fun x : ℝ ↦ x ^ (-(s.re + 1))) Filter.atTop).congr'
        (Filter.EventuallyEq.symm ht) Filter.EventuallyEq.rfl)
      (by linarith only)
      ((Asymptotics.isBigO_zero (fun x : ℝ ↦ x ^ (-(s.re - 1)))
            (nhdsWithin (0 : ℝ) (Set.Ioi 0))).congr'
        (Filter.EventuallyEq.symm hb) Filter.EventuallyEq.rfl)
      (by linarith only)

/-- The Mellin transform of an even smooth compact logarithmic test is
integrable on every vertical line. Zeroth and quadratic Mellin bounds give
the integrable majorant (D0+D2)/(1+T^2); entire Mellin regularity gives
measurability. This supplies the inverse-transform premise without an
independent vertical-integrability hypothesis. -/
theorem verticalIntegrable_mellin_logarithmicTestWeight (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) :
    Complex.VerticalIntegrable (mellin (logarithmicTestWeight g)) σ := by
  obtain ⟨D₀, _, h₀⟩ := mellin_logarithmicTestWeight_uniform_power_bound g he hc hg σ σ 0
  obtain ⟨D₂, _, h₂⟩ := mellin_logarithmicTestWeight_uniform_power_bound g he hc hg σ σ 2
  have hline : Continuous (fun T : ℝ ↦ (σ : ℂ) + T * Complex.I) :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  have hm := (differentiable_mellin_logarithmicTestWeight g hc hg.continuous).continuous
  apply (integrable_inv_one_add_sq.const_mul (D₀ + D₂)).mono' (hm.comp hline).aestronglyMeasurable
  exact
    MeasureTheory.ae_of_all _ fun T ↦ by
      have h₀' := h₀ σ ⟨le_refl σ, le_refl σ⟩ T
      simp only [pow_zero, one_mul] at h₀'
      have h₂' := h₂ σ ⟨le_refl σ, le_refl σ⟩ T
      rw [sq_abs] at h₂'
      simp only [Function.comp_apply]
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (add_pos_of_pos_of_nonneg zero_lt_one (sq_nonneg T))).mpr
      nlinarith only [h₀', h₂']

/-- For an even smooth compact logarithmic test, inversion of its Mellin
transform on any real line recovers the weight at each positive argument.
Forward convergence, vertical integrability and continuity are all proved
from the test hypotheses, then passed to the Mellin inversion theorem.
This evaluates the termwise vertical integrals in the arithmetic side
of the explicit formula. -/
theorem mellinInv_mellin_logarithmicTestWeight (g : ℝ → ℂ) (he : ∀ u : ℝ, g (-u) = g u)
    (hc : HasCompactSupport g) (hg : ContDiff ℝ (↑(⊤ : ℕ∞)) g) (σ : ℝ) {x : ℝ} (hx : 0 < x) :
    mellinInv σ (mellin (logarithmicTestWeight g)) x = logarithmicTestWeight g x := by
  apply
    mellinInv_mellin_eq σ _ hx (mellinConvergent_logarithmicTestWeight g hc hg.continuous σ)
      (verticalIntegrable_mellin_logarithmicTestWeight g he hc hg σ)
  have hl := Real.continuousAt_log (ne_of_gt hx)
  exact
    (Real.continuous_exp.continuousAt.comp (hl.neg.div_const 2)).smul
      (hg.continuous.continuousAt.comp hl)

end PseudoPrime.AnalyticNumberTheory.General
