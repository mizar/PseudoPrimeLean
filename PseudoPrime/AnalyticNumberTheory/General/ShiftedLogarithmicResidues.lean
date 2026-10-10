/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

/-!
# Local residues of shifted logarithmic Perron kernels

The Mellin pole at zero and the translated zeros are treated by analytic regularization.
These local identities do not assert a global contour limit or an infinite zero-sum formula.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.General

/-- For any function F, real scale x and complex shift sigma and argument s, define
-logDeriv F (sigma+s) * x^s/s^2 using totalized complex powers and division.
A zero of F at rho translates to rho-sigma. Under the local analytic and nonvanishing
hypotheses, regularization computes the origin and translated-zero contour contributions. -/
noncomputable def shiftedLogarithmicKernel (F : ℂ → ℂ) (x : ℝ) (σ s : ℂ) : ℂ :=
  -logDeriv F (σ + s) * (x : ℂ) ^ s / s ^ 2

/-- For any F, real x and complex sigma and s, define -logDeriv F (sigma+s) * x^s,
the numerator obtained by removing the kernel's s^2 denominator. If x > 0 and F is
analytic and nonzero at sigma, this numerator is analytic at zero; its derivative
gives the residue coefficient of the kernel's possible double pole. -/
noncomputable def shiftedLogarithmicRegularization (F : ℂ → ℂ) (x : ℝ) (σ s : ℂ) : ℂ :=
  -logDeriv F (σ + s) * (x : ℂ) ^ s

/-- Analyticity and nonvanishing of F at sigma, with x>0, make the regularized numerator
 analytic at zero. Compose the analytic logarithmic derivative with the shift. -/
theorem analyticAt_shiftedLogarithmicRegularization {F : ℂ → ℂ} {x : ℝ} {σ : ℂ}
    (hF : AnalyticAt ℂ F σ) (hne : F σ ≠ 0) (hx : 0 < x) :
    AnalyticAt ℂ (shiftedLogarithmicRegularization F x σ) 0 := by
  have hlog : AnalyticAt ℂ (logDeriv F) σ := hF.deriv.div hF hne
  have hshift : AnalyticAt ℂ (fun s : ℂ ↦ σ + s) 0 := analyticAt_const.add analyticAt_id
  have hlog' : AnalyticAt ℂ (fun s : ℂ ↦ logDeriv F (σ + s)) 0 := by
    exact (show AnalyticAt ℂ (logDeriv F) (σ + 0) by simpa only [add_zero] using hlog).comp hshift
  exact hlog'.neg.mul (analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx))

/-- On the punctured neighborhood of zero, s^2 times the kernel equals its regularization.
 Cancel the nonzero denominator to supply the double-pole rectangle certificate. -/
theorem eventuallyEq_shiftedLogarithmicRegularization (F : ℂ → ℂ) (x : ℝ) (σ : ℂ) :
    Filter.EventuallyEq (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (fun s ↦ (s - 0) ^ 2 * shiftedLogarithmicKernel F x σ s)
      (shiftedLogarithmicRegularization F x σ) := by
  filter_upwards [eventually_mem_nhdsWithin] with s hs
  have hs0 : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs
  unfold shiftedLogarithmicKernel shiftedLogarithmicRegularization
  rw [sub_zero]
  field_simp [hs0]

/-- For F analytic and nonzero at sigma and x>0, the derivative of the regularized numerator
 is minus the derivative of logDeriv F minus logDeriv F times log x. The product and chain
 rules compute the residue at the Mellin pole. -/
theorem deriv_shiftedLogarithmicRegularization {F : ℂ → ℂ} {x : ℝ} {σ : ℂ} (hF : AnalyticAt ℂ F σ)
    (hne : F σ ≠ 0) (hx : 0 < x) :
    deriv (shiftedLogarithmicRegularization F x σ) 0 =
      -deriv (logDeriv F) σ - logDeriv F σ * (Real.log x : ℂ) := by
  have hlog : AnalyticAt ℂ (logDeriv F) σ := hF.deriv.div hF hne
  have hlogd : HasDerivAt (logDeriv F) (deriv (logDeriv F) σ) (σ + id 0) := by
    simpa only [id_eq, add_zero] using hlog.differentiableAt.hasDerivAt
  have hd := (hlogd.comp 0 ((hasDerivAt_id (0 : ℂ)).const_add σ)).neg
  have hp := (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hx.ne'))
  have hh := hd.mul hp
  have heq :
    (-logDeriv F ∘ HAdd.hAdd σ * fun s : ℂ ↦ (x : ℂ) ^ id s) =
      shiftedLogarithmicRegularization F x σ :=
    rfl
  rw [heq] at hh
  simpa only [Function.comp_apply, Pi.neg_apply, id_eq, add_zero, mul_one, Complex.cpow_zero,
    one_mul, neg_mul, sub_eq_add_neg, Complex.ofReal_log hx.le] using hh.deriv

/-- For F analytic and nonzero at sigma and x>0, every sufficiently small centered square
 at zero has boundary integral 2 pi i times the explicit double-pole residue.
 Apply the rectangle Cauchy formula to the analytic numerator. -/
theorem exists_radius_shiftedLogarithmicKernel_origin {F : ℂ → ℂ} {x : ℝ} {σ : ℂ}
    (hF : AnalyticAt ℂ F σ) (hne : F σ ≠ 0) (hx : 0 < x) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (shiftedLogarithmicKernel F x σ)
                (RectangleGeometry.centeredSquareLower 0 r)
                (RectangleGeometry.centeredSquareUpper 0 r) =
              2 * Real.pi * Complex.I *
                (-deriv (logDeriv F) σ - logDeriv F σ * (Real.log x : ℂ)) := by
  obtain ⟨R, hR, hr⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv
      (analyticAt_shiftedLogarithmicRegularization hF hne hx)
      (eventuallyEq_shiftedLogarithmicRegularization F x σ)
  refine ⟨R, hR, fun r hpos hle ↦ ?_⟩
  rw [hr r hpos hle, deriv_shiftedLogarithmicRegularization hF hne hx]

/-- For any regular factor g, natural m, real x and complex sigma, rho and s, define
-(m + (s-(rho-sigma))*logDeriv g (sigma+s))*x^s/s^2. A local logarithmic-derivative
expansion with multiplicity m identifies this with (s-(rho-sigma)) times the kernel.
For x > 0, rho != sigma and g analytic and nonzero at rho, it is analytic there
and evaluates to the shifted zero's residue coefficient. -/
noncomputable def shiftedLogarithmicZeroRegularization (g : ℂ → ℂ) (m : ℕ) (x : ℝ) (σ ρ s : ℂ) :
    ℂ :=
  -((m : ℂ) + (s - (ρ - σ)) * logDeriv g (σ + s)) * (x : ℂ) ^ s / s ^ 2

/-- Addition of sigma maps the punctured neighborhood of rho-sigma into that of rho.
 Continuity and preservation of distinct points transfer local zero expansions. -/
theorem tendsto_shift_punctured (σ ρ : ℂ) :
    Filter.Tendsto (fun s : ℂ ↦ σ + s) (nhdsWithin (ρ - σ) ({ρ - σ}ᶜ : Set ℂ))
      (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have h : Filter.Tendsto (fun s : ℂ ↦ σ + s) (nhds (ρ - σ)) (nhds (σ + (ρ - σ))) :=
      (continuousAt_const.add continuousAt_id).tendsto
    simpa only [show σ + (ρ - σ) = ρ by ring] using h.mono_left nhdsWithin_le_nhds
  · filter_upwards [eventually_mem_nhdsWithin] with s hs
    apply Set.mem_compl_singleton_iff.mpr
    intro heq
    exact
      (Set.mem_compl_singleton_iff.mp hs)
        (eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using heq))

/-- For an analytic nonzero regular factor g at rho, positive x, and rho different from sigma,
 the shifted zero regularization is analytic. Compose the regular logarithmic derivative and
 divide by the nonzero Mellin denominator. -/
theorem analyticAt_shiftedLogarithmicZeroRegularization {g : ℂ → ℂ} {m : ℕ} {x : ℝ} {σ ρ : ℂ}
    (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0) (hx : 0 < x) (hρ : ρ - σ ≠ 0) :
    AnalyticAt ℂ (shiftedLogarithmicZeroRegularization g m x σ ρ) (ρ - σ) := by
  have hlog : AnalyticAt ℂ (logDeriv g) ρ := hg.deriv.div hg hg0
  have hlog' : AnalyticAt ℂ (fun s : ℂ ↦ logDeriv g (σ + s)) (ρ - σ) := by
    apply
      (show AnalyticAt ℂ (logDeriv g) (σ + (ρ - σ)) by
          simpa only [show σ + (ρ - σ) = ρ by ring] using hlog).comp
    exact analyticAt_const.add analyticAt_id
  exact
    ((analyticAt_const.add ((analyticAt_id.sub analyticAt_const).mul hlog')).neg.mul
          (analyticAt_const.cpow analyticAt_id (Complex.ofReal_mem_slitPlane.mpr hx))).div
      (analyticAt_id.pow 2) (pow_ne_zero 2 hρ)

/-- A local logarithmic-derivative expansion at rho gives the shifted kernel's simple-pole
 certificate at rho-sigma, provided this point is nonzero. Transfer the expansion along the
 shift and clear the punctured denominator. -/
theorem eventuallyEq_shiftedLogarithmicZeroRegularization {F g : ℂ → ℂ} {m : ℕ} {x : ℝ} {σ ρ : ℂ}
    (hρ : ρ - σ ≠ 0)
    (hlog :
      Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) (logDeriv F)
        (fun z ↦ (m : ℂ) / (z - ρ) + logDeriv g z)) :
    Filter.EventuallyEq (nhdsWithin (ρ - σ) ({ρ - σ}ᶜ : Set ℂ))
      (fun s ↦ (s - (ρ - σ)) * shiftedLogarithmicKernel F x σ s)
      (shiftedLogarithmicZeroRegularization g m x σ ρ) := by
  have hlog' := hlog.comp_tendsto (tendsto_shift_punctured σ ρ)
  have hn0 : ∀ᶠ s : ℂ in nhds (ρ - σ), s ≠ 0 := compl_singleton_mem_nhds hρ
  have hn : ∀ᶠ s : ℂ in nhdsWithin (ρ - σ) ({ρ - σ}ᶜ : Set ℂ), s ≠ 0 :=
    hn0.filter_mono nhdsWithin_le_nhds
  filter_upwards [hlog', hn, eventually_mem_nhdsWithin] with s hs hs0 hsc
  have hsρ : s - (ρ - σ) ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsc)
  have hsub : σ + s - ρ = s - (ρ - σ) := by ring
  unfold shiftedLogarithmicKernel shiftedLogarithmicZeroRegularization
  change logDeriv F (σ + s) = (m : ℂ) / (σ + s - ρ) + logDeriv g (σ + s) at hs
  rw [hs, hsub]
  field_simp [hs0, hsρ]

/-- For a local expansion with analytic nonzero regular factor, x>0, and rho different from
 sigma, every sufficiently small square around rho-sigma has residue -m*x^(rho-sigma)/(rho-sigma)^2.
 Apply the simple-pole rectangle formula and evaluate the regularized numerator. -/
theorem exists_radius_shiftedLogarithmicKernel_zero {F g : ℂ → ℂ} {m : ℕ} {x : ℝ} {σ ρ : ℂ}
    (hg : AnalyticAt ℂ g ρ) (hg0 : g ρ ≠ 0) (hx : 0 < x) (hρ : ρ - σ ≠ 0)
    (hlog :
      Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) (logDeriv F)
        (fun z ↦ (m : ℂ) / (z - ρ) + logDeriv g z)) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (shiftedLogarithmicKernel F x σ)
                (RectangleGeometry.centeredSquareLower (ρ - σ) r)
                (RectangleGeometry.centeredSquareUpper (ρ - σ) r) =
              2 * Real.pi * Complex.I * (-(m : ℂ) * (x : ℂ) ^ (ρ - σ) / (ρ - σ) ^ 2) := by
  obtain ⟨R, hR, hr⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul
      (analyticAt_shiftedLogarithmicZeroRegularization hg hg0 hx hρ)
      (eventuallyEq_shiftedLogarithmicZeroRegularization hρ hlog)
  refine ⟨R, hR, fun r hpos hle ↦ ?_⟩
  rw [hr r hpos hle]
  simp only [shiftedLogarithmicZeroRegularization, sub_self, zero_mul, add_zero]

end PseudoPrime.AnalyticNumberTheory.General
