/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import PseudoPrime.AnalyticNumberTheory.General.MellinWeights
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SmoothedContour
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.GridCellShrink
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ContourRegularity
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.HadamardMultiplicityFactorization
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroContribution

/-!
# Smoothed Dirichlet L-function contour kernels and finite contour identities

This file defines logarithmic and reciprocal Mellin-weighted L-function kernels and proves
their regularity, local residues, and finite contour identities. No later numerical inequality
is assumed. The completed function keeps mathlib's normalization.
The kernel definitions apply to arbitrary characters of nonzero level; primitivity is required
only by declarations that explicitly assume it, such as the finite contour identity.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Definition: the reciprocal-weight primitive Dirichlet contour kernel is `-L'/L` multiplied by the
reciprocal Mellin factor `x^(s-1)/(s(s-1))`.
Input: cutoff `x`, character `χ`, and contour variable `s`.
Output: the complex integrand for the primitive reciprocal explicit formula.
Role: it uses the same Mellin normalization as the Riemann kernel while retaining the character
dependence needed by downstream modules.
-/
noncomputable def dirichletReciprocalContourKernel {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
      (x : ℂ) ^ (s - 1) /
    (s * (s - 1))

/--
Definition: the logarithmic-weight primitive Dirichlet contour kernel is `-L'/L` multiplied by
the logarithmic Mellin factor `x^s/s²`.
Input: cutoff `x`, character `χ`, and contour variable `s`.
Output: the complex integrand for the primitive logarithmic explicit formula.
Role: this is the contour object whose residues and zero sum will supply the primitive weighted
upper estimate in downstream modules.
-/
noncomputable def dirichletLogContourKernel {N : ℕ} [NeZero N] (x : ℝ) (χ : DirichletCharacter ℂ N)
    (s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s /
    s ^ 2

/--
Definition: the reciprocal primitive kernel with its Mellin simple pole at zero removed.
Input: cutoff `x`, character `χ`, and complex variable `s`.
Output: the analytic candidate for `s` times the reciprocal kernel near zero.
Role: supplies the odd-character zero-side simple-pole certificate.
-/
noncomputable def dirichletReciprocalMellinZeroRegularization {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
      (x : ℂ) ^ (s - 1) /
    (s - 1)

/--
Definition: the logarithmic primitive kernel with its double Mellin pole at zero removed.
Input: cutoff `x`, character `χ`, and complex variable `s`.
Output: the analytic candidate for `s²` times the logarithmic kernel near zero.
Role: supplies the odd-character zero-side double-pole certificate.
-/
noncomputable def dirichletLogMellinZeroRegularization {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) * (x : ℂ) ^ s

/--
Input/assumptions: a positive cutoff and a nontrivial character whose `L`-value at zero is nonzero.
Conclusion: the reciprocal zero-regularization is analytic at zero.
Content: divide the analytic logarithmic derivative by the nonzero Mellin factor `s - 1`.
Role: is the regular part for the reciprocal simple-pole contour identity at zero.
-/
theorem analyticAt_dirichletReciprocalMellinZeroRegularization {N : ℕ} [NeZero N] {x : ℝ}
    (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1)
    (hLzero : DirichletCharacter.LFunction χ 0 ≠ 0) :
    AnalyticAt ℂ
      (dirichletReciprocalMellinZeroRegularization
        x χ)
      0 := by
  have hL := (DirichletCharacter.differentiable_LFunction hχ).analyticAt 0
  have hlog :
    AnalyticAt ℂ
      (fun s ↦ deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) 0 :=
    hL.deriv.div hL hLzero
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) 0 :=
    analyticAt_const.cpow (analyticAt_id.sub analyticAt_const) hxslit
  exact (hlog.neg.mul hpow).div (analyticAt_id.sub analyticAt_const) (by norm_num only)

/--
Input/assumptions: a positive cutoff and a nontrivial character whose `L`-value at zero is nonzero.
Conclusion: the logarithmic zero-regularization is analytic at zero.
Content: its factors are the analytic logarithmic derivative and an analytic positive-base power.
Role: is the regular part for the logarithmic double-pole contour identity at zero.
-/
theorem analyticAt_dirichletLogMellinZeroRegularization {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (hLzero : DirichletCharacter.LFunction χ 0 ≠ 0) :
    AnalyticAt ℂ
      (dirichletLogMellinZeroRegularization x χ)
      0 := by
  have hL := (DirichletCharacter.differentiable_LFunction hχ).analyticAt 0
  have hlog :
    AnalyticAt ℂ
      (fun s ↦ deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) 0 :=
    hL.deriv.div hL hLzero
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) 0 := analyticAt_const.cpow analyticAt_id hxslit
  exact hlog.neg.mul hpow

/--
Input/assumptions: a cutoff and a punctured point near zero.
Conclusion: multiplication by `s` changes the reciprocal kernel into its zero regularization.
Content: cancel the nonzero Mellin factor `s` algebraically.
Role: supplies the simple-principal-part equality at the lower Mellin endpoint.
-/
theorem eventuallyEq_dirichletReciprocalMellinZeroRegularization {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) :
    Filter.EventuallyEq (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (fun s ↦
        (s - 0) *
          dirichletReciprocalContourKernel x χ
            s)
      (dirichletReciprocalMellinZeroRegularization
        x χ) := by
  have honeNhds : ∀ᶠ s : ℂ in nhds 0, s ≠ 1 := compl_singleton_mem_nhds (by norm_num only)
  have hone : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ), s ≠ 1 :=
    honeNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hone, eventually_mem_nhdsWithin] with s hs1 hs0
  unfold dirichletReciprocalContourKernel
    dirichletReciprocalMellinZeroRegularization
  have hs0' : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs0
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp only [sub_zero]
  field_simp

/--
Input/assumptions: a cutoff and a punctured point near zero.
Conclusion: multiplication by `s²` changes the logarithmic kernel into its zero regularization.
Content: cancel the nonzero square of the Mellin factor algebraically.
Role: supplies the double-principal-part equality at the lower Mellin endpoint.
-/
theorem eventuallyEq_dirichletLogMellinZeroRegularization {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) :
    Filter.EventuallyEq (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (fun s ↦
        (s - 0) ^ 2 *
          dirichletLogContourKernel x χ s)
      (dirichletLogMellinZeroRegularization x
        χ) := by
  filter_upwards [eventually_mem_nhdsWithin] with s hs0
  unfold dirichletLogContourKernel
    dirichletLogMellinZeroRegularization
  have hs0' : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs0
  simp only [sub_zero]
  field_simp

/--
Input/assumptions: odd nontrivial primitive character and positive cutoff.
Conclusion: one positive radius bounds every smaller centered square carrying the reciprocal
zero-side residue formula.
Content: retain the neighborhood radius supplied by the shared simple-pole square adapter.
Role: permits the later finite grid to shrink the zero-side square to fit its assigned cell.
-/
theorem exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_zero_of_primitive_odd
    {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (hodd : χ.Odd) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral
                (dirichletReciprocalContourKernel
                  x χ)
                (RectangleGeometry.centeredSquareLower 0 r)
                (RectangleGeometry.centeredSquareUpper 0 r) =
              2 * Real.pi * Complex.I *
                dirichletReciprocalMellinZeroRegularization
                  x χ 0 := by
  exact
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul
      (analyticAt_dirichletReciprocalMellinZeroRegularization
        hx hne
        (dirichletLFunction_zero_ne_zero_of_primitive_odd
          hprimitive hne hodd))
      (eventuallyEq_dirichletReciprocalMellinZeroRegularization
        x χ)

/--
Input/assumptions: odd nontrivial primitive character and positive cutoff.
Conclusion: one positive radius bounds every smaller centered square carrying the logarithmic
zero-side residue formula.
Content: retain the neighborhood radius supplied by the shared double-pole square adapter.
Role: gives the logarithmic kernel the same shrinkable local datum as the reciprocal kernel.
-/
theorem exists_radius_forall_dirichletRectangleBoundaryIntegral_log_zero_of_primitive_odd {N : ℕ}
    [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) (hodd : χ.Odd) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral
                (dirichletLogContourKernel x χ)
                (RectangleGeometry.centeredSquareLower 0 r)
                (RectangleGeometry.centeredSquareUpper 0 r) =
              2 * Real.pi * Complex.I *
                deriv
                  (dirichletLogMellinZeroRegularization
                    x χ)
                  0 := by
  exact
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv
      (analyticAt_dirichletLogMellinZeroRegularization
        hx hne
        (dirichletLFunction_zero_ne_zero_of_primitive_odd
          hprimitive hne hodd))
      (eventuallyEq_dirichletLogMellinZeroRegularization
        x χ)

/--
Definition: the reciprocal primitive kernel with its even-character combined pole at zero removed.
Input: cutoff, zero multiplicity, nonvanishing local factor, and complex variable.
Output: the analytic candidate for `s²` times the reciprocal kernel at an even trivial zero.
Role: supplies the even reciprocal double-pole regular part.
-/
noncomputable def dirichletReciprocalEvenZeroRegularization (x : ℝ) (m : ℕ) (g : ℂ → ℂ) (s : ℂ) :
    ℂ :=
  -((m : ℂ) + s * logDeriv g s) * (x : ℂ) ^ (s - 1) / (s - 1)

/--
Definition: the logarithmic primitive kernel with its even-character combined pole at zero removed.
Input: cutoff, zero multiplicity, nonvanishing local factor, and complex variable.
Output: the analytic candidate for `s³` times the logarithmic kernel at an even trivial zero.
Role: supplies the even logarithmic triple-pole regular part.
-/
noncomputable def dirichletLogEvenZeroRegularization (x : ℝ) (m : ℕ) (g : ℂ → ℂ) (s : ℂ) : ℂ :=
  -((m : ℂ) + s * logDeriv g s) * (x : ℂ) ^ s

/--
Input/assumptions: positive cutoff and analytic nonvanishing local factor at zero.
Conclusion: the even reciprocal combined-pole regularization is analytic at zero.
Content: the local logarithmic derivative, Mellin power, and factor `s-1` are analytic there.
Role: is the regular part for the even reciprocal double-pole certificate.
-/
theorem analyticAt_dirichletReciprocalEvenZeroRegularization {x : ℝ} (hx : 0 < x) (m : ℕ)
    {g : ℂ → ℂ} (hganalytic : AnalyticAt ℂ g 0) (hgzero : g 0 ≠ 0) :
    AnalyticAt ℂ
      (dirichletReciprocalEvenZeroRegularization
        x m g)
      0 := by
  have hlog : AnalyticAt ℂ (logDeriv g) 0 := by
    unfold logDeriv
    exact hganalytic.deriv.div hganalytic hgzero
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) 0 :=
    analyticAt_const.cpow (analyticAt_id.sub analyticAt_const) hxslit
  exact
    ((analyticAt_const.add (analyticAt_id.mul hlog)).neg.mul hpow).div
      (analyticAt_id.sub analyticAt_const) (by norm_num only)

/--
Input/assumptions: positive cutoff and analytic nonvanishing local factor at zero.
Conclusion: the even logarithmic combined-pole regularization is analytic at zero.
Content: it is a product of the analytic local logarithmic derivative expression and Mellin power.
Role: is the regular part for the even logarithmic triple-pole certificate.
-/
theorem analyticAt_dirichletLogEvenZeroRegularization {x : ℝ} (hx : 0 < x) (m : ℕ) {g : ℂ → ℂ}
    (hganalytic : AnalyticAt ℂ g 0) (hgzero : g 0 ≠ 0) :
    AnalyticAt ℂ
      (dirichletLogEvenZeroRegularization x m g)
      0 := by
  have hlog : AnalyticAt ℂ (logDeriv g) 0 := by
    unfold logDeriv
    exact hganalytic.deriv.div hganalytic hgzero
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) 0 := analyticAt_const.cpow analyticAt_id hxslit
  unfold dirichletLogEvenZeroRegularization
  fun_prop

/--
Input/assumptions: a positive cutoff, a nontrivial character, and a regular point away from zero,
one, and zeros of its `L`-function.
Conclusion: the reciprocal primitive contour kernel is differentiable at that point.
Content: combine differentiability of the nontrivial continued `L`-function with elementary
holomorphic rules for division and complex powers.
Role: this is the regular-locus analytic input for the primitive reciprocal contour rectangle.
-/
theorem differentiableAt_dirichletReciprocalContourKernel {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ
      (dirichletReciprocalContourKernel x χ)
      s := by
  have hdiff : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.differentiable_LFunction hχ) s
  have hderiv : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) s :=
    ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s).deriv.differentiableAt
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hcpow : (x : ℂ) ≠ 0 ∨ s - 1 ≠ 0 := Or.inl hxne
  have hden : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  have hs1χ : s ≠ 1 ∨ χ ≠ 1 := Or.inl hs1
  unfold dirichletReciprocalContourKernel
  fun_prop (disch := assumption)

/--
Input/assumptions: a positive cutoff, a nontrivial character, and a regular point away from zero
and zeros of its `L`-function.
Conclusion: the logarithmic primitive contour kernel is differentiable at that point.
Content: the same nontrivial continuation and elementary holomorphic rules apply.
Role: this is the regular-locus analytic input for the primitive logarithmic contour rectangle.
-/
theorem differentiableAt_dirichletLogContourKernel {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {s : ℂ} (hs0 : s ≠ 0)
    (hL : DirichletCharacter.LFunction χ s ≠ 0) :
    DifferentiableAt ℂ
      (dirichletLogContourKernel x χ) s := by
  have hdiff : DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
    (DirichletCharacter.differentiable_LFunction hχ) s
  have hderiv : DifferentiableAt ℂ (deriv (DirichletCharacter.LFunction χ)) s :=
    ((DirichletCharacter.differentiable_LFunction hχ).analyticAt s).deriv.differentiableAt
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hcpow : (x : ℂ) ≠ 0 ∨ s ≠ 0 := Or.inl hxne
  have hden : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  have hs1χ : s ≠ 1 ∨ χ ≠ 1 := Or.inr hχ
  unfold dirichletLogContourKernel
  fun_prop (disch := assumption)

/--
For any real `x`, character `χ`, and complex `s`, define
`-logDeriv (LFunction χ) s * x^(s-1) / s`.
This is the algebraic candidate for `(s-1)` times the reciprocal kernel near one.
Analyticity at one is proved separately for positive `x` and a nontrivial character.
-/
noncomputable def dirichletReciprocalOneRegularization {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) (s : ℂ) : ℂ :=
  -(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) *
      (x : ℂ) ^ (s - 1) /
    s

/--
Input/assumptions: a nontrivial character and positive Mellin parameter.
Conclusion: the reciprocal one-regularization is analytic at one.
Content: `L(χ,1)` is nonzero, so continuation, its derivative, the complex power, and division by
`s` are analytic there.
Role: provides the regular part needed for the simple-pole contour residue at one.
-/
theorem analyticAt_dirichletReciprocalOneRegularization {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    AnalyticAt ℂ
      (dirichletReciprocalOneRegularization x χ)
      1 := by
  have hL : DirichletCharacter.LFunction χ (1 : ℂ) ≠ 0 :=
    dirichletLFunction_one_ne_zero_of_ne_one hχ
  have hlog :
    AnalyticAt ℂ
      (fun s ↦ deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s) 1 := by
    exact
      ((DirichletCharacter.differentiable_LFunction hχ).analyticAt 1).deriv.div
        ((DirichletCharacter.differentiable_LFunction hχ).analyticAt 1) hL
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hconst : AnalyticAt ℂ (fun _ : ℂ ↦ (x : ℂ)) 1 := analyticAt_const
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) 1 :=
    hconst.cpow (analyticAt_id.sub analyticAt_const) hxslit
  unfold dirichletReciprocalOneRegularization
  exact (hlog.neg.mul hpow).div analyticAt_id one_ne_zero

/--
Input/assumptions: any character and any real Mellin parameter.
Conclusion: on the punctured neighborhood of one, `(s - 1)` times the reciprocal kernel equals
the one-regularization.
Content: cancel the nonzero Mellin factor `s - 1`; `s` remains nonzero near one.
Role: this is the simple-principal-part equality used by the shared rectangular residue theorem.
-/
theorem eventuallyEq_dirichletReciprocalOneRegularization {N : ℕ} [NeZero N] (x : ℝ)
    (χ : DirichletCharacter ℂ N) :
    Filter.EventuallyEq (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ))
      (fun s ↦
        (s - 1) *
          dirichletReciprocalContourKernel x χ
            s)
      (dirichletReciprocalOneRegularization x
        χ) := by
  have hzeroNhds : ∀ᶠ s : ℂ in nhds 1, s ≠ 0 := compl_singleton_mem_nhds one_ne_zero
  have hzeroEventually : ∀ᶠ s in nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ), s ≠ 0 :=
    hzeroNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hzeroEventually, eventually_mem_nhdsWithin] with s hs0 hs1
  unfold dirichletReciprocalContourKernel
    dirichletReciprocalOneRegularization
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs1)
  field_simp

/--
Input/assumptions: a nontrivial character and positive Mellin parameter.
Conclusion: one positive radius bounds every smaller centered square carrying the reciprocal
Mellin-point-one residue formula.
Content: retain the neighborhood radius from the shared simple-pole square adapter.
Role: lets the finite primitive grid choose a square at one inside its assigned cell.
-/
theorem exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_eq_residueAtOne {N : ℕ}
    [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral
                (dirichletReciprocalContourKernel
                  x χ)
                (RectangleGeometry.centeredSquareLower 1 r)
                (RectangleGeometry.centeredSquareUpper 1 r) =
              2 * Real.pi * Complex.I *
                dirichletReciprocalOneRegularization
                  x χ 1 := by
  exact
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul
      (analyticAt_dirichletReciprocalOneRegularization
        hx hχ)
      (eventuallyEq_dirichletReciprocalOneRegularization
        x χ)

/--
Input/assumptions: a nontrivial character and a vertical line strictly right of `Re s = 1`.
Conclusion: the primitive logarithmic contour kernel is continuous on that line.
Content: continuation supplies differentiability and nonvanishing; affine composition parametrizes
the line.
Role: this provides the measurability input for the right-edge integral of the primitive downstream
interface
explicit formula.
-/
theorem continuous_dirichletLogContourKernel_line {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {τ : ℝ} (hτ : 1 < τ) :
    Continuous
      (fun y : ℝ ↦
        dirichletLogContourKernel x χ
          ((τ : ℂ) + y * Complex.I)) := by
  have hOn :
    ContinuousOn (dirichletLogContourKernel x χ)
      {s : ℂ | 1 < s.re} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs
    have hs0 : s ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hs; linarith
    have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
    exact
      ContinuousAt.continuousWithinAt
        (differentiableAt_dirichletLogContourKernel
            hx hχ hs0 hL).continuousAt
  have hg : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) := by fun_prop
  exact
    hOn.comp_continuous hg
      (fun y ↦ by
        simpa only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          add_zero] using hτ)

/--
Input/assumptions: a nontrivial character and a vertical line strictly right of `Re s = 1`.
Conclusion: the primitive reciprocal contour kernel is continuous on that line.
Content: as above, with the additional harmless factor `s - 1` nonzero on the line.
Role: this provides the measurability input for the reciprocal right-edge integral.
-/
theorem continuous_dirichletReciprocalContourKernel_line {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {τ : ℝ} (hτ : 1 < τ) :
    Continuous
      (fun y : ℝ ↦
        dirichletReciprocalContourKernel x χ
          ((τ : ℂ) + y * Complex.I)) := by
  have hOn :
    ContinuousOn
      (dirichletReciprocalContourKernel x χ)
      {s : ℂ | 1 < s.re} := by
    intro s hs
    simp only [Set.mem_ofPred_eq] at hs
    have hs0 : s ≠ 0 := by
      intro h; rw [h, Complex.zero_re] at hs; linarith
    have hs1 : s ≠ 1 := by
      intro h; rw [h, Complex.one_re] at hs; linarith
    have hL : DirichletCharacter.LFunction χ s ≠ 0 :=
      DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) hs.le
    exact
      ContinuousAt.continuousWithinAt
        (differentiableAt_dirichletReciprocalContourKernel
            hx hχ hs0 hs1 hL).continuousAt
  have hg : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) := by fun_prop
  exact
    hOn.comp_continuous hg
      (fun y ↦ by
        simpa only [Set.mem_ofPred_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
          Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
          add_zero] using hτ)

/--
Input/assumptions: a nontrivial character, `x > 0`, and a right vertical line `Re s = τ > 1`.
Conclusion: the primitive logarithmic contour kernel is integrable on the whole line.
Content: absolute convergence bounds its logarithmic derivative by the von Mangoldt series and
the Mellin weight supplies an integrable majorant.
Role: it removes the primitive right-edge integrability part of downstream explicit-formula field.
-/
theorem integrable_dirichletLogContourKernel {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {τ : ℝ} (hτ : 1 < τ) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦
        dirichletLogContourKernel x χ
          ((τ : ℂ) + y * Complex.I)) := by
  set C : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ with hC_def
  have hxτ : (0 : ℝ) < x ^ τ := Real.rpow_pos_of_pos hx τ
  have hτ0 : τ ≠ 0 := by linarith
  apply
    MeasureTheory.Integrable.mono'
      (((General.verticalIntegrable_mellinLogKernel
              hτ0).norm).const_mul
        (C * x ^ τ))
  · exact
      (continuous_dirichletLogContourKernel_line
          hx χ hχ hτ).aestronglyMeasurable
  · filter_upwards with y
    set s : ℂ := (τ : ℂ) + y * Complex.I with hs_def
    have hAle :
      ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ C :=
      norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum
        χ hτ y
    have hAle' :
      ‖-(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)‖ ≤ C := by
      simpa only [← neg_div] using hAle
    have hBnorm : ‖(x : ℂ) ^ s‖ = x ^ τ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      rw [hs_def]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    have hKnorm : ‖s⁻¹ ^ 2‖ = (‖s‖ ^ 2)⁻¹ := by rw [norm_pow, norm_inv, inv_pow]
    change
      ‖dirichletLogContourKernel x χ s‖ ≤
        C * x ^ τ * ‖s⁻¹ ^ 2‖
    unfold dirichletLogContourKernel
    rw [norm_div, norm_mul, hBnorm, norm_pow, div_eq_mul_inv, hKnorm]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAle' hxτ.le) (by positivity)

/--
Input/assumptions: a nontrivial character, `x > 0`, and a right vertical line `Re s = τ > 1`.
Conclusion: the primitive reciprocal contour kernel is integrable on the whole line.
Content: the same von Mangoldt bound is paired with the shifted reciprocal Mellin weight.
Role: it supplies the second right-edge integral required by the primitive downstream formula.
-/
theorem integrable_dirichletReciprocalContourKernel {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {τ : ℝ} (hτ : 1 < τ) :
    MeasureTheory.Integrable
      (fun y : ℝ ↦
        dirichletReciprocalContourKernel x χ
          ((τ : ℂ) + y * Complex.I)) := by
  set C : ℝ := ∑' n : ℕ, ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ τ with hC_def
  set σ : ℝ := τ - 1 with hσ_def
  have hxσ : (0 : ℝ) < x ^ σ := Real.rpow_pos_of_pos hx σ
  have hσ0 : σ ≠ 0 := by
    rw [hσ_def]; intro h; linarith [sub_eq_zero.mp h]
  have hσ1 : σ ≠ -1 := by
    rw [hσ_def]; intro h; linarith
  apply
    MeasureTheory.Integrable.mono'
      (((General.verticalIntegrable_mellinReciprocalKernel hσ0
              hσ1).norm).const_mul
        (C * x ^ σ))
  · exact
      (continuous_dirichletReciprocalContourKernel_line
          hx χ hχ hτ).aestronglyMeasurable
  · filter_upwards with y
    set s : ℂ := (τ : ℂ) + y * Complex.I with hs_def
    set s' : ℂ := (σ : ℂ) + y * Complex.I with hs'_def
    have hAle :
      ‖-deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s‖ ≤ C :=
      norm_neg_deriv_div_dirichletLFunction_le_vonMangoldt_tsum
        χ hτ y
    have hAle' :
      ‖-(deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s)‖ ≤ C := by
      simpa only [← neg_div] using hAle
    have hBnorm : ‖(x : ℂ) ^ (s - 1)‖ = x ^ σ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      rw [hs_def, hσ_def]
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re]
    have hDenomEq : s * (s - 1) = s' * (s' + 1) := by
      rw [hs_def, hs'_def, hσ_def]
      push_cast
      ring
    change
      ‖dirichletReciprocalContourKernel x χ s‖ ≤
        C * x ^ σ * ‖(s' * (s' + 1))⁻¹‖
    unfold dirichletReciprocalContourKernel
    rw [norm_div, norm_mul, hBnorm, div_eq_mul_inv, ← hDenomEq, ← norm_inv]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAle' hxσ.le) (norm_nonneg _)

/--
Input/assumptions: a nontrivial character, `x > 0`, and `τ > 1`.
Conclusion: its logarithmic primitive truncated right-edge integral converges to the full integral.
Content: invoke the general interval-integral exhaustion theorem using established
integrability.
Role: this connects the finite rectangle's right edge to the primitive downstream integral
interface.
-/
theorem tendsto_intervalIntegral_dirichletLogContourKernel {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {τ : ℝ} (hτ : 1 < τ) :
    Filter.Tendsto
      (fun T : ℝ ↦
        ∫ y in (-T)..T,
          dirichletLogContourKernel x χ
            ((τ : ℂ) + y * Complex.I))
      Filter.atTop
      (nhds
        (∫ y : ℝ,
          dirichletLogContourKernel x χ
            ((τ : ℂ) + y * Complex.I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_dirichletLogContourKernel hx χ
      hχ hτ)
    Analysis.tendsto_neg_atTop_atBot' Filter.tendsto_id

/--
Input/assumptions: a nontrivial character, `x > 0`, and `τ > 1`.
Conclusion: its reciprocal primitive truncated right-edge integral converges to the full integral.
Content: the reciprocal integrability theorem feeds the same interval-exhaustion interface.
Role: this is the second finite-rectangle right-edge connection required by the primitive
downstream interface
explicit formula.
-/
theorem tendsto_intervalIntegral_dirichletReciprocalContourKernel {N : ℕ} [NeZero N] {x : ℝ}
    (hx : 0 < x) (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) {τ : ℝ} (hτ : 1 < τ) :
    Filter.Tendsto
      (fun T : ℝ ↦
        ∫ y in (-T)..T,
          dirichletReciprocalContourKernel x χ
            ((τ : ℂ) + y * Complex.I))
      Filter.atTop
      (nhds
        (∫ y : ℝ,
          dirichletReciprocalContourKernel x χ
            ((τ : ℂ) + y * Complex.I))) :=
  MeasureTheory.intervalIntegral_tendsto_integral
    (integrable_dirichletReciprocalContourKernel
      hx χ hχ hτ)
    Analysis.tendsto_neg_atTop_atBot' Filter.tendsto_id

/--
Input/assumptions: a zero location, multiplicity, and its nonvanishing analytic local factor.
Conclusion: the reciprocal kernel with the local `L'/L` pole removed.
Content: the factor `(s - ρ)` is absorbed into the numerator of the logarithmic derivative.
Role: its center value gives the reciprocal primitive zero contribution.
-/
noncomputable def dirichletReciprocalZeroRegularization (x : ℝ) (ρ : ℂ) (m : ℕ) (g : ℂ → ℂ)
    (s : ℂ) : ℂ :=
  -((m : ℂ) + (s - ρ) * logDeriv g s) * (x : ℂ) ^ (s - 1) / (s * (s - 1))

/--
Input/assumptions: a zero location, multiplicity, and its nonvanishing analytic local factor.
Conclusion: the logarithmic kernel with the local `L'/L` pole removed.
Content: the same pole cancellation is paired with the logarithmic Mellin weight.
Role: its center value gives the logarithmic primitive zero contribution.
-/
noncomputable def dirichletLogZeroRegularization (x : ℝ) (ρ : ℂ) (m : ℕ) (g : ℂ → ℂ) (s : ℂ) : ℂ :=
  -((m : ℂ) + (s - ρ) * logDeriv g s) * (x : ℂ) ^ s / s ^ 2

/--
Input/assumptions: a nontrivial even character and any real cutoff.
Conclusion: local zero data makes `s²` times the reciprocal kernel equal its regularization.
Content: substitute the logarithmic-derivative local factorization at the forced zero and cancel.
Role: connects the even trivial zero to the shared double-pole contour API.
-/
theorem exists_eventuallyEq_dirichletReciprocalEvenZeroRegularization {N : ℕ} [NeZero N] (x : ℝ)
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (heven : χ.Even) :
    ∃ g : ℂ → ℂ,
      0 <
          dirichletLFunctionZeroMultiplicity χ
            0 ∧
        AnalyticAt ℂ g 0 ∧
        g 0 ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin 0 ({0}ᶜ : Set ℂ))
          (fun s ↦
            (s - 0) ^ 2 *
              dirichletReciprocalContourKernel x
                χ s)
          (dirichletReciprocalEvenZeroRegularization
            x
            (dirichletLFunctionZeroMultiplicity
              χ 0)
            g) := by
  obtain ⟨g, hpos, hganalytic, hgzero, hlog⟩ :=
    exists_eventuallyEq_logDeriv_dirichletLFunction_at_zero
      hne
      (dirichletLFunction_zero_of_even hne
        heven)
  refine ⟨g, hpos, hganalytic, hgzero, ?_⟩
  have honeNhds : ∀ᶠ s : ℂ in nhds 0, s ≠ 1 := compl_singleton_mem_nhds (by norm_num only)
  have hone : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ), s ≠ 1 :=
    honeNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hlog, hone, eventually_mem_nhdsWithin] with s hlogs hs1 hs0
  have hlogs' :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      (dirichletLFunctionZeroMultiplicity χ 0 :
            ℂ) /
          (s - 0) +
        logDeriv g s := by
    rw [← logDeriv_apply]
    exact hlogs
  unfold dirichletReciprocalContourKernel
    dirichletReciprocalEvenZeroRegularization
  rw [hlogs']
  have hs0' : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs0
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp only [sub_zero]
  field_simp

/--
Input/assumptions: a nontrivial even character and any real cutoff.
Conclusion: local zero data makes `s³` times the logarithmic kernel equal its regularization.
Content: substitute the logarithmic-derivative local factorization at the forced zero and cancel.
Role: connects the even trivial zero to the triple-pole contour API.
-/
theorem exists_eventuallyEq_dirichletLogEvenZeroRegularization {N : ℕ} [NeZero N] (x : ℝ)
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (heven : χ.Even) :
    ∃ g : ℂ → ℂ,
      0 <
          dirichletLFunctionZeroMultiplicity χ
            0 ∧
        AnalyticAt ℂ g 0 ∧
        g 0 ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin 0 ({0}ᶜ : Set ℂ))
          (fun s ↦
            (s - 0) ^ 3 *
              dirichletLogContourKernel x χ s)
          (dirichletLogEvenZeroRegularization x
            (dirichletLFunctionZeroMultiplicity
              χ 0)
            g) := by
  obtain ⟨g, hpos, hganalytic, hgzero, hlog⟩ :=
    exists_eventuallyEq_logDeriv_dirichletLFunction_at_zero
      hne
      (dirichletLFunction_zero_of_even hne
        heven)
  refine ⟨g, hpos, hganalytic, hgzero, ?_⟩
  filter_upwards [hlog, eventually_mem_nhdsWithin] with s hlogs hs0
  have hlogs' :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      (dirichletLFunctionZeroMultiplicity χ 0 :
            ℂ) /
          (s - 0) +
        logDeriv g s := by
    rw [← logDeriv_apply]
    exact hlogs
  unfold dirichletLogContourKernel
    dirichletLogEvenZeroRegularization
  rw [hlogs']
  have hs0' : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs0
  simp only [sub_zero]
  field_simp

/--
Input/assumptions: an even nontrivial character and positive cutoff.
Conclusion: some centered square at zero evaluates the reciprocal boundary integral.
Content: the forced local zero yields a double-pole regularization, consumed by the square API.
Role: completes the even reciprocal lower-Mellin local certificate.
-/
theorem exists_dirichletRectangleBoundaryIntegral_reciprocal_zero_of_even {N : ℕ} [NeZero N] {x : ℝ}
    (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) (heven : χ.Even) :
    ∃ R : ℝ,
      0 < R ∧
        ∃ g : ℂ → ℂ,
          RectangleGeometry.rectangleBoundaryIntegral
              (dirichletReciprocalContourKernel
                x χ)
              (RectangleGeometry.centeredSquareLower 0 R)
              (RectangleGeometry.centeredSquareUpper 0 R) =
            2 * Real.pi * Complex.I *
              deriv
                (dirichletReciprocalEvenZeroRegularization
                  x
                  (dirichletLFunctionZeroMultiplicity
                    χ 0)
                  g)
                0 := by
  obtain ⟨g, -, hganalytic, hgzero, heq⟩ :=
    exists_eventuallyEq_dirichletReciprocalEvenZeroRegularization
      x hne heven
  obtain ⟨R, hR, hboundary⟩ :=
    RectangleGeometry.exists_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv
      (analyticAt_dirichletReciprocalEvenZeroRegularization
        hx
        (dirichletLFunctionZeroMultiplicity χ 0)
        hganalytic hgzero)
      heq
  exact ⟨R, hR, g, hboundary⟩

/--
Input/assumptions: positive `x`, a center away from `0,1`, and analytic nonvanishing local data.
Conclusion: the reciprocal zero regularization is analytic at its center.
Content: its log derivative, complex power, and nonzero Mellin denominator are all analytic there.
Role: makes the reciprocal local pole cancellation usable by the rectangle principal-parts API.
-/
theorem analyticAt_dirichletReciprocalZeroRegularization {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ 1) (m : ℕ) {g : ℂ → ℂ} (hganalytic : AnalyticAt ℂ g ρ) (hgzero : g ρ ≠ 0) :
    AnalyticAt ℂ
      (dirichletReciprocalZeroRegularization x ρ
        m g)
      ρ := by
  have hlog : AnalyticAt ℂ (logDeriv g) ρ := by
    unfold logDeriv
    exact hganalytic.deriv.div hganalytic hgzero
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hconst : AnalyticAt ℂ (fun _ : ℂ ↦ (x : ℂ)) ρ := analyticAt_const
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) ρ :=
    hconst.cpow (analyticAt_id.sub analyticAt_const) hxslit
  have hdenominator : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
  unfold dirichletReciprocalZeroRegularization
  fun_prop (disch := assumption)

/--
Input/assumptions: positive `x`, a center away from zero, and analytic nonvanishing local data.
Conclusion: the logarithmic zero regularization is analytic at its center.
Content: it is the product of the pole-cancelled log derivative and the analytic logarithmic weight.
Role: makes the logarithmic local pole cancellation usable by the rectangle principal-parts API.
-/
theorem analyticAt_dirichletLogZeroRegularization {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0) (m : ℕ)
    {g : ℂ → ℂ} (hganalytic : AnalyticAt ℂ g ρ) (hgzero : g ρ ≠ 0) :
    AnalyticAt ℂ
      (dirichletLogZeroRegularization x ρ m g)
      ρ := by
  have hlog : AnalyticAt ℂ (logDeriv g) ρ := by
    unfold logDeriv
    exact hganalytic.deriv.div hganalytic hgzero
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hconst : AnalyticAt ℂ (fun _ : ℂ ↦ (x : ℂ)) ρ := analyticAt_const
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) ρ := hconst.cpow analyticAt_id hxslit
  have hdenominator : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ0
  unfold dirichletLogZeroRegularization
  fun_prop (disch := assumption)

/--
Input/assumptions: arbitrary `x,ρ,m,g`; no regularity or pole-avoidance assumptions.
Conclusion: the reciprocal regularization's center value is the designated zero contribution.
Content: evaluate the absorbed-pole numerator at `s = ρ`.
Role: identifies the residue coefficient used by the finite reciprocal ledger.
-/
theorem dirichletReciprocalZeroRegularization_self (x : ℝ) (ρ : ℂ) (m : ℕ) (g : ℂ → ℂ) :
    dirichletReciprocalZeroRegularization x ρ m
        g ρ =
      -(m : ℂ) * (x : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) := by
  simp only [dirichletReciprocalZeroRegularization,
    sub_self, zero_mul, add_zero, neg_mul]

/--
Input/assumptions: arbitrary `x,ρ,m,g`; no regularity or pole-avoidance assumptions.
Conclusion: the logarithmic regularization's center value is the designated zero contribution.
Content: evaluate the absorbed-pole numerator at `s = ρ`.
Role: identifies the residue coefficient used by the finite logarithmic ledger.
-/
theorem dirichletLogZeroRegularization_self (x : ℝ) (ρ : ℂ) (m : ℕ) (g : ℂ → ℂ) :
    dirichletLogZeroRegularization x ρ m g ρ =
      -(m : ℂ) * (x : ℂ) ^ ρ / ρ ^ 2 := by
  simp only [dirichletLogZeroRegularization,
    sub_self, zero_mul, add_zero, neg_mul]

/--
Input/assumptions: a nontrivial character, an ordinary `L`-zero away from `0,1`,
and any real `x`.
Conclusion: after multiplication by `s - ρ`, the reciprocal kernel agrees locally with its
zero-regularization expression; analyticity additionally requires positive `x`.
Content: substitute the local logarithmic-derivative expansion and clear nonzero denominators.
Role: supplies the simple-principal-part certificate for the reciprocal rectangle residue API.
-/
theorem exists_eventuallyEq_reciprocalKernel_dirichletLFunctionZeroRegularization {N : ℕ} [NeZero N]
    (x : ℝ) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ g : ℂ → ℂ,
      0 <
          dirichletLFunctionZeroMultiplicity χ
            ρ ∧
        AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ))
          (fun s ↦
            (s - ρ) *
              dirichletReciprocalContourKernel x
                χ s)
          (dirichletReciprocalZeroRegularization
            x ρ
            (dirichletLFunctionZeroMultiplicity
              χ ρ)
            g) := by
  obtain ⟨g, hpos, hganalytic, hgzero, hlog⟩ :=
    exists_eventuallyEq_logDeriv_dirichletLFunction_at_zero
      hχ hzero
  refine ⟨g, hpos, hganalytic, hgzero, ?_⟩
  have hzeroNhds : ∀ᶠ s : ℂ in nhds ρ, s ≠ 0 := compl_singleton_mem_nhds hρ0
  have hzeroEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), s ≠ 0 :=
    hzeroNhds.filter_mono nhdsWithin_le_nhds
  have honeNhds : ∀ᶠ s : ℂ in nhds ρ, s ≠ 1 := compl_singleton_mem_nhds hρ1
  have honeEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), s ≠ 1 :=
    honeNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hlog, hzeroEventually, honeEventually, eventually_mem_nhdsWithin] with s hlogs hs0
    hs1 hsρ
  have hlogs' :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      (dirichletLFunctionZeroMultiplicity χ ρ :
            ℂ) /
          (s - ρ) +
        logDeriv g s := by
    rw [← logDeriv_apply]
    exact hlogs
  rw [dirichletReciprocalContourKernel,
    dirichletReciprocalZeroRegularization,
    hlogs']
  have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsρ)
  field_simp

/--
Input/assumptions: a nontrivial character, an ordinary `L`-zero away from `0`,
and any real `x`.
Conclusion: after multiplication by `s - ρ`, the logarithmic kernel agrees locally with its
zero-regularization expression; analyticity additionally requires positive `x`.
Content: substitute the local logarithmic-derivative expansion and clear nonzero denominators.
Role: supplies the simple-principal-part certificate for the logarithmic rectangle residue API.
-/
theorem exists_eventuallyEq_logKernel_dirichletLFunctionZeroRegularization {N : ℕ} [NeZero N]
    (x : ℝ) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ g : ℂ → ℂ,
      0 <
          dirichletLFunctionZeroMultiplicity χ
            ρ ∧
        AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ))
          (fun s ↦
            (s - ρ) *
              dirichletLogContourKernel x χ s)
          (dirichletLogZeroRegularization x ρ
            (dirichletLFunctionZeroMultiplicity
              χ ρ)
            g) := by
  obtain ⟨g, hpos, hganalytic, hgzero, hlog⟩ :=
    exists_eventuallyEq_logDeriv_dirichletLFunction_at_zero
      hχ hzero
  refine ⟨g, hpos, hganalytic, hgzero, ?_⟩
  have hzeroNhds : ∀ᶠ s : ℂ in nhds ρ, s ≠ 0 := compl_singleton_mem_nhds hρ0
  have hzeroEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), s ≠ 0 :=
    hzeroNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hlog, hzeroEventually, eventually_mem_nhdsWithin] with s hlogs hs0 hsρ
  have hlogs' :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      (dirichletLFunctionZeroMultiplicity χ ρ :
            ℂ) /
          (s - ρ) +
        logDeriv g s := by
    rw [← logDeriv_apply]
    exact hlogs
  rw [dirichletLogContourKernel,
    dirichletLogZeroRegularization, hlogs']
  have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsρ)
  field_simp

/--
Input/assumptions: `x > 0`, a nontrivial character, and an ordinary `L`-zero away from `0,1`.
Conclusion: one positive radius works for both local kernel residue formulas and every smaller
positive centered square.
Content: take the minimum of the two radii supplied by the shared simple-pole rectangle theorem.
Role: this common-radius form is the exact local datum required for a simultaneous grid subdivision.
-/
theorem exists_radius_forall_dirichletRectangleBoundaryIntegrals_eq_zeroContributions {N : ℕ}
    [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ 1) (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral
                  (dirichletReciprocalContourKernel
                    x χ)
                  (RectangleGeometry.centeredSquareLower ρ r)
                  (RectangleGeometry.centeredSquareUpper ρ r) =
                2 * Real.pi * Complex.I *
                  (-(dirichletLFunctionZeroMultiplicity
                            χ ρ :
                          ℂ) *
                      (x : ℂ) ^ (ρ - 1) /
                    (ρ * (ρ - 1))) ∧
              RectangleGeometry.rectangleBoundaryIntegral
                  (dirichletLogContourKernel x
                    χ)
                  (RectangleGeometry.centeredSquareLower ρ r)
                  (RectangleGeometry.centeredSquareUpper ρ r) =
                2 * Real.pi * Complex.I *
                  (-(dirichletLFunctionZeroMultiplicity
                            χ ρ :
                          ℂ) *
                      (x : ℂ) ^ ρ /
                    ρ ^ 2) := by
  obtain ⟨g1, -, hganalytic1, hgzero1, heq1⟩ :=
    exists_eventuallyEq_reciprocalKernel_dirichletLFunctionZeroRegularization
      x hχ hρ0 hρ1 hzero
  obtain ⟨g2, -, hganalytic2, hgzero2, heq2⟩ :=
    exists_eventuallyEq_logKernel_dirichletLFunctionZeroRegularization
      x hχ hρ0 hzero
  have hh1 :
    AnalyticAt ℂ
      (dirichletReciprocalZeroRegularization x ρ
        (dirichletLFunctionZeroMultiplicity χ ρ)
        g1)
      ρ :=
    analyticAt_dirichletReciprocalZeroRegularization
      hx hρ0 hρ1 _ hganalytic1 hgzero1
  have hh2 :
    AnalyticAt ℂ
      (dirichletLogZeroRegularization x ρ
        (dirichletLFunctionZeroMultiplicity χ ρ)
        g2)
      ρ :=
    analyticAt_dirichletLogZeroRegularization hx
      hρ0 _ hganalytic2 hgzero2
  obtain ⟨R1, hR1, h1⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul
      hh1 heq1
  obtain ⟨R2, hR2, h2⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul
      hh2 heq2
  let R := min R1 R2
  have hR : 0 < R := lt_min hR1 hR2
  refine ⟨R, hR, fun r hr hrR ↦ ?_⟩
  have hR1' : r ≤ R1 := hrR.trans (min_le_left _ _)
  have hR2' : r ≤ R2 := hrR.trans (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · rw [h1 r hr hR1',
      dirichletReciprocalZeroRegularization_self]
  · rw [h2 r hr hR2',
      dirichletLogZeroRegularization_self]

/--
**the local residue step**: the reciprocal-kernel residue at any point of the primitive singularity
ledger.
Input/assumptions: a nontrivial character and any real `x`; the analytic residue
interpretation at Mellin points is certified separately under the stated contour hypotheses.
Conclusion: a single function on `ℂ` giving the reciprocal-kernel residue at `s = 0` (a
parity-dependent combined residue, since an even character's forced zero at `0` coincides with the
Mellin pole there), `s = 1` (the Mellin residue), and any other point (the ordinary `L`-zero
contribution, `0` if `s` is not actually a zero).
Content: `s = 0` branches on `χ.Even`/`χ.Odd`; the even branch fixes one witness `g` (via
`Classical.choose`) for the local factorization and differentiates the shared double-pole
regularization, matching
`DirichletLFunction.exists_dirichletRectangleBoundaryIntegral_reciprocal_zero_of_even`'s
existential exactly so the two agree pointwise
(`DirichletLFunction.dirichletReciprocalResidueAt_zero_of_even`).
Role: this is the `res` function fed to the generic finite residue theorem assembly
(`RectangleGeometry.rectangleBoundaryIntegral_eq_sum_res`) once the primitive reciprocal finite
contour identity is
assembled.
-/
noncomputable def dirichletReciprocalResidueAt {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) (s : ℂ) : ℂ := by
  classical
    exact
    if s = 0 then
      if h : χ.Even then
        deriv
          (dirichletReciprocalEvenZeroRegularization
            x
            (dirichletLFunctionZeroMultiplicity
              χ 0)
            (Classical.choose
              (exists_eventuallyEq_dirichletReciprocalEvenZeroRegularization
                x hne h)))
          0
      else
        dirichletReciprocalMellinZeroRegularization
          x χ 0
    else
      if s = 1 then
        dirichletReciprocalOneRegularization x χ
          1
      else
        dirichletLFunctionReciprocalZeroContribution
          x χ s

/-- At `s = 0` for an even character, the residue unfolds to the chosen even-zero derivative. -/
theorem dirichletReciprocalResidueAt_zero_of_even {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) (heven : χ.Even) :
    dirichletReciprocalResidueAt hne x 0 =
      deriv
        (dirichletReciprocalEvenZeroRegularization
          x
          (dirichletLFunctionZeroMultiplicity χ
            0)
          (Classical.choose
            (exists_eventuallyEq_dirichletReciprocalEvenZeroRegularization
              x hne heven)))
        0 := by
  classical
  unfold dirichletReciprocalResidueAt
  rw [ite_eq_left rfl, dite_eq_left heven]

/-- At `s = 0` for an odd character, the residue unfolds to the odd Mellin regularization. -/
theorem dirichletReciprocalResidueAt_zero_of_odd {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) (hodd : χ.Odd) :
    dirichletReciprocalResidueAt hne x 0 =
      dirichletReciprocalMellinZeroRegularization
        x χ 0 := by
  classical
  unfold dirichletReciprocalResidueAt
  rw [ite_eq_left rfl, dite_eq_right hodd.not_even]

/-- At `s = 1`, the residue unfolds to the Mellin-one regularization. -/
theorem dirichletReciprocalResidueAt_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) :
    dirichletReciprocalResidueAt hne x 1 =
      dirichletReciprocalOneRegularization x χ
        1 := by
  classical
  unfold dirichletReciprocalResidueAt
  rw [ite_eq_right (by norm_num only), ite_eq_left rfl]

/-- Away from `0` and `1`, the residue unfolds to the ordinary zero contribution. -/
theorem dirichletReciprocalResidueAt_zero_ne_one {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hne : χ ≠ 1) (x : ℝ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    dirichletReciprocalResidueAt hne x s =
      dirichletLFunctionReciprocalZeroContribution
        x χ s := by
  classical
  unfold dirichletReciprocalResidueAt
  rw [ite_eq_right hs0, ite_eq_right hs1]

/--
**the local boundary step (`s = 0`)**: some centered square's reciprocal boundary integral equals
`2πi` times the
residue function's value at `0`, for either parity.
-/
theorem exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_residueAt_zero {N : ℕ}
    [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral
                (dirichletReciprocalContourKernel
                  x χ)
                (RectangleGeometry.centeredSquareLower 0 r)
                (RectangleGeometry.centeredSquareUpper 0 r) =
              2 * Real.pi * Complex.I *
                dirichletReciprocalResidueAt hne
                  x 0 := by
  classical
  rcases χ.even_or_odd with heven | hodd
  · rw [dirichletReciprocalResidueAt_zero_of_even
        hne x heven]
    obtain ⟨-, hganalytic, hgzero, heq⟩ :=
      Classical.choose_spec
        (exists_eventuallyEq_dirichletReciprocalEvenZeroRegularization
          x hne heven)
    exact
      RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv
        (analyticAt_dirichletReciprocalEvenZeroRegularization
          hx _ hganalytic hgzero)
        heq
  · rw [dirichletReciprocalResidueAt_zero_of_odd
        hne x hodd]
    exact
      exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_zero_of_primitive_odd
        hx hprimitive hne hodd

/--
**the local boundary step (general form)**: some centered square's reciprocal boundary integral
equals `2πi`
times the residue function's value, at any point of the primitive singularity ledger (`s = 0`,
`s = 1`, or an ordinary `L`-zero away from both).
-/
theorem exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_residueAt {N : ℕ}
    [NeZero N] {x : ℝ} (hx : 0 < x) {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive)
    (hne : χ ≠ 1) {s : ℂ} (hs : s = 0 ∨ s = 1 ∨ DirichletCharacter.LFunction χ s = 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral
                (dirichletReciprocalContourKernel
                  x χ)
                (RectangleGeometry.centeredSquareLower s r)
                (RectangleGeometry.centeredSquareUpper s r) =
              2 * Real.pi * Complex.I *
                dirichletReciprocalResidueAt hne
                  x s := by
  rcases hs with rfl | rfl | hzero
  · exact
      exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_residueAt_zero
        hx hprimitive hne
  · rw [dirichletReciprocalResidueAt_one hne x]
    exact
      exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_eq_residueAtOne
        hx hne
  · by_cases hs0 : s = 0
    · subst hs0
      exact
        exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_residueAt_zero
          hx hprimitive hne
    · by_cases hs1 : s = 1
      · subst hs1
        rw [dirichletReciprocalResidueAt_one hne
            x]
        exact
          exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_eq_residueAtOne
            hx hne
      · rw [dirichletReciprocalResidueAt_zero_ne_one
            hne x hs0 hs1]
        exact
          (exists_radius_forall_dirichletRectangleBoundaryIntegrals_eq_zeroContributions
                hx hne hs0 hs1 hzero).imp
            fun R hR => ⟨hR.1, fun r hr hrR => (hR.2 r hr hrR).1⟩

/--
Input/assumptions: a horizontal segment stays in the outer rectangle and avoids all primitive
singularity-ledger imaginary coordinates.
Conclusion: both primitive contour kernels are interval-integrable along the segment.
Content: ledger avoidance gives pointwise regularity, hence continuity of each differentiable
kernel on the compact interval.
Role: is the horizontal edge input for a finite primitive grid subdivision.
-/
theorem intervalIntegrable_dirichletKernels_horizontal {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {z w : ℂ} {c a b : ℝ} (ha : a ∈ Set.uIcc z.re w.re)
    (hb : b ∈ Set.uIcc z.re w.re) (hc : c ∈ Set.uIcc z.im w.im)
    (havoid :
      ∀
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hχ z w,
        s.im ≠ c) :
    IntervalIntegrable
        (fun t : ℝ ↦
          dirichletReciprocalContourKernel x χ
            (t + c * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable
        (fun t : ℝ ↦
          dirichletLogContourKernel x χ
            (t + c * Complex.I))
        MeasureTheory.volume a b := by
  have hregular :=
    horizontal_segment_subset_dirichletLFunctionContourRegularSet
      ha hb hc havoid
  constructor <;>
    apply
      RectangleGeometry.intervalIntegrable_horizontal_of_continuousAt <;>
    intro t ht
  · have hs' :
      (((t : ℂ) + c * Complex.I) ≠ 0 ∧ ((t : ℂ) + c * Complex.I) ≠ 1) ∧
        DirichletCharacter.LFunction χ ((t : ℂ) + c * Complex.I) ≠ 0 := by
      simpa only [ne_eq,
        dirichletLFunctionContourRegularSet,
        Set.preimage_compl, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        Set.mem_preimage] using hregular t ht
    have hd :=
      differentiableAt_dirichletReciprocalContourKernel
        hx hχ hs'.1.1 hs'.1.2 hs'.2
    exact hd.continuousAt
  · have hs' :
      (((t : ℂ) + c * Complex.I) ≠ 0 ∧ ((t : ℂ) + c * Complex.I) ≠ 1) ∧
        DirichletCharacter.LFunction χ ((t : ℂ) + c * Complex.I) ≠ 0 := by
      simpa only [ne_eq,
        dirichletLFunctionContourRegularSet,
        Set.preimage_compl, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        Set.mem_preimage] using hregular t ht
    exact
      (differentiableAt_dirichletLogContourKernel
          hx hχ hs'.1.1 hs'.2).continuousAt

/--
Input/assumptions: a vertical segment stays in the outer rectangle and avoids all primitive
singularity-ledger real coordinates.
Conclusion: both primitive contour kernels are interval-integrable along the segment.
Content: this is the vertical counterpart of the horizontal continuity argument.
Role: completes the coordinate-edge input for a finite primitive grid subdivision.
-/
theorem intervalIntegrable_dirichletKernels_vertical {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {z w : ℂ} {c a b : ℝ} (hc : c ∈ Set.uIcc z.re w.re)
    (ha : a ∈ Set.uIcc z.im w.im) (hb : b ∈ Set.uIcc z.im w.im)
    (havoid :
      ∀
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hχ z w,
        s.re ≠ c) :
    IntervalIntegrable
        (fun t : ℝ ↦
          dirichletReciprocalContourKernel x χ
            (c + t * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable
        (fun t : ℝ ↦
          dirichletLogContourKernel x χ
            (c + t * Complex.I))
        MeasureTheory.volume a b := by
  have hregular :=
    vertical_segment_subset_dirichletLFunctionContourRegularSet
      hc ha hb havoid
  constructor <;>
    apply
      RectangleGeometry.intervalIntegrable_vertical_of_continuousAt <;>
    intro t ht
  · have hs' :
      ((c + t * Complex.I) ≠ 0 ∧ (c + t * Complex.I) ≠ 1) ∧
        DirichletCharacter.LFunction χ (c + t * Complex.I) ≠ 0 := by
      simpa only [ne_eq,
        dirichletLFunctionContourRegularSet,
        Set.preimage_compl, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        Set.mem_preimage] using hregular t ht
    have hd :=
      differentiableAt_dirichletReciprocalContourKernel
        hx hχ hs'.1.1 hs'.1.2 hs'.2
    exact hd.continuousAt
  · have hs' :
      ((c + t * Complex.I) ≠ 0 ∧ (c + t * Complex.I) ≠ 1) ∧
        DirichletCharacter.LFunction χ (c + t * Complex.I) ≠ 0 := by
      simpa only [ne_eq,
        dirichletLFunctionContourRegularSet,
        Set.preimage_compl, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
        Set.mem_preimage] using hregular t ht
    exact
      (differentiableAt_dirichletLogContourKernel
          hx hχ hs'.1.1 hs'.2).continuousAt

/--
Input/assumptions: a nontrivial character and positive real `x`.
Conclusion: the primitive reciprocal kernel is differentiable on its regular locus.
Content: specialize the pointwise differentiability theorem to each regular point.
Role: enables Cauchy--Goursat on every primitive regular rectangle.
-/
theorem differentiableOn_dirichletReciprocalContourKernel {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ
      (dirichletReciprocalContourKernel x χ)
      (dirichletLFunctionContourRegularSet
        χ) := by
  intro s hs
  have hs' : (s ≠ 0 ∧ s ≠ 1) ∧ DirichletCharacter.LFunction χ s ≠ 0 := by
    simpa only [ne_eq,
      dirichletLFunctionContourRegularSet,
      Set.preimage_compl, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_preimage] using hs
  exact
    DifferentiableAt.differentiableWithinAt
      (differentiableAt_dirichletReciprocalContourKernel
        hx hχ hs'.1.1 hs'.1.2 hs'.2)

/--
Input/assumptions: a nontrivial character and positive real `x`.
Conclusion: the primitive logarithmic kernel is differentiable on its regular locus.
Content: specialize the pointwise differentiability theorem to each regular point.
Role: enables the logarithmic Cauchy--Goursat identity on primitive regular rectangles.
-/
theorem differentiableOn_dirichletLogContourKernel {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) :
    DifferentiableOn ℂ
      (dirichletLogContourKernel x χ)
      (dirichletLFunctionContourRegularSet
        χ) := by
  intro s hs
  have hs' : (s ≠ 0 ∧ s ≠ 1) ∧ DirichletCharacter.LFunction χ s ≠ 0 := by
    simpa only [ne_eq,
      dirichletLFunctionContourRegularSet,
      Set.preimage_compl, Set.mem_inter_iff, Set.mem_compl_iff, Set.mem_singleton_iff,
      Set.mem_preimage] using hs
  exact
    DifferentiableAt.differentiableWithinAt
      (differentiableAt_dirichletLogContourKernel
        hx hχ hs'.1.1 hs'.2)

/--
**the integrability step**: coordinate avoidance makes the primitive reciprocal kernel integrable
on every finite
outer grid-coordinate segment.
-/
theorem dirichletReciprocalKernelCoordinateIntegrable {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (havoid :
      grid.LedgerAvoidsCoordinates
        (dirichletLFunctionSingularitiesInRectangle
          χ hne z w)) :
    RectangleGeometry.RectangleGridCoordinateIntegrable
      (dirichletReciprocalContourKernel x χ)
      (z.re :: grid.xcuts ++ [w.re]) (z.im :: grid.ycuts ++ [w.im]) := by
  constructor
  · intro c hc a ha b hb
    exact
      (intervalIntegrable_dirichletKernels_horizontal
          hx hne (grid.xcoordinate_mem_uIcc ha) (grid.xcoordinate_mem_uIcc hb)
          (grid.ycoordinate_mem_uIcc hc) fun s hs hsc ↦ (havoid s hs).2 (hsc ▸ hc)).1
  · intro c hc a ha b hb
    exact
      (intervalIntegrable_dirichletKernels_vertical
          hx hne (grid.xcoordinate_mem_uIcc hc) (grid.ycoordinate_mem_uIcc ha)
          (grid.ycoordinate_mem_uIcc hb) fun s hs hsc ↦ (havoid s hs).1 (hsc ▸ hc)).1

/--
For a primitive nontrivial character, `x > 0`, and an oriented rectangle with strictly
increasing real and imaginary corners, assume every point of its singularity ledger lies
in the open rectangle. Then the reciprocal boundary integral is `2πi` times the residue sum.
Combine the local residue certificates, coordinate-integrable grid, and shrink construction
with `rectangleBoundaryIntegral_eq_sum_res` from `RectangleGeometry`.
-/
theorem dirichletReciprocalFiniteContourIdentity {N : ℕ} [NeZero N] {x : ℝ} (hx : 0 < x)
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im)
    (hopen :
      ∀
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne z w,
        s ∈ RectangleGeometry.rectangleOpenBox z w) :
    RectangleGeometry.rectangleBoundaryIntegral
        (dirichletReciprocalContourKernel x χ) z
        w =
      ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne z w,
        2 * Real.pi * Complex.I *
          dirichletReciprocalResidueAt hne x
            s := by
  set S :=
    dirichletLFunctionSingularitiesInRectangle χ
      hne z w with
    hS_def
  have hclosed : ∀ s ∈ S, s ∈ Rectangle.rectangleClosedBox z w :=
    fun s hs ↦
    (mem_dirichletLFunctionSingularitiesInRectangle_iff.mp
        hs).1
  set grid :=
    RectangleGeometry.generatedStrictGridCuts S z w hre him
      hopen with
    hgrid_def
  set cells :=
    (RectangleGeometry.rectangleGridCells z w grid.xcuts
        grid.ycuts).toFinset with
    hcells_def
  have interior :=
    RectangleGeometry.generatedGridInteriorSeparation S z w hre him
      hopen hclosed
  set assignment := interior.toAssignment with hassignment_def
  have havoidCuts : grid.LedgerAvoidsCuts S :=
    RectangleGeometry.generatedStrictGridCuts_avoidsCuts S z w hre
      him hopen
  have havoid : grid.LedgerAvoidsCoordinates S :=
    grid.ledgerAvoidsCoordinates_of_open hopen havoidCuts
  have hcoordint :=
    dirichletReciprocalKernelCoordinateIntegrable
      hx hne grid havoid
  have hgridint :
    RectangleGeometry.RectangleGridSubdivisionIntegrable
      (dirichletReciprocalContourKernel x χ) z w
      grid.xcuts grid.ycuts := by
    apply
      hcoordint.gridSubdivision List.mem_cons_self
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_true])
        List.mem_cons_self
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_true])
        grid.xcuts grid.ycuts
        (fun c hc ↦ by
          simp only [List.cons_append, List.mem_cons, List.mem_append, hc, List.not_mem_nil,
            or_false, true_or, or_true])
        (fun c hc ↦ by
          simp only [List.cons_append, List.mem_cons, List.mem_append, hc, List.not_mem_nil,
            or_false, true_or, or_true])
  have hsum :
    RectangleGeometry.rectangleBoundaryIntegral
        (dirichletReciprocalContourKernel x χ) z
        w =
      ∑ cell ∈ cells,
        RectangleGeometry.rectangleBoundaryIntegral
          (dirichletReciprocalContourKernel x χ)
          cell.1 cell.2 := by
    rw [RectangleGeometry.rectangleBoundaryIntegral_eq_gridSubdivision
        _ z w grid.xcuts grid.ycuts hgridint,
      RectangleGeometry.rectangleGridSubdivision_eq_sum_toFinset _
        z w grid.xcuts grid.ycuts grid.cells_nodup]
  have hxcuts : ∀ u ∈ grid.xcuts, u ∈ Set.uIcc z.re w.re := fun u hu ↦
    Set.mem_uIcc_of_le (grid.xcuts_inside u hu).1.le (grid.xcuts_inside u hu).2.le
  have hycuts : ∀ v ∈ grid.ycuts, v ∈ Set.uIcc z.im w.im := fun v hv ↦
    Set.mem_uIcc_of_le (grid.ycuts_inside v hv).1.le (grid.ycuts_inside v hv).2.le
  have hdiff :
    ∀ cell ∈ cells,
      ∀ y ∈ Rectangle.rectangleClosedBox cell.1 cell.2,
        y ∉ S →
          DifferentiableAt ℂ
            (dirichletReciprocalContourKernel x
              χ)
            y := by
    intro cell hcell y hy hyS
    have hcellSubset :=
      RectangleGeometry.rectangleGridCells_closedBox_subset hxcuts
        hycuts cell (by simpa only [hcells_def, List.mem_toFinset] using hcell)
    have hyz : y ∈ Rectangle.rectangleClosedBox z w :=
      hcellSubset hy
    have hy' : ¬(y = 0 ∨ y = 1 ∨ DirichletCharacter.LFunction χ y = 0) := fun hmem ↦
      hyS
        (mem_dirichletLFunctionSingularitiesInRectangle_iff.mpr
          ⟨hyz, hmem⟩)
    push Not at hy'
    exact
      differentiableAt_dirichletReciprocalContourKernel
        hx hne hy'.1 hy'.2.1 hy'.2.2
  have hsingular_res :
    ∀ cell ∈ RectangleGeometry.finiteSingularCells S cells,
      RectangleGeometry.rectangleBoundaryIntegral
          (dirichletReciprocalContourKernel x χ)
          cell.1 cell.2 =
        2 * Real.pi * Complex.I *
          dirichletReciprocalResidueAt hne x
            (assignment.pointOfCell cell) := by
    intro cell hcell
    have hcellmem :=
      RectangleGeometry.mem_singularCells_iff.mp hcell
    have hcellOrder :=
      RectangleGeometry.mem_rectangleGridCells_re_lt_im_lt
        grid.xcoordinates_pairwise grid.ycoordinates_pairwise
        (by simpa only [hcells_def, List.mem_toFinset] using hcellmem.1)
    set c := assignment.pointOfCell cell with hc_def
    have hpointS : c ∈ S := assignment.point_mem_ledger cell hcell
    have hpointHyp :=
      (mem_dirichletLFunctionSingularitiesInRectangle_iff.mp
          hpointS).2
    obtain ⟨Rc, hRc, hcert⟩ :=
      exists_radius_forall_dirichletRectangleBoundaryIntegral_reciprocal_residueAt
        hx hprimitive hne hpointHyp
    obtain ⟨ε, hε, hball⟩ := interior.exists_closedBall_pointOfCell_subset_open hcell
    set r := min (ε / 2) (Rc / 2) with hr_def
    have hr : 0 < r := lt_min (by linarith) (by linarith)
    have hball' :
      Metric.closedBall c r ⊆
        RectangleGeometry.rectangleOpenBox cell.1 cell.2 :=
      (Metric.closedBall_subset_closedBall
            (le_trans (min_le_left _ _) (by linarith : ε / 2 ≤ ε))).trans
        hball
    have hcuts :=
      RectangleGeometry.centeredSquare_cuts_inside hcellOrder.1
        hcellOrder.2 hr hball'
    set a := RectangleGeometry.centeredSquareLower c r with ha_def
    set b := RectangleGeometry.centeredSquareUpper c r with hb_def
    have hpoint : c ∈ RectangleGeometry.rectangleOpenBox a b :=
      RectangleGeometry.center_mem_centeredSquare_openBox c hr
    have hdiffCell :
      ∀ y ∈ Rectangle.rectangleClosedBox cell.1 cell.2,
        y ∉ S →
          DifferentiableAt ℂ
            (dirichletReciprocalContourKernel x
              χ)
            y :=
      hdiff cell hcellmem.1
    have hcopen :
      c ∈ RectangleGeometry.rectangleOpenBox cell.1 cell.2 :=
      hball' (Metric.mem_closedBall_self hr.le)
    have havoidSq :=
      RectangleGeometry.centeredSquare_augmented_coordinates_avoid
        hcellOrder.1 hcellOrder.2 hr hcopen
    set xs := cell.1.re :: [a.re, b.re] ++ [cell.2.re] with hxs_def
    set ys := cell.1.im :: [a.im, b.im] ++ [cell.2.im] with hys_def
    have hxmem : ∀ u ∈ xs, u ∈ Set.uIcc cell.1.re cell.2.re := by
      intro u hu
      simp only [hxs_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with (rfl | rfl | rfl) | rfl
      · exact Set.left_mem_uIcc
      · exact Set.mem_uIcc_of_le hcuts.1.le (hcuts.2.1.trans hcuts.2.2.1).le
      · exact Set.mem_uIcc_of_le (hcuts.1.trans hcuts.2.1).le hcuts.2.2.1.le
      · exact Set.right_mem_uIcc
    have hymem : ∀ v ∈ ys, v ∈ Set.uIcc cell.1.im cell.2.im := by
      intro v hv
      simp only [hys_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with (rfl | rfl | rfl) | rfl
      · exact Set.left_mem_uIcc
      · exact Set.mem_uIcc_of_le hcuts.2.2.2.1.le (hcuts.2.2.2.2.1.trans hcuts.2.2.2.2.2).le
      · exact Set.mem_uIcc_of_le (hcuts.2.2.2.1.trans hcuts.2.2.2.2.1).le hcuts.2.2.2.2.2.le
      · exact Set.right_mem_uIcc
    have hcoordint :=
      assignment.kernelCoordinateIntegrable
        (dirichletReciprocalContourKernel x χ)
        hcell hdiffCell xs ys hxmem hymem havoidSq.1 havoidSq.2
    have hgrid3 :
      RectangleGeometry.RectangleGridSubdivisionIntegrable
        (dirichletReciprocalContourKernel x χ)
        cell.1 cell.2 [a.re, b.re] [a.im, b.im] :=
      hcoordint.gridSubdivision
        (by
          simp only [hxs_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, true_or])
        (by
          simp only [hxs_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, or_true])
        (by
          simp only [hys_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, true_or])
        (by
          simp only [hys_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
            or_false, or_true])
        [a.re, b.re] [a.im, b.im]
        (fun u hu ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
          rcases hu with rfl | rfl <;>
            simp only [hxs_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false, true_or, or_true])
        (fun v hv ↦ by
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
          rcases hv with rfl | rfl <;>
            simp only [hys_def, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
              or_false, true_or, or_true])
    have hshrink :=
      assignment.parent_boundaryIntegral_eq_of_shrink
        (dirichletReciprocalContourKernel x χ)
        hcell hcuts.1 hcuts.2.1 hcuts.2.2.1 hcuts.2.2.2.1 hcuts.2.2.2.2.1 hcuts.2.2.2.2.2 hpoint
        hdiffCell hgrid3
    rw [hshrink]
    have hrRc : r ≤ Rc := le_trans (min_le_right _ _) (by linarith : Rc / 2 ≤ Rc)
    exact hcert r hr hrRc
  exact
    RectangleGeometry.rectangleBoundaryIntegral_eq_sum_res
      (dirichletReciprocalContourKernel x χ)
      (fun s ↦
        2 * Real.pi * Complex.I *
          dirichletReciprocalResidueAt hne x s)
      S cells z w assignment hsum hdiff hsingular_res

/--
**the outer-rectangle step**: once both Mellin points lie in the outer rectangle, the residue sum
over the whole
primitive singularity ledger splits off the `s = 1` and `s = 0` contributions, leaving only the
ordinary `L`-zero residues. Splitting this way — rather than trying to write `S` as a disjoint
union of `{0, 1}` and a zero ledger up front — sidesteps the even-character overlap at `s = 0`
(where `L(0,χ) = 0` puts `0` in both the Mellin-pole role and the zero-ledger role): `S` itself
already de-duplicates that overlap as a plain `Finset` union, so erasing `1` and then `0` from `S`
is always well-defined regardless of parity.
-/
theorem dirichletSplitReciprocalSingularitySum {N : ℕ} [NeZero N] (x : ℝ)
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {z w : ℂ}
    (h1 :
      (1 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle
          χ hne z w)
    (h0 :
      (0 : ℂ) ∈
        dirichletLFunctionSingularitiesInRectangle
          χ hne z w) :
    ∑
        s ∈
          dirichletLFunctionSingularitiesInRectangle
            χ hne z w,
        dirichletReciprocalResidueAt hne x s =
      dirichletReciprocalResidueAt hne x 1 +
        dirichletReciprocalResidueAt hne x 0 +
        ∑
          ρ ∈
            ((dirichletLFunctionSingularitiesInRectangle
                      χ hne z w).erase
                  1).erase
              0,
          dirichletReciprocalResidueAt hne x
            ρ := by
  classical
  have h0' :
    (0 : ℂ) ∈
      (dirichletLFunctionSingularitiesInRectangle
            χ hne z w).erase
        1 :=
    Finset.mem_erase.mpr ⟨by norm_num only, h0⟩
  rw [← Finset.add_sum_erase _ _ h1, ← Finset.add_sum_erase _ _ h0']
  ring

/--
For a nontrivial character and any real `x`, membership in the singularity ledger after
erasing `1` and `0` makes the designated reciprocal residue equal its ordinary
`LFunction` zero contribution. Unfold the residue away from the Mellin points.
The comparison to completed-zero norms is a separate multiplicity-bridge step.
-/
theorem dirichletReciprocalResidueAt_eq_zeroContribution_of_mem_erase {N : ℕ} [NeZero N] (x : ℝ)
    {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1) {z w : ℂ} {ρ : ℂ}
    (hρ :
      ρ ∈
        ((dirichletLFunctionSingularitiesInRectangle
                  χ hne z w).erase
              1).erase
          0) :
    dirichletReciprocalResidueAt hne x ρ =
      dirichletLFunctionReciprocalZeroContribution
        x χ ρ := by
  have hρ0 : ρ ≠ 0 := (Finset.mem_erase.mp hρ).1
  have hρ1 : ρ ≠ 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hρ)).1
  exact
    dirichletReciprocalResidueAt_zero_ne_one hne
      x hρ0 hρ1

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
