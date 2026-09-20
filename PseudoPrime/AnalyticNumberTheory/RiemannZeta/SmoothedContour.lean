/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.GridCuts
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.PoleOneRegularization
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Topology.MetricSpace.HausdorffDistance
import PseudoPrime.AnalyticNumberTheory.General.PoleResidueCalculus
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroContribution
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.SingularityGeometry
import PseudoPrime.AnalyticNumberTheory.General.MellinWeights
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.Boundary
import PseudoPrime.AnalyticNumberTheory.RectangleGeometry.GridCutConstruction
import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedMangoldt
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroMassBounds

/-!
# Smoothed Riemann-zeta contour kernels and finite explicit-formula identities

This file defines the logarithmic and reciprocal Mellin-weighted logarithmic derivatives of
zeta, their regularizations and residues, finite contour identities, and vertical integrals.
These analytic identities do not use downstream numerical inequalities; those remain downstream.
-/

namespace PseudoPrime.AnalyticNumberTheory.RiemannZeta

/--
The logarithmic-derivative kernel for the reciprocal Riemann explicit formula.

The input `x` is the real cutoff and `s` is the contour variable.  The factors `s` and `s-1`
produce the residues at zero and one, while `x^(s-1)` produces the reciprocal Mangoldt weight.
-/
noncomputable def riemannZetaReciprocalContourKernel (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ (s - 1) / (s * (s - 1))

/-- The logarithmically weighted Riemann kernel used in the later estimate. -/
noncomputable def riemannZetaLogContourKernel (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s / s ^ 2

/-- The reciprocal kernel after removing its Mellin pole at zero. -/
noncomputable def riemannZetaReciprocalZeroRegularization (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ (s - 1) / (s - 1)

/-- The logarithmically weighted kernel after removing its double Mellin pole at zero. -/
noncomputable def riemannZetaLogZeroRegularization (x : ℝ) (s : ℂ) : ℂ :=
  -(deriv riemannZeta s / riemannZeta s) * (x : ℂ) ^ s

/-- The reciprocal kernel after removing its double pole at one. -/
noncomputable def riemannZetaReciprocalOneRegularization (x : ℝ) (s : ℂ) : ℂ :=
  riemannZetaOneLogDerivativeRegularization s * (x : ℂ) ^ (s - 1) / s

/-- The logarithmic kernel after removing its simple pole at one. -/
noncomputable def riemannZetaLogOneRegularization (x : ℝ) (s : ℂ) : ℂ :=
  riemannZetaOneLogDerivativeRegularization s * (x : ℂ) ^ s / s ^ 2

/-- The reciprocal kernel with a zeta-zero pole of multiplicity `m` removed at `ρ`. -/
noncomputable def riemannZetaReciprocalZetaZeroRegularization (x : ℝ) (ρ : ℂ) (m : ℕ) (g : ℂ → ℂ)
    (s : ℂ) : ℂ :=
  -((m : ℂ) + (s - ρ) * logDeriv g s) * (x : ℂ) ^ (s - 1) / (s * (s - 1))

/-- The logarithmic kernel with a zeta-zero pole of multiplicity `m` removed at `ρ`. -/
noncomputable def riemannZetaLogZetaZeroRegularization (x : ℝ) (ρ : ℂ) (m : ℕ) (g : ℂ → ℂ) (s : ℂ) :
    ℂ :=
  -((m : ℂ) + (s - ρ) * logDeriv g s) * (x : ℂ) ^ s / s ^ 2

/-!
Generic circle-integral residue formulas for regularized simple and double
poles are provided by `PseudoPrime.AnalyticNumberTheory.General.PoleResidueCalculus`.
-/

/-- The reciprocal contour kernel is differentiable away from zero, one, and zeta zeros. -/
theorem differentiableAt_riemannZetaReciprocalContourKernel {x : ℝ} (hx : 0 < x) {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hszeta : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (riemannZetaReciprocalContourKernel x) s := by
  have hzeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hscompl : s ∈ ({1}ᶜ : Set ℂ) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq] using hs1
  have hderivWithin := (differentiableOn_riemannZeta.deriv isOpen_compl_singleton) s hscompl
  have hderiv : DifferentiableAt ℂ (deriv riemannZeta) s :=
    hderivWithin.differentiableAt (isOpen_compl_singleton.mem_nhds hscompl)
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hsdenominator : s * (s - 1) ≠ 0 := mul_ne_zero hs0 (sub_ne_zero.mpr hs1)
  unfold riemannZetaReciprocalContourKernel
  fun_prop (disch := assumption)

/-- The logarithmically weighted kernel is differentiable away from zero, one, and zeta zeros. -/
theorem differentiableAt_riemannZetaLogContourKernel {x : ℝ} (hx : 0 < x) {s : ℂ} (hs0 : s ≠ 0)
    (hs1 : s ≠ 1) (hszeta : riemannZeta s ≠ 0) :
    DifferentiableAt ℂ (riemannZetaLogContourKernel x) s := by
  have hzeta : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs1
  have hscompl : s ∈ ({1}ᶜ : Set ℂ) := by
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff, ne_eq] using hs1
  have hderivWithin := (differentiableOn_riemannZeta.deriv isOpen_compl_singleton) s hscompl
  have hderiv : DifferentiableAt ℂ (deriv riemannZeta) s :=
    hderivWithin.differentiableAt (isOpen_compl_singleton.mem_nhds hscompl)
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hsdenominator : s ^ 2 ≠ 0 := pow_ne_zero 2 hs0
  unfold riemannZetaLogContourKernel
  fun_prop (disch := assumption)

/-- Multiplication by `s` removes the reciprocal kernel's Mellin pole away from zero and one. -/
theorem mul_riemannZetaReciprocalContourKernel (x : ℝ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    s * riemannZetaReciprocalContourKernel x s = riemannZetaReciprocalZeroRegularization x s := by
  unfold riemannZetaReciprocalContourKernel riemannZetaReciprocalZeroRegularization
  field_simp

/-- Multiplication by `s²` removes the logarithmic kernel's double Mellin pole away from zero. -/
theorem sq_mul_riemannZetaLogContourKernel (x : ℝ) {s : ℂ} (hs0 : s ≠ 0) :
    s ^ 2 * riemannZetaLogContourKernel x s = riemannZetaLogZeroRegularization x s := by
  unfold riemannZetaLogContourKernel riemannZetaLogZeroRegularization
  field_simp

/-- Near zero, multiplying the reciprocal kernel by `s` gives its zero-regularized extension. -/
theorem eventuallyEq_riemannZetaReciprocalZeroRegularization (x : ℝ) :
    Filter.EventuallyEq (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (fun s ↦ (s - 0) * riemannZetaReciprocalContourKernel x s)
      (riemannZetaReciprocalZeroRegularization x) := by
  have honeNhds : ∀ᶠ s : ℂ in nhds 0, s ≠ 1 := compl_singleton_mem_nhds (by norm_num only)
  have hone : ∀ᶠ s in nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ), s ≠ 1 :=
    honeNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hone, eventually_mem_nhdsWithin] with s hs1 hs0
  rw [sub_zero]
  exact mul_riemannZetaReciprocalContourKernel x (Set.mem_compl_singleton_iff.mp hs0) hs1

/-- Near zero, `s²` times the logarithmic kernel gives its zero-regularized extension. -/
theorem eventuallyEq_riemannZetaLogZeroRegularization (x : ℝ) :
    Filter.EventuallyEq (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (fun s ↦ (s - 0) ^ 2 * riemannZetaLogContourKernel x s)
      (riemannZetaLogZeroRegularization x) := by
  filter_upwards [eventually_mem_nhdsWithin] with s hs0
  rw [sub_zero]
  exact sq_mul_riemannZetaLogContourKernel x (Set.mem_compl_singleton_iff.mp hs0)

/-- The reciprocal zero-regularization is analytic near zero. -/
theorem analyticAt_riemannZetaReciprocalZeroRegularization {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (riemannZetaReciprocalZeroRegularization x) 0 := by
  have hzeta : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 zero_ne_one
  have hzeta0 : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]; norm_num only
  have hlog : AnalyticAt ℂ (fun s ↦ deriv riemannZeta s / riemannZeta s) 0 :=
    hzeta.deriv.div hzeta hzeta0
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) 0 :=
    analyticAt_const.cpow (analyticAt_id.sub analyticAt_const) hxslit
  have hdenominator : (0 : ℂ) - 1 ≠ 0 := by norm_num only
  unfold riemannZetaReciprocalZeroRegularization
  fun_prop (disch := assumption)

/-- The logarithmic zero-regularization is analytic near zero. -/
theorem analyticAt_riemannZetaLogZeroRegularization {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (riemannZetaLogZeroRegularization x) 0 := by
  have hzeta : AnalyticAt ℂ riemannZeta 0 := analyticOn_riemannZeta 0 zero_ne_one
  have hzeta0 : riemannZeta 0 ≠ 0 := by
    rw [riemannZeta_zero]; norm_num only
  have hlog : AnalyticAt ℂ (fun s ↦ deriv riemannZeta s / riemannZeta s) 0 :=
    hzeta.deriv.div hzeta hzeta0
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) 0 := analyticAt_const.cpow analyticAt_id hxslit
  unfold riemannZetaLogZeroRegularization
  fun_prop

/-- The regularized logarithmic kernel has the expected leading coefficient at zero. -/
theorem riemannZetaLogZeroRegularization_zero (x : ℝ) :
    riemannZetaLogZeroRegularization x 0 = -Complex.log (2 * Real.pi) := by
  rw [riemannZetaLogZeroRegularization, deriv_riemannZeta_zero, riemannZeta_zero]
  rw [Complex.cpow_zero, mul_one]
  ring

/-- The regularized reciprocal kernel has the expected residue coefficient at zero. -/
theorem riemannZetaReciprocalZeroRegularization_zero (x : ℝ) :
    riemannZetaReciprocalZeroRegularization x 0 = Complex.log (2 * Real.pi) * (x : ℂ)⁻¹ := by
  rw [riemannZetaReciprocalZeroRegularization, deriv_riemannZeta_zero, riemannZeta_zero]
  rw [show (0 : ℂ) - 1 = -1 by ring, Complex.cpow_neg_one]
  norm_num only
  ring

/-- Near one, `(s-1)²` times the reciprocal kernel equals its regularized extension. -/
theorem eventuallyEq_riemannZetaReciprocalOneRegularization (x : ℝ) :
    Filter.EventuallyEq (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ))
      (fun s ↦ (s - 1) ^ 2 * riemannZetaReciprocalContourKernel x s)
      (riemannZetaReciprocalOneRegularization x) := by
  have hzeroNhds : ∀ᶠ s : ℂ in nhds 1, s ≠ 0 :=
    compl_singleton_mem_nhds (by norm_num only : (1 : ℂ) ≠ 0)
  have hzero : ∀ᶠ s in nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ), s ≠ 0 :=
    hzeroNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [eventually_mem_nhdsWithin, eventuallyEq_riemannZetaOneLogDerivativeRegularization,
    hzero] with s hs hsreg hs0
  rw [riemannZetaReciprocalContourKernel, riemannZetaReciprocalOneRegularization, ← hsreg]
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hs)
  field_simp

/-- Near one, `s-1` times the logarithmic kernel equals its regularized extension. -/
theorem eventuallyEq_riemannZetaLogOneRegularization (x : ℝ) :
    Filter.EventuallyEq (nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ))
      (fun s ↦ (s - 1) * riemannZetaLogContourKernel x s) (riemannZetaLogOneRegularization x) := by
  have hzeroNhds : ∀ᶠ s : ℂ in nhds 1, s ≠ 0 :=
    compl_singleton_mem_nhds (by norm_num only : (1 : ℂ) ≠ 0)
  have hzero : ∀ᶠ s in nhdsWithin (1 : ℂ) ({1}ᶜ : Set ℂ), s ≠ 0 :=
    hzeroNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [eventuallyEq_riemannZetaOneLogDerivativeRegularization, hzero] with s hsreg hs0
  rw [riemannZetaLogContourKernel, riemannZetaLogOneRegularization, ← hsreg]
  field_simp

/-- The reciprocal one-regularization is analytic near one. -/
theorem analyticAt_riemannZetaReciprocalOneRegularization {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (riemannZetaReciprocalOneRegularization x) 1 := by
  have hregular := analyticAt_riemannZetaOneLogDerivativeRegularization
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) 1 :=
    analyticAt_const.cpow (analyticAt_id.sub analyticAt_const) hxslit
  have hdenominator : (1 : ℂ) ≠ 0 := one_ne_zero
  unfold riemannZetaReciprocalOneRegularization
  fun_prop (disch := assumption)

/-- The logarithmic one-regularization is analytic near one. -/
theorem analyticAt_riemannZetaLogOneRegularization {x : ℝ} (hx : 0 < x) :
    AnalyticAt ℂ (riemannZetaLogOneRegularization x) 1 := by
  have hregular := analyticAt_riemannZetaOneLogDerivativeRegularization
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) 1 := analyticAt_const.cpow analyticAt_id hxslit
  have hdenominator : (1 : ℂ) ^ 2 ≠ 0 := by norm_num only
  unfold riemannZetaLogOneRegularization
  fun_prop (disch := assumption)

/-- The logarithmic kernel's residue coefficient at one is `x`. -/
theorem riemannZetaLogOneRegularization_one (x : ℝ) : riemannZetaLogOneRegularization x 1 = x := by
  simp only [riemannZetaLogOneRegularization, riemannZetaOneLogDerivativeRegularization_one,
    Complex.cpow_one, one_mul, one_pow, div_one]

/-!
Local meromorphic factorization and analytic multiplicities of zeta are
provided by `PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting`.
-/

/-- The reciprocal zeta-zero regularization is analytic near its center. -/
theorem analyticAt_riemannZetaReciprocalZetaZeroRegularization {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (m : ℕ) {g : ℂ → ℂ} (hganalytic : AnalyticAt ℂ g ρ)
    (hgzero : g ρ ≠ 0) : AnalyticAt ℂ (riemannZetaReciprocalZetaZeroRegularization x ρ m g) ρ := by
  have hlog : AnalyticAt ℂ (logDeriv g) ρ := by
    unfold logDeriv
    exact hganalytic.deriv.div hganalytic hgzero
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) ρ :=
    analyticAt_const.cpow (analyticAt_id.sub analyticAt_const) hxslit
  have hdenominator : ρ * (ρ - 1) ≠ 0 := mul_ne_zero hρ0 (sub_ne_zero.mpr hρ1)
  unfold riemannZetaReciprocalZetaZeroRegularization
  fun_prop (disch := assumption)

/-- The logarithmic zeta-zero regularization is analytic near its center. -/
theorem analyticAt_riemannZetaLogZetaZeroRegularization {x : ℝ} (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (m : ℕ) {g : ℂ → ℂ} (hganalytic : AnalyticAt ℂ g ρ) (hgzero : g ρ ≠ 0) :
    AnalyticAt ℂ (riemannZetaLogZetaZeroRegularization x ρ m g) ρ := by
  have hlog : AnalyticAt ℂ (logDeriv g) ρ := by
    unfold logDeriv
    exact hganalytic.deriv.div hganalytic hgzero
  have hxslit : (x : ℂ) ∈ Complex.slitPlane := Complex.ofReal_mem_slitPlane.2 hx
  have hpow : AnalyticAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ s) ρ := analyticAt_const.cpow analyticAt_id hxslit
  have hdenominator : ρ ^ 2 ≠ 0 := pow_ne_zero 2 hρ0
  unfold riemannZetaLogZetaZeroRegularization
  fun_prop (disch := assumption)

/-- The reciprocal zero-regularization evaluates to the weighted negative multiplicity. -/
theorem riemannZetaReciprocalZetaZeroRegularization_self (x : ℝ) (ρ : ℂ) (m : ℕ) (g : ℂ → ℂ) :
    riemannZetaReciprocalZetaZeroRegularization x ρ m g ρ =
      -(m : ℂ) * (x : ℂ) ^ (ρ - 1) / (ρ * (ρ - 1)) := by
  simp only [riemannZetaReciprocalZetaZeroRegularization, sub_self, zero_mul, add_zero, neg_mul]

/-- The logarithmic zero-regularization evaluates to the weighted negative multiplicity. -/
theorem riemannZetaLogZetaZeroRegularization_self (x : ℝ) (ρ : ℂ) (m : ℕ) (g : ℂ → ℂ) :
    riemannZetaLogZetaZeroRegularization x ρ m g ρ = -(m : ℂ) * (x : ℂ) ^ ρ / ρ ^ 2 := by
  simp only [riemannZetaLogZetaZeroRegularization, sub_self, zero_mul, add_zero, neg_mul]

/--
At a zeta zero away from zero and one, the scaled reciprocal kernel agrees locally with its
regularization.
-/
theorem exists_eventuallyEq_reciprocalKernel_zetaZeroRegularization (x : ℝ) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    ∃ g : ℂ → ℂ,
      0 < riemannZetaZeroMultiplicity ρ ∧
        AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ))
          (fun s ↦ (s - ρ) * riemannZetaReciprocalContourKernel x s)
          (riemannZetaReciprocalZetaZeroRegularization x ρ (riemannZetaZeroMultiplicity ρ) g) := by
  obtain ⟨g, hpos, hganalytic, hgzero, hlog⟩ :=
    exists_eventuallyEq_logDeriv_riemannZeta_at_zero hρ1 hzero
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
    deriv riemannZeta s / riemannZeta s =
      (riemannZetaZeroMultiplicity ρ : ℂ) / (s - ρ) + logDeriv g s := by
    rw [← logDeriv_apply]
    exact hlogs
  rw [riemannZetaReciprocalContourKernel, riemannZetaReciprocalZetaZeroRegularization, hlogs']
  have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsρ)
  field_simp

/--
At a zeta zero away from zero and one, the scaled logarithmic kernel agrees locally with its
regularization.
-/
theorem exists_eventuallyEq_logKernel_zetaZeroRegularization (x : ℝ) {ρ : ℂ} (hρ0 : ρ ≠ 0)
    (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    ∃ g : ℂ → ℂ,
      0 < riemannZetaZeroMultiplicity ρ ∧
        AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ))
          (fun s ↦ (s - ρ) * riemannZetaLogContourKernel x s)
          (riemannZetaLogZetaZeroRegularization x ρ (riemannZetaZeroMultiplicity ρ) g) := by
  obtain ⟨g, hpos, hganalytic, hgzero, hlog⟩ :=
    exists_eventuallyEq_logDeriv_riemannZeta_at_zero hρ1 hzero
  refine ⟨g, hpos, hganalytic, hgzero, ?_⟩
  have hzeroNhds : ∀ᶠ s : ℂ in nhds ρ, s ≠ 0 := compl_singleton_mem_nhds hρ0
  have hzeroEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), s ≠ 0 :=
    hzeroNhds.filter_mono nhdsWithin_le_nhds
  filter_upwards [hlog, hzeroEventually, eventually_mem_nhdsWithin] with s hlogs hs0 hsρ
  have hlogs' :
    deriv riemannZeta s / riemannZeta s =
      (riemannZetaZeroMultiplicity ρ : ℂ) / (s - ρ) + logDeriv g s := by
    rw [← logDeriv_apply]
    exact hlogs
  rw [riemannZetaLogContourKernel, riemannZetaLogZetaZeroRegularization, hlogs']
  have hsρ' : s - ρ ≠ 0 := sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsρ)
  field_simp

/-!
Finite zeta zero ledgers and the simple poles of its logarithmic derivative
are provided by `PseudoPrime.AnalyticNumberTheory.RiemannZeta.ZeroCounting`.
The contour and grid statements use closed and open rectangle sets directly.
-/

/-- The residue of the reciprocal kernel's simple pole at zero. -/
noncomputable def riemannZetaReciprocalResidueAtZero (x : ℝ) : ℂ :=
  riemannZetaReciprocalZeroRegularization x 0

/-- The residue of the reciprocal kernel's double pole at one. -/
noncomputable def riemannZetaReciprocalResidueAtOne (x : ℝ) : ℂ :=
  deriv (riemannZetaReciprocalOneRegularization x) 1

/-- The residue of the logarithmic kernel's double pole at zero. -/
noncomputable def riemannZetaLogResidueAtZero (x : ℝ) : ℂ :=
  deriv (riemannZetaLogZeroRegularization x) 0

/-- The residue of the logarithmic kernel's simple pole at one. -/
noncomputable def riemannZetaLogResidueAtOne (x : ℝ) : ℂ :=
  riemannZetaLogOneRegularization x 1

/-- The reciprocal-kernel residues at zero and one that lie inside a closed rectangle. -/
noncomputable def riemannZetaReciprocalMellinPoleLedger (x : ℝ) (z w : ℂ) : ℂ := by
  classical
    exact
    (if (0 : ℂ) ∈ Rectangle.rectangleClosedBox z w then riemannZetaReciprocalResidueAtZero x
      else 0) +
      if (1 : ℂ) ∈ Rectangle.rectangleClosedBox z w then riemannZetaReciprocalResidueAtOne x else 0

/-- The logarithmic-kernel residues at zero and one that lie inside a closed rectangle. -/
noncomputable def riemannZetaLogMellinPoleLedger (x : ℝ) (z w : ℂ) : ℂ := by
  classical
    exact
    (if (0 : ℂ) ∈ Rectangle.rectangleClosedBox z w then riemannZetaLogResidueAtZero x else 0) +
      if (1 : ℂ) ∈ Rectangle.rectangleClosedBox z w then riemannZetaLogResidueAtOne x else 0

/-- The total reciprocal-kernel residue ledger in a closed rectangle. -/
noncomputable def riemannZetaReciprocalContourResidueLedger (x : ℝ) (z w : ℂ) : ℂ :=
  riemannZetaReciprocalMellinPoleLedger x z w + riemannZetaReciprocalContourZeroLedger x z w

/-- The total logarithmic-kernel residue ledger in a closed rectangle. -/
noncomputable def riemannZetaLogContourResidueLedger (x : ℝ) (z w : ℂ) : ℂ :=
  riemannZetaLogMellinPoleLedger x z w + riemannZetaLogContourZeroLedger x z w

/-!
The triple-pole divided-slope decomposition is provided by
`PseudoPrime.AnalyticNumberTheory.General.PoleResidueCalculus`.
-/

/--
Both Mellin-pole square boundary integrals match `2πi` times their residues on every sufficiently
small radius.

This is the square-contour counterpart of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`exists_radius_forall_circleIntegrals_eq_mellinResidues`,
bundling all four `s = 0`/`s = 1` cases at one common radius bound.
-/
theorem exists_radius_forall_llsRectangleBoundaryIntegrals_eq_mellinResidues {x : ℝ} (hx : 0 < x) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
                  (RectangleGeometry.centeredSquareLower 0 r)
                  (RectangleGeometry.centeredSquareUpper 0 r) =
                2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtZero x ∧
              RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
                  (RectangleGeometry.centeredSquareLower 1 r)
                  (RectangleGeometry.centeredSquareUpper 1 r) =
                2 * Real.pi * Complex.I * riemannZetaLogResidueAtOne x ∧
              RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
                  (RectangleGeometry.centeredSquareLower 1 r)
                  (RectangleGeometry.centeredSquareUpper 1 r) =
                2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtOne x ∧
              RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
                  (RectangleGeometry.centeredSquareLower 0 r)
                  (RectangleGeometry.centeredSquareUpper 0 r) =
                2 * Real.pi * Complex.I * riemannZetaLogResidueAtZero x := by
  obtain ⟨R1, hR1, h1⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul
      (analyticAt_riemannZetaReciprocalZeroRegularization hx)
      (eventuallyEq_riemannZetaReciprocalZeroRegularization x)
  obtain ⟨R2, hR2, h2⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul
      (analyticAt_riemannZetaLogOneRegularization hx)
      (eventuallyEq_riemannZetaLogOneRegularization x)
  obtain ⟨R3, hR3, h3⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv
      (analyticAt_riemannZetaReciprocalOneRegularization hx)
      (eventuallyEq_riemannZetaReciprocalOneRegularization x)
  obtain ⟨R4, hR4, h4⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul_deriv
      (analyticAt_riemannZetaLogZeroRegularization hx)
      (eventuallyEq_riemannZetaLogZeroRegularization x)
  let R := min (min R1 R2) (min R3 R4)
  have hR : 0 < R := lt_min (lt_min hR1 hR2) (lt_min hR3 hR4)
  refine ⟨R, hR, fun r hr hrR ↦ ?_⟩
  have hR1' : r ≤ R1 := hrR.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hR2' : r ≤ R2 := hrR.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hR3' : r ≤ R3 := hrR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hR4' : r ≤ R4 := hrR.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact ⟨h1 r hr hR1', h2 r hr hR2', h3 r hr hR3', h4 r hr hR4'⟩

/--
Both kernel square boundary integrals around a zeta zero match `2πi` times its contribution on
every sufficiently small radius.

This is the square-contour counterpart of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`exists_radius_forall_circleIntegrals_eq_zeroContributions`.
-/
theorem exists_radius_forall_llsRectangleBoundaryIntegrals_eq_zeroContributions {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
                  (RectangleGeometry.centeredSquareLower ρ r)
                  (RectangleGeometry.centeredSquareUpper ρ r) =
                2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ ∧
              RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
                  (RectangleGeometry.centeredSquareLower ρ r)
                  (RectangleGeometry.centeredSquareUpper ρ r) =
                2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ := by
  obtain ⟨g1, -, hganalytic1, hgzero1, heq1⟩ :=
    exists_eventuallyEq_reciprocalKernel_zetaZeroRegularization x hρ0 hρ1 hzero
  obtain ⟨g2, -, hganalytic2, hgzero2, heq2⟩ :=
    exists_eventuallyEq_logKernel_zetaZeroRegularization x hρ0 hρ1 hzero
  have hh1 :
    AnalyticAt ℂ
      (riemannZetaReciprocalZetaZeroRegularization x ρ (riemannZetaZeroMultiplicity ρ) g1) ρ :=
    analyticAt_riemannZetaReciprocalZetaZeroRegularization hx hρ0 hρ1 _ hganalytic1 hgzero1
  have hh2 :
    AnalyticAt ℂ (riemannZetaLogZetaZeroRegularization x ρ (riemannZetaZeroMultiplicity ρ) g2) ρ :=
    analyticAt_riemannZetaLogZetaZeroRegularization hx hρ0 _ hganalytic2 hgzero2
  obtain ⟨R1, hR1, h1⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul hh1 heq1
  obtain ⟨R2, hR2, h2⟩ :=
    RectangleGeometry.exists_radius_forall_rectangleBoundaryIntegral_eq_two_pi_I_mul hh2 heq2
  let R := min R1 R2
  have hR : 0 < R := lt_min hR1 hR2
  refine ⟨R, hR, fun r hr hrR ↦ ?_⟩
  have hR1' : r ≤ R1 := hrR.trans (min_le_left _ _)
  have hR2' : r ≤ R2 := hrR.trans (min_le_right _ _)
  refine ⟨?_, ?_⟩
  · rw [h1 r hr hR1', riemannZetaReciprocalZetaZeroRegularization_self,
      riemannZetaReciprocalZeroContribution]
  · rw [h2 r hr hR2', riemannZetaLogZetaZeroRegularization_self, riemannZetaLogZeroContribution]

/--
All zeta zeros in one rectangle share a positive radius for both kernel square boundary formulas.

This is the square-contour counterpart of
`PseudoPrime.AnalyticNumberTheory.RiemannZeta.`
`exists_common_radius_circleIntegrals_eq_zeroContributions`.
-/
theorem exists_common_radius_llsRectangleBoundaryIntegrals_eq_zeroContributions {x : ℝ} (hx : 0 < x)
    (z w : ℂ) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            ∀ ρ ∈ riemannZetaZerosInAnyRectangle z w,
              RectangleGeometry.rectangleBoundaryIntegral
                    (RiemannZeta.riemannZetaReciprocalContourKernel x)
                    (RectangleGeometry.centeredSquareLower ρ r)
                    (RectangleGeometry.centeredSquareUpper ρ r) =
                  2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ ∧
                RectangleGeometry.rectangleBoundaryIntegral
                    (RiemannZeta.riemannZetaLogContourKernel x)
                    (RectangleGeometry.centeredSquareLower ρ r)
                    (RectangleGeometry.centeredSquareUpper ρ r) =
                  2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ := by
  classical
  let S := riemannZetaZerosInAnyRectangle z w
  let certificate (ρ : ℂ) (hρ : ρ ∈ S) :=
    exists_radius_forall_llsRectangleBoundaryIntegrals_eq_zeroContributions hx
      (ne_zero_of_mem_riemannZetaZerosInAnyRectangle hρ)
      (ne_one_of_mem_riemannZetaZerosInAnyRectangle hρ)
      ((mem_riemannZetaZerosInAnyRectangle_iff.mp hρ).2)
  let radius (ρ : ℂ) : ℝ := if hρ : ρ ∈ S then (certificate ρ hρ).choose else 1
  have hradius_pos (ρ : ℂ) (hρ : ρ ∈ S) : 0 < radius ρ := by
    dsimp only [radius]
    rw [dite_eq_left hρ]
    exact (certificate ρ hρ).choose_spec.1
  have hradius_formula (ρ : ℂ) (hρ : ρ ∈ S) (r : ℝ) (hr : 0 < r) (hrradius : r ≤ radius ρ) :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
          (RectangleGeometry.centeredSquareLower ρ r) (RectangleGeometry.centeredSquareUpper ρ r) =
        2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ ∧
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
          (RectangleGeometry.centeredSquareLower ρ r) (RectangleGeometry.centeredSquareUpper ρ r) =
        2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ := by
    dsimp only [radius] at hrradius
    rw [dite_eq_left hρ] at hrradius
    exact (certificate ρ hρ).choose_spec.2 r hr hrradius
  let values := S.image radius ∪ {1}
  have hvalues : values.Nonempty :=
    ⟨1, by simp only [Finset.union_singleton, Finset.mem_insert, Finset.mem_image, true_or, values]⟩
  let R := values.min' hvalues
  have hRpos : 0 < R := by
    have hRmem := Finset.min'_mem values hvalues
    change 0 < values.min' hvalues
    rcases Finset.mem_union.mp hRmem with hRmem | hRmem
    · rcases Finset.mem_image.mp hRmem with ⟨ρ, hρ, hρR⟩
      rw [← hρR]
      exact hradius_pos ρ hρ
    · rw [Finset.mem_singleton.mp hRmem]
      norm_num only
  refine ⟨R, hRpos, ?_⟩
  intro r hr hrR ρ hρ
  have hradius_mem : radius ρ ∈ values :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩)
  have hRradius : R ≤ radius ρ := Finset.min'_le values _ hradius_mem
  exact hradius_formula ρ hρ r hr (hrR.trans hRradius)

/-- For `x > 0`, both kernels are interval-integrable on a horizontal segment
inside the rectangle when its height avoids every singularity in the finite ledger. -/
theorem intervalIntegrable_riemannZetaKernels_horizontal {x : ℝ} (hx : 0 < x) {z w : ℂ} {c a b : ℝ}
    (ha : a ∈ Set.uIcc z.re w.re) (hb : b ∈ Set.uIcc z.re w.re) (hc : c ∈ Set.uIcc z.im w.im)
    (havoid : ∀ s ∈ riemannZetaSingularitiesInRectangle z w, s.im ≠ c) :
    IntervalIntegrable (fun t : ℝ ↦ riemannZetaReciprocalContourKernel x (t + c * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable (fun t : ℝ ↦ riemannZetaLogContourKernel x (t + c * Complex.I))
        MeasureTheory.volume a b := by
  have hregular := horizontal_segment_subset_riemannZetaRegularSet ha hb hc havoid
  constructor <;> apply RectangleGeometry.intervalIntegrable_horizontal_of_continuousAt <;>
    intro t ht
  · exact
      (differentiableAt_riemannZetaReciprocalContourKernel hx (hregular t ht).1 (hregular t ht).2.1
          (hregular t ht).2.2).continuousAt
  · exact
      (differentiableAt_riemannZetaLogContourKernel hx (hregular t ht).1 (hregular t ht).2.1
          (hregular t ht).2.2).continuousAt

/-- Both zeta contour kernels are integrable on a ledger-avoiding vertical segment. -/
theorem intervalIntegrable_riemannZetaKernels_vertical {x : ℝ} (hx : 0 < x) {z w : ℂ} {c a b : ℝ}
    (hc : c ∈ Set.uIcc z.re w.re) (ha : a ∈ Set.uIcc z.im w.im) (hb : b ∈ Set.uIcc z.im w.im)
    (havoid : ∀ s ∈ riemannZetaSingularitiesInRectangle z w, s.re ≠ c) :
    IntervalIntegrable (fun t : ℝ ↦ riemannZetaReciprocalContourKernel x (c + t * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable (fun t : ℝ ↦ riemannZetaLogContourKernel x (c + t * Complex.I))
        MeasureTheory.volume a b := by
  have hregular := vertical_segment_subset_riemannZetaRegularSet hc ha hb havoid
  constructor <;> apply RectangleGeometry.intervalIntegrable_vertical_of_continuousAt <;> intro t ht
  · exact
      (differentiableAt_riemannZetaReciprocalContourKernel hx (hregular t ht).1 (hregular t ht).2.1
          (hregular t ht).2.2).continuousAt
  · exact
      (differentiableAt_riemannZetaLogContourKernel hx (hregular t ht).1 (hregular t ht).2.1
          (hregular t ht).2.2).continuousAt

/-- For `x > 0`, both kernels are interval-integrable on a horizontal segment
in an assigned singular cell, provided its height differs from the assigned
point's height and the parent cell lies in the outer rectangle. -/
theorem RiemannZetaSingularCellAssignment.intervalIntegrable_horizontal {x : ℝ} (hx : 0 < x)
    {z w : ℂ} {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    {c a b : ℝ} (ha : a ∈ Set.uIcc parent.1.re parent.2.re)
    (hb : b ∈ Set.uIcc parent.1.re parent.2.re) (hc : c ∈ Set.uIcc parent.1.im parent.2.im)
    (havoid : (assignment.pointOfCell parent).im ≠ c) :
    IntervalIntegrable (fun t : ℝ ↦ riemannZetaReciprocalContourKernel x (t + c * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable (fun t : ℝ ↦ riemannZetaLogContourKernel x (t + c * Complex.I))
        MeasureTheory.volume a b := by
  have hregular (t : ℝ) (ht : t ∈ Set.uIcc a b) :
    (t : ℂ) + c * Complex.I ∈ RiemannZeta.riemannZetaRegularSet := by
    apply assignment.mem_regular_of_mem_parent_of_ne hparent hparentSubset
    · exact
        ⟨by
          simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
            add_zero] using Set.uIcc_subset_uIcc ha hb ht,
          by
          simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
            zero_add] using hc⟩
    · intro heq
      apply havoid
      have him := congrArg Complex.im heq
      simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
        Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero, zero_add] using him.symm
  constructor <;> apply RectangleGeometry.intervalIntegrable_horizontal_of_continuousAt <;>
    intro t ht
  · exact
      (differentiableAt_riemannZetaReciprocalContourKernel hx (hregular t ht).1 (hregular t ht).2.1
          (hregular t ht).2.2).continuousAt
  · exact
      (differentiableAt_riemannZetaLogContourKernel hx (hregular t ht).1 (hregular t ht).2.1
          (hregular t ht).2.2).continuousAt

/-- Both kernels are integrable on a vertical parent-cell segment away from the assigned point. -/
theorem RiemannZetaSingularCellAssignment.intervalIntegrable_vertical {x : ℝ} (hx : 0 < x) {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    {c a b : ℝ} (hc : c ∈ Set.uIcc parent.1.re parent.2.re)
    (ha : a ∈ Set.uIcc parent.1.im parent.2.im) (hb : b ∈ Set.uIcc parent.1.im parent.2.im)
    (havoid : (assignment.pointOfCell parent).re ≠ c) :
    IntervalIntegrable (fun t : ℝ ↦ riemannZetaReciprocalContourKernel x (c + t * Complex.I))
        MeasureTheory.volume a b ∧
      IntervalIntegrable (fun t : ℝ ↦ riemannZetaLogContourKernel x (c + t * Complex.I))
        MeasureTheory.volume a b := by
  have hregular (t : ℝ) (ht : t ∈ Set.uIcc a b) :
    (c : ℂ) + t * Complex.I ∈ riemannZetaRegularSet := by
    apply assignment.mem_regular_of_mem_parent_of_ne hparent hparentSubset
    · exact
        ⟨by
          simpa only [Set.mem_preimage, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
            Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self,
            add_zero] using hc,
          by
          simpa only [Set.mem_preimage, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.ofReal_re, Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero,
            zero_add] using Set.uIcc_subset_uIcc ha hb ht⟩
    · intro heq
      apply havoid
      have hre := congrArg Complex.re heq
      simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hre.symm
  constructor <;> apply RectangleGeometry.intervalIntegrable_vertical_of_continuousAt <;> intro t ht
  · exact
      (differentiableAt_riemannZetaReciprocalContourKernel hx (hregular t ht).1 (hregular t ht).2.1
          (hregular t ht).2.2).continuousAt
  · exact
      (differentiableAt_riemannZetaLogContourKernel hx (hregular t ht).1 (hregular t ht).2.1
          (hregular t ht).2.2).continuousAt

/-- Finite parent-cell coordinates avoiding the assigned point integrate both contour kernels. -/
theorem RiemannZetaSingularCellAssignment.kernelCoordinateIntegrable {x : ℝ} (hx : 0 < x) {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    (xcoordinates ycoordinates : List ℝ)
    (hxmem : ∀ c ∈ xcoordinates, c ∈ Set.uIcc parent.1.re parent.2.re)
    (hymem : ∀ c ∈ ycoordinates, c ∈ Set.uIcc parent.1.im parent.2.im)
    (hxavoid : ∀ c ∈ xcoordinates, (assignment.pointOfCell parent).re ≠ c)
    (hyavoid : ∀ c ∈ ycoordinates, (assignment.pointOfCell parent).im ≠ c) :
    RectangleGeometry.RectangleGridCoordinateIntegrable (riemannZetaReciprocalContourKernel x)
        xcoordinates ycoordinates ∧
      RectangleGeometry.RectangleGridCoordinateIntegrable (riemannZetaLogContourKernel x)
        xcoordinates ycoordinates := by
  constructor
  · constructor
    · intro c hc a ha b hb
      exact
        (RiemannZetaSingularCellAssignment.intervalIntegrable_horizontal hx assignment hparent
            hparentSubset (hxmem a ha) (hxmem b hb) (hymem c hc) (hyavoid c hc)).1
    · intro c hc a ha b hb
      exact
        (RiemannZetaSingularCellAssignment.intervalIntegrable_vertical hx assignment hparent
            hparentSubset (hxmem c hc) (hymem a ha) (hymem b hb) (hxavoid c hc)).1
  · constructor
    · intro c hc a ha b hb
      exact
        (RiemannZetaSingularCellAssignment.intervalIntegrable_horizontal hx assignment hparent
            hparentSubset (hxmem a ha) (hxmem b hb) (hymem c hc) (hyavoid c hc)).2
    · intro c hc a ha b hb
      exact
        (RiemannZetaSingularCellAssignment.intervalIntegrable_vertical hx assignment hparent
            hparentSubset (hxmem c hc) (hymem a ha) (hymem b hb) (hxavoid c hc)).2

/-- A cell-contained centered square supplies both local `3 × 3` grid certificates. -/
theorem RiemannZetaSingularCellAssignment.centeredSquare_kernelGridSubdivisionIntegrable {x : ℝ}
    (hx : 0 < x) {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : RiemannZetaSingularCellAssignment z w cells) {parent : ℂ × ℂ}
    (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    (hre : parent.1.re < parent.2.re) (him : parent.1.im < parent.2.im) {r : ℝ} (hr : 0 < r)
    (hball :
      Metric.closedBall (assignment.pointOfCell parent) r ⊆
        RectangleGeometry.rectangleOpenBox parent.1 parent.2) :
    let a := RectangleGeometry.centeredSquareLower (assignment.pointOfCell parent) r
    let b := RectangleGeometry.centeredSquareUpper (assignment.pointOfCell parent) r
    RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x)
        parent.1 parent.2 [a.re, b.re] [a.im, b.im] ∧
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) parent.1
        parent.2 [a.re, b.re] [a.im, b.im] := by
  let c := assignment.pointOfCell parent
  let a := RectangleGeometry.centeredSquareLower c r
  let b := RectangleGeometry.centeredSquareUpper c r
  have hcopen : c ∈ RectangleGeometry.rectangleOpenBox parent.1 parent.2 :=
    hball (Metric.mem_closedBall_self hr.le)
  have hcuts := RectangleGeometry.centeredSquare_cuts_inside hre him hr hball
  have havoid := RectangleGeometry.centeredSquare_augmented_coordinates_avoid hre him hr hcopen
  let xs := parent.1.re :: [a.re, b.re] ++ [parent.2.re]
  let ys := parent.1.im :: [a.im, b.im] ++ [parent.2.im]
  have hxmem : ∀ u ∈ xs, u ∈ Set.uIcc parent.1.re parent.2.re := by
    intro u hu
    simp only [xs, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with (rfl | rfl | rfl) | rfl
    · exact Set.left_mem_uIcc
    · exact Set.mem_uIcc_of_le hcuts.1.le (hcuts.2.1.trans hcuts.2.2.1).le
    · exact Set.mem_uIcc_of_le (hcuts.1.trans hcuts.2.1).le hcuts.2.2.1.le
    · exact Set.right_mem_uIcc
  have hymem : ∀ v ∈ ys, v ∈ Set.uIcc parent.1.im parent.2.im := by
    intro v hv
    simp only [ys, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl | rfl) | rfl
    · exact Set.left_mem_uIcc
    · exact Set.mem_uIcc_of_le hcuts.2.2.2.1.le (hcuts.2.2.2.2.1.trans hcuts.2.2.2.2.2).le
    · exact Set.mem_uIcc_of_le (hcuts.2.2.2.1.trans hcuts.2.2.2.2.1).le hcuts.2.2.2.2.2.le
    · exact Set.right_mem_uIcc
  have edges :=
    RiemannZetaSingularCellAssignment.kernelCoordinateIntegrable hx assignment hparent hparentSubset
      xs ys hxmem hymem havoid.1 havoid.2
  have hxcuts : ∀ u ∈ [a.re, b.re], u ∈ xs := by
    intro u hu
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
    rcases hu with rfl | rfl <;>
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        true_or, or_true, xs]
  have hycuts : ∀ v ∈ [a.im, b.im], v ∈ ys := by
    intro v hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl <;>
      simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
        true_or, or_true, ys]
  constructor
  · exact
      edges.1.gridSubdivision
        (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            true_or, xs])
        (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            or_true, xs])
        (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            true_or, ys])
        (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            or_true, ys])
        _ _ hxcuts hycuts
  · exact
      edges.2.gridSubdivision
        (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            true_or, xs])
        (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            or_true, xs])
        (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            true_or, ys])
        (by
          simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false,
            or_true, ys])
        _ _ hxcuts hycuts

/-- Geometric separation and local residue formulas for a punctured zeta rectangle.

`radius` and `radius_pos` give a common positive radius. `boundary_disjoint`
and `pairwise_disjoint` separate the removed closed balls from the outer
boundary and each other. `zero_integrals` and `mellin_integrals` give both
kernel formulas on circles about the enclosed zeta zeros and about zero and
one. `square_zero_integrals` and `square_mellin_integrals` give their centered-square
counterparts at the same radius. `regular_subset` places the remaining punctured
rectangle in the common regular locus. These data feed boundary decomposition. -/
structure RiemannZetaPuncturedContourCertificate (x : ℝ) (z w : ℂ) where
  radius : ℝ
  radius_pos : 0 < radius
  boundary_disjoint :
    ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
      Disjoint (Metric.closedBall s radius) (RectangleGeometry.rectangleClosedBoxBoundary z w)
  pairwise_disjoint :
    ∀ s ∈ riemannZetaSingularitiesInRectangle z w,
      ∀ t ∈ riemannZetaSingularitiesInRectangle z w,
        s ≠ t → Disjoint (Metric.closedBall s radius) (Metric.closedBall t radius)
  zero_integrals :
    ∀ ρ ∈ riemannZetaZerosInAnyRectangle z w,
      (∮ s in C(ρ, radius), riemannZetaReciprocalContourKernel x s) =
          2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ ∧
        (∮ s in C(ρ, radius), riemannZetaLogContourKernel x s) =
          2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ
  mellin_integrals :
    (∮ s in C(0, radius), riemannZetaReciprocalContourKernel x s) =
        2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtZero x ∧
      (∮ s in C(1, radius), riemannZetaLogContourKernel x s) =
        2 * Real.pi * Complex.I * riemannZetaLogResidueAtOne x ∧
      (∮ s in C(1, radius), riemannZetaReciprocalContourKernel x s) =
        2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtOne x ∧
      (∮ s in C(0, radius), riemannZetaLogContourKernel x s) =
        2 * Real.pi * Complex.I * riemannZetaLogResidueAtZero x
  square_zero_integrals :
    ∀ ρ ∈ riemannZetaZerosInAnyRectangle z w,
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
            (RectangleGeometry.centeredSquareLower ρ radius)
            (RectangleGeometry.centeredSquareUpper ρ radius) =
          2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ ∧
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
            (RectangleGeometry.centeredSquareLower ρ radius)
            (RectangleGeometry.centeredSquareUpper ρ radius) =
          2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ
  square_mellin_integrals :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
          (RectangleGeometry.centeredSquareLower 0 radius)
          (RectangleGeometry.centeredSquareUpper 0 radius) =
        2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtZero x ∧
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
          (RectangleGeometry.centeredSquareLower 1 radius)
          (RectangleGeometry.centeredSquareUpper 1 radius) =
        2 * Real.pi * Complex.I * riemannZetaLogResidueAtOne x ∧
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
          (RectangleGeometry.centeredSquareLower 1 radius)
          (RectangleGeometry.centeredSquareUpper 1 radius) =
        2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtOne x ∧
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
          (RectangleGeometry.centeredSquareLower 0 radius)
          (RectangleGeometry.centeredSquareUpper 0 radius) =
        2 * Real.pi * Complex.I * riemannZetaLogResidueAtZero x
  regular_subset : riemannZetaPuncturedRectangle z w radius ⊆ riemannZetaRegularSet

/-- The finite sum of reciprocal-kernel integrals around all enclosed singularities. -/
noncomputable def riemannZetaReciprocalLocalCircleLedger (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) : ℂ := by
  classical
    exact
    (if (0 : ℂ) ∈ Rectangle.rectangleClosedBox z w then
        ∮ s in C(0, certificate.radius), riemannZetaReciprocalContourKernel x s
      else 0) +
      (if (1 : ℂ) ∈ Rectangle.rectangleClosedBox z w then
        ∮ s in C(1, certificate.radius), riemannZetaReciprocalContourKernel x s
      else 0) +
      ∑ ρ ∈ riemannZetaZerosInAnyRectangle z w,
        ∮ s in C(ρ, certificate.radius), riemannZetaReciprocalContourKernel x s

/-- The finite sum of logarithmic-kernel integrals around all enclosed singularities. -/
noncomputable def riemannZetaLogLocalCircleLedger (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) : ℂ := by
  classical
    exact
    (if (0 : ℂ) ∈ Rectangle.rectangleClosedBox z w then
        ∮ s in C(0, certificate.radius), riemannZetaLogContourKernel x s
      else 0) +
      (if (1 : ℂ) ∈ Rectangle.rectangleClosedBox z w then
        ∮ s in C(1, certificate.radius), riemannZetaLogContourKernel x s
      else 0) +
      ∑ ρ ∈ riemannZetaZerosInAnyRectangle z w,
        ∮ s in C(ρ, certificate.radius), riemannZetaLogContourKernel x s

/-- The reciprocal circle-integral sum indexed uniformly by the full singularity ledger. -/
noncomputable def riemannZetaReciprocalAllSingularityCircleLedger (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) : ℂ :=
  ∑ s ∈ riemannZetaSingularitiesInRectangle z w,
    ∮ u in C(s, certificate.radius), riemannZetaReciprocalContourKernel x u

/-- The logarithmic circle-integral sum indexed uniformly by the full singularity ledger. -/
noncomputable def riemannZetaLogAllSingularityCircleLedger (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) : ℂ :=
  ∑ s ∈ riemannZetaSingularitiesInRectangle z w,
    ∮ u in C(s, certificate.radius), riemannZetaLogContourKernel x u

/-- The uniformly indexed reciprocal circle ledger equals the separated local-circle ledger. -/
theorem riemannZetaReciprocalAllSingularityCircleLedger_eq_localCircleLedger {x : ℝ} {z w : ℂ}
    (certificate : RiemannZetaPuncturedContourCertificate x z w) :
    riemannZetaReciprocalAllSingularityCircleLedger x z w certificate =
      riemannZetaReciprocalLocalCircleLedger x z w certificate := by
  unfold riemannZetaReciprocalAllSingularityCircleLedger
  rw [sum_riemannZetaSingularitiesInRectangle]
  rfl

/-- The uniformly indexed logarithmic circle ledger equals the separated local-circle ledger. -/
theorem riemannZetaLogAllSingularityCircleLedger_eq_localCircleLedger {x : ℝ} {z w : ℂ}
    (certificate : RiemannZetaPuncturedContourCertificate x z w) :
    riemannZetaLogAllSingularityCircleLedger x z w certificate =
      riemannZetaLogLocalCircleLedger x z w certificate := by
  unfold riemannZetaLogAllSingularityCircleLedger
  rw [sum_riemannZetaSingularitiesInRectangle]
  rfl

/--
A local geometric replacement of every singular cell boundary by its assigned small circle.

The assignment supplies the finite bijection between cells and singularities.  The two equality
fields are the remaining local geometric facts for the reciprocal and logarithmic kernels.  They
are deliberately separated from the analytic evaluation of each circle already stored in the
punctured-contour certificate.
-/
structure RiemannZetaSingularCellBoundaryCertificate (x : ℝ) (z w : ℂ) (cells : Finset (ℂ × ℂ))
    (certificate : RiemannZetaPuncturedContourCertificate x z w) where
  assignment : RiemannZetaSingularCellAssignment z w cells
  reciprocal_boundary_eq_circle :
    ∀ cell ∈ riemannZetaSingularCells z w cells,
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2 =
        ∮ u in C(assignment.pointOfCell cell, certificate.radius),
          riemannZetaReciprocalContourKernel x u
  log_boundary_eq_circle :
    ∀ cell ∈ riemannZetaSingularCells z w cells,
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2 =
        ∮ u in C(assignment.pointOfCell cell, certificate.radius), riemannZetaLogContourKernel x u

/--
Add local boundary identities to a geometrically separated singular-cell grid.

The separation certificate supplies the assignment automatically.  The two remaining hypotheses
are precisely the reciprocal and logarithmic local boundary deformations for each singular cell.
-/
noncomputable def riemannZetaSingularCellBoundaryCertificateOfSeparation {x : ℝ} {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} {certificate : RiemannZetaPuncturedContourCertificate x z w}
    (separation : RiemannZetaGridSingularitySeparation z w cells)
    (hreciprocal :
      ∀ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
            cell.2 =
          ∮ u in C(separation.toAssignment.pointOfCell cell, certificate.radius),
            riemannZetaReciprocalContourKernel x u)
    (hlog :
      ∀ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2 =
          ∮ u in C(separation.toAssignment.pointOfCell cell, certificate.radius),
            riemannZetaLogContourKernel x u) :
    RiemannZetaSingularCellBoundaryCertificate x z w cells certificate := by
  exact ⟨separation.toAssignment, hreciprocal, hlog⟩

/-- Add local boundary identities directly to an interior-separated grid. -/
noncomputable def riemannZetaSingularCellBoundaryCertificateOfInteriorSeparation {x : ℝ} {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} {certificate : RiemannZetaPuncturedContourCertificate x z w}
    (interior : RiemannZetaGridInteriorSeparation z w cells)
    (hreciprocal :
      ∀ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
            cell.2 =
          ∮ u in C(interior.toAssignment.pointOfCell cell, certificate.radius),
            riemannZetaReciprocalContourKernel x u)
    (hlog :
      ∀ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2 =
          ∮ u in C(interior.toAssignment.pointOfCell cell, certificate.radius),
            riemannZetaLogContourKernel x u) :
    RiemannZetaSingularCellBoundaryCertificate x z w cells certificate := by
  exact ⟨interior.toAssignment, hreciprocal, hlog⟩

/--
A finite grid-level certificate for the complete punctured-contour boundary decomposition.

The cell family lies in the outer rectangle.  The two boundary fields identify the outer contour
with the sum of every cell boundary; these may be supplied by
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.rectangleGridSubdivision`.  The
singular-cell certificate then replaces precisely the nonregular cell boundaries by their assigned
small circles.  Regular-cell cancellation is derived rather than stored.
-/
structure RiemannZetaGridBoundaryCertificate (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) where
  cells : Finset (ℂ × ℂ)
  cell_subset :
    ∀ cell ∈ cells, Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w
  reciprocal_boundary_eq_cells :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) z w =
      ∑ cell ∈ cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2
  log_boundary_eq_cells :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) z w =
      ∑ cell ∈ cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2
  singular_geometry : RiemannZetaSingularCellBoundaryCertificate x z w cells certificate

/--
Build the grid-level boundary certificate from finite real and imaginary cut lists.

`Nodup` permits the ordered cell list to be converted to a `Finset` without losing multiplicity.
The two integrability certificates drive the generic grid-subdivision theorem for each zeta kernel.
Cell containment and singular-cell local geometry remain explicit geometric inputs.
-/
noncomputable def riemannZetaGridBoundaryCertificateOfCuts (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) (xcuts ycuts : List ℝ)
    (hnodup : (RectangleGeometry.rectangleGridCells z w xcuts ycuts).Nodup)
    (hreciprocal :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x) z
        w xcuts ycuts)
    (hlog :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) z w xcuts
        ycuts)
    (hsubset :
      ∀ cell ∈ (RectangleGeometry.rectangleGridCells z w xcuts ycuts).toFinset,
        Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w)
    (geometry :
      RiemannZetaSingularCellBoundaryCertificate x z w
        (RectangleGeometry.rectangleGridCells z w xcuts ycuts).toFinset certificate) :
    RiemannZetaGridBoundaryCertificate x z w certificate := by
  let cells := (RectangleGeometry.rectangleGridCells z w xcuts ycuts).toFinset
  refine ⟨cells, hsubset, ?_, ?_, geometry⟩
  · unfold RectangleGeometry.rectangleBoundaryIntegral
    calc
      _ =
          RectangleGeometry.rectangleGridSubdivision (riemannZetaReciprocalContourKernel x) z w
            xcuts ycuts :=
        RectangleGeometry.rectangleBoundaryIntegral_eq_gridSubdivision _ z w xcuts ycuts hreciprocal
      _ =
          ∑ cell ∈ cells,
            RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
              cell.1 cell.2 :=
        RectangleGeometry.rectangleGridSubdivision_eq_sum_toFinset _ z w xcuts ycuts hnodup
  · unfold RectangleGeometry.rectangleBoundaryIntegral
    calc
      _ =
          RectangleGeometry.rectangleGridSubdivision (riemannZetaLogContourKernel x) z w xcuts
            ycuts :=
        RectangleGeometry.rectangleBoundaryIntegral_eq_gridSubdivision _ z w xcuts ycuts hlog
      _ =
          ∑ cell ∈ cells,
            RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1
              cell.2 :=
        RectangleGeometry.rectangleGridSubdivision_eq_sum_toFinset _ z w xcuts ycuts hnodup

/--
Build the grid certificate when every cut coordinate lies in the corresponding outer interval.

The generic grid-cell containment theorem discharges `cell_subset`, leaving no per-cell inclusion
proof for callers.
-/
noncomputable def riemannZetaGridBoundaryCertificateOfCutsInside (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) (xcuts ycuts : List ℝ)
    (hnodup : (RectangleGeometry.rectangleGridCells z w xcuts ycuts).Nodup)
    (hxcuts : ∀ u ∈ xcuts, u ∈ Set.uIcc z.re w.re) (hycuts : ∀ v ∈ ycuts, v ∈ Set.uIcc z.im w.im)
    (hreciprocal :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x) z
        w xcuts ycuts)
    (hlog :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) z w xcuts
        ycuts)
    (geometry :
      RiemannZetaSingularCellBoundaryCertificate x z w
        (RectangleGeometry.rectangleGridCells z w xcuts ycuts).toFinset certificate) :
    RiemannZetaGridBoundaryCertificate x z w certificate := by
  apply
    riemannZetaGridBoundaryCertificateOfCuts x z w certificate xcuts ycuts hnodup hreciprocal hlog
  · intro cell hcell
    have hcellList : cell ∈ RectangleGeometry.rectangleGridCells z w xcuts ycuts := by
      simpa only [List.mem_toFinset] using hcell
    exact RectangleGeometry.rectangleGridCells_closedBox_subset hxcuts hycuts cell hcellList
  · exact geometry

/--
Build the grid certificate from duplicate-free endpoint-augmented coordinate lists.

The generic two-dimensional cell theorem derives cell `Nodup`; cut membership separately derives
cell containment.
-/
noncomputable def riemannZetaGridBoundaryCertificateOfNodupCoordinates (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) (xcuts ycuts : List ℝ)
    (hxcoordinates : (z.re :: xcuts ++ [w.re]).Nodup)
    (hycoordinates : (z.im :: ycuts ++ [w.im]).Nodup) (hxcuts : ∀ u ∈ xcuts, u ∈ Set.uIcc z.re w.re)
    (hycuts : ∀ v ∈ ycuts, v ∈ Set.uIcc z.im w.im)
    (hreciprocal :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x) z
        w xcuts ycuts)
    (hlog :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) z w xcuts
        ycuts)
    (geometry :
      RiemannZetaSingularCellBoundaryCertificate x z w
        (RectangleGeometry.rectangleGridCells z w xcuts ycuts).toFinset certificate) :
    RiemannZetaGridBoundaryCertificate x z w certificate := by
  exact
    riemannZetaGridBoundaryCertificateOfCutsInside x z w certificate xcuts ycuts
      (RectangleGeometry.rectangleGridCells_nodup hxcoordinates hycoordinates) hxcuts hycuts
      hreciprocal hlog geometry

/--
Coordinate avoidance makes both zeta kernels integrable on every finite grid-coordinate segment.

`xcoordinates_pairwise`, `ycoordinates_pairwise`, `xcoordinate_mem_uIcc`, and
`ycoordinate_mem_uIcc` come directly from the generic
`PseudoPrime.AnalyticNumberTheory.RectangleGeometry.StrictGridCuts` API; no compatibility alias
or repeated geometry declarations are used here.
-/
theorem RiemannZetaGrid.kernelCoordinateIntegrable {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (havoid : (RiemannZetaGrid.LedgerAvoidsCoordinates grid)) :
    RectangleGeometry.RectangleGridCoordinateIntegrable (riemannZetaReciprocalContourKernel x)
        (z.re :: grid.xcuts ++ [w.re]) (z.im :: grid.ycuts ++ [w.im]) ∧
      RectangleGeometry.RectangleGridCoordinateIntegrable (riemannZetaLogContourKernel x)
        (z.re :: grid.xcuts ++ [w.re]) (z.im :: grid.ycuts ++ [w.im]) := by
  constructor
  · constructor
    · intro c hc a ha b hb
      exact
        (intervalIntegrable_riemannZetaKernels_horizontal hx (grid.xcoordinate_mem_uIcc ha)
            (grid.xcoordinate_mem_uIcc hb) (grid.ycoordinate_mem_uIcc hc) fun s hs hsc ↦
            (havoid s hs).2 (hsc ▸ hc)).1
    · intro c hc a ha b hb
      exact
        (intervalIntegrable_riemannZetaKernels_vertical hx (grid.xcoordinate_mem_uIcc hc)
            (grid.ycoordinate_mem_uIcc ha) (grid.ycoordinate_mem_uIcc hb) fun s hs hsc ↦
            (havoid s hs).1 (hsc ▸ hc)).1
  · constructor
    · intro c hc a ha b hb
      exact
        (intervalIntegrable_riemannZetaKernels_horizontal hx (grid.xcoordinate_mem_uIcc ha)
            (grid.xcoordinate_mem_uIcc hb) (grid.ycoordinate_mem_uIcc hc) fun s hs hsc ↦
            (havoid s hs).2 (hsc ▸ hc)).2
    · intro c hc a ha b hb
      exact
        (intervalIntegrable_riemannZetaKernels_vertical hx (grid.xcoordinate_mem_uIcc hc)
            (grid.ycoordinate_mem_uIcc ha) (grid.ycoordinate_mem_uIcc hb) fun s hs hsc ↦
            (havoid s hs).1 (hsc ▸ hc)).2

/-- Coordinate avoidance supplies both recursive zeta-kernel grid certificates. -/
theorem RiemannZetaGrid.kernelGridSubdivisionIntegrable {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (grid : RectangleGeometry.StrictGridCuts z w)
    (havoid : (RiemannZetaGrid.LedgerAvoidsCoordinates grid)) :
    RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x) z w
        grid.xcuts grid.ycuts ∧
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) z w
        grid.xcuts grid.ycuts := by
  have edges := RiemannZetaGrid.kernelCoordinateIntegrable hx grid havoid
  have hxcuts : ∀ c ∈ grid.xcuts, c ∈ z.re :: grid.xcuts ++ [w.re] := by
    intro c hc
    simp only [List.cons_append, List.mem_cons, List.mem_append, hc, List.not_mem_nil, or_false,
      true_or, or_true]
  have hycuts : ∀ c ∈ grid.ycuts, c ∈ z.im :: grid.ycuts ++ [w.im] := by
    intro c hc
    simp only [List.cons_append, List.mem_cons, List.mem_append, hc, List.not_mem_nil, or_false,
      true_or, or_true]
  constructor
  · exact
      edges.1.gridSubdivision
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            true_or])
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_true])
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            true_or])
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_true])
        grid.xcuts grid.ycuts hxcuts hycuts
  · exact
      edges.2.gridSubdivision
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            true_or])
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_true])
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            true_or])
        (by
          simp only [List.cons_append, List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            or_true])
        grid.xcuts grid.ycuts hxcuts hycuts

/-- The concrete finite-ledger grid has both zeta-kernel subdivision certificates. -/
theorem riemannZetaGeneratedGridSubdivisionIntegrable {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im) (hregular : RiemannZetaRectangleBoundaryIsRegular z w) :
    let grid := riemannZetaGeneratedStrictGridCuts z w hre him hregular
    RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x) z w
        grid.xcuts grid.ycuts ∧
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) z w
        grid.xcuts grid.ycuts := by
  let grid := riemannZetaGeneratedStrictGridCuts z w hre him hregular
  apply RiemannZetaGrid.kernelGridSubdivisionIntegrable hx grid
  exact
    (RiemannZetaGrid.ledgerAvoidsCoordinates_of_boundaryRegular grid) hregular
      (riemannZetaGeneratedStrictGridCuts_avoidsCuts hre him hregular)

/--
Build the grid certificate from strictly increasing cuts lying between ordered endpoints.

The endpoint-augmentation theorem turns the order hypotheses into duplicate-free coordinate
lists.  The preceding constructor then supplies both grid-cell uniqueness and containment.
-/
noncomputable def riemannZetaGridBoundaryCertificateOfStrictCuts (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) (xcuts ycuts : List ℝ)
    (hre : z.re < w.re) (him : z.im < w.im) (hxorder : xcuts.Pairwise (· < ·))
    (hyorder : ycuts.Pairwise (· < ·)) (hxcuts : ∀ u ∈ xcuts, z.re < u ∧ u < w.re)
    (hycuts : ∀ v ∈ ycuts, z.im < v ∧ v < w.im)
    (hreciprocal :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x) z
        w xcuts ycuts)
    (hlog :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) z w xcuts
        ycuts)
    (geometry :
      RiemannZetaSingularCellBoundaryCertificate x z w
        (RectangleGeometry.rectangleGridCells z w xcuts ycuts).toFinset certificate) :
    RiemannZetaGridBoundaryCertificate x z w certificate := by
  apply riemannZetaGridBoundaryCertificateOfNodupCoordinates x z w certificate xcuts ycuts
  · exact RectangleGeometry.endpointAugmentedCoordinates_nodup hre hxorder hxcuts
  · exact RectangleGeometry.endpointAugmentedCoordinates_nodup him hyorder hycuts
  · exact fun u hu ↦ Set.mem_uIcc_of_le (le_of_lt (hxcuts u hu).1) (le_of_lt (hxcuts u hu).2)
  · exact fun v hv ↦ Set.mem_uIcc_of_le (le_of_lt (hycuts v hv).1) (le_of_lt (hycuts v hv).2)
  · exact hreciprocal
  · exact hlog
  · exact geometry

/--
Build the grid boundary certificate from a packaged strict-grid geometry certificate.

All coordinate ordering, interior containment, and duplicate-elimination obligations are
discharged by `grid`; only kernel integrability and singular-cell local geometry remain explicit.
-/
noncomputable def riemannZetaGridBoundaryCertificateOfStrictGridCuts (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w)
    (grid : RectangleGeometry.StrictGridCuts z w)
    (hreciprocal :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x) z
        w grid.xcuts grid.ycuts)
    (hlog :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) z w
        grid.xcuts grid.ycuts)
    (geometry :
      RiemannZetaSingularCellBoundaryCertificate x z w
        (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset certificate) :
    RiemannZetaGridBoundaryCertificate x z w certificate := by
  exact
    riemannZetaGridBoundaryCertificateOfStrictCuts x z w certificate grid.xcuts grid.ycuts
      grid.re_lt grid.im_lt grid.xcuts_pairwise grid.ycuts_pairwise grid.xcuts_inside
      grid.ycuts_inside hreciprocal hlog geometry

/-- A certified reciprocal singular-cell sum equals the uniformly indexed circle ledger. -/
theorem RiemannZetaSingularCellBoundaryCertificate.sum_reciprocal_eq_circleLedger {x : ℝ} {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} {certificate : RiemannZetaPuncturedContourCertificate x z w}
    (geometry : RiemannZetaSingularCellBoundaryCertificate x z w cells certificate) :
    (∑ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2) =
      riemannZetaReciprocalAllSingularityCircleLedger x z w certificate := by
  rw [riemannZetaReciprocalAllSingularityCircleLedger]
  calc
    _ =
        ∑ cell ∈ riemannZetaSingularCells z w cells,
          ∮ u in C(geometry.assignment.pointOfCell cell, certificate.radius),
            riemannZetaReciprocalContourKernel x u :=
      by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact geometry.reciprocal_boundary_eq_circle cell hcell
    _ = _ :=
      geometry.assignment.sum_pointOfCell fun s ↦
        ∮ u in C(s, certificate.radius), riemannZetaReciprocalContourKernel x u

/-- A certified logarithmic singular-cell sum equals the uniformly indexed circle ledger. -/
theorem RiemannZetaSingularCellBoundaryCertificate.sum_log_eq_circleLedger {x : ℝ} {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} {certificate : RiemannZetaPuncturedContourCertificate x z w}
    (geometry : RiemannZetaSingularCellBoundaryCertificate x z w cells certificate) :
    (∑ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2) =
      riemannZetaLogAllSingularityCircleLedger x z w certificate := by
  rw [riemannZetaLogAllSingularityCircleLedger]
  calc
    _ =
        ∑ cell ∈ riemannZetaSingularCells z w cells,
          ∮ u in C(geometry.assignment.pointOfCell cell, certificate.radius),
            riemannZetaLogContourKernel x u :=
      by
      apply Finset.sum_congr rfl
      intro cell hcell
      exact geometry.log_boundary_eq_circle cell hcell
    _ = _ :=
      geometry.assignment.sum_pointOfCell fun s ↦
        ∮ u in C(s, certificate.radius), riemannZetaLogContourKernel x u

/-- A certified reciprocal singular-cell sum equals the existing local-circle ledger. -/
theorem RiemannZetaSingularCellBoundaryCertificate.sum_reciprocal_eq_localCircleLedger {x : ℝ}
    {z w : ℂ} {cells : Finset (ℂ × ℂ)} {certificate : RiemannZetaPuncturedContourCertificate x z w}
    (geometry : RiemannZetaSingularCellBoundaryCertificate x z w cells certificate) :
    (∑ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2) =
      riemannZetaReciprocalLocalCircleLedger x z w certificate := by
  exact
    geometry.sum_reciprocal_eq_circleLedger.trans
      (riemannZetaReciprocalAllSingularityCircleLedger_eq_localCircleLedger certificate)

/-- A certified logarithmic singular-cell sum equals the existing local-circle ledger. -/
theorem RiemannZetaSingularCellBoundaryCertificate.sum_log_eq_localCircleLedger {x : ℝ} {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} {certificate : RiemannZetaPuncturedContourCertificate x z w}
    (geometry : RiemannZetaSingularCellBoundaryCertificate x z w cells certificate) :
    (∑ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2) =
      riemannZetaLogLocalCircleLedger x z w certificate := by
  exact
    geometry.sum_log_eq_circleLedger.trans
      (riemannZetaLogAllSingularityCircleLedger_eq_localCircleLedger certificate)

/-- The remaining geometric boundary decomposition for the reciprocal kernel. -/
def RiemannZetaReciprocalBoundaryDecomposition (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) : Prop :=
  RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) z w =
    riemannZetaReciprocalLocalCircleLedger x z w certificate

/-- The remaining geometric boundary decomposition for the logarithmic kernel. -/
def RiemannZetaLogBoundaryDecomposition (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) : Prop :=
  RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) z w =
    riemannZetaLogLocalCircleLedger x z w certificate

/-- Both geometric decompositions attached to one punctured-contour certificate. -/
def RiemannZetaBoundaryDecomposition (x : ℝ) (z w : ℂ)
    (certificate : RiemannZetaPuncturedContourCertificate x z w) : Prop :=
  RiemannZetaReciprocalBoundaryDecomposition x z w certificate ∧
    RiemannZetaLogBoundaryDecomposition x z w certificate

/-- The finite reciprocal-kernel contour identity to be proved by residue summation. -/
def RiemannZetaReciprocalFiniteContourIdentity (x : ℝ) (z w : ℂ) : Prop :=
  RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) z w =
    2 * Real.pi * Complex.I * riemannZetaReciprocalContourResidueLedger x z w

/-- The finite logarithmic-kernel contour identity to be proved by residue summation. -/
def RiemannZetaLogFiniteContourIdentity (x : ℝ) (z w : ℂ) : Prop :=
  RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) z w =
    2 * Real.pi * Complex.I * riemannZetaLogContourResidueLedger x z w

/--
The reciprocal finite-contour identity solved for its right vertical side.

Input/assumptions: `hidentity` is the residue theorem on the rectangle from `z` to `w`.
Conclusion: the oriented right-edge integral is the residue ledger, the two horizontal edges,
and the left edge.  This is the algebraic form used when a sequence of regular rectangles tends
to infinite height.
Proof: unfold the four-edge boundary normalization and rearrange in `ℂ`.
Role: it isolates the only finite-contour algebra needed by the reciprocal vertical-limit step.
-/
theorem riemannZetaReciprocal_rightVertical_eq_of_finiteContourIdentity {x : ℝ} {z w : ℂ}
    (hidentity : RiemannZetaReciprocalFiniteContourIdentity x z w) :
    Complex.I •
        (∫ y : ℝ in z.im..w.im, riemannZetaReciprocalContourKernel x (w.re + y * Complex.I)) =
      2 * Real.pi * Complex.I * riemannZetaReciprocalContourResidueLedger x z w -
          (∫ u : ℝ in z.re..w.re, riemannZetaReciprocalContourKernel x (u + z.im * Complex.I)) +
        (∫ u : ℝ in z.re..w.re, riemannZetaReciprocalContourKernel x (u + w.im * Complex.I)) +
        Complex.I •
          (∫ y : ℝ in z.im..w.im, riemannZetaReciprocalContourKernel x (z.re + y * Complex.I)) := by
  unfold RiemannZetaReciprocalFiniteContourIdentity at hidentity
  unfold RectangleGeometry.rectangleBoundaryIntegral at hidentity
  linear_combination hidentity

/--
The logarithmic finite-contour identity solved for its right vertical side.

Input/assumptions: `hidentity` is the residue theorem on the rectangle from `z` to `w`.
Conclusion: the oriented right-edge integral is the residue ledger, the two horizontal edges,
and the left edge.  This is the finite algebraic precursor of the logarithmic vertical-limit
estimate.
Proof: unfold the four-edge boundary normalization and rearrange in `ℂ`.
Role: it gives the exact identity to which horizontal and left-edge estimates will be applied.
-/
theorem riemannZetaLog_rightVertical_eq_of_finiteContourIdentity {x : ℝ} {z w : ℂ}
    (hidentity : RiemannZetaLogFiniteContourIdentity x z w) :
    Complex.I • (∫ y : ℝ in z.im..w.im, riemannZetaLogContourKernel x (w.re + y * Complex.I)) =
      2 * Real.pi * Complex.I * riemannZetaLogContourResidueLedger x z w -
          (∫ u : ℝ in z.re..w.re, riemannZetaLogContourKernel x (u + z.im * Complex.I)) +
        (∫ u : ℝ in z.re..w.re, riemannZetaLogContourKernel x (u + w.im * Complex.I)) +
        Complex.I •
          (∫ y : ℝ in z.im..w.im, riemannZetaLogContourKernel x (z.re + y * Complex.I)) := by
  unfold RiemannZetaLogFiniteContourIdentity at hidentity
  unfold RectangleGeometry.rectangleBoundaryIntegral at hidentity
  linear_combination hidentity

/-- The reciprocal kernel's residue at zero is `log(2π)/x`. -/
theorem riemannZetaReciprocalResidueAtZero_eq (x : ℝ) :
    riemannZetaReciprocalResidueAtZero x = Complex.log (2 * Real.pi) * (x : ℂ)⁻¹ := by
  exact riemannZetaReciprocalZeroRegularization_zero x

/-- The logarithmic kernel's residue at one is `x`. -/
theorem riemannZetaLogResidueAtOne_eq (x : ℝ) : riemannZetaLogResidueAtOne x = x := by
  exact riemannZetaLogOneRegularization_one x

/-- The reciprocal residue formula at zero survives every sufficiently small radius. -/
theorem exists_radius_forall_circleIntegral_reciprocalKernel_zero_eq_residue {x : ℝ} (hx : 0 < x) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            (∮ z in C(0, r), riemannZetaReciprocalContourKernel x z) =
              2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtZero x := by
  have honeNhds : ∀ᶠ s : ℂ in nhds 0, s ≠ 1 :=
    compl_singleton_mem_nhds (by norm_num only : (0 : ℂ) ≠ 1)
  have hone : ∀ᶠ s : ℂ in nhdsWithin 0 ({0}ᶜ : Set ℂ), s ≠ 1 :=
    honeNhds.filter_mono nhdsWithin_le_nhds
  have heq :
    Filter.EventuallyEq (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (fun s ↦ (s - 0) * riemannZetaReciprocalContourKernel x s)
      (riemannZetaReciprocalZeroRegularization x) := by
    filter_upwards [eventually_mem_nhdsWithin, hone] with s hs0 hs1
    simpa only [sub_zero] using
      mul_riemannZetaReciprocalContourKernel x (Set.mem_compl_singleton_iff.mp hs0) hs1
  simpa only [riemannZetaReciprocalResidueAtZero] using
    General.exists_radius_forall_circleIntegral_eq_two_pi_I_mul
      (analyticAt_riemannZetaReciprocalZeroRegularization hx) heq

/-- The logarithmic residue formula at one survives every sufficiently small radius. -/
theorem exists_radius_forall_circleIntegral_logKernel_one_eq_residue {x : ℝ} (hx : 0 < x) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            (∮ z in C(1, r), riemannZetaLogContourKernel x z) =
              2 * Real.pi * Complex.I * riemannZetaLogResidueAtOne x := by
  simpa only [riemannZetaLogResidueAtOne] using
    General.exists_radius_forall_circleIntegral_eq_two_pi_I_mul
      (analyticAt_riemannZetaLogOneRegularization hx)
      (eventuallyEq_riemannZetaLogOneRegularization x)

/-- The reciprocal kernel's double-pole residue at one is `log x - 1 - γ`. -/
theorem riemannZetaReciprocalResidueAtOne_eq {x : ℝ} (hx : 0 < x) :
    riemannZetaReciprocalResidueAtOne x = Complex.log x - 1 - Real.eulerMascheroniConstant := by
  have hregular := differentiableAt_riemannZetaOneLogDerivativeRegularization
  have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  have hcpow : (x : ℂ) ≠ 0 ∨ (1 : ℂ) - 1 ≠ 0 := Or.inl hxne
  have hpow : DifferentiableAt ℂ (fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) 1 := by
    fun_prop (disch := assumption)
  unfold riemannZetaReciprocalResidueAtOne riemannZetaReciprocalOneRegularization
  have hdiv := ((hregular.mul hpow).hasDerivAt.div (hasDerivAt_id 1) one_ne_zero).deriv
  change
    deriv
        ((riemannZetaOneLogDerivativeRegularization * fun s : ℂ ↦ (x : ℂ) ^ (s - 1)) / (id : ℂ → ℂ))
        1 =
      _
  rw [hdiv]
  have hmul := (hregular.hasDerivAt.mul hpow.hasDerivAt).deriv
  rw [hmul, Complex.deriv_const_cpow (by fun_prop)]
  rw [deriv_riemannZetaOneLogDerivativeRegularization_one]
  simp only [sub_self, Complex.cpow_zero, mul_one, riemannZetaOneLogDerivativeRegularization_one,
    differentiableAt_fun_id, differentiableAt_const, deriv_fun_sub, deriv_id'', deriv_const',
    sub_zero, one_mul, id_eq, Pi.mul_apply, one_pow, div_one]
  ring

/-- The reciprocal residue formula at one survives every sufficiently small radius. -/
theorem exists_radius_forall_circleIntegral_reciprocalKernel_one_eq_residue {x : ℝ} (hx : 0 < x) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            (∮ z in C(1, r), riemannZetaReciprocalContourKernel x z) =
              2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtOne x := by
  simpa only [riemannZetaReciprocalResidueAtOne] using
    General.exists_radius_forall_circleIntegral_eq_two_pi_I_mul_deriv
      (analyticAt_riemannZetaReciprocalOneRegularization hx)
      (eventuallyEq_riemannZetaReciprocalOneRegularization x)

/-- The logarithmic residue formula at zero survives every sufficiently small radius. -/
theorem exists_radius_forall_circleIntegral_logKernel_zero_eq_residue {x : ℝ} (hx : 0 < x) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            (∮ z in C(0, r), riemannZetaLogContourKernel x z) =
              2 * Real.pi * Complex.I * riemannZetaLogResidueAtZero x := by
  have heq :
    Filter.EventuallyEq (nhdsWithin 0 ({0}ᶜ : Set ℂ))
      (fun s ↦ (s - 0) ^ 2 * riemannZetaLogContourKernel x s)
      (riemannZetaLogZeroRegularization x) := by
    filter_upwards [eventually_mem_nhdsWithin] with s hs0
    simpa only [sub_zero] using
      sq_mul_riemannZetaLogContourKernel x (Set.mem_compl_singleton_iff.mp hs0)
  simpa only [riemannZetaLogResidueAtZero] using
    General.exists_radius_forall_circleIntegral_eq_two_pi_I_mul_deriv
      (analyticAt_riemannZetaLogZeroRegularization hx) heq

/-- All four Mellin-pole formulas share one radius stable under shrinking. -/
theorem exists_radius_forall_circleIntegrals_eq_mellinResidues {x : ℝ} (hx : 0 < x) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            (∮ z in C(0, r), riemannZetaReciprocalContourKernel x z) =
                2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtZero x ∧
              (∮ z in C(1, r), riemannZetaLogContourKernel x z) =
                2 * Real.pi * Complex.I * riemannZetaLogResidueAtOne x ∧
              (∮ z in C(1, r), riemannZetaReciprocalContourKernel x z) =
                2 * Real.pi * Complex.I * riemannZetaReciprocalResidueAtOne x ∧
              (∮ z in C(0, r), riemannZetaLogContourKernel x z) =
                2 * Real.pi * Complex.I * riemannZetaLogResidueAtZero x := by
  obtain ⟨RreciprocalZero, hRreciprocalZero, hreciprocalZero⟩ :=
    exists_radius_forall_circleIntegral_reciprocalKernel_zero_eq_residue hx
  obtain ⟨RlogOne, hRlogOne, hlogOne⟩ :=
    exists_radius_forall_circleIntegral_logKernel_one_eq_residue hx
  obtain ⟨RreciprocalOne, hRreciprocalOne, hreciprocalOne⟩ :=
    exists_radius_forall_circleIntegral_reciprocalKernel_one_eq_residue hx
  obtain ⟨RlogZero, hRlogZero, hlogZero⟩ :=
    exists_radius_forall_circleIntegral_logKernel_zero_eq_residue hx
  let R := min (min RreciprocalZero RlogOne) (min RreciprocalOne RlogZero)
  have hR : 0 < R := lt_min (lt_min hRreciprocalZero hRlogOne) (lt_min hRreciprocalOne hRlogZero)
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  have hrreciprocalZero : r ≤ RreciprocalZero :=
    hrR.trans ((min_le_left _ _).trans (min_le_left _ _))
  have hrlogOne : r ≤ RlogOne := hrR.trans ((min_le_left _ _).trans (min_le_right _ _))
  have hrreciprocalOne : r ≤ RreciprocalOne :=
    hrR.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrlogZero : r ≤ RlogZero := hrR.trans ((min_le_right _ _).trans (min_le_right _ _))
  exact
    ⟨hreciprocalZero r hr hrreciprocalZero, hlogOne r hr hrlogOne,
      hreciprocalOne r hr hrreciprocalOne, hlogZero r hr hrlogZero⟩

/-- A reciprocal zero contribution is the center value of every matching regularization. -/
theorem riemannZetaReciprocalZeroContribution_eq_regularization_self (x : ℝ) (ρ : ℂ) (g : ℂ → ℂ) :
    riemannZetaReciprocalZeroContribution x ρ =
      riemannZetaReciprocalZetaZeroRegularization x ρ (riemannZetaZeroMultiplicity ρ) g ρ := by
  rw [riemannZetaReciprocalZetaZeroRegularization_self]
  rfl

/-- A logarithmic zero contribution is the center value of every matching regularization. -/
theorem riemannZetaLogZeroContribution_eq_regularization_self (x : ℝ) (ρ : ℂ) (g : ℂ → ℂ) :
    riemannZetaLogZeroContribution x ρ =
      riemannZetaLogZetaZeroRegularization x ρ (riemannZetaZeroMultiplicity ρ) g ρ := by
  rw [riemannZetaLogZetaZeroRegularization_self]
  rfl

/-- The reciprocal zero-contribution formula survives every sufficiently small radius. -/
theorem exists_radius_forall_circleIntegral_reciprocalKernel_eq_zeroContribution {x : ℝ}
    (hx : 0 < x) {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            (∮ z in C(ρ, r), riemannZetaReciprocalContourKernel x z) =
              2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ := by
  obtain ⟨g, _, hganalytic, hgzero, heq⟩ :=
    exists_eventuallyEq_reciprocalKernel_zetaZeroRegularization x hρ0 hρ1 hzero
  have hregular :=
    analyticAt_riemannZetaReciprocalZetaZeroRegularization hx hρ0 hρ1
      (riemannZetaZeroMultiplicity ρ) hganalytic hgzero
  obtain ⟨R, hR, hintegral⟩ :=
    General.exists_radius_forall_circleIntegral_eq_two_pi_I_mul hregular heq
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  rw [hintegral r hr hrR]
  rw [← riemannZetaReciprocalZeroContribution_eq_regularization_self x ρ g]

/-- The logarithmic zero-contribution formula survives every sufficiently small radius. -/
theorem exists_radius_forall_circleIntegral_logKernel_eq_zeroContribution {x : ℝ} (hx : 0 < x)
    {ρ : ℂ} (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            (∮ z in C(ρ, r), riemannZetaLogContourKernel x z) =
              2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ := by
  obtain ⟨g, _, hganalytic, hgzero, heq⟩ :=
    exists_eventuallyEq_logKernel_zetaZeroRegularization x hρ0 hρ1 hzero
  have hregular :=
    analyticAt_riemannZetaLogZetaZeroRegularization hx hρ0 (riemannZetaZeroMultiplicity ρ)
      hganalytic hgzero
  obtain ⟨R, hR, hintegral⟩ :=
    General.exists_radius_forall_circleIntegral_eq_two_pi_I_mul hregular heq
  refine ⟨R, hR, ?_⟩
  intro r hr hrR
  rw [hintegral r hr hrR]
  rw [← riemannZetaLogZeroContribution_eq_regularization_self x ρ g]

/-- Both kernel formulas at a zeta zero share one radius stable under shrinking. -/
theorem exists_radius_forall_circleIntegrals_eq_zeroContributions {x : ℝ} (hx : 0 < x) {ρ : ℂ}
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hzero : riemannZeta ρ = 0) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            (∮ z in C(ρ, r), riemannZetaReciprocalContourKernel x z) =
                2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ ∧
              (∮ z in C(ρ, r), riemannZetaLogContourKernel x z) =
                2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ := by
  obtain ⟨Rreciprocal, hRreciprocal, hreciprocal⟩ :=
    exists_radius_forall_circleIntegral_reciprocalKernel_eq_zeroContribution hx hρ0 hρ1 hzero
  obtain ⟨Rlog, hRlog, hlog⟩ :=
    exists_radius_forall_circleIntegral_logKernel_eq_zeroContribution hx hρ0 hρ1 hzero
  refine ⟨min Rreciprocal Rlog, lt_min hRreciprocal hRlog, ?_⟩
  intro r hr hrmin
  have hrreciprocal : r ≤ Rreciprocal := le_trans hrmin (min_le_left _ _)
  have hrlog : r ≤ Rlog := le_trans hrmin (min_le_right _ _)
  constructor
  · exact hreciprocal r hr hrreciprocal
  · exact hlog r hr hrlog

/-- All zeta zeros in one rectangle share a positive radius for both kernel formulas. -/
theorem exists_common_radius_circleIntegrals_eq_zeroContributions {x : ℝ} (hx : 0 < x) (z w : ℂ) :
    ∃ R : ℝ,
      0 < R ∧
        ∀ r : ℝ,
          0 < r →
            r ≤ R →
            ∀ ρ ∈ riemannZetaZerosInAnyRectangle z w,
              (∮ s in C(ρ, r), riemannZetaReciprocalContourKernel x s) =
                  2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ ∧
                (∮ s in C(ρ, r), riemannZetaLogContourKernel x s) =
                  2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ := by
  classical
  let S := riemannZetaZerosInAnyRectangle z w
  let certificate (ρ : ℂ) (hρ : ρ ∈ S) :=
    exists_radius_forall_circleIntegrals_eq_zeroContributions hx
      (ne_zero_of_mem_riemannZetaZerosInAnyRectangle hρ)
      (ne_one_of_mem_riemannZetaZerosInAnyRectangle hρ)
      ((mem_riemannZetaZerosInAnyRectangle_iff.mp hρ).2)
  let radius (ρ : ℂ) : ℝ := if hρ : ρ ∈ S then (certificate ρ hρ).choose else 1
  have hradius_pos (ρ : ℂ) (hρ : ρ ∈ S) : 0 < radius ρ := by
    dsimp only [radius]
    rw [dite_eq_left hρ]
    exact (certificate ρ hρ).choose_spec.1
  have hradius_formula (ρ : ℂ) (hρ : ρ ∈ S) (r : ℝ) (hr : 0 < r) (hrradius : r ≤ radius ρ) :
    (∮ s in C(ρ, r), riemannZetaReciprocalContourKernel x s) =
        2 * Real.pi * Complex.I * riemannZetaReciprocalZeroContribution x ρ ∧
      (∮ s in C(ρ, r), riemannZetaLogContourKernel x s) =
        2 * Real.pi * Complex.I * riemannZetaLogZeroContribution x ρ := by
    dsimp only [radius] at hrradius
    rw [dite_eq_left hρ] at hrradius
    exact (certificate ρ hρ).choose_spec.2 r hr hrradius
  let values := S.image radius ∪ {1}
  have hvalues : values.Nonempty :=
    ⟨1, by simp only [Finset.union_singleton, Finset.mem_insert, Finset.mem_image, true_or, values]⟩
  let R := values.min' hvalues
  have hRpos : 0 < R := by
    have hRmem := Finset.min'_mem values hvalues
    change 0 < values.min' hvalues
    rcases Finset.mem_union.mp hRmem with hRmem | hRmem
    · rcases Finset.mem_image.mp hRmem with ⟨ρ, hρ, hρR⟩
      rw [← hρR]
      exact hradius_pos ρ hρ
    · rw [Finset.mem_singleton.mp hRmem]
      norm_num only
  refine ⟨R, hRpos, ?_⟩
  intro r hr hrR ρ hρ
  have hradius_mem : radius ρ ∈ values :=
    Finset.mem_union_left _ (Finset.mem_image.mpr ⟨ρ, hρ, rfl⟩)
  have hRradius : R ≤ radius ρ := Finset.min'_le values _ hradius_mem
  exact hradius_formula ρ hρ r hr (hrR.trans hRradius)

/-- For positive `x`, a rectangle with regular boundary admits a punctured-contour
certificate below any prescribed positive radius. Take a minimum of the
geometric and analytic radius bounds; all local formulas persist upon shrinking. -/
theorem exists_riemannZetaPuncturedContourCertificate_le {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w) {ε : ℝ} (hε : 0 < ε) :
    Nonempty
      { certificate : RiemannZetaPuncturedContourCertificate x z w // certificate.radius ≤ ε } := by
  obtain ⟨Rgeometry, hRgeometry, hboundary, hpairs⟩ :=
    exists_pairwise_disjoint_riemannZetaSingularityRadius hregular
  obtain ⟨Rzero, hRzero, hzero⟩ := exists_common_radius_circleIntegrals_eq_zeroContributions hx z w
  obtain ⟨Rmellin, hRmellin, hmellin⟩ := exists_radius_forall_circleIntegrals_eq_mellinResidues hx
  obtain ⟨RsquareZero, hRsquareZero, hsquareZero⟩ :=
    exists_common_radius_llsRectangleBoundaryIntegrals_eq_zeroContributions hx z w
  obtain ⟨RsquareMellin, hRsquareMellin, hsquareMellin⟩ :=
    exists_radius_forall_llsRectangleBoundaryIntegrals_eq_mellinResidues hx
  let R := min (min (min (min Rgeometry Rzero) Rmellin) (min RsquareZero RsquareMellin)) ε
  have hR : 0 < R :=
    lt_min
      (lt_min (lt_min (lt_min hRgeometry hRzero) hRmellin) (lt_min hRsquareZero hRsquareMellin)) hε
  have hRgeometry' : R ≤ Rgeometry :=
    (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _)))
  have hRzero' : R ≤ Rzero :=
    (min_le_left _ _).trans ((min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _)))
  have hRmellin' : R ≤ Rmellin :=
    (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have hRsquareZero' : R ≤ RsquareZero :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hRsquareMellin' : R ≤ RsquareMellin :=
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hRε : R ≤ ε := min_le_right _ _
  refine
    ⟨⟨{   radius := R
          radius_pos := hR
          boundary_disjoint := ?_
          pairwise_disjoint := ?_
          zero_integrals := hzero R hR hRzero'
          mellin_integrals := hmellin R hR hRmellin'
          square_zero_integrals := hsquareZero R hR hRsquareZero'
          square_mellin_integrals := hsquareMellin R hR hRsquareMellin'
          regular_subset := riemannZetaPuncturedRectangle_subset_regularSet hR.le }, hRε⟩⟩
  · intro s hs
    apply RectangleGeometry.disjoint_closedBall_rectangleClosedBoxBoundary
    intro y hy
    exact lt_of_le_of_lt hRgeometry' (hboundary s hs y hy)
  · intro s hs t ht hst
    apply RectangleGeometry.disjoint_singularity_closedBalls
    have hpairs' := hpairs s hs t ht hst
    linarith

/--
Choose a punctured-contour certificate whose closed circles lie inside their assigned open cells.

Finite interior separation first gives a common positive cell margin.  The bounded certificate
constructor then shrinks all analytic and geometric radii below that margin, while retaining every
local circle formula needed by the residue ledger.
-/
theorem RiemannZetaGridInteriorSeparation.exists_puncturedContourCertificate_inside_cells {x : ℝ}
    (hx : 0 < x) {z w : ℂ} (hregular : RiemannZetaRectangleBoundaryIsRegular z w)
    {cells : Finset (ℂ × ℂ)} (interior : RiemannZetaGridInteriorSeparation z w cells) :
    Nonempty
      { certificate : RiemannZetaPuncturedContourCertificate x z w //
        ∀ cell ∈ riemannZetaSingularCells z w cells,
          Metric.closedBall (interior.toAssignment.pointOfCell cell) certificate.radius ⊆
            RectangleGeometry.rectangleOpenBox cell.1 cell.2 } := by
  obtain ⟨ε, hε, hcells⟩ := interior.exists_common_cell_radius
  obtain ⟨certificate, hradius⟩ := exists_riemannZetaPuncturedContourCertificate_le hx hregular hε
  refine ⟨⟨certificate, ?_⟩⟩
  intro cell hcell y hy
  apply hcells cell hcell
  exact Metric.mem_closedBall.mpr ((Metric.mem_closedBall.mp hy).trans hradius)

/-- The generated strict grid admits a puncture certificate contained cell by cell. -/
theorem exists_riemannZetaGeneratedPuncturedContourCertificate_inside_cells {x : ℝ} (hx : 0 < x)
    {z w : ℂ} (hre : z.re < w.re) (him : z.im < w.im)
    (hregular : RiemannZetaRectangleBoundaryIsRegular z w) :
    let grid := riemannZetaGeneratedStrictGridCuts z w hre him hregular
    let cells := (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset
    let interior := riemannZetaGeneratedGridInteriorSeparation hre him hregular
    Nonempty
      { certificate : RiemannZetaPuncturedContourCertificate x z w //
        ∀ cell ∈ riemannZetaSingularCells z w cells,
          Metric.closedBall (interior.toAssignment.pointOfCell cell) certificate.radius ⊆
            RectangleGeometry.rectangleOpenBox cell.1 cell.2 } := by
  let grid := riemannZetaGeneratedStrictGridCuts z w hre him hregular
  let cells := (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset
  let interior : RiemannZetaGridInteriorSeparation z w cells :=
    riemannZetaGeneratedGridInteriorSeparation hre him hregular
  exact
    RiemannZetaGridInteriorSeparation.exists_puncturedContourCertificate_inside_cells hx hregular
      interior

/--
For the generated grid, only the two cell-to-circle identities remain to build the boundary data.

All cut ordering, cell containment, singularity assignment, and both kernel integrability
certificates are supplied by the generated-grid theorems.  The hypotheses are exactly the local
deformation statements still requiring the dedicated punctured-cell argument.
-/
noncomputable def riemannZetaGeneratedGridBoundaryCertificate {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im) (hregular : RiemannZetaRectangleBoundaryIsRegular z w)
    (certificate : RiemannZetaPuncturedContourCertificate x z w)
    (hreciprocal :
      let grid := riemannZetaGeneratedStrictGridCuts z w hre him hregular
      let cells := (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset
      let interior := riemannZetaGeneratedGridInteriorSeparation hre him hregular
      ∀ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
            cell.2 =
          ∮ u in C(interior.toAssignment.pointOfCell cell, certificate.radius),
            riemannZetaReciprocalContourKernel x u)
    (hlog :
      let grid := riemannZetaGeneratedStrictGridCuts z w hre him hregular
      let cells := (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset
      let interior := riemannZetaGeneratedGridInteriorSeparation hre him hregular
      ∀ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2 =
          ∮ u in C(interior.toAssignment.pointOfCell cell, certificate.radius),
            riemannZetaLogContourKernel x u) :
    RiemannZetaGridBoundaryCertificate x z w certificate := by
  let grid := riemannZetaGeneratedStrictGridCuts z w hre him hregular
  let cells := (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset
  let interior : RiemannZetaGridInteriorSeparation z w cells :=
    riemannZetaGeneratedGridInteriorSeparation hre him hregular
  have hintegrable := riemannZetaGeneratedGridSubdivisionIntegrable hx hre him hregular
  let geometry :=
    riemannZetaSingularCellBoundaryCertificateOfInteriorSeparation interior hreciprocal hlog
  exact
    riemannZetaGridBoundaryCertificateOfStrictGridCuts x z w certificate grid hintegrable.1
      hintegrable.2 geometry

/-- The reciprocal local-circle ledger equals `2πi` times its residue ledger. -/
theorem riemannZetaReciprocalLocalCircleLedger_eq_residueLedger {x : ℝ} {z w : ℂ}
    (certificate : RiemannZetaPuncturedContourCertificate x z w) :
    riemannZetaReciprocalLocalCircleLedger x z w certificate =
      2 * Real.pi * Complex.I * riemannZetaReciprocalContourResidueLedger x z w := by
  classical
  have hmellin := certificate.mellin_integrals
  have hsum :
    (∑ ρ ∈ riemannZetaZerosInAnyRectangle z w,
        ∮ s in C(ρ, certificate.radius), riemannZetaReciprocalContourKernel x s) =
      2 * Real.pi * Complex.I * riemannZetaReciprocalContourZeroLedger x z w := by
    rw [riemannZetaReciprocalContourZeroLedger, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact (certificate.zero_integrals ρ hρ).1
  unfold riemannZetaReciprocalLocalCircleLedger
  rw [hmellin.1, hmellin.2.2.1, hsum]
  unfold riemannZetaReciprocalContourResidueLedger riemannZetaReciprocalMellinPoleLedger
  split_ifs <;> ring

/-- The logarithmic local-circle ledger equals `2πi` times its residue ledger. -/
theorem riemannZetaLogLocalCircleLedger_eq_residueLedger {x : ℝ} {z w : ℂ}
    (certificate : RiemannZetaPuncturedContourCertificate x z w) :
    riemannZetaLogLocalCircleLedger x z w certificate =
      2 * Real.pi * Complex.I * riemannZetaLogContourResidueLedger x z w := by
  classical
  have hmellin := certificate.mellin_integrals
  have hsum :
    (∑ ρ ∈ riemannZetaZerosInAnyRectangle z w,
        ∮ s in C(ρ, certificate.radius), riemannZetaLogContourKernel x s) =
      2 * Real.pi * Complex.I * riemannZetaLogContourZeroLedger x z w := by
    rw [riemannZetaLogContourZeroLedger, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro ρ hρ
    exact (certificate.zero_integrals ρ hρ).2
  unfold riemannZetaLogLocalCircleLedger
  rw [hmellin.2.2.2, hmellin.2.1, hsum]
  unfold riemannZetaLogContourResidueLedger riemannZetaLogMellinPoleLedger
  split_ifs <;> ring

/-- The geometric reciprocal decomposition implies the finite reciprocal contour identity. -/
theorem riemannZetaReciprocalFiniteContourIdentity_of_boundaryDecomposition
    (certificate : RiemannZetaPuncturedContourCertificate x z w)
    (hdecomposition : RiemannZetaReciprocalBoundaryDecomposition x z w certificate) :
    RiemannZetaReciprocalFiniteContourIdentity x z w := by
  unfold RiemannZetaReciprocalBoundaryDecomposition at hdecomposition
  unfold RiemannZetaReciprocalFiniteContourIdentity
  rw [hdecomposition, riemannZetaReciprocalLocalCircleLedger_eq_residueLedger certificate]

/-- The geometric logarithmic decomposition implies the finite logarithmic contour identity. -/
theorem riemannZetaLogFiniteContourIdentity_of_boundaryDecomposition {x : ℝ} {z w : ℂ}
    (certificate : RiemannZetaPuncturedContourCertificate x z w)
    (hdecomposition : RiemannZetaLogBoundaryDecomposition x z w certificate) :
    RiemannZetaLogFiniteContourIdentity x z w := by
  unfold RiemannZetaLogBoundaryDecomposition at hdecomposition
  unfold RiemannZetaLogFiniteContourIdentity
  rw [hdecomposition, riemannZetaLogLocalCircleLedger_eq_residueLedger certificate]

/-- Both geometric decompositions imply both finite zeta contour identities. -/
theorem riemannZetaFiniteContourIdentities_of_boundaryDecomposition {x : ℝ} {z w : ℂ}
    (certificate : RiemannZetaPuncturedContourCertificate x z w)
    (hdecomposition : RiemannZetaBoundaryDecomposition x z w certificate) :
    RiemannZetaReciprocalFiniteContourIdentity x z w ∧
      RiemannZetaLogFiniteContourIdentity x z w := by
  exact
    ⟨riemannZetaReciprocalFiniteContourIdentity_of_boundaryDecomposition certificate
        hdecomposition.1,
      riemannZetaLogFiniteContourIdentity_of_boundaryDecomposition certificate hdecomposition.2⟩

/-- The reciprocal contour kernel is differentiable throughout its regular locus. -/
theorem differentiableOn_riemannZetaReciprocalContourKernel {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (riemannZetaReciprocalContourKernel x) riemannZetaRegularSet := by
  intro s hs
  exact
    DifferentiableAt.differentiableWithinAt
      (differentiableAt_riemannZetaReciprocalContourKernel hx hs.1 hs.2.1 hs.2.2)

/-- The logarithmically weighted kernel is differentiable throughout its regular locus. -/
theorem differentiableOn_riemannZetaLogContourKernel {x : ℝ} (hx : 0 < x) :
    DifferentiableOn ℂ (riemannZetaLogContourKernel x) riemannZetaRegularSet := by
  intro s hs
  exact
    DifferentiableAt.differentiableWithinAt
      (differentiableAt_riemannZetaLogContourKernel hx hs.1 hs.2.1 hs.2.2)

/-- Both zeta kernels are differentiable on a cell-contained punctured centered square. -/
theorem RiemannZetaSingularCellAssignment.differentiableOn_centeredSquarePuncturedRegion {x : ℝ}
    (hx : 0 < x) {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : RiemannZetaSingularCellAssignment z w cells) {parent : ℂ × ℂ}
    (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    (hre : parent.1.re < parent.2.re) (him : parent.1.im < parent.2.im) {R ρ : ℝ} (hR : 0 < R)
    (hρ : 0 < ρ)
    (hball :
      Metric.closedBall (assignment.pointOfCell parent) R ⊆
        RectangleGeometry.rectangleOpenBox parent.1 parent.2) :
    DifferentiableOn ℂ (riemannZetaReciprocalContourKernel x)
        (centeredSquarePuncturedRegion (assignment.pointOfCell parent) R ρ) ∧
      DifferentiableOn ℂ (riemannZetaLogContourKernel x)
        (centeredSquarePuncturedRegion (assignment.pointOfCell parent) R ρ) := by
  have hsubset :=
    assignment.centeredSquarePuncturedRegion_subset_regularSet hparent hparentSubset hre him hR hρ
      hball
  exact
    ⟨(differentiableOn_riemannZetaReciprocalContourKernel hx).mono hsubset,
      (differentiableOn_riemannZetaLogContourKernel hx).mono hsubset⟩

/-- A regular rectangle has zero reciprocal-kernel boundary integral. -/
theorem llsRectangleBoundaryIntegral_reciprocal_eq_zero {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hrect : RiemannZetaRectangleIsRegular z w) :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) z w = 0 := by
  change (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ riemannZetaRegularSet at hrect
  unfold RectangleGeometry.rectangleBoundaryIntegral
  exact
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ z w
      ((differentiableOn_riemannZetaReciprocalContourKernel hx).mono hrect)

/-- A regular rectangle has zero logarithmic-kernel boundary integral. -/
theorem llsRectangleBoundaryIntegral_log_eq_zero {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hrect : RiemannZetaRectangleIsRegular z w) :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) z w = 0 := by
  change (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) ⊆ riemannZetaRegularSet at hrect
  unfold RectangleGeometry.rectangleBoundaryIntegral
  exact
    Complex.integral_boundary_rect_eq_zero_of_differentiableOn _ z w
      ((differentiableOn_riemannZetaLogContourKernel hx).mono hrect)

/--
Regularity of the eight cells surrounding an inner rectangle contracts both zeta contours to it.

The two subdivision certificates perform the algebraic `3 × 3` cancellation.  Cauchy--Goursat
sets every noncentral cell boundary to zero, so only the inner rectangle remains for each kernel.
-/
theorem riemannZetaContourKernels_boundary_eq_innerRectangle {x : ℝ} (hx : 0 < x) {z w a b : ℂ}
    (hreciprocal :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaReciprocalContourKernel x) z
        w [a.re, b.re] [a.im, b.im])
    (hlog :
      RectangleGeometry.RectangleGridSubdivisionIntegrable (riemannZetaLogContourKernel x) z w
        [a.re, b.re] [a.im, b.im])
    (hnodup : (RectangleGeometry.rectangleGridCells z w [a.re, b.re] [a.im, b.im]).Nodup)
    (hregular :
      ∀ cell ∈ (RectangleGeometry.rectangleGridCells z w [a.re, b.re] [a.im, b.im]).toFinset,
        cell ≠ (a, b) → RiemannZetaRectangleIsRegular cell.1 cell.2) :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) z w =
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) a b ∧
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) z w =
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) a b := by
  constructor
  · apply RectangleGeometry.rectangleBoundaryIntegral_eq_innerRectangle _ z w a b hreciprocal hnodup
    intro cell hcell hne
    exact llsRectangleBoundaryIntegral_reciprocal_eq_zero hx (hregular cell hcell hne)
  · apply RectangleGeometry.rectangleBoundaryIntegral_eq_innerRectangle _ z w a b hlog hnodup
    intro cell hcell hne
    exact llsRectangleBoundaryIntegral_log_eq_zero hx (hregular cell hcell hne)

/--
A cell-contained centered square contracts both singular-cell contours to its square boundary.

The ball containment supplies strict cuts, finite coordinate integrability, and a centered point in
the inner open rectangle.  Assignment uniqueness makes all eight surrounding cells regular, so the
preceding Cauchy--Goursat contraction theorem applies without further local hypotheses.
-/
theorem RiemannZetaSingularCellAssignment.boundary_eq_centeredSquare {x : ℝ} (hx : 0 < x) {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    (hre : parent.1.re < parent.2.re) (him : parent.1.im < parent.2.im) {r : ℝ} (hr : 0 < r)
    (hball :
      Metric.closedBall (assignment.pointOfCell parent) r ⊆
        RectangleGeometry.rectangleOpenBox parent.1 parent.2) :
    let a := RectangleGeometry.centeredSquareLower (assignment.pointOfCell parent) r
    let b := RectangleGeometry.centeredSquareUpper (assignment.pointOfCell parent) r
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) parent.1
          parent.2 =
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) a b ∧
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) parent.1
          parent.2 =
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) a b := by
  let c := assignment.pointOfCell parent
  let a := RectangleGeometry.centeredSquareLower c r
  let b := RectangleGeometry.centeredSquareUpper c r
  have hcuts := RectangleGeometry.centeredSquare_cuts_inside hre him hr hball
  have hintegrable :=
    RiemannZetaSingularCellAssignment.centeredSquare_kernelGridSubdivisionIntegrable hx assignment
      hparent hparentSubset hre him hr hball
  have hnodup :=
    RectangleGeometry.threeByThreeGrid_nodup hcuts.1 hcuts.2.1 hcuts.2.2.1 hcuts.2.2.2.1
      hcuts.2.2.2.2.1 hcuts.2.2.2.2.2
  apply riemannZetaContourKernels_boundary_eq_innerRectangle hx hintegrable.1 hintegrable.2 hnodup
  exact
    assignment.threeByThree_surrounding_regular hparent hparentSubset hcuts.1 hcuts.2.1 hcuts.2.2.1
      hcuts.2.2.2.1 hcuts.2.2.2.2.1 hcuts.2.2.2.2.2
      (RectangleGeometry.center_mem_centeredSquare_openBox c hr)

/-- Both local kernel integrals are invariant between nested circles in one singular cell. -/
theorem RiemannZetaSingularCellAssignment.circleIntegrals_eq_of_le {x : ℝ} (hx : 0 < x) {z w : ℂ}
    {cells : Finset (ℂ × ℂ)} (assignment : RiemannZetaSingularCellAssignment z w cells)
    {parent : ℂ × ℂ} (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hball :
      Metric.closedBall (assignment.pointOfCell parent) R ⊆
        RectangleGeometry.rectangleOpenBox parent.1 parent.2) :
    (∮ u in C(assignment.pointOfCell parent, R), riemannZetaReciprocalContourKernel x u) =
        ∮ u in C(assignment.pointOfCell parent, r), riemannZetaReciprocalContourKernel x u ∧
      (∮ u in C(assignment.pointOfCell parent, R), riemannZetaLogContourKernel x u) =
        ∮ u in C(assignment.pointOfCell parent, r), riemannZetaLogContourKernel x u := by
  constructor
  · exact
      assignment.circleIntegral_eq_of_le hparent hparentSubset hr hrR hball
        (differentiableOn_riemannZetaReciprocalContourKernel hx)
  · exact
      assignment.circleIntegral_eq_of_le hparent hparentSubset hr hrR hball
        (differentiableOn_riemannZetaLogContourKernel hx)

/--
Same-radius square-to-circle identities complete the local singular-cell deformation.

The parent boundary first contracts to the centered square.  The supplied identities replace that
square by the circle of coordinate radius `R`, and annulus invariance then shrinks this circle to
the target radius `r`.  Thus the only remaining analytic input is the same-radius comparison.
-/
theorem RiemannZetaSingularCellAssignment.boundary_eq_circle_of_square_eq_circle {x : ℝ}
    (hx : 0 < x) {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : RiemannZetaSingularCellAssignment z w cells) {parent : ℂ × ℂ}
    (hparent : parent ∈ riemannZetaSingularCells z w cells)
    (hparentSubset :
      Rectangle.rectangleClosedBox parent.1 parent.2 ⊆ Rectangle.rectangleClosedBox z w)
    (hre : parent.1.re < parent.2.re) (him : parent.1.im < parent.2.im) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R)
    (hball :
      Metric.closedBall (assignment.pointOfCell parent) R ⊆
        RectangleGeometry.rectangleOpenBox parent.1 parent.2)
    (hsquareReciprocal :
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
          (RectangleGeometry.centeredSquareLower (assignment.pointOfCell parent) R)
          (RectangleGeometry.centeredSquareUpper (assignment.pointOfCell parent) R) =
        ∮ u in C(assignment.pointOfCell parent, R), riemannZetaReciprocalContourKernel x u)
    (hsquareLog :
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
          (RectangleGeometry.centeredSquareLower (assignment.pointOfCell parent) R)
          (RectangleGeometry.centeredSquareUpper (assignment.pointOfCell parent) R) =
        ∮ u in C(assignment.pointOfCell parent, R), riemannZetaLogContourKernel x u) :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) parent.1
          parent.2 =
        ∮ u in C(assignment.pointOfCell parent, r), riemannZetaReciprocalContourKernel x u ∧
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) parent.1
          parent.2 =
        ∮ u in C(assignment.pointOfCell parent, r), riemannZetaLogContourKernel x u := by
  have hR : 0 < R := hr.trans_le hrR
  have hsquare :=
    RiemannZetaSingularCellAssignment.boundary_eq_centeredSquare hx assignment hparent hparentSubset
      hre him hR hball
  have hcircle :=
    RiemannZetaSingularCellAssignment.circleIntegrals_eq_of_le hx assignment hparent hparentSubset
      hr hrR hball
  exact
    ⟨hsquare.1.trans (hsquareReciprocal.trans hcircle.1),
      hsquare.2.trans (hsquareLog.trans hcircle.2)⟩

/--
A punctured-contour certificate discharges both cell-to-circle boundary identities for every
singular cell, using its bundled Mellin/zeta-zero circle and square boundary formulas.

The assigned point of every singular cell is `0`, `1`, or a zeta zero (`point_mem_ledger`).  In each
case the certificate already carries matching circle and square formulas at the same radius, so
their composition (`.trans .symm`) supplies `boundary_eq_circle_of_square_eq_circle`'s same-radius
hypothesis directly, with `r = R = certificate.radius`.
-/
theorem RiemannZetaSingularCellAssignment.reciprocal_log_boundary_eq_circle_of_certificate {x : ℝ}
    (hx : 0 < x) {z w : ℂ} {cells : Finset (ℂ × ℂ)}
    (assignment : RiemannZetaSingularCellAssignment z w cells)
    (certificate : RiemannZetaPuncturedContourCertificate x z w)
    (hcellsSubset :
      ∀ cell ∈ cells, Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w)
    (hballs :
      ∀ cell ∈ riemannZetaSingularCells z w cells,
        Metric.closedBall (assignment.pointOfCell cell) certificate.radius ⊆
          RectangleGeometry.rectangleOpenBox cell.1 cell.2)
    (hcellOrder :
      ∀ cell ∈ riemannZetaSingularCells z w cells, cell.1.re < cell.2.re ∧ cell.1.im < cell.2.im)
    {cell : ℂ × ℂ} (hcell : cell ∈ riemannZetaSingularCells z w cells) :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2 =
        ∮ u in C(assignment.pointOfCell cell, certificate.radius),
          riemannZetaReciprocalContourKernel x u ∧
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2 =
        ∮ u in C(assignment.pointOfCell cell, certificate.radius),
          riemannZetaLogContourKernel x u := by
  have hparentSubset := hcellsSubset cell (mem_riemannZetaSingularCells_iff.mp hcell).1
  have horder := hcellOrder cell hcell
  have hball := hballs cell hcell
  have hpointMem := assignment.point_mem_ledger cell hcell
  rw [mem_riemannZetaSingularitiesInRectangle_iff] at hpointMem
  rcases hpointMem.2 with h0 | h1 | hzero
  · have hsq :
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
          (RectangleGeometry.centeredSquareLower (assignment.pointOfCell cell) certificate.radius)
          (RectangleGeometry.centeredSquareUpper (assignment.pointOfCell cell) certificate.radius) =
        ∮ u in C(assignment.pointOfCell cell, certificate.radius),
          riemannZetaReciprocalContourKernel x u := by
      rw [h0]
      exact certificate.square_mellin_integrals.1.trans certificate.mellin_integrals.1.symm
    have hsl :
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
          (RectangleGeometry.centeredSquareLower (assignment.pointOfCell cell) certificate.radius)
          (RectangleGeometry.centeredSquareUpper (assignment.pointOfCell cell) certificate.radius) =
        ∮ u in C(assignment.pointOfCell cell, certificate.radius),
          riemannZetaLogContourKernel x u := by
      rw [h0]
      exact certificate.square_mellin_integrals.2.2.2.trans certificate.mellin_integrals.2.2.2.symm
    exact
      RiemannZetaSingularCellAssignment.boundary_eq_circle_of_square_eq_circle hx assignment hcell
        hparentSubset horder.1 horder.2 certificate.radius_pos le_rfl hball hsq hsl
  · have hsq :
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
          (RectangleGeometry.centeredSquareLower (assignment.pointOfCell cell) certificate.radius)
          (RectangleGeometry.centeredSquareUpper (assignment.pointOfCell cell) certificate.radius) =
        ∮ u in C(assignment.pointOfCell cell, certificate.radius),
          riemannZetaReciprocalContourKernel x u := by
      rw [h1]
      exact certificate.square_mellin_integrals.2.2.1.trans certificate.mellin_integrals.2.2.1.symm
    have hsl :
      RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x)
          (RectangleGeometry.centeredSquareLower (assignment.pointOfCell cell) certificate.radius)
          (RectangleGeometry.centeredSquareUpper (assignment.pointOfCell cell) certificate.radius) =
        ∮ u in C(assignment.pointOfCell cell, certificate.radius),
          riemannZetaLogContourKernel x u := by
      rw [h1]
      exact certificate.square_mellin_integrals.2.1.trans certificate.mellin_integrals.2.1.symm
    exact
      RiemannZetaSingularCellAssignment.boundary_eq_circle_of_square_eq_circle hx assignment hcell
        hparentSubset horder.1 horder.2 certificate.radius_pos le_rfl hball hsq hsl
  · have hρmem := mem_riemannZetaZerosInAnyRectangle_iff.mpr ⟨hpointMem.1, hzero⟩
    have hsq :=
      (certificate.square_zero_integrals _ hρmem).1.trans
        (certificate.zero_integrals _ hρmem).1.symm
    have hsl :=
      (certificate.square_zero_integrals _ hρmem).2.trans
        (certificate.zero_integrals _ hρmem).2.symm
    exact
      RiemannZetaSingularCellAssignment.boundary_eq_circle_of_square_eq_circle hx assignment hcell
        hparentSubset horder.1 horder.2 certificate.radius_pos le_rfl hball hsq hsl

/-- Every certified cell has zero reciprocal-kernel boundary integral. -/
theorem RiemannZetaRegularCellLedger.reciprocal_cell_integral_eq_zero {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (ledger : RiemannZetaRegularCellLedger z w) {cell : ℂ × ℂ} (hcell : cell ∈ ledger.cells) :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
        cell.2 =
      0 := by
  exact llsRectangleBoundaryIntegral_reciprocal_eq_zero hx (ledger.cell_isRegular hcell)

/-- Every certified cell has zero logarithmic-kernel boundary integral. -/
theorem RiemannZetaRegularCellLedger.log_cell_integral_eq_zero {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (ledger : RiemannZetaRegularCellLedger z w) {cell : ℂ × ℂ} (hcell : cell ∈ ledger.cells) :
    RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2 =
      0 := by
  exact llsRectangleBoundaryIntegral_log_eq_zero hx (ledger.cell_isRegular hcell)

/-- The sum of reciprocal-kernel boundary integrals over a regular-cell ledger is zero. -/
theorem RiemannZetaRegularCellLedger.sum_reciprocal_cell_integrals_eq_zero {x : ℝ} (hx : 0 < x)
    {z w : ℂ} (ledger : RiemannZetaRegularCellLedger z w) :
    (∑ cell ∈ ledger.cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2) =
      0 := by
  apply Finset.sum_eq_zero
  intro cell hcell
  exact RiemannZetaRegularCellLedger.reciprocal_cell_integral_eq_zero hx ledger hcell

/-- The sum of logarithmic-kernel boundary integrals over a regular-cell ledger is zero. -/
theorem RiemannZetaRegularCellLedger.sum_log_cell_integrals_eq_zero {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (ledger : RiemannZetaRegularCellLedger z w) :
    (∑ cell ∈ ledger.cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2) =
      0 := by
  apply Finset.sum_eq_zero
  intro cell hcell
  exact RiemannZetaRegularCellLedger.log_cell_integral_eq_zero hx ledger hcell

/-- After filtering a finite cell family, only singular cells contribute to the reciprocal sum. -/
theorem sum_reciprocal_cell_integrals_eq_sum_singularCells {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (cells : Finset (ℂ × ℂ))
    (hsubset :
      ∀ cell ∈ cells,
        Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w) :
    (∑ cell ∈ cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2) =
      ∑ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2 := by
  let ledger := riemannZetaRegularCellLedgerOfCells z w cells hsubset
  have hzero := RiemannZetaRegularCellLedger.sum_reciprocal_cell_integrals_eq_zero hx ledger
  have hpartition :=
    sum_regularCells_add_sum_singularCells z w cells
      (fun cell ↦
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2)
  change
    (∑ cell ∈ riemannZetaRegularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x) cell.1
          cell.2) =
      0 at hzero
  rw [← hpartition, hzero, zero_add]

/-- After filtering a finite cell family, only singular cells contribute to the logarithmic sum. -/
theorem sum_log_cell_integrals_eq_sum_singularCells {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (cells : Finset (ℂ × ℂ))
    (hsubset :
      ∀ cell ∈ cells,
        Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w) :
    (∑ cell ∈ cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2) =
      ∑ cell ∈ riemannZetaSingularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1
          cell.2 := by
  let ledger := riemannZetaRegularCellLedgerOfCells z w cells hsubset
  have hzero := RiemannZetaRegularCellLedger.sum_log_cell_integrals_eq_zero hx ledger
  have hpartition :=
    sum_regularCells_add_sum_singularCells z w cells
      (fun cell ↦
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2)
  change
    (∑ cell ∈ riemannZetaRegularCells z w cells,
        RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1 cell.2) =
      0 at hzero
  rw [← hpartition, hzero, zero_add]

/--
A finite grid certificate implies both geometric boundary decompositions.

For each kernel, the outer boundary first becomes the sum over all cells.  The regular-cell filter
vanishes by Cauchy--Goursat, leaving only singular cells, and the stored local geometry replaces
their boundaries by the existing local-circle ledger.
-/
theorem RiemannZetaGridBoundaryCertificate.boundaryDecomposition {x : ℝ} (hx : 0 < x) {z w : ℂ}
    {certificate : RiemannZetaPuncturedContourCertificate x z w}
    (grid : RiemannZetaGridBoundaryCertificate x z w certificate) :
    RiemannZetaBoundaryDecomposition x z w certificate := by
  constructor
  · unfold RiemannZetaReciprocalBoundaryDecomposition
    calc
      _ =
          ∑ cell ∈ grid.cells,
            RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
              cell.1 cell.2 :=
        grid.reciprocal_boundary_eq_cells
      _ =
          ∑ cell ∈ riemannZetaSingularCells z w grid.cells,
            RectangleGeometry.rectangleBoundaryIntegral (riemannZetaReciprocalContourKernel x)
              cell.1 cell.2 :=
        sum_reciprocal_cell_integrals_eq_sum_singularCells hx grid.cells grid.cell_subset
      _ = _ := grid.singular_geometry.sum_reciprocal_eq_localCircleLedger
  · unfold RiemannZetaLogBoundaryDecomposition
    calc
      _ =
          ∑ cell ∈ grid.cells,
            RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1
              cell.2 :=
        grid.log_boundary_eq_cells
      _ =
          ∑ cell ∈ riemannZetaSingularCells z w grid.cells,
            RectangleGeometry.rectangleBoundaryIntegral (riemannZetaLogContourKernel x) cell.1
              cell.2 :=
        sum_log_cell_integrals_eq_sum_singularCells hx grid.cells grid.cell_subset
      _ = _ := grid.singular_geometry.sum_log_eq_localCircleLedger

/-- A finite grid certificate implies both finite Riemann-zeta contour identities. -/
theorem RiemannZetaGridBoundaryCertificate.finiteContourIdentities {x : ℝ} (hx : 0 < x) {z w : ℂ}
    {certificate : RiemannZetaPuncturedContourCertificate x z w}
    (grid : RiemannZetaGridBoundaryCertificate x z w certificate) :
    RiemannZetaReciprocalFiniteContourIdentity x z w ∧
      RiemannZetaLogFiniteContourIdentity x z w := by
  exact
    riemannZetaFiniteContourIdentities_of_boundaryDecomposition certificate
      (grid.boundaryDecomposition hx)

/-- For positive `x`, an ordered rectangle with regular boundary admits a
finite-grid boundary certificate. Generate separating cuts and a cell-contained
puncture certificate, then use its matching circle and square residue formulas
to discharge each singular-cell deformation. -/
theorem exists_riemannZetaGeneratedGridBoundaryCertificate {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im) (hregular : RiemannZetaRectangleBoundaryIsRegular z w) :
    ∃ certificate : RiemannZetaPuncturedContourCertificate x z w,
      Nonempty (RiemannZetaGridBoundaryCertificate x z w certificate) := by
  let grid := riemannZetaGeneratedStrictGridCuts z w hre him hregular
  let cells := (RectangleGeometry.rectangleGridCells z w grid.xcuts grid.ycuts).toFinset
  let interior : RiemannZetaGridInteriorSeparation z w cells :=
    riemannZetaGeneratedGridInteriorSeparation hre him hregular
  obtain ⟨certificate, hballs⟩ :=
    exists_riemannZetaGeneratedPuncturedContourCertificate_inside_cells hx hre him hregular
  have hcellsSubset :
    ∀ cell ∈ cells, Rectangle.rectangleClosedBox cell.1 cell.2 ⊆ Rectangle.rectangleClosedBox z w :=
    fun cell hcell ↦
    RectangleGeometry.rectangleGridCells_closedBox_subset
      (fun u hu ↦ grid.xcoordinate_mem_uIcc (List.mem_cons_of_mem _ (List.mem_append_left _ hu)))
      (fun v hv ↦ grid.ycoordinate_mem_uIcc (List.mem_cons_of_mem _ (List.mem_append_left _ hv)))
      cell (List.mem_toFinset.mp hcell)
  have hcellOrder :
    ∀ cell ∈ riemannZetaSingularCells z w cells, cell.1.re < cell.2.re ∧ cell.1.im < cell.2.im :=
    fun cell hcell ↦
    RectangleGeometry.mem_rectangleGridCells_re_lt_im_lt grid.xcoordinates_pairwise
      grid.ycoordinates_pairwise
      (List.mem_toFinset.mp (mem_riemannZetaSingularCells_iff.mp hcell).1)
  refine
    ⟨certificate,
      ⟨riemannZetaGeneratedGridBoundaryCertificate hx hre him hregular certificate
          (fun cell hcell ↦
            (RiemannZetaSingularCellAssignment.reciprocal_log_boundary_eq_circle_of_certificate hx
                interior.toAssignment certificate hcellsSubset hballs hcellOrder hcell).1)
          (fun cell hcell ↦
            (RiemannZetaSingularCellAssignment.reciprocal_log_boundary_eq_circle_of_certificate hx
                interior.toAssignment certificate hcellsSubset hballs hcellOrder hcell).2)⟩⟩

/-- For positive `x`, an ordered rectangle with regular boundary satisfies
both finite zeta contour identities. Singularities inside the rectangle are allowed. -/
theorem riemannZetaFiniteContourIdentities_of_regular {x : ℝ} (hx : 0 < x) {z w : ℂ}
    (hre : z.re < w.re) (him : z.im < w.im) (hregular : RiemannZetaRectangleBoundaryIsRegular z w) :
    RiemannZetaReciprocalFiniteContourIdentity x z w ∧
      RiemannZetaLogFiniteContourIdentity x z w := by
  obtain ⟨certificate, ⟨grid⟩⟩ :=
    exists_riemannZetaGeneratedGridBoundaryCertificate hx hre him hregular
  exact grid.finiteContourIdentities hx

/-- The logarithmically weighted von Mangoldt sum equals a vertical-line integral
of the logarithmic zeta contour kernel. Apply Mellin inversion to each weight,
exchange the summation and integration by a summable majorant, and identify
the von Mangoldt Dirichlet series with `-ζ'/ζ`. -/
theorem mellinWeightTwo_vonMangoldt_tsum_eq {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * General.mellinWeightTwo ((n : ℝ) / x) =
      (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, riemannZetaLogContourKernel x ((τ : ℂ) + y * Complex.I) := by
  have hτ0 : (0 : ℝ) < τ := lt_trans one_pos hτ
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set K : ℝ → ℂ := fun y ↦ ((τ : ℂ) + y * Complex.I)⁻¹ ^ 2 with hK_def
  have hK_int : MeasureTheory.Integrable K := General.verticalIntegrable_mellinLogKernel hτ0.ne'
  set H : ℕ → ℝ → ℂ := fun n y ↦
    (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) *
      (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) with
    hH_def
  set G : ℕ → ℝ → ℂ := fun n y ↦ K y * H n y with hG_def
  have hnormH :
    ∀ n : ℕ,
      n ≠ 0 → ∀ y : ℝ, ‖H n y‖ = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ τ := by
    intro n hn y
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn_cpow : ‖(n : ℂ) ^ (-((τ : ℂ) + (y : ℂ) * Complex.I))‖ = (n : ℝ) ^ (-τ) := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      congr 1
      simp only [neg_add_rev, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero,
        zero_add]
    have hx_cpow : ‖(x : ℂ) ^ ((τ : ℂ) + (y : ℂ) * Complex.I)‖ = x ^ τ := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
        Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero]
    rw [hH_def]
    simp only [norm_mul, hn_cpow, hx_cpow]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  -- (1) term-by-term Mellin inversion
  have hterm_raw :
    ∀ n : ℕ,
      n ≠ 0 →
        General.mellinWeightTwo ((n : ℝ) / x) =
          (2 * Real.pi : ℝ)⁻¹ •
            ∫ y : ℝ,
              (((n : ℝ) / x : ℝ) : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) *
                (1 / ((τ : ℂ) + y * Complex.I) ^ 2) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnx : (0 : ℝ) < (n : ℝ) / x := div_pos hnpos hx
    have hmellin := General.mellinInv_mellinWeightTwo_eq (σ := τ) (x := (n : ℝ) / x) hτ0 hnx
    rw [← hmellin]
    simp only [mellinInv, smul_eq_mul, one_div]
  have hterm :
    ∀ n : ℕ,
      n ≠ 0 →
        (ArithmeticFunction.vonMangoldt n : ℂ) * General.mellinWeightTwo ((n : ℝ) / x) =
          (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, G n y := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [hterm_raw n hn, mul_smul_comm]
    congr 1
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    simp only [hG_def, hH_def, hK_def]
    rw [General.cpow_div_eq_cpow_mul_cpow_neg hnpos.le hx, neg_neg, one_div, inv_pow,
      Complex.ofReal_natCast]
    ring
  -- (2) each `G n` is integrable, dominated by a constant multiple of `K`
  have hGint : ∀ n : ℕ, MeasureTheory.Integrable (G n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hG0 : G 0 = fun _ ↦ (0 : ℂ) := by
        funext y
        simp only [hG_def, hH_def, neg_add_rev, ArithmeticFunction.map_zero, Complex.ofReal_zero,
          CharP.cast_eq_zero, zero_mul, mul_zero]
      rw [hG0]
      exact MeasureTheory.integrable_zero _ _ _
    · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      apply hK_int.mul_bdd
      · have hline : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) :=
          continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have hHcont : Continuous (H n) := by
          rw [hH_def]
          exact
            (continuous_const.mul (hline.neg.const_cpow (Or.inl hnC))).mul
              (hline.const_cpow (Or.inl hxC))
        exact hHcont.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun y ↦ (hnormH n hn y).le
  -- (3) the `L¹` norms of `G n` are summable
  have hGnorm_eq :
    ∀ n : ℕ,
      n ≠ 0 →
        ∫ y : ℝ, ‖G n y‖ =
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ τ) * ∫ y : ℝ, ‖K y‖ := by
    intro n hn
    have hcongr :
      (fun y : ℝ ↦ ‖G n y‖) = fun y : ℝ ↦
        (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ τ) * ‖K y‖ := by
      funext y
      rw [hG_def, norm_mul, hnormH n hn y, mul_comm]
    rw [hcongr, MeasureTheory.integral_const_mul]
  have hSummableL : Summable (fun n : ℕ ↦ ∫ y : ℝ, ‖G n y‖) := by
    have hΛ_summable :
      Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ)) := by
      have hLS :
        Summable
          (fun n : ℕ ↦
            ‖LSeries.term (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (τ : ℂ) n‖) :=
        summable_norm_iff.mpr
          (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (τ : ℂ))
            (by simpa only [Complex.ofReal_re] using hτ))
      refine hLS.congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
          zero_mul]
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        rw [LSeries.term_def]
        simp only [hn, ite_false]
        rw [norm_div, show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
          Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.ofReal_re, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.rpow_neg hnpos.le, div_eq_mul_inv]
    have hΛx_summable := hΛ_summable.mul_right (x ^ τ * ∫ y : ℝ, ‖K y‖)
    apply hΛx_summable.congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_mul, hG_def, hH_def,
        neg_add_rev, Complex.ofReal_zero, mul_zero, norm_zero, MeasureTheory.integral_zero]
    · rw [hGnorm_eq n hn]
      ring
  -- (4) exchange the sum and the integral
  have hInterchange := MeasureTheory.hasSum_integral_of_summable_integral_norm hGint hSummableL
  have hsum_eq_integral : ∑' n : ℕ, ∫ y : ℝ, G n y = ∫ y : ℝ, ∑' n : ℕ, G n y :=
    hInterchange.tsum_eq
  -- (5) identify the inner sum over `n` with the logarithmic contour kernel
  have hinner :
    ∀ y : ℝ, ∑' n : ℕ, G n y = riemannZetaLogContourKernel x ((τ : ℂ) + y * Complex.I) := by
    intro y
    have hLS :=
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (τ : ℂ) + y * Complex.I)
        (by
          simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hτ)
    have hsum :
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) =
        -deriv riemannZeta ((τ : ℂ) + y * Complex.I) / riemannZeta ((τ : ℂ) + y * Complex.I) := by
      rw [← hLS]
      unfold LSeries
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, CharP.cast_eq_zero,
          neg_add_rev, zero_mul, LSeries.term_zero]
      · rw [LSeries.term_def]
        simp only [hn, ite_false, div_eq_mul_inv, Complex.cpow_neg]
    calc
      ∑' n : ℕ, G n y =
          ∑' n : ℕ,
            K y *
              ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I))) *
              (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) :=
        by
        refine tsum_congr fun n ↦ ?_
        rw [hG_def, hH_def]
        ring
      _ =
          K y *
            (∑' n : ℕ,
              (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I))) *
            (x : ℂ) ^ ((τ : ℂ) + y * Complex.I) :=
        by rw [tsum_mul_right, tsum_mul_left]
      _ = riemannZetaLogContourKernel x ((τ : ℂ) + y * Complex.I) := by
        rw [hsum, hK_def, riemannZetaLogContourKernel]
        simp only [div_eq_mul_inv, inv_pow]
        ring
  -- assemble
  have hLHS :
    ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * General.mellinWeightTwo ((n : ℝ) / x) =
      ∑' n : ℕ, (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, G n y := by
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, CharP.cast_eq_zero, zero_div,
        zero_mul, mul_inv_rev, hG_def, hH_def, neg_add_rev, mul_zero, MeasureTheory.integral_zero,
        smul_zero]
    · exact hterm n hn
  rw [hLHS, tsum_const_smul'' (2 * Real.pi : ℝ)⁻¹, hsum_eq_integral]
  congr 1
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)

/-- The reciprocally weighted von Mangoldt sum equals a vertical-line integral
of the reciprocal zeta contour kernel. The extra `1/n` changes the Dirichlet
series argument from the Mellin line `τ-1` to `τ`. With `u=s+1`, the Mellin
factor becomes `x^(u-1)/(u*(u-1))`. Mellin inversion and a summable majorant
justify summing under the integral. -/
theorem mellinWeightOne_vonMangoldt_div_tsum_eq {x : ℝ} (hx : 0 < x) {τ : ℝ} (hτ : 1 < τ) :
    ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * General.mellinWeightOne ((n : ℝ) / x) =
      (2 * Real.pi : ℝ)⁻¹ •
        ∫ y : ℝ, riemannZetaReciprocalContourKernel x ((τ : ℂ) + y * Complex.I) := by
  set σ : ℝ := τ - 1 with hσ_def
  have hσ0 : (0 : ℝ) < σ := by
    rw [hσ_def]; linarith
  have hσ1 : σ ≠ -1 := by
    rw [hσ_def]; intro h; linarith
  have hxC : (x : ℂ) ≠ 0 := by exact_mod_cast hx.ne'
  set K : ℝ → ℂ := fun y ↦ (((τ : ℂ) + y * Complex.I) * ((τ : ℂ) + y * Complex.I - 1))⁻¹ with hK_def
  have hK_int : MeasureTheory.Integrable K := by
    have hVI := General.verticalIntegrable_mellinReciprocalKernel hσ0.ne' hσ1
    unfold Complex.VerticalIntegrable at hVI
    have heq : (fun y : ℝ ↦ (((σ : ℂ) + y * Complex.I) * ((σ : ℂ) + y * Complex.I + 1))⁻¹) = K := by
      funext y
      rw [hK_def, hσ_def]
      push_cast
      ring_nf
    rwa [heq] at hVI
  set H : ℕ → ℝ → ℂ := fun n y ↦
    (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) *
      (x : ℂ) ^ ((τ : ℂ) + y * Complex.I - 1) with
    hH_def
  set G : ℕ → ℝ → ℂ := fun n y ↦ K y * H n y with hG_def
  have hnormH :
    ∀ n : ℕ,
      n ≠ 0 →
        ∀ y : ℝ, ‖H n y‖ = ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1) := by
    intro n hn y
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn_cpow : ‖(n : ℂ) ^ (-((τ : ℂ) + (y : ℂ) * Complex.I))‖ = (n : ℝ) ^ (-τ) := by
      rw [show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
        Complex.norm_cpow_eq_rpow_re_of_pos hnpos]
      congr 1
      simp only [neg_add_rev, Complex.add_re, Complex.neg_re, Complex.mul_re, Complex.ofReal_re,
        Complex.I_re, mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, neg_zero,
        zero_add]
    have hx_cpow : ‖(x : ℂ) ^ ((τ : ℂ) + (y : ℂ) * Complex.I - 1)‖ = x ^ (τ - 1) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
      congr 1
      simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        mul_zero, Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero, Complex.one_re]
    rw [hH_def]
    simp only [norm_mul, hn_cpow, hx_cpow]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  -- (1) term-by-term Mellin inversion
  have hterm_raw :
    ∀ n : ℕ,
      n ≠ 0 →
        General.mellinWeightOne ((n : ℝ) / x) =
          (2 * Real.pi : ℝ)⁻¹ •
            ∫ y : ℝ,
              (((n : ℝ) / x : ℝ) : ℂ) ^ (-((σ : ℂ) + y * Complex.I)) *
                (1 / (((σ : ℂ) + y * Complex.I) * ((σ : ℂ) + y * Complex.I + 1))) := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnx : (0 : ℝ) < (n : ℝ) / x := div_pos hnpos hx
    have hmellin := General.mellinInv_mellinWeightOne_eq (σ := σ) (x := (n : ℝ) / x) hσ0 hnx
    rw [← hmellin]
    simp only [mellinInv, smul_eq_mul, one_div]
  have hterm :
    ∀ n : ℕ,
      n ≠ 0 →
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * General.mellinWeightOne ((n : ℝ) / x) =
          (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, G n y := by
    intro n hn
    have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    rw [hterm_raw n hn, mul_smul_comm]
    congr 1
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with y
    simp only [hG_def, hH_def, hK_def]
    rw [General.cpow_div_eq_cpow_mul_cpow_neg hnpos.le hx, neg_neg, one_div, Complex.ofReal_natCast]
    have hshift : ((τ : ℂ) + y * Complex.I - 1) = (σ : ℂ) + y * Complex.I := by
      rw [hσ_def]; push_cast; ring
    have hshift' : ((σ : ℂ) + y * Complex.I + 1) = (τ : ℂ) + y * Complex.I := by
      rw [hσ_def]; push_cast; ring
    rw [hshift, hshift']
    rw [show (-((σ : ℂ) + y * Complex.I)) = 1 + -((τ : ℂ) + y * Complex.I) by
        rw [hσ_def]; push_cast; ring,
      Complex.cpow_add _ _ hnC, Complex.cpow_one]
    field_simp
  -- (2) each `G n` is integrable, dominated by a constant multiple of `K`
  have hGint : ∀ n : ℕ, MeasureTheory.Integrable (G n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · have hG0 : G 0 = fun _ ↦ (0 : ℂ) := by
        funext y
        simp only [hG_def, hH_def, neg_add_rev, ArithmeticFunction.map_zero, Complex.ofReal_zero,
          CharP.cast_eq_zero, zero_mul, mul_zero]
      rw [hG0]
      exact MeasureTheory.integrable_zero _ _ _
    · have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast hn
      apply hK_int.mul_bdd
      · have hline : Continuous (fun y : ℝ ↦ (τ : ℂ) + y * Complex.I) :=
          continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
        have hHcont : Continuous (H n) := by
          rw [hH_def]
          exact
            (continuous_const.mul (hline.neg.const_cpow (Or.inl hnC))).mul
              ((hline.sub continuous_const).const_cpow (Or.inl hxC))
        exact hHcont.aestronglyMeasurable
      · exact Filter.Eventually.of_forall fun y ↦ (hnormH n hn y).le
  -- (3) the `L¹` norms of `G n` are summable
  have hGnorm_eq :
    ∀ n : ℕ,
      n ≠ 0 →
        ∫ y : ℝ, ‖G n y‖ =
          (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1)) * ∫ y : ℝ, ‖K y‖ := by
    intro n hn
    have hcongr :
      (fun y : ℝ ↦ ‖G n y‖) = fun y : ℝ ↦
        (ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ) * x ^ (τ - 1)) * ‖K y‖ := by
      funext y
      rw [hG_def, norm_mul, hnormH n hn y, mul_comm]
    rw [hcongr, MeasureTheory.integral_const_mul]
  have hSummableL : Summable (fun n : ℕ ↦ ∫ y : ℝ, ‖G n y‖) := by
    have hΛ_summable :
      Summable (fun n : ℕ ↦ ArithmeticFunction.vonMangoldt n * (n : ℝ) ^ (-τ)) := by
      have hLS :
        Summable
          (fun n : ℕ ↦
            ‖LSeries.term (fun m : ℕ ↦ (ArithmeticFunction.vonMangoldt m : ℂ)) (τ : ℂ) n‖) :=
        summable_norm_iff.mpr
          (ArithmeticFunction.LSeriesSummable_vonMangoldt (s := (τ : ℂ))
            (by simpa only [Complex.ofReal_re] using hτ))
      refine hLS.congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [LSeries.term_zero, norm_zero, ArithmeticFunction.map_zero, CharP.cast_eq_zero,
          zero_mul]
      · have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
        rw [LSeries.term_def]
        simp only [hn, ite_false]
        rw [norm_div, show ((n : ℂ)) = ((n : ℝ) : ℂ) from (Complex.ofReal_natCast n).symm,
          Complex.norm_cpow_eq_rpow_re_of_pos hnpos, Complex.ofReal_re, Complex.norm_real,
          Real.norm_eq_abs, abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg,
          Real.rpow_neg hnpos.le, div_eq_mul_inv]
    have hΛx_summable := hΛ_summable.mul_right (x ^ (τ - 1) * ∫ y : ℝ, ‖K y‖)
    apply hΛx_summable.congr
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ArithmeticFunction.map_zero, CharP.cast_eq_zero, zero_mul, hG_def, hH_def,
        neg_add_rev, Complex.ofReal_zero, mul_zero, norm_zero, MeasureTheory.integral_zero]
    · rw [hGnorm_eq n hn]
      ring
  -- (4) exchange the sum and the integral
  have hInterchange := MeasureTheory.hasSum_integral_of_summable_integral_norm hGint hSummableL
  have hsum_eq_integral : ∑' n : ℕ, ∫ y : ℝ, G n y = ∫ y : ℝ, ∑' n : ℕ, G n y :=
    hInterchange.tsum_eq
  -- (5) identify the inner sum over `n` with the reciprocal contour kernel
  have hinner :
    ∀ y : ℝ, ∑' n : ℕ, G n y = riemannZetaReciprocalContourKernel x ((τ : ℂ) + y * Complex.I) := by
    intro y
    have hLS :=
      ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := (τ : ℂ) + y * Complex.I)
        (by
          simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, mul_zero,
            Complex.ofReal_im, Complex.I_im, mul_one, sub_self, add_zero] using hτ)
    have hsum :
      ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I)) =
        -deriv riemannZeta ((τ : ℂ) + y * Complex.I) / riemannZeta ((τ : ℂ) + y * Complex.I) := by
      rw [← hLS]
      unfold LSeries
      refine tsum_congr fun n ↦ ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, CharP.cast_eq_zero,
          neg_add_rev, zero_mul, LSeries.term_zero]
      · rw [LSeries.term_def]
        simp only [hn, ite_false, div_eq_mul_inv, Complex.cpow_neg]
    calc
      ∑' n : ℕ, G n y =
          ∑' n : ℕ,
            K y *
              ((ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I))) *
              (x : ℂ) ^ ((τ : ℂ) + y * Complex.I - 1) :=
        by
        refine tsum_congr fun n ↦ ?_
        rw [hG_def, hH_def]
        ring
      _ =
          K y *
            (∑' n : ℕ,
              (ArithmeticFunction.vonMangoldt n : ℂ) * (n : ℂ) ^ (-((τ : ℂ) + y * Complex.I))) *
            (x : ℂ) ^ ((τ : ℂ) + y * Complex.I - 1) :=
        by rw [tsum_mul_right, tsum_mul_left]
      _ = riemannZetaReciprocalContourKernel x ((τ : ℂ) + y * Complex.I) := by
        rw [hsum, hK_def, riemannZetaReciprocalContourKernel]
        simp only [div_eq_mul_inv]
        ring
  -- assemble
  have hLHS :
    ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n : ℂ) / (n : ℂ) * General.mellinWeightOne ((n : ℝ) / x) =
      ∑' n : ℕ, (2 * Real.pi : ℝ)⁻¹ • ∫ y : ℝ, G n y := by
    refine tsum_congr fun n ↦ ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [ArithmeticFunction.map_zero, Complex.ofReal_zero, CharP.cast_eq_zero, div_zero,
        zero_div, zero_mul, mul_inv_rev, hG_def, hH_def, neg_add_rev, mul_zero,
        MeasureTheory.integral_zero, smul_zero]
    · exact hterm n hn
  rw [hLHS, tsum_const_smul'' (2 * Real.pi : ℝ)⁻¹, hsum_eq_integral]
  congr 1
  exact MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hinner)

end PseudoPrime.AnalyticNumberTheory.RiemannZeta
