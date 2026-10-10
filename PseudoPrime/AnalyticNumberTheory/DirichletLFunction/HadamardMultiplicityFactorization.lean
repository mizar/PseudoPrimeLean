/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.ZeroCounting
public import Mathlib.Order.Filter.Finite
public import Mathlib.Topology.Instances.Complex
public import Mathlib.Analysis.Calculus.LogDeriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Ring

/-!
# Finite multiplicity-aware Hadamard factorization for Dirichlet `L`-functions

Define the finite genus-one product over a nontrivial character's completed zeros in a rectangle.
For primitive characters, completed nonvanishing at zero permits nonzero zero-locations in
these factors; matching multiplicities give local analytic units and an entire patched quotient.
The logarithmic derivative splits into a finite zero sum and the quotient's logarithmic derivative.
The final declarations give ordinary `L` multiplicities and local factorizations for nontrivial
characters, without requiring primitivity. All constructions are independent of contour kernels.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a character at a positive level and a complex point, define the natural-valued analytic
order of its ordinary `L`-function using `analyticOrderNatAt`. The definition is total, including
at infinite analytic order. For nontrivial characters the order is finite, and at zeros it is
positive; the following theorems use it in local factorizations and logarithmic residues. -/
noncomputable def dirichletLFunctionZeroMultiplicity {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ

/--
Input/assumptions: a nontrivial character and one zero of its continued `L`-function.
Conclusion: the associated analytic multiplicity is positive.
Content: a zero has nonzero analytic order, while global nontriviality makes that order finite.
Role: records the positive integer coefficient of a primitive zero residue.
-/
theorem dirichletLFunctionZeroMultiplicity_pos {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) {ρ : ℂ} (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    0 < dirichletLFunctionZeroMultiplicity χ ρ := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have horder : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 :=
    hanalytic.analyticOrderAt_ne_zero.mpr hzero
  have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hmero := hanalytic.meromorphicOrderAt_eq
    rw [htop] at hmero
    exact
      meromorphicOrderAt_dirichletLFunction_ne_top χ hχ ρ (by simpa only [ENat.map_top] using hmero)
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  apply Nat.pos_of_ne_zero
  intro hmult
  apply horder
  rw [← hcast, show analyticOrderNatAt (DirichletCharacter.LFunction χ) ρ = 0 from hmult]
  simp only [CharP.cast_eq_zero]

/--
Input/assumptions: a nontrivial character and a complex point.
Conclusion: a local analytic factorization of its continued `L`-function at that point.
Content: finite analytic order extracts a nonvanishing analytic factor after the vanishing power.
Role: this is the local input for proving the logarithmic-derivative residue formula at a zero.
-/
theorem exists_dirichletLFunction_localFactor {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ ≠ 1) (ρ : ℂ) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        DirichletCharacter.LFunction χ =ᶠ[nhds ρ] fun s ↦
          (s - ρ) ^ dirichletLFunctionZeroMultiplicity χ ρ • g s := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have hfinite : analyticOrderAt (DirichletCharacter.LFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hmero := hanalytic.meromorphicOrderAt_eq
    rw [htop] at hmero
    exact
      meromorphicOrderAt_dirichletLFunction_ne_top χ hχ ρ (by simpa only [ENat.map_top] using hmero)
  simpa only [dirichletLFunctionZeroMultiplicity] using hanalytic.analyticOrderAt_ne_top.mp hfinite

/--
Input/assumptions: a nontrivial character and one zero of its (uncompleted) `L`-function.
Conclusion: near that zero its logarithmic derivative is multiplicity over `s - ρ` plus an
analytic logarithmic derivative.
Content: differentiate the finite-order local factorization and use product logarithmic-derivative
rules away from the center.
Role: the local identity from which a contour kernel's principal part at an `L`-zero is obtained.
-/
theorem exists_eventuallyEq_logDeriv_dirichletLFunction_at_zero {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    ∃ g : ℂ → ℂ,
      0 < dirichletLFunctionZeroMultiplicity χ ρ ∧
        AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ))
          (logDeriv (DirichletCharacter.LFunction χ))
          (fun s ↦ (dirichletLFunctionZeroMultiplicity χ ρ : ℂ) / (s - ρ) + logDeriv g s) := by
  obtain ⟨g, hganalytic, hgzero, hfactor⟩ := exists_dirichletLFunction_localFactor hχ ρ
  refine ⟨g, dirichletLFunctionZeroMultiplicity_pos hχ hzero, hganalytic, hgzero, ?_⟩
  have hlog :
    Filter.EventuallyEq (nhdsWithin ρ ({ρ}ᶜ : Set ℂ)) (logDeriv (DirichletCharacter.LFunction χ))
      (logDeriv fun s ↦ (s - ρ) ^ dirichletLFunctionZeroMultiplicity χ ρ • g s) :=
    (logDeriv_congr_nhds hfactor).filter_mono nhdsWithin_le_nhds
  have hganalyticEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), AnalyticAt ℂ g s :=
    hganalytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds
  have hgzeroEventually : ∀ᶠ s in nhdsWithin ρ ({ρ}ᶜ : Set ℂ), g s ≠ 0 :=
    ((hganalytic.continuousAt.ne_iff_eventually_ne continuousAt_const).mp hgzero).filter_mono
      nhdsWithin_le_nhds
  filter_upwards [hlog, hganalyticEventually, hgzeroEventually, eventually_mem_nhdsWithin] with s
    hlogs hsanalytic hgs hsρ
  simp only [smul_eq_mul] at hlogs
  rw [hlogs]
  change logDeriv ((fun s ↦ (s - ρ) ^ dirichletLFunctionZeroMultiplicity χ ρ) * g) s = _
  rw [logDeriv_mul s]
  · rw [logDeriv_fun_pow (by fun_prop)]
    simp only [logDeriv_apply]
    rw [deriv_sub_const]
    simp only [deriv_id'', one_div, add_left_inj]
    ring
  · exact pow_ne_zero _ (sub_ne_zero.mpr (Set.mem_compl_singleton_iff.mp hsρ))
  · exact hgs
  · fun_prop
  · exact hsanalytic.differentiableAt

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
