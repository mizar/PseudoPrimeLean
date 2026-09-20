/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import Mathlib.Analysis.Meromorphic.NormalForm
import Mathlib.Analysis.Meromorphic.Order
import Mathlib.Analysis.Meromorphic.RCLike
import Mathlib.NumberTheory.LSeries.DirichletContinuation
import PseudoPrime.AnalyticNumberTheory.Rectangle.Basic
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.Basic

/-!
# Zero counting for Dirichlet `L`-functions

Fully generic facts about the (uncompleted and completed) Dirichlet `L`-function of an arbitrary
nontrivial character: finite meromorphic order everywhere, finiteness of the zero set on any
compact set (in particular any closed rectangle), the resulting finite zero ledgers, and the
positive analytic multiplicity of a completed zero together with its local factorization. None of
this mentions any application-specific contour kernel.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: two complex corners.
Conclusion: the closed axis-aligned rectangle determined by those corners.
Content: this is the shared rectangular box geometry specialized to primitive Dirichlet `L` data.
Role: it indexes finite primitive-zero ledgers used by the later contour-residue identity.
-/
def dirichletCompletedLFunctionRectangleBox (z w : ℂ) : Set ℂ :=
  Rectangle.rectangleClosedBox z w

/--
Input/assumptions: two complex corners.
Conclusion: the primitive contour rectangle is compact.
Content: it is a product of two closed bounded real intervals.
Role: compactness gives finiteness of the primitive `L` zero ledger.
-/
theorem isCompact_dirichletCompletedLFunctionRectangleBox (z w : ℂ) :
    IsCompact (dirichletCompletedLFunctionRectangleBox z w) := by
  exact isCompact_uIcc.reProdIm isCompact_uIcc

/--
Input/assumptions: a nontrivial complex Dirichlet character.
Conclusion: its continued `L`-function has finite meromorphic order at every complex point.
Content: an entire nonzero function has one finite-order nonzero value, and the meromorphic
identity principle propagates finite order globally.
Role: this is the finiteness certificate required by the finite zero-set divisor API.
-/
theorem meromorphicOrderAt_dirichletLFunction_ne_top {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (s : ℂ) : meromorphicOrderAt (DirichletCharacter.LFunction χ) s ≠ ⊤ := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) 2 :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt 2
  have htwo : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by
        change (1 : ℝ) ≤ 2
        norm_num only)
  have horder : meromorphicOrderAt (DirichletCharacter.LFunction χ) 2 = 0 :=
    hanalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr htwo
  have hmero : Meromorphic (DirichletCharacter.LFunction χ) := fun u ↦
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt u |>.meromorphicAt
  apply (hmero.exists_meromorphicOrderAt_ne_top_iff_forall.mp ?_) s
  exact
    ⟨2, by
      rw [horder];
      simp only [ne_eq, LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true]⟩

/--
Input/assumptions: a compact complex set and a nontrivial character.
Conclusion: the set of zeros of its continued `L`-function in that compact set is finite.
Content: the entire continuation is in meromorphic normal form and has finite order everywhere.
Role: it supplies the finite zero ledger needed before a primitive rectangle contour is assembled.
-/
theorem finite_dirichletLFunction_zerosOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {K : Set ℂ} (hcompact : IsCompact K) :
    (K ∩ DirichletCharacter.LFunction χ ⁻¹' {0}).Finite := by
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.LFunction χ) K := fun s _ ↦
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have hnormal : MeromorphicNFOn (DirichletCharacter.LFunction χ) K := hanalytic.meromorphicNFOn
  rw [hnormal.zero_set_eq_divisor_support fun u ↦
      meromorphicOrderAt_dirichletLFunction_ne_top χ hχ u]
  exact (MeromorphicOn.divisor (DirichletCharacter.LFunction χ) K).finiteSupport hcompact

/--
Input/assumptions: a nontrivial character and two complex corners.
Conclusion: its continued `L`-zeros in the closed rectangle form a finite set.
Content: specialize compact zero finiteness to the rectangle.
Role: provides the finiteness proof used to define the rectangle's `Finset` ledger.
-/
theorem finite_dirichletLFunction_zerosInRectangle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (z w : ℂ) :
    (dirichletCompletedLFunctionRectangleBox z w ∩ DirichletCharacter.LFunction χ ⁻¹' {0}).Finite :=
  finite_dirichletLFunction_zerosOn χ hχ (isCompact_dirichletCompletedLFunctionRectangleBox z w)

/--
Input/assumptions: a nontrivial character and closed rectangle.
Conclusion: a finite ledger of exactly the continued `L`-zeros inside that rectangle.
Content: convert the certified finite set of zeros to a `Finset`.
Role: its finite sums will be the primitive zero contributions in the rectangle residue formula.
-/
noncomputable def dirichletLFunctionZerosInRectangle {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) (z w : ℂ) : Finset ℂ :=
  (finite_dirichletLFunction_zerosInRectangle χ hχ z w).toFinset

/--
Input/assumptions: a point and a primitive rectangle zero ledger.
Conclusion: membership is equivalent to lying in the rectangle and being an `L`-zero.
Content: unfold the finite-set-to-finset conversion.
Role: lets residue and boundary arguments recover the analytic facts attached to a ledger entry.
-/
theorem mem_dirichletLFunctionZerosInRectangle_iff {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {hχ : χ ≠ 1} {z w ρ : ℂ} :
    ρ ∈ dirichletLFunctionZerosInRectangle χ hχ z w ↔
      ρ ∈ dirichletCompletedLFunctionRectangleBox z w ∧ DirichletCharacter.LFunction χ ρ = 0 := by
  simp only [dirichletLFunctionZerosInRectangle, Set.Finite.mem_toFinset, Set.mem_inter_iff,
    Set.mem_preimage, Set.mem_singleton_iff]

/--
Input/assumptions: a nontrivial Dirichlet character.
Conclusion: its completed `L`-function is nonzero at the Euler-half-plane point two.
Content: if the completed value were zero, the completed-to-uncompleted identity would force
`L(χ,2)=0`, contradicting standard Dirichlet `L` nonvanishing.
Role: supplies the global nonzero witness needed to make completed-`L` zero ledgers finite.
-/
theorem dirichletCompletedLFunction_two_ne_zero {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) : DirichletCharacter.completedLFunction χ (2 : ℂ) ≠ 0 := by
  intro hcompleted
  have hL : DirichletCharacter.LFunction χ (2 : ℂ) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ)
      (by
        change (1 : ℝ) ≤ 2
        norm_num only)
  have hrelation :=
    dirichletLFunction_eq_completed_div_gammaFactor χ (2 : ℂ)
      (Or.inl
        (by
          intro h
          have h' := congrArg Complex.re h
          change (2 : ℝ) = 0 at h'
          norm_num only at h'))
  apply hL
  rw [hrelation, hcompleted]
  simp only [zero_div]

/--
Input/assumptions: a nontrivial Dirichlet character.
Conclusion: its completed `L`-function has finite meromorphic order at every complex point.
Content: entire continuation and the nonzero value at two invoke the connected meromorphic-order
identity principle.
Role: this is the order certificate used by the completed function's compact zero-set ledger.
-/
theorem meromorphicOrderAt_dirichletCompletedLFunction_ne_top {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (s : ℂ) :
    meromorphicOrderAt (DirichletCharacter.completedLFunction χ) s ≠ ⊤ := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) 2 :=
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt 2
  have horder : meromorphicOrderAt (DirichletCharacter.completedLFunction χ) 2 = 0 :=
    hanalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr
      (dirichletCompletedLFunction_two_ne_zero χ hχ)
  have hmero : Meromorphic (DirichletCharacter.completedLFunction χ) := fun u ↦
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt u |>.meromorphicAt
  apply (hmero.exists_meromorphicOrderAt_ne_top_iff_forall.mp ?_) s
  exact
    ⟨2, by
      rw [horder];
      simp only [ne_eq, LinearOrderedAddCommGroupWithTop.zero_ne_top, not_false_eq_true]⟩

/--
Input/assumptions: a compact complex set and a nontrivial character.
Conclusion: the completed `L`-zeros in that compact set are finite.
Content: entire completed continuation is in meromorphic normal form and has finite order globally.
Role: establishes the finite zero-set side of the completed-function contour ledger using the
nonzero value at two.
-/
theorem finite_dirichletCompletedLFunction_zerosOn {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {K : Set ℂ} (hcompact : IsCompact K) :
    (K ∩ DirichletCharacter.completedLFunction χ ⁻¹' {0}).Finite := by
  have hanalytic : AnalyticOnNhd ℂ (DirichletCharacter.completedLFunction χ) K := fun s _ ↦
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt s
  have hnormal : MeromorphicNFOn (DirichletCharacter.completedLFunction χ) K :=
    hanalytic.meromorphicNFOn
  rw [hnormal.zero_set_eq_divisor_support fun u ↦
      meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ u]
  exact (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ) K).finiteSupport hcompact

/--
Input/assumptions: a nontrivial character and two rectangle corners.
Conclusion: a finite ledger of all completed `L`-zeros in that closed rectangle.
Content: specialize compact zero finiteness and convert the resulting set to a `Finset`.
Role: this is the zero ledger naturally compatible with the completed functional equation.
-/
noncomputable def dirichletCompletedLFunctionZerosInRectangle {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (z w : ℂ) : Finset ℂ :=
  (finite_dirichletCompletedLFunction_zerosOn χ hχ
      (isCompact_dirichletCompletedLFunctionRectangleBox z w)).toFinset

/--
Input/assumptions: a point and a completed `L` rectangle zero ledger.
Conclusion: membership is exactly rectangle membership together with vanishing of completed `L`.
Content: unfold the finite-set-to-finset conversion.
Role: lets later functional-equation and Gamma bookkeeping attach local data to ledger entries.
-/
theorem mem_dirichletCompletedLFunctionZerosInRectangle_iff {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} {hχ : χ ≠ 1} {z w ρ : ℂ} :
    ρ ∈ dirichletCompletedLFunctionZerosInRectangle χ hχ z w ↔
      ρ ∈ dirichletCompletedLFunctionRectangleBox z w ∧
        DirichletCharacter.completedLFunction χ ρ = 0 := by
  simp only [dirichletCompletedLFunctionZerosInRectangle, Set.Finite.mem_toFinset,
    Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff]

/--
Definition: the analytic multiplicity of a completed primitive Dirichlet `L` zero.
Input: a character and complex point.
Output: the natural analytic order of `completedLFunction` at that point.
Role: supplies the multiplicity-aware coefficients for the primitive completed-`L` Hadamard
product and its logarithmic derivative.
-/
noncomputable def dirichletCompletedLFunctionZeroMultiplicity {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (ρ : ℂ) : ℕ :=
  analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ

/--
Input/assumptions: a nontrivial character and a completed `L` zero.
Conclusion: its completed analytic multiplicity is positive.
Content: entire nontriviality rules out infinite order, while vanishing rules out order zero.
Role: establishes positive coefficients for the primitive completed-Hadamard finite ledger.
-/
theorem dirichletCompletedLFunctionZeroMultiplicity_pos {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0) :
    0 < dirichletCompletedLFunctionZeroMultiplicity χ ρ := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) ρ :=
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt ρ
  have horder : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ 0 :=
    hanalytic.analyticOrderAt_ne_zero.mpr hzero
  have hfinite : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hmero := hanalytic.meromorphicOrderAt_eq
    rw [htop] at hmero
    exact
      meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ ρ
        (by simpa only [ENat.map_top] using hmero)
  have hcast := Nat.cast_analyticOrderNatAt hfinite
  apply Nat.pos_of_ne_zero
  intro hmult
  apply horder
  rw [← hcast, show analyticOrderNatAt (DirichletCharacter.completedLFunction χ) ρ = 0 from hmult]
  simp only [CharP.cast_eq_zero]

/--
Input/assumptions: a nontrivial character and a complex point.
Conclusion: the completed `L`-function factors locally into its analytic zero power and a
nonvanishing analytic unit.
Content: finite analytic order for the entire nonzero completed function supplies the factor.
Role: is the local factorization required by the multiplicity-aware finite Hadamard quotient.
-/
theorem exists_dirichletCompletedLFunction_localFactor {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) (ρ : ℂ) :
    ∃ g : ℂ → ℂ,
      AnalyticAt ℂ g ρ ∧
        g ρ ≠ 0 ∧
        DirichletCharacter.completedLFunction χ =ᶠ[nhds ρ] fun s ↦
          (s - ρ) ^ dirichletCompletedLFunctionZeroMultiplicity χ ρ • g s := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.completedLFunction χ) ρ :=
    (DirichletCharacter.differentiable_completedLFunction hχ).analyticAt ρ
  have hfinite : analyticOrderAt (DirichletCharacter.completedLFunction χ) ρ ≠ ⊤ := by
    intro htop
    have hmero := hanalytic.meromorphicOrderAt_eq
    rw [htop] at hmero
    exact
      meromorphicOrderAt_dirichletCompletedLFunction_ne_top χ hχ ρ
        (by simpa only [ENat.map_top] using hmero)
  simpa only [dirichletCompletedLFunctionZeroMultiplicity] using
    hanalytic.analyticOrderAt_ne_top.mp hfinite

/--
Input/assumptions: a nontrivial character and a zero of its (uncompleted) `L`-function.
Conclusion: the logarithmic derivative has a simple pole at that zero.
Content: finite nonzero meromorphic order of `L` invokes mathlib's logarithmic-derivative order
theorem.
Role: verifies that each zero-ledger point is an isolated residue singularity for a contour shift.
-/
theorem meromorphicOrderAt_logDeriv_dirichletLFunction_zero_eq_neg_one {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hχ : χ ≠ 1) {ρ : ℂ}
    (hzero : DirichletCharacter.LFunction χ ρ = 0) :
    meromorphicOrderAt (logDeriv (DirichletCharacter.LFunction χ)) ρ = -1 := by
  have hanalytic : AnalyticAt ℂ (DirichletCharacter.LFunction χ) ρ :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt ρ
  have horder : meromorphicOrderAt (DirichletCharacter.LFunction χ) ρ ≠ 0 := by
    intro horderZero
    exact (hanalytic.meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mp horderZero) hzero
  exact
    meromorphicOrderAt_logDeriv_eq_neg_one hanalytic.meromorphicAt horder
      (meromorphicOrderAt_dirichletLFunction_ne_top χ hχ ρ)

end DirichletLFunction

end AnalyticNumberTheory

end PseudoPrime
