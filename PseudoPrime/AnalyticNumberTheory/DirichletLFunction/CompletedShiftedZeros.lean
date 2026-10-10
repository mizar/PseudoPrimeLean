/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.GoodHeight
public import Mathlib.Analysis.Calculus.LogDeriv

/-!
# Completed zero ledgers after the central shift

Translation by one half places completed zeros in Mellin coordinates.
Finite analytic orders and compact divisor support supply finite contour ledgers.
-/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character, the completed function shifted by one half
has finite analytic order everywhere. It is entire and nonzero at the translated origin;
the identity theorem propagates finite order. This excludes infinite zero multiplicities
in shifted contour ledgers. -/
theorem shifted_completed_order_ne_top {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    analyticOrderAt (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) s ≠ ⊤ := by
  let F : ℂ → ℂ := fun z => χ.completedLFunction (z + 1 / 2)
  have hF : AnalyticOnNhd ℂ F Set.univ := fun z _ =>
    ((χ.differentiable_completedLFunction hne).analyticAt _).comp
      (analyticAt_id.add analyticAt_const)
  have hz : F (-1 / 2) ≠ 0 := by
    dsimp only [F]
    simpa only [neg_div, neg_add_cancel] using
      dirichletCompletedLFunction_zero_ne_zero_of_primitive hprimitive hne
  have ho : analyticOrderAt F (-1 / 2) = 0 := analyticOrderAt_eq_zero.mpr (Or.inr hz)
  exact
    hF.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ (Set.mem_univ _)
      (Set.mem_univ _) (ho ▸ ENat.zero_ne_top)

/-- For a primitive nonprincipal character and compact complex set, the shifted completed
function has finitely many zeros there. Finite analytic orders identify its zero set with
finite divisor support. This supplies compact zero ledgers. -/
theorem finite_shifted_completed_zeros {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) {U : Set ℂ} (hU : IsCompact U) :
    (U ∩ (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) ⁻¹' {0}).Finite := by
  let F : ℂ → ℂ := fun z => χ.completedLFunction (z + 1 / 2)
  have hF : AnalyticOnNhd ℂ F U := fun z _ =>
    ((χ.differentiable_completedLFunction hne).analyticAt _).comp
      (analyticAt_id.add analyticAt_const)
  have hnormal := hF.meromorphicNFOn
  rw [hnormal.zero_set_eq_divisor_support fun u => ?_]
  · exact (MeromorphicOn.divisor F U).finiteSupport hU
  · rw [(hF u u.property).meromorphicOrderAt_eq]
    exact fun ht => shifted_completed_order_ne_top hprimitive hne u (ENat.map_eq_top_iff.mp ht)

/-- For a nonprincipal character, translating by one half evaluates its logarithmic
derivative at the translated point. The chain rule and the unit derivative of translation
prove the identity. This connects shifted residues with horizontal contour estimates. -/
theorem logDeriv_shifted_completed {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N} (hne : χ ≠ 1)
    (s : ℂ) :
    logDeriv (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) s =
      logDeriv χ.completedLFunction (s + 1 / 2) := by
  have hd : DifferentiableAt ℂ (fun z : ℂ => z + 1 / 2) s := differentiableAt_id.add_const _
  have he := logDeriv_comp ((χ.differentiable_completedLFunction hne) _) hd
  simpa only [Function.comp_def, deriv_add_const, deriv_id'', mul_one] using he

/-- For a primitive nonprincipal character, shifted completed zeros and the possible
Mellin pole in a closed rectangle form a finite set. Compact zero finiteness and a
singleton union certify the contour ledger. -/
theorem finite_completedKernelSingularities {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (z w : ℂ) :
    {s ∈ Rectangle.rectangleClosedBox z w |
        s = -1 / 2 ∨ χ.completedLFunction (s + 1 / 2) = 0}.Finite := by
  have hf :=
    finite_shifted_completed_zeros hprimitive hne (Rectangle.isCompact_rectangleClosedBox z w)
  apply (hf.union (Set.finite_singleton (-1 / 2 : ℂ))).subset
  intro s hs
  rcases hs.2 with hp | hz
  · exact Or.inr hp
  · exact Or.inl ⟨hs.1, hz⟩

/-- The finite ledger of shifted completed zeros and the possible pole at minus one half
within a closed rectangle. Primitivity and nonprincipality certify finiteness.
This finset indexes weighted Mellin contour residues. -/
noncomputable def completedKernelSingularities {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (z w : ℂ) : Finset ℂ :=
  (finite_completedKernelSingularities hprimitive hne z w).toFinset

/-- Ledger membership means closed rectangle membership and either the kernel pole
or a shifted completed zero. Unfold finite-set conversion to recover the analytic
conditions used by residue assembly. -/
theorem mem_completedKernelSingularities {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    {hprimitive : χ.IsPrimitive} {hne : χ ≠ 1} {z w s : ℂ} :
    s ∈ completedKernelSingularities hprimitive hne z w ↔
      s ∈ Rectangle.rectangleClosedBox z w ∧
        (s = -1 / 2 ∨ χ.completedLFunction (s + 1 / 2) = 0) := by
  simp only [completedKernelSingularities, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]

/-- Translation by one half preserves the analytic order at the translated point.
The derivative of translation is one, so analytic-order composition applies without
primitivity or nonprincipality. This identifies shifted zero multiplicities. -/
theorem shifted_completed_order {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ) :
    analyticOrderAt (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) s =
      analyticOrderAt χ.completedLFunction (s + 1 / 2) := by
  have ha : AnalyticAt ℂ (fun z : ℂ => z + 1 / 2) s := analyticAt_id.add analyticAt_const
  have hd : deriv (fun z : ℂ => z + 1 / 2) s ≠ 0 :=
    (((hasDerivAt_id s).add_const (1 / 2)).deriv).trans_ne one_ne_zero
  exact analyticOrderAt_comp_of_deriv_ne_zero ha hd

/-- For a primitive nonprincipal character, the natural analytic order of the shifted
completion equals the integer divisor of the unshifted completion. Finite order and
translation invariance turn the divisor formula into this cast identity. This matches
finite contour multiplicities with the global zero series. -/
theorem shifted_completed_orderNat_eq_divisor {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (s : ℂ) :
    (analyticOrderNatAt (fun z : ℂ => χ.completedLFunction (z + 1 / 2)) s : ℤ) =
      MeromorphicOn.divisor χ.completedLFunction Set.univ (s + 1 / 2) := by
  have hF : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ =>
    (χ.differentiable_completedLFunction hne).analyticAt z
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply hF (Set.mem_univ _), ← shifted_completed_order χ s,
    ← Nat.cast_analyticOrderNatAt (shifted_completed_order_ne_top hp hne s)]
  simp only [ENat.map_natCast, WithTop.untop₀_coe]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
