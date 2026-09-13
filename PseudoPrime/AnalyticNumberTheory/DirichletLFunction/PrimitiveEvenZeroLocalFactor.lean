/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveEvenZeroResidue
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.EvenZeroLocalFactor

/-!
# Canonical local factor and downstream reciprocal residue

Connect the even Dirichlet L-function local factor to the reciprocal kernel regularization.
-/

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/--
Input/assumptions: nonzero modulus `N`, a primitive nontrivial even character `χ`, and `x : ℝ`.
Conclusion: `(s - 0)² K_x(s) =ᶠ[𝓝[≠] 0]
DirichletLFunction.dirichletReciprocalEvenZeroRegularization x 1 G_χ`.
Content: `logDeriv_congr_nhds` on `L =ᶠ[𝓝 0] fun s ↦ s · G_χ(s)`
(`eventuallyEq_dirichletLFunction_evenZeroLocalFactor`) plus `logDeriv_mul` (for `s ≠ 0`, `G_χ(s) ≠
0` nearby by continuity) gives `logDeriv L(s) = 1/s + logDeriv G_χ(s)` on a punctured
neighborhood; substituting into the kernel/regularization definitions and clearing denominators
(`field_simp`) finishes. The local factor is the canonical `G_χ`, with multiplicity `1`.
Role: the canonical-factor regularization identity, letting the even residue be computed directly
from `G_χ` without inspecting a witness selected by `Classical.choose`.
-/
theorem eventuallyEq_dirichletReciprocalEvenZeroRegularization_canonical {N : ℕ} [NeZero N] {x : ℝ}
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (heven : χ.Even) :
    Filter.EventuallyEq (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (fun s =>
        (s - 0) ^ 2 *
          dirichletReciprocalContourKernel x χ
            s)
      (dirichletReciprocalEvenZeroRegularization
        x 1
        (dirichletEvenZeroLocalFactor χ)) := by
  obtain ⟨hGanalytic, hG0⟩ :=
    analyticAt_and_ne_zero_dirichletEvenZeroLocalFactor
      hprimitive hne
  have heq :=
    eventuallyEq_dirichletLFunction_evenZeroLocalFactor
      hprimitive hne heven
  have hlogeq := logDeriv_congr_nhds heq
  have hGnear :
    ∀ᶠ s in nhds (0 : ℂ),
      dirichletEvenZeroLocalFactor χ s ≠ 0 :=
    hGanalytic.continuousAt.eventually_ne hG0
  have honeNhds : ∀ᶠ s : ℂ in nhds 0, s ≠ 1 := compl_singleton_mem_nhds (by norm_num only)
  filter_upwards [hlogeq.filter_mono nhdsWithin_le_nhds, honeNhds.filter_mono nhdsWithin_le_nhds,
    hGnear.filter_mono nhdsWithin_le_nhds, eventually_mem_nhdsWithin,
    hGanalytic.eventually_analyticAt.filter_mono nhdsWithin_le_nhds] with s hlogeqs hs1 hGsne hs0
    hGsanalytic
  have hs0' : s ≠ 0 := Set.mem_compl_singleton_iff.mp hs0
  have hlogs' :
    deriv (DirichletCharacter.LFunction χ) s / DirichletCharacter.LFunction χ s =
      (1 : ℂ) / (s - 0) +
        logDeriv
          (dirichletEvenZeroLocalFactor χ)
          s := by
    have hmul := logDeriv_mul s hs0' hGsne differentiableAt_id hGsanalytic.differentiableAt
    rw [← logDeriv_apply, hlogeqs,
      show
        (fun s : ℂ =>
            s *
              dirichletEvenZeroLocalFactor χ
                s) =
          id * dirichletEvenZeroLocalFactor χ
        from by
        funext s
        rfl,
      hmul]
    congr 1
    rw [logDeriv_apply]
    simp only [deriv_id', id_eq, one_div, sub_zero]
  unfold dirichletReciprocalContourKernel
    dirichletReciprocalEvenZeroRegularization
  rw [hlogs']
  have hs1' : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  simp only [sub_zero]
  push_cast
  field_simp

/--
Input/assumptions: `N ≥ 1`, `χ` primitive nontrivial even mod `N`, `x : ℝ`.
Conclusion: `DirichletLFunction.dirichletReciprocalResidueAt hne x 0 =
  deriv (DirichletLFunction.dirichletReciprocalEvenZeroRegularization x 1 G_χ) 0`.
Content: both the regularization of the witness `g` selected by `Classical.choose` and that of `G_χ`
regularization equal `(s - 0)² K_x(s)` on the punctured neighborhood of `0`
(`DirichletLFunction.exists_eventuallyEq_dirichletReciprocalEvenZeroRegularization`, multiplicity
rewritten to `1`
via `dirichletLFunctionZeroMultiplicity_zero_of_primitive_even_eq_one`; the canonical identity is
`eventuallyEq_dirichletReciprocalEvenZeroRegularization_canonical`), hence equal each other there
(transitivity); both regularizations also agree exactly *at* `0` regardless of the local factor
(`R(0) = m/x` from the definition, independent of `g`); `eventuallyEq_nhds_of_eventuallyEq_nhdsNE`
upgrades punctured + pointwise equality to a full-neighborhood `EventuallyEq`, and
`Filter.EventuallyEq.deriv_eq` transfers this to the derivatives at `0`.
Role: **eliminates `Classical.choose` entirely** — the even residue is now expressed purely in
terms of the canonical, concretely-defined `G_χ`, ready for the regularization derivative formula
and the special value of `logDeriv G_χ 0`.
-/
theorem dirichletReciprocalResidueAt_zero_of_primitive_even_eq {N : ℕ} [NeZero N]
    {χ : DirichletCharacter ℂ N} (hprimitive : χ.IsPrimitive) (hne : χ ≠ 1) (heven : χ.Even)
    (x : ℝ) :
    dirichletReciprocalResidueAt hne x 0 =
      deriv
        (dirichletReciprocalEvenZeroRegularization
          x 1 (dirichletEvenZeroLocalFactor χ))
        0 := by
  rw [dirichletReciprocalResidueAt_zero_of_even
      hne x heven]
  set g :=
    Classical.choose
      (exists_eventuallyEq_dirichletReciprocalEvenZeroRegularization
        x hne heven)
  obtain ⟨-, hganalytic, hgzero, hpunct_chosen⟩ :=
    Classical.choose_spec
      (exists_eventuallyEq_dirichletReciprocalEvenZeroRegularization
        x hne heven)
  have hmult1 :=
    dirichletLFunctionZeroMultiplicity_zero_of_primitive_even_eq_one
      hprimitive hne heven
  have hpunct_canon :=
    eventuallyEq_dirichletReciprocalEvenZeroRegularization_canonical
      (x := x) hprimitive hne heven
  rw [← hmult1] at hpunct_canon
  have hpunct :
    Filter.EventuallyEq (nhdsWithin (0 : ℂ) ({0}ᶜ : Set ℂ))
      (dirichletReciprocalEvenZeroRegularization
        x
        (dirichletLFunctionZeroMultiplicity χ 0)
        g)
      (dirichletReciprocalEvenZeroRegularization
        x
        (dirichletLFunctionZeroMultiplicity χ 0)
        (dirichletEvenZeroLocalFactor χ)) :=
    hpunct_chosen.symm.trans hpunct_canon
  have hpt :
    dirichletReciprocalEvenZeroRegularization x
        (dirichletLFunctionZeroMultiplicity χ 0)
        g 0 =
      dirichletReciprocalEvenZeroRegularization
        x
        (dirichletLFunctionZeroMultiplicity χ 0)
        (dirichletEvenZeroLocalFactor χ) 0 := by
    unfold
      dirichletReciprocalEvenZeroRegularization
    simp only [zero_mul, add_zero, zero_sub, neg_mul, neg_div_neg_eq, div_one]
  have hderiv := (eventuallyEq_nhds_of_eventuallyEq_nhdsNE hpunct hpt).deriv_eq
  rw [hmult1] at hderiv
  rw [hmult1]
  exact hderiv

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
