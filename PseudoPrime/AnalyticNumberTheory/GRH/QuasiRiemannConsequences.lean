/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.AnalyticNumberTheory.GRH.QuasiRiemannHypothesis
import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveZeroTransfer

/-! # RH and GRH imply the corresponding quasi-Riemann hypotheses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- RH implies the zeta quasi-Riemann hypothesis. A zero with real part above
`7/8` is nontrivial, so RH places it on the critical line, a contradiction. -/
theorem quasiRiemannHypothesis_of_RH (hRH : RiemannHypothesis) : QuasiRiemannHypothesis := by
  intro s hs hz
  have hspos : 0 < s.re := by linarith only [hs]
  have hz' : (1 : DirichletCharacter ℂ 1).LFunction s = 0 := by
    simpa only [DirichletCharacter.LFunction_modOne_eq] using hz
  have hh :=
    (dirichletRiemannHypothesis_one_iff.mpr hRH) s hz'
      (not_mem_dirichletTrivialZeros_of_re_pos (1 : DirichletCharacter ℂ 1) hspos)
  linarith only [hs, hh]

/-- GRH for primitive Dirichlet characters implies the quasi-Riemann
hypothesis for all Dirichlet characters. The primitive case follows from
GRH; change of level transfers zeros in the positive half-plane, while the
principal case is reduced to zeta and nonzero finite Euler factors. -/
theorem dirichletQuasiRH_of_GRH (hGRH : GeneralizedRiemannHypothesis) :
    DirichletQuasiRiemannHypothesis := by
  intro q _ χ s hs hpole
  have hspos : 0 < s.re := by linarith only [hs]
  by_cases hχ : χ = 1
  · subst χ
    have hs1 : s ≠ 1 := fun h ↦ hpole ⟨rfl, h⟩
    have hzeta := quasiRiemannHypothesis_of_RH hGRH.riemann s hs
    have hprod :=
      DirichletLFunction.LFactorProduct_ne_zero_of_re_pos (N := q) (1 : DirichletCharacter ℂ 1)
        hspos
    have heuler :=
      DirichletCharacter.LFunction_changeLevel (one_dvd q) (1 : DirichletCharacter ℂ 1) (s := s)
        (Or.inr hs1)
    rw [DirichletCharacter.changeLevel_one, DirichletCharacter.LFunction_modOne_eq] at heuler
    rw [heuler]
    exact mul_ne_zero hzeta hprod
  · intro hz
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    have hpz := (DirichletLFunction.L_zero_iff_primitive_of_re_pos hχ hspos).mp hz
    have hh :=
      hGRH.zero_re_eq_half χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hpz
        hspos
    linarith only [hs, hh]

end PseudoPrime.AnalyticNumberTheory.GRH
