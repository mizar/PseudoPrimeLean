/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.GRH.Definition
public import PseudoPrime.AnalyticNumberTheory.GRH.ZeroClassification
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PrimitiveZeroTransfer
import PseudoPrime.AnalyticNumberTheory.RiemannZeta.TrivialZeros
import PseudoPrime.AnalyticNumberTheory.RiemannXi.ZeroFiniteness

/-! # Alternative formulations of the Riemann hypotheses -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.GRH

/-- The Riemann zeta function's zeros outside the negative even integers lie on the critical
line. The point `1` is explicitly excluded, matching mathlib's Riemann hypothesis. -/
def RiemannZetaZerosOnLine : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → (¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1)) → s ≠ 1 → s.re = 1 / 2

/-- For every complex Dirichlet character of nonzero modulus, its L-function is nonzero to
the right of the critical line, excluding the principal character at `1`. -/
def DirichletLNonvanishingRightOfHalf : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    1 / 2 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- Every zero in the open critical strip of any complex Dirichlet L-function of nonzero
modulus lies on the critical line. -/
def DirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N) (s : ℂ),
    0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- Every zero in the open critical strip of a primitive complex Dirichlet L-function of
nonzero modulus lies on the critical line. -/
def PrimitiveDirichletLZerosOnLine : Prop :=
  ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N),
    χ.IsPrimitive →
      ∀ s : ℂ, 0 < s.re → s.re < 1 → DirichletCharacter.LFunction χ s = 0 → s.re = 1 / 2

/-- GRH implies the open-strip statement for primitive Dirichlet L-functions: positive real
part excludes the prescribed trivial zeros. -/
theorem GeneralizedRiemannHypothesis.primitive_zeros_on_line (h : GeneralizedRiemannHypothesis) :
    PrimitiveDirichletLZerosOnLine := fun N _ χ hp s hs _ hz ↦ h.zero_re_eq_half N χ hp s hz hs

/-- The open-strip statement for all Dirichlet characters specializes to primitive characters. -/
theorem DirichletLZerosOnLine.primitive (h : DirichletLZerosOnLine) :
    PrimitiveDirichletLZerosOnLine := fun N _ χ _ s hs ht hz ↦ h N χ s hs ht hz

/-- The primitive open-strip statement implies the per-character hypothesis for every
nonprincipal primitive character. Nonpositive zeros are trivial, and the right boundary is
zero-free, so any remaining zero lies in the open critical strip. -/
theorem PrimitiveDirichletLZerosOnLine.nonprincipal (h : PrimitiveDirichletLZerosOnLine) {N : ℕ}
    [NeZero N] (χ : DirichletCharacter ℂ N) (hp : χ.IsPrimitive) (hne : χ ≠ 1) :
    DirichletRiemannHypothesis χ := fun s hz ht ↦
  h N χ hp s
    (lt_of_not_ge fun hs ↦
      ht
        (mem_trivialZeros_of_gammaFactor_eq_zero χ hne
          (gammaFactor_eq_zero_of_LFunction_zero_re_nonpos χ hp hne hz hs)))
    (lt_of_not_ge fun hs ↦ DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hne) hs hz)
    hz

/-- For a nonprincipal character, the primitive open-strip statement applies to its zeros via
the primitive character of its conductor. The finite Euler factors are nonzero in this strip. -/
theorem PrimitiveDirichletLZerosOnLine.nonprincipal_zero (h : PrimitiveDirichletLZerosOnLine)
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hne : χ ≠ 1) {s : ℂ} (hs : 0 < s.re)
    (ht : s.re < 1) (hz : χ.LFunction s = 0) : s.re = 1 / 2 :=
  letI : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  h χ.conductor χ.primitiveCharacter χ.primitiveCharacter_isPrimitive s hs ht
    ((DirichletLFunction.L_zero_iff_primitive_of_re_pos hne hs).mp hz)

/-- The primitive open-strip hypothesis implies RH. Negative-real-part zeros are trivial;
on the boundary `Re s = 0`, the xi functional equation reflects a zero to the zero-free line
`Re s = 1`. The modulus-one character then supplies the critical-line conclusion. -/
theorem PrimitiveDirichletLZerosOnLine.zeta (h : PrimitiveDirichletLZerosOnLine) :
    RiemannZetaZerosOnLine := by
  intro s hz ht _
  have hlt : s.re < 1 := lt_of_not_ge (fun hs ↦ riemannZeta_ne_zero_of_one_le_re hs hz)
  have hpos : 0 < s.re := by
    by_contra hn
    have hnonpos : s.re ≤ 0 := le_of_not_gt hn
    by_cases hneg : s.re < 0
    · exact ht (RiemannZeta.exists_neg_even_of_zeta_zero_re_neg hneg hz)
    · have hre : s.re = 0 := le_antisymm hnonpos (le_of_not_gt hneg)
      have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hz (le_of_not_gt hneg)
      have hxi' : RiemannXi.riemannXi (1 - s) = 0 := (RiemannXi.riemannXi_one_sub s).trans hxi
      have hz' := RiemannXi.riemannZeta_zero_of_riemannXi_zero hxi'
      have hright : 1 ≤ (1 - s).re := by
        simpa only [Complex.sub_re, Complex.one_re, hre, sub_zero] using (le_refl (1 : ℝ))
      exact riemannZeta_ne_zero_of_one_le_re hright hz'
  have hz' : (1 : DirichletCharacter ℂ 1).LFunction s = 0 :=
    DirichletCharacter.LFunction_modOne_eq.symm ▸ hz
  exact h 1 1 DirichletCharacter.isPrimitive_one_level_one s hpos hlt hz'

/-- GRH places every Dirichlet L-zero in the open strip on the critical line. For a
nonprincipal character, transfer the zero to its primitive character; for the principal
character, use its zeta factor and the nonvanishing finite Euler factors. -/
theorem GeneralizedRiemannHypothesis.zeros_on_line (h : GeneralizedRiemannHypothesis) :
    DirichletLZerosOnLine := by
  intro N _ χ s hs ht hz
  by_cases hχ : χ = 1
  · subst χ
    have hs1 : s ≠ 1 := fun he ↦ (ne_of_lt ht) (he ▸ Complex.one_re)
    have heuler :=
      DirichletCharacter.LFunction_changeLevel (one_dvd N) (1 : DirichletCharacter ℂ 1) (s := s)
        (Or.inr hs1)
    rw [DirichletCharacter.changeLevel_one, DirichletCharacter.LFunction_modOne_eq] at heuler
    have hp :=
      DirichletLFunction.LFactorProduct_ne_zero_of_re_pos (N := N) (1 : DirichletCharacter ℂ 1) hs
    have hzeta : riemannZeta s = 0 := (mul_eq_zero.mp (heuler.symm.trans hz)).resolve_right hp
    have hzeta' : (1 : DirichletCharacter ℂ 1).LFunction s = 0 :=
      DirichletCharacter.LFunction_modOne_eq.symm ▸ hzeta
    exact h.zero_re_eq_half 1 1 DirichletCharacter.isPrimitive_one_level_one s hzeta' hs
  · exact h.primitive_zeros_on_line.nonprincipal_zero χ hχ hs ht hz

/-- Right-half-plane nonvanishing puts primitive zeros in the open strip on the critical line.
The functional equations reflect a zero left of the line to a zero on its right; the principal
case uses xi and the nonprincipal case uses the completed Dirichlet L-function. -/
theorem DirichletLNonvanishingRightOfHalf.primitive (h : DirichletLNonvanishingRightOfHalf) :
    PrimitiveDirichletLZerosOnLine := by
  intro N _ χ hp s hs ht hz
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hr
  · have href : 1 / 2 < (1 - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith only [hl]
    by_cases hχ : χ = 1
    · subst χ
      have hN : N = 1 := hp.symm.trans DirichletCharacter.conductor_one
      subst N
      have hzeta : riemannZeta s = 0 := DirichletCharacter.LFunction_modOne_eq ▸ hz
      have hxi := RiemannXi.xi_zero_of_zeta_zero_of_re_nonneg hzeta hs.le
      have hxi' : RiemannXi.riemannXi (1 - s) = 0 := (RiemannXi.riemannXi_one_sub s).trans hxi
      have hzeta' := RiemannXi.riemannZeta_zero_of_riemannXi_zero hxi'
      have hL : (1 : DirichletCharacter ℂ 1).LFunction (1 - s) = 0 :=
        DirichletCharacter.LFunction_modOne_eq.symm ▸ hzeta'
      have hs1 : (1 - s) ≠ 1 := by
        intro he
        have hh := congrArg Complex.re he
        simp only [Complex.sub_re, Complex.one_re] at hh
        linarith only [hs, hh]
      exact h 1 1 (1 - s) href (Or.inr hs1) hL
    · have hgamma : χ.gammaFactor s ≠ 0 := fun hg ↦
        not_mem_dirichletTrivialZeros_of_re_pos χ hs
          (mem_trivialZeros_of_gammaFactor_eq_zero χ hχ hg)
      have he :=
        DirichletLFunction.L_eq_completed_div_gammaFactor χ s
          (Or.inr (DirichletLFunction.character_level_ne_one_of_ne_one hχ))
      have hc : χ.completedLFunction s = 0 :=
        (div_eq_zero_iff.mp (he.symm.trans hz)).resolve_right hgamma
      have heq : (1 : ℂ) - (1 - s) = s := sub_sub_cancel 1 s
      have hc' := DirichletLFunction.completed_inv_zero_of_one_sub_zero hp (1 - s) (heq.symm ▸ hc)
      have he' :=
        DirichletLFunction.L_eq_completed_div_gammaFactor χ⁻¹ (1 - s)
          (Or.inr (DirichletLFunction.character_level_ne_one_of_ne_one hχ))
      have hz' : χ⁻¹.LFunction (1 - s) = 0 := by rw [he', hc', zero_div]
      exact h N χ⁻¹ (1 - s) href (Or.inl (inv_ne_one.mpr hχ)) hz'
  · exact h N χ s hr (Or.inr (fun he ↦ (ne_of_lt ht) (he ▸ Complex.one_re))) hz

/-- GRH gives nonvanishing to the right of the critical line. Inside the strip this follows
from the all-character zero statement, and on or beyond `Re s = 1` from unconditional
nonvanishing with the stated principal-character exception. -/
theorem GeneralizedRiemannHypothesis.nonvanishing_right (h : GeneralizedRiemannHypothesis) :
    DirichletLNonvanishingRightOfHalf := by
  intro N _ χ s hs hex hz
  by_cases ht : s.re < 1
  · have hspos : 0 < s.re := by linarith only [hs]
    have hh := h.zeros_on_line N χ s hspos ht hz
    linarith only [hs, hh]
  · exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hex (le_of_not_gt ht) hz

/-- The zeta formulation is exactly mathlib's Riemann hypothesis: the definitions agree. -/
theorem riemannZetaZerosOnLine_iff : RiemannZetaZerosOnLine ↔ RiemannHypothesis :=
  Iff.rfl

/-- The primitive open-strip formulation is equivalent to GRH. The forward implication first
recovers RH from the modulus-one character, then separates principal and nonprincipal characters. -/
theorem primitive_zeros_on_line_iff_grh :
    PrimitiveDirichletLZerosOnLine ↔ GeneralizedRiemannHypothesis := by
  constructor
  · intro h N _ χ hprim
    by_cases hχ : χ = 1
    · subst χ
      have hN : N = 1 := hprim.symm.trans DirichletCharacter.conductor_one
      subst N
      exact dirichletRiemannHypothesis_one_iff.mpr (riemannZetaZerosOnLine_iff.mp h.zeta)
    · exact h.nonprincipal χ hprim hχ
  · exact GeneralizedRiemannHypothesis.primitive_zeros_on_line

/-- The open-strip formulation for all Dirichlet characters is equivalent to GRH. Restriction
to primitive characters gives one direction; zero transfer and the principal Euler product give
the other. -/
theorem zeros_on_line_iff_grh : DirichletLZerosOnLine ↔ GeneralizedRiemannHypothesis :=
  ⟨fun h ↦ primitive_zeros_on_line_iff_grh.mp h.primitive,
    GeneralizedRiemannHypothesis.zeros_on_line⟩

/-- The right-half-plane nonvanishing formulation is equivalent to GRH. Reflection supplies
the primitive zero statement, and GRH supplies nonvanishing for all characters. -/
theorem nonvanishing_right_iff_grh :
    DirichletLNonvanishingRightOfHalf ↔ GeneralizedRiemannHypothesis :=
  ⟨fun h ↦ primitive_zeros_on_line_iff_grh.mp h.primitive,
    GeneralizedRiemannHypothesis.nonvanishing_right⟩

end PseudoPrime.AnalyticNumberTheory.GRH
