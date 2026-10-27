/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularDualScaleFormula

/-! # Dual-scale formula for primitive annihilator characters -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH and scale at least one, specialize the real dual-scale identity to
nonprincipal annihilator characters at their primitive conductors. Supply conductor size,
primitivity and nonprincipal inverse internally. Both arithmetic scales and Gamma terms
retain their signs. This is the input to the subgroup dual-scale comparison. -/
theorem triangular18_annihilator_dual_scale_signed_formula {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 ≤ x) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let G :=
      fun (i : NumberTheory.subgroupAnnihilator H) (ψ : DirichletCharacter ℂ (i.val.conductor))
        (y : ℝ) ↦
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (∫ t : ℝ,
          logDeriv ψ.gammaFactor ((((9 / 16 : ℝ) : ℂ) + Complex.I * t) + 1 / 2) *
            (K.function (((9 / 16 : ℝ) : ℂ) + Complex.I * t) *
              (y : ℂ) ^ (((9 / 16 : ℝ) : ℂ) + Complex.I * t)))
    let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
    (∑ i ∈ S,
        ((∑' n : ℕ, K.summand (i.val.primitiveCharacter) x n) +
            (∑' n : ℕ, K.summand (i.val.primitiveCharacter)⁻¹ x⁻¹ n) +
            (∑' ρ : ℂ, K.oscillatingZeroTerm (i.val.primitiveCharacter) x ρ)).re) =
      triangularKernelProfile 18 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
        ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let f := fun χ : A ↦ χ.val.conductor
  let : ∀ χ : A, NeZero (f χ) := fun χ ↦ ⟨χ.val.conductor_ne_zero⟩
  let S := Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1)
  have hn (χ : A) (hχ : χ ∈ S) : χ.val ≠ 1 := (Finset.mem_filter.mp hχ).2
  have hp (χ : A) (hχ : χ ∈ S) : χ.val.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val (hn χ hχ)
  exact
    triangular18_dual_scale_signed_family_formula S f (fun χ ↦ χ.val.primitiveCharacter) hGRH
      (fun χ hχ ↦
        (by norm_num only : 2 ≤ 3).trans
          (NumberTheory.three_le_conductor_of_ne_one χ.val (hn χ hχ)))
      (fun χ _ ↦ DirichletCharacter.primitiveCharacter_isPrimitive χ.val) hp
      (fun χ hχ ↦ inv_ne_one.mpr (hp χ hχ)) hx

end PseudoPrime.LLS.PaperStatements
