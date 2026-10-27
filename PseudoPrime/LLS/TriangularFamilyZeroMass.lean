/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSignedZeroMass
public import PseudoPrime.LLS.TriangularSubgroupAverage

/-! # Signed triangular zero mass at varying primitive conductors -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For a finite primitive character family with possibly different conductors,
sum the signed alpha-18 zero-mass bounds. The conductor logarithms and both
scale-one arithmetic real parts remain explicit. This supports primitivized
annihilator families without a common-conductor assumption. -/
theorem triangular18_family_absoluteMass_le_signed {ι : Type*} (S : Finset ι) (f : ι → ℕ)
    [∀ i, NeZero (f i)] (χ : (i : ι) → DirichletCharacter ℂ (f i))
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hf : ∀ i ∈ S, 2 ≤ f i)
    (hp : ∀ i ∈ S, (χ i).IsPrimitive) (hne : ∀ i ∈ S, χ i ≠ 1) (hinv : ∀ i ∈ S, (χ i)⁻¹ ≠ 1) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑ i ∈ S, (∑' ρ : ℂ, ‖K.kernelZeroTerm (χ i) ρ‖)) ≤
      36 * (∑ i ∈ S, Real.log (f i)) -
          (∑ i ∈ S, ((∑' n : ℕ, K.summand (χ i) 1 n).re + (∑' n : ℕ, K.summand ((χ i)⁻¹) 1 n).re)) +
        110000 * S.card := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have h :=
    Finset.sum_le_sum (s := S)
      (fun i hi ↦
        triangular18_absoluteMass_le_signed_arithmetic (hf i hi) hGRH (hp i hi) (hne i hi)
          (hinv i hi))
  change (∑ i ∈ S, (∑' ρ : ℂ, ‖K.kernelZeroTerm (χ i) ρ‖)) ≤ _ at h ⊢
  simp only [sub_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at h
  simpa only [Finset.sum_add_distrib, mul_comm (S.card : ℝ) 110000] using h

end PseudoPrime.LLS.PaperStatements

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, the nonprincipal annihilator characters give a signed alpha-18
zero-mass bound at their individual primitive conductors. Primitive validity
and conductor size are supplied internally. The arithmetic real-part sum is
retained for the following subgroup comparison. -/
theorem triangular18_annihilator_absoluteMass_le_signed {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) :
    letI := Classical.propDecidable
    letI : ∀ χ : NumberTheory.subgroupAnnihilator H, NeZero χ.val.conductor := fun χ ↦
      ⟨χ.val.conductor_ne_zero⟩
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let S := Finset.univ.filter (fun χ : NumberTheory.subgroupAnnihilator H ↦ χ.val ≠ 1)
    (∑ χ ∈ S, (∑' ρ : ℂ, ‖K.kernelZeroTerm χ.val.primitiveCharacter ρ‖)) ≤
      36 * (∑ χ ∈ S, Real.log χ.val.conductor) -
          (∑ χ ∈ S,
            ((∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re +
              (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re)) +
        110000 * S.card := by
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
    triangular18_family_absoluteMass_le_signed S f (fun χ ↦ χ.val.primitiveCharacter) hGRH
      (fun χ hχ ↦
        (by norm_num only : 2 ≤ 3).trans
          (NumberTheory.three_le_conductor_of_ne_one χ.val (hn χ hχ)))
      (fun χ _ ↦ DirichletCharacter.primitiveCharacter_isPrimitive χ.val) hp
      (fun χ hχ ↦ inv_ne_one.mpr (hp χ hχ))

end PseudoPrime.LLS.PaperStatements
