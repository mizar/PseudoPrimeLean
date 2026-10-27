/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularDualScaleAnnihilator
public import PseudoPrime.LLS.TriangularSignedAverage
public import PseudoPrime.LLS.TriangularPrincipalUpperBounds

/-! # Dual-scale arithmetic cancellation in the triangular subgroup average -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For an annihilator subgroup and positive scale, the inverse-character
primitive arithmetic sum at inverse scale is at least minus the level-one principal sum.
Use full primitive aggregate positivity, remove the principal member, and identify inverse
real parts. This controls the dual arithmetic term without a conductor remainder. -/
theorem triangular18_nonprincipal_inverse_scale_sum_lower {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) {x : ℝ} (hx : 0 < x) :
    letI := Classical.propDecidable
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18);
    -(∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re ≤
      ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
        (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ x⁻¹ n).re := by
  classical
  let _ := Classical.propDecidable
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let A := NumberTheory.subgroupAnnihilator H
  let F := fun χ : A ↦ (∑' n : ℕ, K.summand χ.val.primitiveCharacter x⁻¹ n).re
  have hn := MellinKernel.primitive_tsum_sum_re_nonneg K A (inv_pos.mpr hx)
  rw [Complex.re_sum] at hn
  have he := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re :=
    congrArg Complex.re (tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x⁻¹))
  have hr (χ : A) : (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ x⁻¹ n).re = F χ := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact MellinKernel.tsum_summand_inv_re_eq K χ.val.primitiveCharacter (inv_pos.mpr hx)
  have hs := Finset.sum_congr (s₁ := Finset.univ.erase (1 : A)) rfl (fun χ _ ↦ hr χ)
  change -_ ≤ _
  rw [hs]
  rw [hp] at he
  change 0 ≤ ∑ χ : A, F χ at hn
  linarith only [hn, he]

/-- Under GRH and scale at least one, the nonprincipal primitive arithmetic
plus oscillating zero aggregate is bounded by the triangular conductor profile, signed
Gamma integrals at both scales, and the inverse-scale level-one principal sum.
Combine the exact dual formula with the lower bound for inverse arithmetic.
This removes the dual arithmetic family while retaining Gamma signs. -/
theorem triangular18_annihilator_dual_scale_arithmetic_upper {q : ℕ} [NeZero q]
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
            (∑' ρ : ℂ, K.oscillatingZeroTerm (i.val.primitiveCharacter) x ρ)).re) ≤
      triangularKernelProfile 18 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
        ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re +
        (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x⁻¹ n).re := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  have hf : Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1) = Finset.univ.erase (1 : A) := by
    have hn (χ : A) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (hn χ)]
  have he := triangular18_annihilator_dual_scale_signed_formula H hGRH hx
  have hd := triangular18_nonprincipal_inverse_scale_sum_lower H (zero_lt_one.trans_le hx)
  dsimp only at he hd ⊢
  rw [hf] at he ⊢
  simp only [Complex.add_re, Finset.sum_add_distrib] at he ⊢
  linarith only [he, hd]

/-- Under the same hypotheses, bound the inverse-scale level-one sum
by the explicit RH upper bound evaluated at inverse scale. The remaining principal cost
decays with the scale; both Gamma integrals keep their signs. This supplies the numerical
arithmetic component of the dual-scale subgroup comparison. -/
theorem triangular18_annihilator_dual_scale_arithmetic_upper_numeric {q : ℕ} [NeZero q]
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
            (∑' ρ : ℂ, K.oscillatingZeroTerm (i.val.primitiveCharacter) x ρ)).re) ≤
      triangularKernelProfile 18 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
        ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re +
        300000000 * Real.sqrt x⁻¹ +
        1300000 * (x⁻¹) ^ (1 / 4 : ℝ) := by
  have h := triangular18_annihilator_dual_scale_arithmetic_upper H hGRH hx
  have hp :=
    triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann
      (inv_pos.mpr (zero_lt_one.trans_le hx))
  dsimp only at h ⊢
  linarith only [h, hp]

end PseudoPrime.LLS.PaperStatements
