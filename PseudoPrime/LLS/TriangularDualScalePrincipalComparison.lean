/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularDualScaleArithmeticBounds

/-! # Finite principal comparison from the signed dual-scale formula -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, scale at least one and containment of eligible primes through X,
bound the finite principal arithmetic sum times the subgroup index by the signed dual
primitive budgets plus the principal arithmetic cost. Split the principal member from
the primitive average and apply the arithmetic-only dual bound. Gamma terms at both
scales and scale-one arithmetic deductions are retained for later numerical evaluation. -/
theorem triangular18_finite_principal_le_dual_signed {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
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
    (H.index : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      triangularKernelProfile 18 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
            ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re +
            300000000 * Real.sqrt x⁻¹ +
            1300000 * (x⁻¹) ^ (1 / 4 : ℝ) +
            36 * (∑ i ∈ S, Real.log i.val.conductor) -
          (∑ i ∈ S,
            ((∑' n : ℕ, K.summand i.val.primitiveCharacter 1 n).re +
              (∑' n : ℕ, K.summand (i.val.primitiveCharacter)⁻¹ 1 n).re)) -
          36 * S.card +
        300000000 * Real.sqrt x +
        1300000 * x ^ (1 / 4 : ℝ) := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let F := fun χ : A ↦ (∑' n : ℕ, K.summand χ.val.primitiveCharacter x n).re
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
  have hs := Finset.sum_erase_add (s := Finset.univ) F (Finset.mem_univ (1 : A))
  have hp : F (1 : A) = (∑' n : ℕ, K.summand (1 : DirichletCharacter ℂ 1) x n).re :=
    congrArg Complex.re (tsum_congr (MellinKernel.principal_primitive_summand_eq_level_one K x))
  rw [hp] at hs
  have hc :=
    MellinKernel.principal_sum_le_primitive_average_of_noSmallPrimes K H (zero_lt_one.trans_le hx)
      hsmall
  have hb := triangular18_annihilator_arithmetic_upper_dual_signed H hGRH hx
  have hP := triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann (zero_lt_one.trans_le hx)
  dsimp only at hb ⊢
  rw [hf] at hb ⊢
  change (H.index : ℝ) * _ ≤ ∑ χ : A, F χ at hc
  linarith only [hc, hs, hb, hP]

end PseudoPrime.LLS.PaperStatements
