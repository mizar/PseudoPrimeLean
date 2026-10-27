/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularGammaInteriorBounds
public import PseudoPrime.LLS.TriangularDualScalePrincipalComparison

/-!
# Finite principal comparison with signed interior Gamma budgets

Evaluate both Gamma terms in the logarithmic support and sum their negative budgets
over the nonprincipal primitive annihilator family.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH, eligible-prime containment through X and 1≤x with log x≤36, the
finite principal sum times the subgroup index is bounded by the dual arithmetic
budgets with the two Gamma integrals replaced by the signed cost
card(S)(-3(36-log x)/2+9). Apply the two interior Gamma bounds termwise and sum.
The conductor profile and scale-one arithmetic deductions remain in the comparison. -/
theorem triangular18_finite_principal_le_dual_interior {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hlog : Real.log x ≤ 36)
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → residueInSubgroup q H p) :
    letI := Classical.propDecidable
    letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
      ⟨i.val.conductor_ne_zero⟩
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    let S := Finset.univ.filter (fun i : NumberTheory.subgroupAnnihilator H ↦ i.val ≠ 1)
    (H.index : ℝ) * (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) ≤
      triangularKernelProfile 18 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
            (S.card : ℝ) * (-(3 / 2) * (36 - Real.log x) + 9) +
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
  have h := triangular18_finite_principal_le_dual_signed H hGRH hx hsmall
  have hpoint (i : NumberTheory.subgroupAnnihilator H) :
    (G i i.val.primitiveCharacter x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re ≤
      -(3 / 2) * (36 - Real.log x) + 9 := by
    have h1 :=
      triangular18_gammaIntegral_re_le_interior i.val.primitiveCharacter (b := 9 / 16)
        (by norm_num only) (by norm_num only) hx hlog
    have h2 :=
      triangular18_inverse_gammaIntegral_re_le_interior (i.val.primitiveCharacter)⁻¹ (b := 9 / 16)
        (by norm_num only) (by norm_num only) hx hlog
    change ((G i i.val.primitiveCharacter x).re + (G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re) ≤ _
    dsimp only at h1 h2
    dsimp only [G, K]
    simp only [Complex.ofReal_inv, triangularMellinKernel] at h1 h2 ⊢
    linarith only [h1, h2]
  have hb :
    (∑ i ∈ S, (G i i.val.primitiveCharacter x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re) ≤
      (S.card : ℝ) * (-(3 / 2) * (36 - Real.log x) + 9) := by
    have hh := Finset.sum_le_sum (s := S) (fun i _ ↦ hpoint i)
    simpa only [Finset.sum_const, nsmul_eq_mul] using hh
  dsimp only [G, S] at hb
  dsimp only at h ⊢
  linarith only [h, hb]

end PseudoPrime.LLS.PaperStatements
