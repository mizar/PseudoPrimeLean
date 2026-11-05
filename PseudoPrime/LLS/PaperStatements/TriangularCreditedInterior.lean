/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.TriangularDualScaleInteriorNumerics
public import PseudoPrime.LLS.PaperStatements.TriangularScaleOneCredit

/-! # Signed interior comparison with the scale-one arithmetic credit -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH inside triangular support, retain the scale-one finite principal sum
in the signed conductor comparison. The negative Gamma budget is valid only here. -/
theorem triangular18_creditedInterior_numeric {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x X : ℝ} (hx : 1 ≤ x)
    (hlog : Real.log x ≤ 36) (hX : 0 ≤ X) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ X → NumberTheory.residueInSubgroup q H p) :
    (H.index : ℝ) *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
            ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
                (1 : DirichletCharacter ℂ q) x n).re) +
        2 * (H.index : ℝ) *
          (∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
            ((triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).summand
                (1 : DirichletCharacter ℂ 1) 1 n).re) ≤
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        (72 - Real.log x) * subgroupConductorLogSum H +
        ((H.index : ℝ) - 1) * (-81 + (3 / 2) * Real.log x) := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have hf : Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1) = Finset.univ.erase (1 : A) := by
    have he (χ : A) : χ.val = 1 ↔ χ = 1 := by
      constructor
      · intro h
        exact Subtype.ext h
      · intro h
        exact congrArg Subtype.val h
    apply Finset.ext
    intro χ
    simp only [Finset.mem_filter, Finset.mem_erase, Finset.mem_univ, true_and, and_true,
      not_congr (he χ)]
  have hcard : ((Finset.univ.erase (1 : A)).card : ℝ) = (H.index : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))),
      Nat.cast_one, NumberTheory.card_subgroupAnnihilator]
  have hcond :
    (∑ χ ∈ Finset.univ.erase (1 : A), Real.log χ.val.conductor) = subgroupConductorLogSum H := by
    unfold subgroupConductorLogSum
    apply Finset.sum_congr
    · apply Finset.ext
      intro χ
      simp only [Finset.mem_erase, Finset.mem_univ]
    · intro χ _
      rfl
  have hp : triangularKernelProfile 18 x = 36 - Real.log x := by
    unfold triangularKernelProfile
    rw [abs_of_nonneg (Real.log_nonneg hx)]
    norm_num only
    exact max_eq_right (sub_nonneg.mpr hlog)
  have hb := triangular18_finite_principal_le_dual_interior H hGRH hx hlog hsmall
  dsimp only at hb
  rw [hf, hcard, hcond, hp] at hb
  have ha := triangular18_scaleOne_pair_lower H hX hlarge hsmall
  have h1 := triangular18_level_one_arithmetic_upper_of_rh hGRH.riemann (x := 1) (by norm_num only)
  simp only [Real.sqrt_one, Real.one_rpow, mul_one] at h1
  dsimp only at ha
  change (H.index : ℝ) * _ + 2 * (H.index : ℝ) * _ ≤ _
  nlinarith only [hb, ha, h1]

/-- With every prime factor strictly beyond the cutoff, the finite principal sum
at any scale agrees with its level-one counterpart, including the cutoff endpoint. -/
theorem finite_principal_eq_level_one (K : MellinKernel) {q : ℕ} [NeZero q] {x X : ℝ} (hX : 0 ≤ X)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → X < (p : ℝ)) :
    (∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ q) x n).re) =
      ∑ n ∈ Finset.Icc 1 ⌊X⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re := by
  have hd : ∀ p : ℕ, p.Prime → p ∣ q → ⌊X⌋₊ < p := by
    intro p hp hpq
    exact (Nat.floor_lt hX).mpr (hlarge p hp hpq)
  have heq := MellinKernel.principal_sum_level_one_of_no_divisor K (q := q) x hd
  have hI : Finset.Ioc 0 ⌊X⌋₊ = Finset.Icc 1 ⌊X⌋₊ := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Icc, Nat.one_le_iff_ne_zero, Nat.pos_iff_ne_zero]
  have h := congrArg Complex.re heq
  simpa only [hI, Complex.re_sum] using h

/-- Under GRH and small-prime containment, bound the combined scale-x and scale-one
level-one sums by the signed interior conductor budget. Strict prime-factor exclusion
justifies the exact principal-sum replacement. -/
theorem triangular18_joint_interior {q : ℕ} [NeZero q] (H : Subgroup (ZMod q)ˣ)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x)
    (hlog : Real.log x ≤ 36) (hlarge : ∀ p : ℕ, p.Prime → p ∣ q → x < (p : ℝ))
    (hsmall : ∀ p : ℕ, p.Prime → ¬p ∣ q → (p : ℝ) ≤ x → NumberTheory.residueInSubgroup q H p) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (H.index : ℝ) *
        ((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) x n).re) +
          2 * (∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (K.summand (1 : DirichletCharacter ℂ 1) 1 n).re)) ≤
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
        1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
        602600000 +
        ((H.index : ℝ) - 1) * ((72 - Real.log x) * Real.log q - 81 + (3 / 2) * Real.log x) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  have heq :=
    finite_principal_eq_level_one K (q := q) (x := x) (X := x) (by linarith only [hx]) hlarge
  have hb :=
    triangular18_creditedInterior_numeric H hGRH hx hlog (by linarith only [hx]) hlarge hsmall
  rw [heq] at hb
  have hcoef : 0 ≤ 72 - Real.log x := by linarith only [hlog]
  have hu := mul_le_mul_of_nonneg_left (subgroupConductorLogSum_le H) hcoef
  nlinarith only [hb, hu]

end PseudoPrime.LLS.PaperStatements
