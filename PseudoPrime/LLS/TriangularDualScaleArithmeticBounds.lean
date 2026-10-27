/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularDualScaleAverage

/-! # Arithmetic-only triangular dual-scale comparison -/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For primitive nonprincipal GRH data with nonprincipal inverse and positive scale,
the oscillating zero real part is at least minus the conductor term plus both scale-one
arithmetic real parts and thirty-six. Bound its norm by the absolute mass and apply
the signed negative Gamma budget. This preserves the scale-one arithmetic cancellation. -/
theorem triangular18_oscillating_zero_re_lower_signed {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (-36 * Real.log q + (∑' n : ℕ, K.summand χ 1 n).re + (∑' n : ℕ, K.summand χ⁻¹ 1 n).re + 36 ≤
      (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re) := by
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let Z := ∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ
  have hs := MellinKernel.summable_oscillatingZeroTerm K hq hGRH hp hne hinv hx
  have ht := norm_tsum_le_tsum_norm hs.norm
  have he : (∑' ρ : ℂ, ‖K.oscillatingZeroTerm χ x ρ‖) = ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ :=
    tsum_congr (MellinKernel.norm_oscillatingZeroTerm K χ hx)
  have hz : ‖Z‖ ≤ ∑' ρ : ℂ, ‖K.kernelZeroTerm χ ρ‖ := ht.trans_eq he
  have hm := triangular18_absoluteMass_le_signed_arithmetic_sub_thirty_six hq hGRH hp hne hinv
  have hr := Complex.re_le_norm (-Z)
  rw [Complex.neg_re, norm_neg] at hr
  change -36 * Real.log q + _ + _ + 36 ≤ Z.re
  linarith only [hz, hm, hr]

/-- Under GRH and scale at least one, bound the nonprincipal primitive arithmetic
aggregate by the dual conductor profile, both signed Gamma integrals, and the inverse-scale
principal cost, minus the scale-one arithmetic pair and thirty-six per member.
Combine the dual average upper bound with the signed oscillating zero lower bound.
This removes the oscillating zero aggregate without an estimated left-contour remainder. -/
theorem triangular18_annihilator_arithmetic_upper_dual_signed {q : ℕ} [NeZero q]
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
    (∑ i ∈ S, (∑' n : ℕ, K.summand (i.val.primitiveCharacter) x n).re) ≤
      triangularKernelProfile 18 x * (∑ i ∈ S, Real.log (i.val.conductor)) +
          ∑ i ∈ S, (G i (i.val.primitiveCharacter) x + G i (i.val.primitiveCharacter)⁻¹ x⁻¹).re +
          300000000 * Real.sqrt x⁻¹ +
          1300000 * (x⁻¹) ^ (1 / 4 : ℝ) +
          36 * (∑ i ∈ S, Real.log i.val.conductor) -
        (∑ i ∈ S,
          ((∑' n : ℕ, K.summand i.val.primitiveCharacter 1 n).re +
            (∑' n : ℕ, K.summand (i.val.primitiveCharacter)⁻¹ 1 n).re)) -
        36 * S.card := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let S := Finset.univ.filter (fun χ : A ↦ χ.val ≠ 1)
  have hn (χ : A) (hχ : χ ∈ S) : χ.val ≠ 1 := (Finset.mem_filter.mp hχ).2
  have hp (χ : A) (hχ : χ ∈ S) : χ.val.primitiveCharacter ≠ 1 :=
    AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val (hn χ hχ)
  let : ∀ χ : A, NeZero χ.val.conductor := fun χ ↦ ⟨χ.val.conductor_ne_zero⟩
  have hz (χ : A) (hχ : χ ∈ S) :
    -36 * Real.log χ.val.conductor + (∑' n : ℕ, K.summand χ.val.primitiveCharacter 1 n).re +
        (∑' n : ℕ, K.summand (χ.val.primitiveCharacter)⁻¹ 1 n).re +
        36 ≤
      (∑' ρ : ℂ, K.oscillatingZeroTerm χ.val.primitiveCharacter x ρ).re := by
    let : NeZero χ.val.conductor := ⟨χ.val.conductor_ne_zero⟩
    exact
      triangular18_oscillating_zero_re_lower_signed
        ((by norm_num only : 2 ≤ 3).trans
          (NumberTheory.three_le_conductor_of_ne_one χ.val (hn χ hχ)))
        hGRH (DirichletCharacter.primitiveCharacter_isPrimitive χ.val) (hp χ hχ)
        (inv_ne_one.mpr (hp χ hχ)) (zero_lt_one.trans_le hx)
  have hsum := Finset.sum_le_sum (s := S) hz
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul] at hsum
  have h := triangular18_annihilator_dual_scale_arithmetic_upper_numeric H hGRH hx
  dsimp only at h ⊢
  simp only [Complex.add_re, Finset.sum_add_distrib] at h
  simp only [Complex.add_re, Finset.sum_add_distrib]
  linarith only [h, hsum]

end PseudoPrime.LLS.PaperStatements
