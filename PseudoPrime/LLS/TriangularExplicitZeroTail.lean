/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.TriangularSignedZeroInteriorComparison
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.PoissonNumericalBounds

/-!
# Explicit alpha-18 zero tails and compact-height witness comparison

Bound heights at least one through the numerical centered Poisson formula, uniformly
in positive scale, and retain only the low-height zero aggregate in the witness gap.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

open AnalyticNumberTheory.DirichletLFunction in
/-- For a primitive nonprincipal character under individual RH and a completed zero
at height at least one, the alpha-18 kernel term has norm at most eight times its
Poisson term at three halves. Use critical-line location and the height-square bound.
This supplies an explicit tail majorant without a local-count existence constant. -/
theorem triangular18_zero_norm_le_eight_poisson_of_height {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {ρ : ℂ} (hheight : 1 ≤ |ρ.im|) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖K.kernelZeroTerm χ ρ‖ ≤
      8 *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          (1 / Complex.normSq (((3 / 2 : ℝ) : ℂ) - ρ))) := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD : D = 0
  · dsimp only [D] at hD
    simp only [MellinKernel.kernelZeroTerm, hD, Int.cast_zero, zero_mul, norm_zero, mul_zero,
      le_refl]
  · have hr :=
      completedLFunction_zero_re_eq_half_of_dirichletRH hRH hp hinv
        (dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD)
    have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
    have hn : (0 : ℝ) ≤ D := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    have he : Complex.normSq (((3 / 2 : ℝ) : ℂ) - ρ) = 1 + ρ.im ^ 2 := by
      rw [Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im, hr]
      ring
    have hs : 1 ≤ ρ.im ^ 2 := by
      have hh := mul_self_le_mul_self zero_le_one hheight
      simpa only [← pow_two, sq_abs, one_pow] using hh
    have hb :=
      Analysis.triangularMellinFunction_height_sq_norm_le_four (by norm_num only : (18 : ℝ) ≠ 0)
        ρ.im
    have hk : ‖Analysis.triangularMellinFunction 18 (Complex.I * ρ.im)‖ ≤ 8 / (1 + ρ.im ^ 2) := by
      apply (le_div_iff₀ (by linarith only [sq_nonneg ρ.im] : 0 < 1 + ρ.im ^ 2)).mpr
      have hm :=
        mul_le_mul_of_nonneg_right hs
          (norm_nonneg (Analysis.triangularMellinFunction 18 (Complex.I * ρ.im)))
      nlinarith only [hb, hm]
    change ‖(D : ℂ) * Analysis.triangularMellinFunction 18 (Complex.I * ρ.im)‖ ≤ _
    rw [norm_mul, Complex.norm_intCast, abs_of_nonneg hn, he]
    exact (mul_le_mul_of_nonneg_left hk hn).trans_eq (by ring)

open AnalyticNumberTheory.DirichletLFunction in
/-- For primitive nonprincipal RH data, nonprincipal inverse and every positive
scale, the alpha-18 oscillating zero series restricted to heights at least one has norm
at most 4 log q+96. Dominate by eight Poisson terms and use the numerical centered
Poisson bound at three halves. The constant is independent of the scale. -/
theorem triangular18_oscillating_zero_tail_norm_le_explicit {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hRH : AnalyticNumberTheory.GRH.DirichletRiemannHypothesis χ)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    ‖∑' ρ : ℂ, if 1 ≤ |ρ.im| then K.oscillatingZeroTerm χ x ρ else 0‖ ≤ 4 * Real.log q + 96 := by
  classical
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let P := fun ρ : ℂ ↦
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
      (1 / Complex.normSq (((3 / 2 : ℝ) : ℂ) - ρ))
  let F := fun ρ : ℂ ↦ if 1 ≤ |ρ.im| then K.oscillatingZeroTerm χ x ρ else 0
  have hP : Summable P := by
    have h :=
      summable_completed_poisson_terms hq hRH hp hne hinv (s := ((3 / 2 : ℝ) : ℂ))
        (by norm_num only [Complex.ofReal_re])
    norm_num only [Complex.ofReal_re] at h
    exact h
  have hP0 (ρ : ℂ) : 0 ≤ P ρ := by
    have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (DirichletCharacter.differentiable_completedLFunction hne).analyticAt z
    exact
      mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ)
        (div_nonneg zero_le_one (Complex.normSq_nonneg _))
  have hb (ρ : ℂ) : ‖F ρ‖ ≤ 8 * P ρ := by
    dsimp only [F]
    by_cases hh : 1 ≤ |ρ.im|
    · rw [ite_eq_left hh, MellinKernel.norm_oscillatingZeroTerm K χ hx]
      exact triangular18_zero_norm_le_eight_poisson_of_height hRH hp hne hinv hh
    · rw [ite_eq_right hh, norm_zero]
      exact mul_nonneg (by norm_num only) (hP0 ρ)
  have hmajor := hP.mul_left (8 : ℝ)
  have hs : Summable F := hmajor.of_norm_bounded hb
  have hnorm := hmajor.of_nonneg_of_le (fun ρ ↦ norm_nonneg (F ρ)) hb
  have hsum := Summable.tsum_le_tsum hb hnorm hmajor
  rw [tsum_mul_left] at hsum
  have he :=
    completed_poissonSum_centered_le_inv_gap hq hRH hp hne hinv (σ := 3 / 2) (by norm_num only)
      (by norm_num only)
  norm_num only at he
  have hu : (∑' ρ : ℂ, P ρ) ≤ Real.log q / 2 + 12 := by
    have h := (abs_le.mp he).2
    linarith only [h]
  have ht := (norm_tsum_le_tsum_norm hs.norm).trans hsum
  change ‖∑' ρ : ℂ, F ρ‖ ≤ _
  linarith only [ht, hu]

/-- For primitive nonprincipal GRH data and positive scale, the full oscillating
zero real part is at least its height-below-one part minus 4 log q+96. Split two
absolutely convergent series and apply the explicit tail norm bound. This isolates
the compact-height cancellation still required for the target comparison. -/
theorem triangular18_oscillating_zero_re_lower_by_low_height {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 0 < x) :
    let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
    (∑' ρ : ℂ, if |ρ.im| < 1 then K.oscillatingZeroTerm χ x ρ else 0).re - (4 * Real.log q + 96) ≤
      (∑' ρ : ℂ, K.oscillatingZeroTerm χ x ρ).re := by
  classical
  let K := triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)
  let F := fun ρ : ℂ ↦ K.oscillatingZeroTerm χ x ρ
  let Lo := fun ρ : ℂ ↦ if |ρ.im| < 1 then F ρ else 0
  let Hi := fun ρ : ℂ ↦ if 1 ≤ |ρ.im| then F ρ else 0
  have hs := MellinKernel.summable_oscillatingZeroTerm K hq hGRH hp hne hinv hx
  have hlo : Summable Lo :=
    hs.norm.of_norm_bounded
      (fun ρ ↦ by
        dsimp only [Lo, F]
        by_cases hh : |ρ.im| < 1
        · rw [ite_eq_left hh]
        · rw [ite_eq_right hh, norm_zero]; exact norm_nonneg _)
  have hhi : Summable Hi :=
    hs.norm.of_norm_bounded
      (fun ρ ↦ by
        dsimp only [Hi, F]
        by_cases hh : 1 ≤ |ρ.im|
        · rw [ite_eq_left hh]
        · rw [ite_eq_right hh, norm_zero]; exact norm_nonneg _)
  have he (ρ : ℂ) : F ρ = Lo ρ + Hi ρ := by
    dsimp only [Lo, Hi]
    by_cases hh : |ρ.im| < 1
    · rw [ite_eq_left hh, ite_eq_right (not_le.mpr hh), add_zero]
    · rw [ite_eq_right hh, ite_eq_left (le_of_not_gt hh), zero_add]
  have hsum : (∑' ρ : ℂ, F ρ) = (∑' ρ : ℂ, Lo ρ) + ∑' ρ : ℂ, Hi ρ := by
    rw [tsum_congr he, hlo.tsum_add hhi]
  have ht := triangular18_oscillating_zero_tail_norm_le_explicit hq (hGRH q χ hp) hp hne hinv hx
  have hr := Complex.re_le_norm (-(∑' ρ : ℂ, Hi ρ))
  rw [Complex.neg_re, norm_neg] at hr
  change (∑' ρ : ℂ, Lo ρ).re - _ ≤ (∑' ρ : ℂ, F ρ).re
  rw [hsum, Complex.add_re]
  linarith only [hr, ht]

/-- The nonprincipal primitive annihilator aggregate of real oscillating zero
terms at heights strictly below one for the alpha-18 kernel. The conductor instances
and finite family match the full signed zero aggregate. This total definition is the
compact-height term retained in the numerical witness gap. -/
noncomputable def triangular18_annihilator_lowZeroRealSum {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (x : ℝ) : ℝ :=
  letI := Classical.propDecidable
  letI : ∀ i : NumberTheory.subgroupAnnihilator H, NeZero i.val.conductor := fun i ↦
    ⟨i.val.conductor_ne_zero⟩
  ∑ χ ∈ Finset.univ.erase (1 : NumberTheory.subgroupAnnihilator H),
    (∑' ρ : ℂ,
        if |ρ.im| < 1 then
          (triangularMellinKernel (by norm_num only : (0 : ℝ) < 18)).oscillatingZeroTerm
            χ.val.primitiveCharacter x ρ
        else 0).re

/-- Under GRH and positive scale, the full primitive annihilator zero real sum
is at least its height-below-one part minus four times the exact conductor logarithm
sum and 96 per nonprincipal character. Sum the individual tail lower bounds and
identify the annihilator cardinality. This retains exact conductor costs. -/
theorem triangular18_annihilator_zeroRealSum_lower_by_low_height {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 0 < x) :
    triangular18_annihilator_lowZeroRealSum H x - 4 * subgroupConductorLogSum H -
        96 * ((H.index : ℝ) - 1) ≤
      triangular18_annihilator_zeroRealSum H x := by
  classical
  let _ := Classical.propDecidable
  let A := NumberTheory.subgroupAnnihilator H
  let : ∀ χ : A, NeZero χ.val.conductor := fun χ ↦ ⟨χ.val.conductor_ne_zero⟩
  have hpoint (χ : A) (hχ : χ ∈ Finset.univ.erase (1 : A)) :=
    triangular18_oscillating_zero_re_lower_by_low_height
      ((by norm_num only : 2 ≤ 3).trans
        (NumberTheory.three_le_conductor_of_ne_one χ.val
          (fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he))))
      hGRH (DirichletCharacter.primitiveCharacter_isPrimitive χ.val)
      (AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val
        (fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he)))
      (inv_ne_one.mpr
        (AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ.val
          (fun he ↦ (Finset.mem_erase.mp hχ).1 (Subtype.ext he))))
      hx
  have hs := Finset.sum_le_sum (s := Finset.univ.erase (1 : A)) hpoint
  have hcard : ((Finset.univ.erase (1 : A)).card : ℝ) = (H.index : ℝ) - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (Fintype.card_pos_iff.mpr ⟨1⟩))),
      Nat.cast_one, NumberTheory.card_subgroupAnnihilator]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    nsmul_eq_mul, hcard] at hs
  have hcond :
    (∑ χ ∈ Finset.univ.erase (1 : A), Real.log χ.val.conductor) = subgroupConductorLogSum H := by
    unfold subgroupConductorLogSum
    apply Finset.sum_congr
    · apply Finset.ext
      intro χ
      simp only [Finset.mem_erase, Finset.mem_univ]
    · intro χ _
      rfl
  rw [hcond] at hs
  unfold triangular18_annihilator_lowZeroRealSum triangular18_annihilator_zeroRealSum
  simpa only [sub_sub, mul_comm] using hs

/-- Under GRH, 1<x with log x≤36 and a strict gap including the height-below-one
zero aggregate, a prime at most x divides the level or lies outside the subgroup.
Bound the explicit tail by the ambient conductor sum and apply the zero-retained gap.
The conductor coefficient is 40-log x; the compact zero contribution remains explicit. -/
theorem exists_prime_factor_or_outside_of_triangular18_low_height_gap {q : ℕ} [NeZero q]
    (H : Subgroup (ZMod q)ˣ) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ}
    (hx : 1 < x) (hlog : Real.log x ≤ 36)
    (hgap :
      300000000 * (Real.sqrt x + Real.sqrt x⁻¹) +
          1300000 * (x ^ (1 / 4 : ℝ) + (x⁻¹) ^ (1 / 4 : ℝ)) +
          ((H.index : ℝ) - 1) * ((40 - Real.log x) * Real.log q + 51 + (3 / 2) * Real.log x) <
        (H.index : ℝ) *
            (Real.sqrt x * (68 + 4 * Real.exp (-18)) - 1456 * x ^ (1 / 4 : ℝ) -
              36 * Real.log q / (Real.sqrt x - 1)) +
          triangular18_annihilator_lowZeroRealSum H x) :
    ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ x ∧ (p ∣ q ∨ ¬residueInSubgroup q H p) := by
  have hz := triangular18_annihilator_zeroRealSum_lower_by_low_height H hGRH (zero_lt_one.trans hx)
  have hc :=
    mul_le_mul_of_nonneg_left (subgroupConductorLogSum_le H) (by norm_num only : (0 : ℝ) ≤ 4)
  apply exists_prime_factor_or_outside_of_triangular18_zero_retained_gap H hGRH hx hlog
  nlinarith only [hgap, hz, hc]

end PseudoPrime.LLS.PaperStatements
