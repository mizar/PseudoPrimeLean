/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.CompletedGenusZeroSums

/-! # Unconditional local multiplicity bounds for completed Dirichlet zeros -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction

/-- For a primitive nonprincipal character with nonprincipal inverse, a divisor in
an ordinate window of radius one is bounded by four times its shifted inverse-square
mass. The open critical strip bounds the squared distance from `3/2 + it` by four.
This compares local multiplicity with an unconditional summable genus series. -/
theorem completed_divisor_le_four_mul_shifted_mass_unconditionally {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hp : χ.IsPrimitive) (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {t : ℝ} {ρ : ℂ}
    (ht : |ρ.im - t| ≤ 1) :
    (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
      4 *
        ((MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) *
          ‖(((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ)⁻¹‖ ^ 2) := by
  let D := MeromorphicOn.divisor χ.completedLFunction Set.univ ρ
  by_cases hD : D = 0
  · change (D : ℝ) ≤ 4 * ((D : ℝ) * _)
    simp only [hD, Int.cast_zero, zero_mul, mul_zero, le_refl]
  · have hz := dirichletCompletedLFunction_zero_of_divisor_univ_ne_zero hne hD
    have hrlo := completedLFunction_zero_re_pos hp hinv hz
    have hrhi := completedLFunction_zero_re_lt_one hne hz
    have ha : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
      (χ.differentiable_completedLFunction hne).analyticAt z
    have hn : (0 : ℝ) ≤ D := by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg ha ρ
    have he :
      Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ) =
        (3 / 2 - ρ.re) ^ 2 + (t - ρ.im) ^ 2 := by
      simp only [Complex.normSq_apply, Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.I_re,
        Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero,
        Complex.sub_im, Complex.add_im, Complex.mul_im, zero_add, one_mul]
      ring
    have hd : 0 < Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ) := by
      rw [he]
      nlinarith only [hrhi, sq_nonneg (t - ρ.im), sq_nonneg (ρ.re - 1)]
    have hupper : Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ) ≤ 4 := by
      rw [he]
      have hprod := mul_nonneg hrlo.le (sub_nonneg.mpr hrhi.le)
      have htl := (abs_le.mp ht).1
      have htu := (abs_le.mp ht).2
      have htp :=
        mul_nonneg (by linarith only [htl] : 0 ≤ 1 + (ρ.im - t))
          (by linarith only [htu] : 0 ≤ 1 - (ρ.im - t))
      nlinarith only [hprod, htp, hrlo.le]
    have hratio : (1 : ℝ) ≤ 4 / Complex.normSq (((3 / 2 : ℝ) : ℂ) + Complex.I * t - ρ) :=
      (le_div_iff₀ hd).mpr (by simpa only [one_mul] using hupper)
    have hb := mul_le_mul_of_nonneg_left hratio hn
    change (D : ℝ) ≤ 4 * ((D : ℝ) * _)
    rw [norm_inv, inv_pow, ← Complex.normSq_eq_norm_sq]
    simp only [mul_one] at hb
    convert hb using 1
    ring

/-- Uniformly in primitive nonprincipal characters, their nonprincipal inverses, and
moduli at least two, finite multiplicity in every ordinate window of radius one is
bounded by an absolute constant times the conductor and height logarithms. Sum the
pointwise shifted-mass comparison and use the unconditional genus mass estimate.
This supplies the local input for quantitative high-zero tails without RH. -/
theorem exists_uniform_local_zeroMultiplicity_bound_unconditionally :
    ∃ C : ℝ,
      0 < C ∧
        ∀ (q : ℕ) [NeZero q],
          2 ≤ q →
            ∀ (χ : DirichletCharacter ℂ q),
              χ.IsPrimitive →
                χ ≠ 1 →
                χ⁻¹ ≠ 1 →
                ∀ (t : ℝ) (S : Finset ℂ),
                  (∀ ρ ∈ S, |ρ.im - t| ≤ 1) →
                    ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
                      C * (Real.log q + Real.log (4 + |t|) + 1) := by
  let A := LogFreeDensity.completedGenusMassShiftConstant
  let B := LogFreeDensity.completedGenusMassCenterConstant
  let C := 8 * (13 + |A| + |B| * (Real.log 4 + 1))
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num only)
  have hC : 0 < C := by
    dsimp only [C]
    nlinarith only [abs_nonneg A,
      mul_nonneg (abs_nonneg B) (by linarith only [hlog4] : 0 ≤ Real.log 4 + 1)]
  refine ⟨C, hC, ?_⟩
  intro q _ hq χ hp hne hinv t S hS
  let s : ℂ := ((3 / 2 : ℝ) : ℂ) + Complex.I * t
  have hs : 1 < s.re := by
    norm_num only [s, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
      Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  have hsum := LogFreeDensity.summable_completed_genus_inverse_square hq hne hp hinv hs
  have hAn : AnalyticOnNhd ℂ χ.completedLFunction Set.univ := fun z _ ↦
    (χ.differentiable_completedLFunction hne).analyticAt z
  have hnonneg (ρ : ℂ) :
    0 ≤ (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 :=
    mul_nonneg (by exact_mod_cast MeromorphicOn.AnalyticOnNhd.divisor_nonneg hAn ρ) (sq_nonneg _)
  have hfinite := hsum.sum_le_tsum S (fun ρ _ ↦ hnonneg ρ)
  have hpoint :
    ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) ≤
      4 *
        ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 := by
    rw [Finset.mul_sum]
    exact
      Finset.sum_le_sum
        (fun ρ hρ ↦
          completed_divisor_le_four_mul_shifted_mass_unconditionally hp hne hinv (hS ρ hρ))
  obtain ⟨a, b, ha, hb, _, _, hmass⟩ :=
    LogFreeDensity.exists_completed_genus_inverse_square_mass_le_uniform_bound hq hne hp hinv (η :=
      1 / 2) (by norm_num only) le_rfl t
  have he : (((1 + 1 / 2 : ℝ) : ℂ) + Complex.I * t) = s := by
    dsimp only [s]
    norm_num only
  rw [he, ha, hb] at hmass
  change
    (∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2) ≤
      (1 / (1 / 2)) *
        (4 / (1 / 2) + A * (Real.log (4 + |t|) + 1) + Real.log q + 4 +
          B * (Real.log 4 + 1)) at hmass
  have hlogq : 0 ≤ Real.log q :=
    Real.log_nonneg
      (by
        have hqr : (2 : ℝ) ≤ q := by exact_mod_cast hq
        linarith only [hqr])
  have hlogt : 0 ≤ Real.log (4 + |t|) := Real.log_nonneg (by linarith only [abs_nonneg t])
  have hA := le_abs_self A
  have hB := le_abs_self B
  have haTerm :=
    mul_le_mul_of_nonneg_right hA (by linarith only [hlogt] : 0 ≤ Real.log (4 + |t|) + 1)
  have hbTerm := mul_le_mul_of_nonneg_right hB (by linarith only [hlog4] : 0 ≤ Real.log 4 + 1)
  have hlog : 1 ≤ Real.log q + Real.log (4 + |t|) + 1 := by linarith only [hlogq, hlogt]
  have hAt :=
    mul_le_mul_of_nonneg_left
      (by linarith only [hlogq] : Real.log (4 + |t|) + 1 ≤ Real.log q + Real.log (4 + |t|) + 1)
      (abs_nonneg A)
  have hBt :=
    mul_le_mul_of_nonneg_left hlog
      (mul_nonneg (abs_nonneg B) (by linarith only [hlog4] : 0 ≤ Real.log 4 + 1))
  have hnum := mul_le_mul_of_nonneg_left hlog (by norm_num only : (0 : ℝ) ≤ 12)
  calc
    _ ≤
        4 *
          ∑ ρ ∈ S, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 :=
      hpoint
    _ ≤
        4 *
          ∑' ρ : ℂ, (MeromorphicOn.divisor χ.completedLFunction Set.univ ρ : ℝ) * ‖(s - ρ)⁻¹‖ ^ 2 :=
      mul_le_mul_of_nonneg_left hfinite (by norm_num only)
    _ ≤ _ := by
      dsimp only [C]
      norm_num only at hmass
      nlinarith only [hmass, haTerm, hbTerm, hAt, hBt, hnum, hlogq, hlogt]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction
