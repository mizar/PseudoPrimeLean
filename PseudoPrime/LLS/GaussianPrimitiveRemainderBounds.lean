/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GaussianArchimedeanBounds
public import PseudoPrime.LLS.GaussianLeftMomentBounds
public import PseudoPrime.LLS.GaussianPoleBounds
public import PseudoPrime.LLS.GaussianCharacterZeroBounds
public import PseudoPrime.LLS.GaussianSignedLeftAverage
public import PseudoPrime.LLS.GaussianSignedArchimedeanAverage
public import PseudoPrime.NumberTheory.DirichletCharacterSmallLevels

/-! # Variable-scale primitive Gaussian arithmetic bounds

The actual contour formula combines the Gaussian archimedean, pole, and left-moment
estimates. The certified Gaussian zero mass gives the nonprincipal arithmetic upper bound.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- Under GRH for primitive nonprincipal conductor 3≤m≤q, nonprincipal inverse,
ambient q≥20000 and scale x≥1, the actual Gaussian completed remainder is bounded
by 64/9 plus its explicit pole and left-moment errors. Combine the actual contour
formula with the multiplier-dependent integral and pole estimates. This supplies a
numerical remainder with conductor and scale dependence, without an eventual gate. -/
theorem norm_gaussian_primitive_remainder_le_variable_scale {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) :
    ‖(∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ)‖ ≤
      64 / 9 + (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  let P :=
    MellinKernel.weightedResidue gaussianGammaMellinKernel
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)
  let J :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gaussianGammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hx1 : 1 ≤ x := hx
  have hr : ‖S - (P - Z + J)‖ ≤ 64 / 9 :=
    norm_gaussian_completed_remainder_le_sixty_four_ninths (by linarith only [hm]) hGRH hp hne hinv
      (a := -9 / 16) (b := 9 / 16) (by norm_num only)
      (by
        change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
      (by
        change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
      (by norm_num only) (by norm_num only) hx1 (by norm_num only) (by norm_num only)
  have hP0 := gaussian_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx1)
  have hP : ‖P‖ ≤ (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) := hP0
  have hJ : ‖J‖ ≤ (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) :=
    norm_gaussian_left_integral_le_moments hp hne hinv (zero_lt_one.trans_le hx)
  have he : S + Z = (S - (P - Z + J)) + P + J := by ring
  change ‖S + Z‖ ≤ _
  rw [he]
  have hn1 := norm_add_le (S - (P - Z + J)) P
  have hn2 := norm_add_le ((S - (P - Z + J)) + P) J
  linarith only [hr, hP, hJ, hn1, hn2]

/-- Under GRH and the same conductor hypotheses, the real part of the completed
Gaussian remainder keeps the signed left-contour estimate. The completed
contour formula leaves only the right-contour norm allowance, the pole bound,
and the Gaussian average of the signed left integral. -/
theorem re_gaussian_primitive_remainder_le_variable_scale {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 1 ≤ x) :
    ((∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ)).re ≤
      (512 / 27 : ℝ) / x + (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  let P :=
    MellinKernel.weightedResidue gaussianGammaMellinKernel
      (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2)
  let J :=
    ((1 / (2 * Real.pi) : ℝ) : ℂ) *
      (∫ t : ℝ,
        -logDeriv χ.completedLFunction (((-9 / 16 : ℝ) : ℂ) + Complex.I * t + 1 / 2) *
          (gaussianGammaMellinKernel.function (((-9 / 16 : ℝ) : ℂ) + Complex.I * t) *
            (x : ℂ) ^ (((-9 / 16 : ℝ) : ℂ) + Complex.I * t)))
  have hq2 : 2 ≤ m := (by decide : 2 ≤ 3).trans hm
  have herr : (S - (P - Z + J)).re ≤ (512 / 27 : ℝ) / x := by
    change
      ((∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n) -
            (MellinKernel.weightedResidue gaussianGammaMellinKernel
                  (fun z : ℂ ↦ χ.completedLFunction (z + 1 / 2)) x (-1 / 2) -
                (∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ) +
              J)).re ≤
        _
    exact
      re_gaussian_completed_remainder_le_inv hGRH hp hne hinv (a := -9 / 16) (b := 9 / 16)
        (by norm_num only)
        (by
          change (-1 / 2 - 1 / 8 : ℝ) < -9 / 16; norm_num only)
        (by
          change (9 / 16 : ℝ) ≤ 1 / 2 + 1 / 8; norm_num only)
        (by norm_num only) (by norm_num only) hx (by norm_num only) (by norm_num only)
  have hP := gaussian_poleResidue_le_ambient hq hm hmq hp hne hGRH (zero_lt_one.trans_le hx)
  have hJ : J.re ≤ (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
    dsimp only [J]
    rw [gaussian_signed_left_integral_eq_logGaussianAverage hp hne hinv (zero_lt_one.trans_le hx)]
    exact re_gaussian_signed_left_integral_le hp hne hinv (zero_lt_one.trans_le hx)
  have hidentity : S + Z = (S - (P - Z + J)) + P + J := by ring
  have hpr : P.re ≤ (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) :=
    (Complex.re_le_norm _).trans hP
  rw [hidentity]
  change (S - (P - Z + J)).re + P.re + J.re ≤ _
  linarith only [herr, hpr, hJ]

/-- Under the same primitive, ambient, scale, and GRH hypotheses, the actual
Gaussian arithmetic sum is bounded by (161/400)log m+12871 / 1000 plus the explicit
variable-scale remainder. Add the certified oscillating zero-sum norm to the
completed remainder. This supplies the nonprincipal input for the MR comparison. -/
theorem gaussian_primitive_sum_re_le_variable_scale {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n).re ≤
      (161 / 400 : ℝ) * Real.log m + 12871 / 1000 + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hz :=
    norm_gaussian_oscillatingZeroSum_lt_principal (by linarith only [hm]) hGRH hp hne hinv hxpos
  have hr := norm_gaussian_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
  nlinarith only [hz.le, hr, hn, hre, hlogm]

/-- Bound the primitive Gaussian arithmetic sum using the signed real-part
remainder. The oscillating zero sum is still charged by its certified norm;
the left-contour contribution now has no positive conductor-log term. -/
theorem gaussian_primitive_sum_re_le_variable_scale_signed {q m : ℕ} [NeZero m] (hq : 20000 ≤ q)
    (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) {x : ℝ} (hx : 1 ≤ x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n).re ≤
      (161 / 400 : ℝ) * Real.log m + 12871 / 1000 + (512 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hz :=
    norm_gaussian_oscillatingZeroSum_lt_principal (by linarith only [hm]) hGRH hp hne hinv hxpos
  have hr := re_gaussian_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx
  have hnegZ : -Z.re ≤ ‖Z‖ := by
    have h := Complex.re_le_norm (-Z)
    simpa only [Complex.neg_re, norm_neg] using h
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
  have hZ : -Z.re ≤ (161 / 400 : ℝ) * Real.log m + 12871 / 1000 := by
    linarith only [hnegZ, hz.le, hlogm]
  have hidentity : S.re = (S + Z).re - Z.re := by
    rw [Complex.add_re]
    ring
  rw [hidentity]
  change (S + Z).re - Z.re ≤ _
  linarith only [hr, hZ]

/-- When the primitive character is one on all primes through 50000, transfer
the Gaussian prefix gain into the variable-scale sum bound. The completed
remainder keeps its existing conductor-sensitive estimate. -/
theorem gaussian_primitive_sum_re_le_variable_scale_prefix_gain {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ p = 1) {x : ℝ}
    (hx : 1 ≤ x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n).re ≤
      (161 / 400 : ℝ) * Real.log m + 159169 / 50000 + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hz :=
    norm_gaussian_oscillatingZeroSum_lt_prefix_gain (by linarith only [hm]) hGRH hp hne hinv hsmall
      hxpos
  have hr := norm_gaussian_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
  nlinarith only [hz, hr, hn, hre, hlogm]

/-- Retain the certified 50000-prime prefix gain while using the signed
real-part remainder, so the left-contour contribution is independent of the
conductor logarithm. -/
theorem gaussian_primitive_sum_re_le_variable_scale_prefix_gain_signed {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ p = 1) {x : ℝ}
    (hx : 1 ≤ x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n).re ≤
      (161 / 400 : ℝ) * Real.log m + 159169 / 50000 + (512 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hz :=
    norm_gaussian_oscillatingZeroSum_lt_prefix_gain (by linarith only [hm]) hGRH hp hne hinv hsmall
      hxpos
  have hr := re_gaussian_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx
  have hnegZ : -Z.re ≤ ‖Z‖ := by
    have h := Complex.re_le_norm (-Z)
    simpa only [Complex.neg_re, norm_neg] using h
  have hZ : -Z.re ≤ (20115621 / 50000000 : ℝ) * Real.log m + 159169 / 50000 := by
    have hlogm : 0 ≤ Real.log (m : ℝ) :=
      Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
    linarith only [hnegZ, hz.le, hlogm]
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
  have hidentity : S.re = (S + Z).re - Z.re := by
    rw [Complex.add_re]
    ring
  rw [hidentity]
  change (S + Z).re - Z.re ≤ _
  linarith only [hr, hZ, hlogm]

/-- When the primitive character is one on all primes through 1000, transfer
the Gaussian prefix gain into the variable-scale sum bound. -/
theorem gaussian_primitive_sum_re_le_variable_scale_prefix1000_gain {q m : ℕ} [NeZero m]
    (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) {χ : DirichletCharacter ℂ m}
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 1000 → χ p = 1) {x : ℝ}
    (hx : 1 ≤ x) :
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n).re ≤
      (161 / 400 : ℝ) * Real.log m + 5969 / 1000 + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) := by
  let S := ∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n
  let Z := ∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hz :=
    norm_gaussian_oscillatingZeroSum_lt_prefix1000_gain (by linarith only [hm]) hGRH hp hne hinv
      hsmall hxpos
  have hr := norm_gaussian_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx
  have hn : ‖S‖ ≤ ‖S + Z‖ + ‖Z‖ := by
    have h := norm_sub_le (S + Z) Z
    rw [add_sub_cancel_right] at h
    exact h
  have hre := Complex.re_le_norm S
  change S.re ≤ _
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
  nlinarith only [hz, hr, hn, hre, hlogm]

/-- Under the primitive ambient GRH hypotheses and x≥4, the actual Gaussian
completed remainder is at most 128(1+log(q)log(x)/sqrt(x)). Use log(q)≥9,
bound the pole by 2log(q)/sqrt(x), and the actual left moment by
120log(q)/sqrt(x). This supplies a numerical U=128 and its full application range. -/
theorem norm_gaussian_primitive_remainder_le_contract {q m : ℕ} [NeZero m]
    {χ : DirichletCharacter ℂ m} (hq : 20000 ≤ q) (hm : 3 ≤ m) (hmq : m ≤ q) (hp : χ.IsPrimitive)
    (hne : χ ≠ 1) (hinv : χ⁻¹ ≠ 1) (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    {x : ℝ} (hx : 4 ≤ x) :
    ‖(∑' n : ℕ, gaussianGammaMellinKernel.summand χ x n) +
          (∑' ρ : ℂ, gaussianGammaMellinKernel.oscillatingZeroTerm χ x ρ)‖ ≤
      128 * (1 + Real.log q * Real.log x / Real.sqrt x) := by
  have hx1 : 1 ≤ x := (by norm_num only : (1 : ℝ) ≤ 4).trans hx
  have hqpow : (2 : ℝ) ^ 14 ≤ q := by exact_mod_cast ((by decide : 2 ^ 14 ≤ 20000).trans hq)
  have hqlog := Real.log_le_log (pow_pos (by norm_num only : (0 : ℝ) < 2) 14) hqpow
  rw [Real.log_pow] at hqlog
  norm_num only [Nat.cast_ofNat] at hqlog
  have hL : 9 ≤ Real.log (q : ℝ) := by linarith only [hqlog, Real.log_two_gt_d9]
  have hlogx : 1 ≤ Real.log x := by
    have h := Real.log_le_log (by norm_num only : (0 : ℝ) < 4) hx
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num only, Real.log_pow] at h
    norm_num only [Nat.cast_ofNat] at h
    linarith only [h, Real.log_two_gt_d9]
  have hmpos : (0 : ℝ) < m := by exact_mod_cast ((by decide : 0 < 3).trans_le hm)
  have hlogm := Real.log_le_log hmpos (Nat.cast_le.mpr hmq)
  have hlogm0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast ((by decide : 1 ≤ 3).trans hm))
  have hP : (2129 / 2000 : ℝ) * ((7 / 6) * Real.log q + 4) ≤ 2 * Real.log q := by linarith only [hL]
  have hJ : (11 / 10 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) ≤ 120 * Real.log q := by
    linarith only [hL, hlogm]
  have hC : 0 ≤ (11 / 10 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) := by linarith only [hlogm0]
  have hpw := Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num only : (-9 / 16 : ℝ) ≤ -1 / 2)
  have he : x ^ (-1 / 2 : ℝ) = 1 / Real.sqrt x := by
    rw [neg_div, Real.rpow_neg (zero_le_one.trans hx1), ← Real.sqrt_eq_rpow, one_div]
  rw [he] at hpw
  have hleft1 := mul_le_mul_of_nonneg_left hpw hC
  have hleft2 :=
    mul_le_mul_of_nonneg_right hJ (div_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (Real.sqrt_nonneg x))
  have hleft :
    (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log m + 283) + 5 / 3) ≤
      120 * Real.log q / Real.sqrt x := by
    simp only [div_eq_mul_inv] at hleft1 hleft2 ⊢
    nlinarith only [hleft1, hleft2]
  have hpole := div_le_div_of_nonneg_right hP (Real.sqrt_nonneg x)
  have hlast := mul_le_mul_of_nonneg_left hlogx (by linarith only [hL] : 0 ≤ 128 * Real.log q)
  rw [mul_one] at hlast
  have hlast' := div_le_div_of_nonneg_right hlast (Real.sqrt_nonneg x)
  have hgap := div_nonneg (by linarith only [hL] : 0 ≤ 6 * Real.log q) (Real.sqrt_nonneg x)
  have hr := norm_gaussian_primitive_remainder_le_variable_scale hq hm hmq hp hne hinv hGRH hx1
  simp only [div_eq_mul_inv] at hpole hleft hlast' hgap hr ⊢
  nlinarith only [hr, hpole, hleft, hlast', hgap]

/-- For a nonprincipal character at level q≥20000 and scale x≥1 under GRH, bound its
 primitive Gaussian sum with the actual conductor, ambient pole logarithm and explicit left error.
 Transfer to the primitive source and its inverse. This supplies the variable-scale upper input
 for coefficient-preserving non-one witness threshold optimization. -/
theorem gaussian_primitiveCharacter_sum_re_le_variable_scale {q : ℕ} [NeZero q] (hq : 20000 ≤ q)
    (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩;
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (161 / 400 : ℝ) * Real.log χ.conductor + 12871 / 1000 + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gaussian_primitive_sum_re_le_variable_scale hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hx

/-- Transfer the signed variable-scale bound to the primitive source of any
nonprincipal character. The ambient level remains in the pole term, while the
left-contour error depends only on the Gaussian scale. -/
theorem gaussian_primitiveCharacter_sum_re_le_variable_scale_signed {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis) {x : ℝ} (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (161 / 400 : ℝ) * Real.log χ.conductor + 12871 / 1000 + (512 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gaussian_primitive_sum_re_le_variable_scale_signed hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hx

/-- For a nonprincipal level-q character whose primitive source is one on
primes through 50000, use the transferred Gaussian prefix gain at its conductor. -/
theorem gaussian_primitiveCharacter_sum_re_le_variable_scale_prefix_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ.primitiveCharacter p = 1) {x : ℝ}
    (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (161 / 400 : ℝ) * Real.log χ.conductor + 159169 / 50000 + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gaussian_primitive_sum_re_le_variable_scale_prefix_gain hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hsmall hx

/-- Transfer the signed 50000-prefix bound to the primitive source of a
nonprincipal character at level q. -/
theorem gaussian_primitiveCharacter_sum_re_le_variable_scale_prefix_gain_signed {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 50000 → χ.primitiveCharacter p = 1) {x : ℝ}
    (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (161 / 400 : ℝ) * Real.log χ.conductor + 159169 / 50000 + (512 / 27 : ℝ) / x +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (473 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gaussian_primitive_sum_re_le_variable_scale_prefix_gain_signed hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hsmall hx

/-- For a nonprincipal level-q character whose primitive source is one on
primes through 1000, use the transferred Gaussian prefix gain at its conductor. -/
theorem gaussian_primitiveCharacter_sum_re_le_variable_scale_prefix1000_gain {q : ℕ} [NeZero q]
    (hq : 20000 ≤ q) (χ : DirichletCharacter ℂ q) (hne : χ ≠ 1)
    (hGRH : AnalyticNumberTheory.GRH.GeneralizedRiemannHypothesis)
    (hsmall : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ 1000 → χ.primitiveCharacter p = 1) {x : ℝ} (hx : 1 ≤ x) :
    let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
    (∑' n : ℕ, gaussianGammaMellinKernel.summand χ.primitiveCharacter x n).re ≤
      (161 / 400 : ℝ) * Real.log χ.conductor + 5969 / 1000 + 64 / 9 +
        (2129 / 2000 : ℝ) * (((7 / 6 : ℝ) * Real.log q + 4) / Real.sqrt x) +
        (11 / 10 : ℝ) * x ^ (-9 / 16 : ℝ) * ((16 / 5) * (Real.log χ.conductor + 283) + 5 / 3) := by
  let : NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩
  have hm := NumberTheory.three_le_conductor_of_ne_one χ hne
  have hmq := Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) χ.conductor_dvd_level
  have hnp := AnalyticNumberTheory.Arithmetic.primitiveCharacter_ne_one χ hne
  exact
    gaussian_primitive_sum_re_le_variable_scale_prefix1000_gain hq hm hmq hGRH
      (DirichletCharacter.primitiveCharacter_isPrimitive χ) hnp (inv_ne_one.mpr hnp) hsmall hx

end PseudoPrime.LLS.PaperStatements
