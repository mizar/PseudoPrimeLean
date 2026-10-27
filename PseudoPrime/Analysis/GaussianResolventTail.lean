/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GaussianResolventCertificate
public import PseudoPrime.Analysis.GaussianGammaNormCurvature
public import PseudoPrime.Analysis.GammaResolventTail

/-! # Gaussian resolvent domination outside the compact interval

An exact shifted polynomial with positive coefficients certifies the rational tail.
The existing Gamma decay bound also bounds the Gaussian-weighted norm.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Product of the twelve shifted resolvent denominators at t²=256+v.
Every factor is positive for nonnegative v, so clearing the product preserves inequalities. -/
private noncomputable def gaussianResolventTailDenominator (v : ℝ) : ℝ :=
  (v + 102521 / 400) * (v + 10259321 / 40000) * (v + 16433 / 64) * (v + 25721 / 100) *
    (v + 10316729 / 40000) *
    (v + 4145 / 16) *
    (v + 10434481 / 40000) *
    (v + 421921 / 1600) *
    (v + 1073 / 4) *
    (v + 2754481 / 10000) *
    (v + 11474321 / 40000) *
    (v + 305 / 1)

/-- The exact degree-twelve numerator of D(v)((1+t²)g(t)-1/40000).
All thirteen coefficients are positive. This supplies a rational certificate for the tail. -/
private noncomputable def gaussianResolventTailPolynomial (v : ℝ) : ℝ :=
  (1998617669171507888874919180336867095990154524078044107764734244413 /
        134217728000000000000000000000000000000000 :
      ℝ) +
    (432186366581654434375454602737718421546978608713816869591846304963 /
          671088640000000000000000000000000000000000 :
        ℝ) *
      v ^ 1 +
    (4248756185499098801899622151782252793922205201114169770594686437 /
          335544320000000000000000000000000000000000 :
        ℝ) *
      v ^ 2 +
    (12557723054924054770437242944157895567609850884128385813868511 /
          83886080000000000000000000000000000000000 :
        ℝ) *
      v ^ 3 +
    (3109891796052139624765726392263563185277302079883424018729 /
          2621440000000000000000000000000000000000 :
        ℝ) *
      v ^ 4 +
    (435982960488347345000979301067937864937790188270665933 /
          65536000000000000000000000000000000000 :
        ℝ) *
      v ^ 5 +
    (1112997222155697512288267785424491457229991661121 / 40960000000000000000000000000000000 : ℝ) *
      v ^ 6 +
    (16790673621554651515496450417567568836044269 / 204800000000000000000000000000000 : ℝ) * v ^ 7 +
    (4688838751140660044950002774784015257 / 25600000000000000000000000000 : ℝ) * v ^ 8 +
    (95814932381095720479289323409 / 320000000000000000000000 : ℝ) * v ^ 9 +
    (2760370183523241460437 / 8000000000000000000 : ℝ) * v ^ 10 +
    (101852613980517 / 400000000000000 : ℝ) * v ^ 11 +
    (913349 / 10000000000 : ℝ) * v ^ 12

/-- For nonnegative v and t²=256+v, clearing denominators gives the stated
shifted polynomial. Rational normalization and a ring identity certify all coefficients. -/
private theorem gaussianResolvent_tail_identity (t v : ℝ) (ht : t ^ 2 = 256 + v) (hv : 0 ≤ v) :
    gaussianResolventTailDenominator v * ((1 + t ^ 2) * gaussianResolventMajorant t - 1 / 40000) =
      gaussianResolventTailPolynomial v := by
  simp only [gaussianResolventMajorant, gaussianResolventCoefficients, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  rw [ht]
  norm_num only
  dsimp only [gaussianResolventTailDenominator, gaussianResolventTailPolynomial]
  have h0 : (121 + 400 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h1 : (19321 + 40000 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h2 : (49 + 64 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h3 : (121 + 100 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h4 : (76729 + 40000 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h5 : (49 + 16 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h6 : (194481 + 40000 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h7 : (12321 + 1600 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h8 : (49 + 4 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h9 : (194481 + 10000 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h10 : (1234321 + 40000 * (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  have h11 : (49 + (256 + v) : ℝ) ≠ 0 := ne_of_gt (by linarith only [hv])
  field_simp (discharger :=
    first
    | (norm_num only; done)
    | exact h0
    | exact h1
    | exact h2
    | exact h3
    | exact h4
    | exact h5
    | exact h6
    | exact h7
    | exact h8
    | exact h9
    | exact h10
    | exact h11)
  ring

/-- For nonnegative v, all twelve shifted factors are positive.
Their product therefore permits cancellation in the tail comparison. -/
private theorem gaussianResolvent_tail_denominator_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < gaussianResolventTailDenominator v := by
  dsimp only [gaussianResolventTailDenominator]
  repeat' apply mul_pos
  all_goals exact add_pos_of_nonneg_of_pos hv (by norm_num only)

/-- For nonnegative v, the shifted polynomial is positive. Its constant term
is positive and each remaining coefficient-times-power term is nonnegative. -/
private theorem gaussianResolvent_tail_polynomial_pos {v : ℝ} (hv : 0 ≤ v) :
    0 < gaussianResolventTailPolynomial v := by
  dsimp only [gaussianResolventTailPolynomial]
  repeat' apply add_pos_of_pos_of_nonneg
  · norm_num only
  all_goals exact mul_nonneg (by norm_num only) (pow_nonneg hv _)

/-- For t²≥256, the scaled rational majorant exceeds 1/40000.
Use the exact shifted polynomial and positive denominator to supply the tail lower bound. -/
theorem gaussianResolvent_scaled_gt_of_sq_ge_256 {t : ℝ} (ht : 256 ≤ t ^ 2) :
    (1 / 40000 : ℝ) < (1 + t ^ 2) * gaussianResolventMajorant t := by
  have hv : 0 ≤ t ^ 2 - 256 := sub_nonneg.mpr ht
  have he := gaussianResolvent_tail_identity t (t ^ 2 - 256) (by ring) hv
  have hd := gaussianResolvent_tail_denominator_pos hv
  have hp := gaussianResolvent_tail_polynomial_pos hv
  have hm : 0 < (1 + t ^ 2) * gaussianResolventMajorant t - 1 / 40000 :=
    (mul_pos_iff_of_pos_left hd).mp (he.symm ▸ hp)
  exact sub_pos.mp hm

/-- At every real height, the Gaussian kernel norm is at most the unweighted
Gamma norm. The exact vertical-line identity and exp(-t²/4)≤1 preserve its tail estimate. -/
theorem norm_gaussianGammaFunction_le_Gamma (t : ℝ) :
    ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ ≤
      ‖Complex.Gamma ((1 / 2 : ℂ) + Complex.I * (t : ℂ))‖ := by
  have h := norm_gaussianGammaFunction_vertical 0 t
  simp only [Complex.ofReal_zero, zero_add, zero_pow (by decide : 2 ≠ 0), zero_sub,
    add_comm (Complex.I * (t : ℂ)) (1 / 2)] at h
  have he : Real.exp (-(t ^ 2) / 4) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith only [sq_nonneg t])
  rw [h]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left he (norm_nonneg _)

/-- For |t|≥16, the scaled Gaussian kernel norm is below 1/40000.
Apply Gaussian damping to the existing unweighted Gamma tail bound. -/
theorem scaled_gaussianGammaFunction_lt_of_abs_ge_sixteen {t : ℝ} (ht : 16 ≤ |t|) :
    (1 + t ^ 2) * ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ < 1 / 40000 := by
  exact
    (mul_le_mul_of_nonneg_left (norm_gaussianGammaFunction_le_Gamma t)
          (add_nonneg (by norm_num only : (0 : ℝ) ≤ 1) (sq_nonneg t))).trans_lt
      (scaled_Gamma_half_add_I_lt_of_abs_ge_sixteen ht)

/-- For |t|≥16, the rational majorant strictly dominates the actual Gaussian
kernel norm. Compare their scaled bounds and cancel the positive factor 1+t². -/
theorem norm_gaussianGammaFunction_lt_gaussianResolvent_of_abs_ge_sixteen {t : ℝ} (ht : 16 ≤ |t|) :
    ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ < gaussianResolventMajorant t := by
  have hs : (256 : ℝ) ≤ t ^ 2 := by nlinarith only [ht, sq_abs t]
  have h :=
    (scaled_gaussianGammaFunction_lt_of_abs_ge_sixteen ht).trans
      (gaussianResolvent_scaled_gt_of_sq_ge_256 hs)
  exact (mul_lt_mul_iff_right₀ (by nlinarith only [sq_nonneg t] : 0 < 1 + t ^ 2)).mp h

/-- A domination certificate on |t|≤16 extends to every real height.
The proved rational and analytic tail covers the complementary interval.
This transfers the remaining compact certificate to the global zero-mass input. -/
theorem norm_gaussianGammaFunction_le_gaussianResolvent_of_compact
    (h :
      ∀ t : ℝ,
        |t| ≤ 16 → ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ ≤ gaussianResolventMajorant t)
    (t : ℝ) : ‖gaussianGammaFunction (Complex.I * (t : ℂ))‖ ≤ gaussianResolventMajorant t := by
  by_cases ht : |t| ≤ 16
  · exact h t ht
  · exact (norm_gaussianGammaFunction_lt_gaussianResolvent_of_abs_ge_sixteen (le_of_not_ge ht)).le

end PseudoPrime.Analysis
