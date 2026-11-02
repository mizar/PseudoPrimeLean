/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.PaperStatements.RationalPoleDoubleAbelInputs
public import PseudoPrime.Analysis.ScaledLogMoments
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Second variation of the selected fourth-pole principal weight

The fixed K4 density has integrable logarithmic moments at the support's lower endpoint.
A positive three-term majorant gives the rational variation budget 1369/650. These selected
kernel evaluations stay separate from the stable general moment API and from entrance
certificates, so changing an entrance does not rebuild the analytic identities.
-/

@[expose] public section

namespace PseudoPrime.LLS.PaperStatements

/-- For positive u and any real power p, normalize the exponential and square-root
factor into exp(-14/13) times u^(p-7/13). Expand positive powers as exponentials.
This exposes the moment parameter used for the actual second-density integrals. -/
theorem fourPole_second_power_factor {u : ℝ} (hu : 0 < u) (p : ℝ) :
    u ^ p * Real.exp (-fourPoleCoord u) / (u * Real.sqrt u) =
      Real.exp (-(14 / 13 : ℝ)) * u ^ (p - 7 / 13) := by
  calc
    _ =
        (Real.exp (Real.log u * p) * Real.exp (-fourPoleCoord u)) /
          (Real.exp (Real.log u) * Real.exp (Real.log u * (1 / 2))) :=
      by rw [Real.rpow_def_of_pos hu, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hu, Real.exp_log hu]
    _ = Real.exp (-(14 / 13 : ℝ)) * Real.exp (Real.log u * (p - 7 / 13)) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_sub, ← Real.exp_add]
      congr 1
      dsimp only [fourPoleCoord]
      ring
    _ = _ := by rw [Real.rpow_def_of_pos hu]

/-- For every positive moment parameter, the selected logarithmic coordinate has
integrable moments on the full support with the displayed exact value.
Factor the coordinate into (25/26)(28/25-log u) and reuse the general scaled log moment.
This provides all polynomial terms in the second-density evaluation. -/
theorem fourPole_coord_moment (n : ℕ) {s : ℝ} (hs : 0 < s) :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ u ^ (s - 1) * fourPoleCoord u ^ n)
        (Set.Ioc 0 (Real.exp (28 / 25 : ℝ))) ∧
      (∫ u : ℝ in (0 : ℝ)..Real.exp (28 / 25 : ℝ), u ^ (s - 1) * fourPoleCoord u ^ n) =
        (25 / 26 : ℝ) ^ n * Real.exp ((28 / 25 : ℝ) * s) * ((n.factorial : ℝ) / s ^ (n + 1)) := by
  have h := Analysis.scaled_log_moment n (28 / 25) hs
  have he :
    (fun u : ℝ ↦ u ^ (s - 1) * fourPoleCoord u ^ n) =
      (fun u : ℝ ↦ (25 / 26 : ℝ) ^ n * (u ^ (s - 1) * (28 / 25 - Real.log u) ^ n)) := by
    funext u
    have hv : fourPoleCoord u = (25 / 26 : ℝ) * (28 / 25 - Real.log u) := by
      dsimp only [fourPoleCoord]
      ring
    rw [hv, mul_pow]
    ring
  rw [he]
  refine ⟨h.1.const_mul _, ?_⟩
  rw [intervalIntegral.integral_const_mul, h.2]
  ring

/-- A power-weighted term of the K4 second density is integrable when p+6/13 is positive.
Its exact integral follows from the preceding power factor and coordinate moment.
The cases p=0, p=1/2 and p=1 control integrability, error variation and the main term. -/
theorem fourPole_density_moment (n : ℕ) (p : ℝ) (hp : 0 < p + (6 / 13 : ℝ)) :
    MeasureTheory.IntegrableOn
        (fun u : ℝ ↦
          u ^ p * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) * fourPoleCoord u ^ n)
        (Set.Ioc 0 (Real.exp (28 / 25 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (28 / 25 : ℝ)),
          u ^ p * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) * fourPoleCoord u ^ n) =
        (Real.exp (-(14 / 13 : ℝ)) / 6) *
          ((25 / 26 : ℝ) ^ n * Real.exp ((28 / 25 : ℝ) * (p + 6 / 13)) *
            ((n.factorial : ℝ) / (p + 6 / 13) ^ (n + 1))) := by
  have h := fourPole_coord_moment n hp
  rw [intervalIntegral.integral_of_le (Real.exp_pos _).le] at h
  have he :
    (fun u : ℝ ↦
        u ^ p * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) *
          fourPoleCoord u ^
            n) =ᵐ[MeasureTheory.volume.restrict (Set.Ioc 0 (Real.exp (28 / 25 : ℝ)))]
      (fun u : ℝ ↦
        (Real.exp (-(14 / 13 : ℝ)) / 6) * (u ^ (p + 6 / 13 - 1) * fourPoleCoord u ^ n)) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
    have hf := fourPole_second_power_factor hu.1 p
    have hexp : p + (6 / 13 : ℝ) - 1 = p - 7 / 13 := by ring
    rw [hexp]
    calc
      _ = (u ^ p * Real.exp (-fourPoleCoord u) / (u * Real.sqrt u)) / 6 * fourPoleCoord u ^ n := by
        ring
      _ = _ := by
        rw [hf]; ring
  refine ⟨(h.1.const_mul (Real.exp (-(14 / 13 : ℝ)) / 6)).congr he.symm, ?_⟩
  rw [MeasureTheory.integral_congr_ae he, MeasureTheory.integral_const_mul, h.2]

/-- The positive polynomial majorant for the absolute K4 second Abel density.
Replace the negative quadratic coefficient by its absolute value, retaining the cubic
and linear terms. It is nonnegative on the positive support and its square-root-weighted
integral gives the explicit error budget used after the second Abel identity. -/
noncomputable def fourPoleSecondMajorant (u : ℝ) : ℝ :=
  Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) *
    ((6 / 13 : ℝ) ^ 2 * fourPoleCoord u ^ 3 +
      6 * (25 / 26 : ℝ) * (6 / 13 : ℝ) * fourPoleCoord u ^ 2 +
      6 * (25 / 26 : ℝ) ^ 2 * fourPoleCoord u)

/-- The actual signed second Abel density is integrable on the full positive support.
Combine its three logarithmic moments at the positive parameter 6/13.
This justifies the clipped-atom integrals without assuming a derivative at zero. -/
theorem fourPole_second_integrable :
    MeasureTheory.IntegrableOn fourPoleSecondDensity (Set.Ioc 0 (Real.exp (28 / 25 : ℝ))) := by
  have h1 := fourPole_density_moment 1 0 (by norm_num only)
  have h2 := fourPole_density_moment 2 0 (by norm_num only)
  have h3 := fourPole_density_moment 3 0 (by norm_num only)
  simp only [Real.rpow_zero, one_mul, pow_one] at h1 h2 h3
  have he :
    fourPoleSecondDensity =
      (fun u : ℝ ↦
        (6 / 13 : ℝ) ^ 2 *
              (Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) * fourPoleCoord u ^ 3) -
            (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ)) *
              (Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) * fourPoleCoord u ^ 2) +
          (6 * (25 / 26 : ℝ) ^ 2) *
            (Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) * fourPoleCoord u)) := by
    funext u
    dsimp only [fourPoleSecondDensity]
    ring
  rw [he]
  exact ((h3.1.const_mul _).sub (h2.1.const_mul _)).add (h1.1.const_mul _)

/-- The square-root-weighted majorant is integrable and has exact integral 1369/650.
Evaluate its three moments at parameter 25/26; the two exponential factors cancel.
This rational value bounds the actual second variation without numerical quadrature. -/
theorem fourPole_second_majorant_integral :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * fourPoleSecondMajorant u)
        (Set.Ioc 0 (Real.exp (28 / 25 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (28 / 25 : ℝ)), Real.sqrt u * fourPoleSecondMajorant u) =
        (1369 / 650 : ℝ) := by
  have h1 := fourPole_density_moment 1 (1 / 2) (by norm_num only)
  have h2 := fourPole_density_moment 2 (1 / 2) (by norm_num only)
  have h3 := fourPole_density_moment 3 (1 / 2) (by norm_num only)
  simp only [← Real.sqrt_eq_rpow, pow_one] at h1 h2 h3
  have he :
    (fun u : ℝ ↦ Real.sqrt u * fourPoleSecondMajorant u) =
      (fun u : ℝ ↦
        (6 / 13 : ℝ) ^ 2 *
            (Real.sqrt u * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) *
              fourPoleCoord u ^ 3) +
          (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ)) *
            (Real.sqrt u * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) *
              fourPoleCoord u ^ 2) +
          (6 * (25 / 26 : ℝ) ^ 2) *
            (Real.sqrt u * Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) *
              fourPoleCoord u)) := by
    funext u
    dsimp only [fourPoleSecondMajorant]
    ring
  rw [he]
  have hi3 := h3.1.const_mul ((6 / 13 : ℝ) ^ 2)
  have hi2 := h2.1.const_mul (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ))
  have hi1 := h1.1.const_mul (6 * (25 / 26 : ℝ) ^ 2)
  refine ⟨(hi3.add hi2).add hi1, ?_⟩
  have hsum := MeasureTheory.integral_add (hi3.add hi2) hi1
  have hsum2 := MeasureTheory.integral_add hi3 hi2
  simp only [Pi.add_apply] at hsum hsum2
  rw [hsum, hsum2, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, h3.2, h2.2, h1.2]
  norm_num only [Nat.factorial, Nat.reduceAdd, Nat.cast_ofNat]
  have hexp : Real.exp (-(14 / 13 : ℝ)) * Real.exp (14 / 13 : ℝ) = 1 := by
    rw [← Real.exp_add]
    norm_num only [neg_add_cancel, Real.exp_zero]
  nlinarith only [hexp]

/-- On the positive support, the absolute second density is below its positive majorant.
The logarithmic coordinate is nonnegative, so the triangle inequality bounds each term.
This supplies the pointwise domination for the actual variation integral. -/
theorem fourPole_second_abs_le {u : ℝ} (hu : 0 < u) (hl : Real.log u ≤ 28 / 25) :
    |fourPoleSecondDensity u| ≤ fourPoleSecondMajorant u := by
  have hv : 0 ≤ fourPoleCoord u := by
    dsimp only [fourPoleCoord]
    linarith only [hl]
  have hbase : 0 ≤ Real.exp (-fourPoleCoord u) / (6 * u * Real.sqrt u) :=
    div_nonneg (Real.exp_nonneg _)
      (mul_nonneg (mul_nonneg (by norm_num only) hu.le) (Real.sqrt_nonneg _))
  have ha : 0 ≤ (6 / 13 : ℝ) ^ 2 * fourPoleCoord u ^ 3 := mul_nonneg (sq_nonneg _) (pow_nonneg hv _)
  have hb : 0 ≤ 6 * (25 / 26 : ℝ) * (6 / 13 : ℝ) * fourPoleCoord u ^ 2 :=
    mul_nonneg (by norm_num only) (sq_nonneg _)
  have hc : 0 ≤ 6 * (25 / 26 : ℝ) ^ 2 * fourPoleCoord u := mul_nonneg (by norm_num only) hv
  have htriangle :=
    abs_add_le
      ((6 / 13 : ℝ) ^ 2 * fourPoleCoord u ^ 3 -
        6 * (25 / 26 : ℝ) * (6 / 13 : ℝ) * fourPoleCoord u ^ 2)
      (6 * (25 / 26 : ℝ) ^ 2 * fourPoleCoord u)
  have hsub :=
    abs_sub ((6 / 13 : ℝ) ^ 2 * fourPoleCoord u ^ 3)
      (6 * (25 / 26 : ℝ) * (6 / 13 : ℝ) * fourPoleCoord u ^ 2)
  rw [abs_of_nonneg ha, abs_of_nonneg hb] at hsub
  rw [abs_of_nonneg hc] at htriangle
  dsimp only [fourPoleSecondDensity, fourPoleSecondMajorant]
  rw [abs_mul, abs_of_nonneg hbase]
  exact mul_le_mul_of_nonneg_left (by linarith only [htriangle, hsub]) hbase

/-- The square-root-weighted absolute second density is integrable and has integral
at most 1369/650 on the full support. Multiply the integrable density norm by the
continuous square root and integrate the pointwise majorant comparison.
This is the actual variation bound entering the improved principal gap. -/
theorem fourPole_second_variation :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * |fourPoleSecondDensity u|)
        (Set.Ioc 0 (Real.exp (28 / 25 : ℝ))) ∧
      (∫ u : ℝ in Set.Ioc 0 (Real.exp (28 / 25 : ℝ)), Real.sqrt u * |fourPoleSecondDensity u|) ≤
        (1369 / 650 : ℝ) := by
  have hi :=
    MeasureTheory.IntegrableOn.mul_continuousOn_of_subset fourPole_second_integrable.norm
      Real.continuous_sqrt.continuousOn measurableSet_Ioc isCompact_Icc
      (Set.Ioc_subset_Icc_self : Set.Ioc (0 : ℝ) (Real.exp (28 / 25 : ℝ)) ⊆ _)
  simp only [Real.norm_eq_abs] at hi
  have hiL :
    MeasureTheory.IntegrableOn (fun u : ℝ ↦ Real.sqrt u * |fourPoleSecondDensity u|)
      (Set.Ioc 0 (Real.exp (28 / 25 : ℝ))) := by
    simpa only [mul_comm] using hi
  refine ⟨hiL, ?_⟩
  rw [← fourPole_second_majorant_integral.2]
  apply MeasureTheory.integral_mono_ae hiL fourPole_second_majorant_integral.1
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with u hu
  have hl : Real.log u ≤ 28 / 25 := (Real.log_le_iff_le_exp hu.1).mpr hu.2
  exact mul_le_mul_of_nonneg_left (fourPole_second_abs_le hu.1 hl) (Real.sqrt_nonneg _)

end PseudoPrime.LLS.PaperStatements
