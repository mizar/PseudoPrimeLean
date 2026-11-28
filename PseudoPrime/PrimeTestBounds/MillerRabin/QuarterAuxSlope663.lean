/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterProfile663

/-! # Six-frequency linear gain for the quarter-square bound -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The quadratic minus linear combination on the six frequencies of (137.11).
It applies to both the Gram and the residue profiles. -/
noncomputable def quarterAuxMix663 (f : ℚ → ℝ) : ℝ :=
  (∑ i,
        ∑ j,
          (quarterCoeff663 i : ℝ) * (quarterCoeff663 j : ℝ) *
            f (quarterFreq663 i - quarterFreq663 j)) /
      2 -
    ∑ i, (quarterCoeff663 i : ℝ) * f (quarterFreq663 i)

/-- The unshifted conductor profile sampled at a rational frequency. -/
noncomputable def quarterConductorProfile663 (s : ℚ) : ℝ :=
  2 * Real.exp ((-(11 / 10) * |s| : ℚ) : ℝ) * quarterAuxProfile656 (|s| : ℚ)

private def conductorApprox (s : ℚ) : ℚ :=
  2 * profileExpTaylor (-(11 / 10) * |s|) * shiftedCoeff 0 |s|

private theorem conductor_error (s : ℚ) (hx : |(-(11 / 10) * |s| : ℚ)| ≤ 11)
    (hq : |shiftedCoeff 0 (|s|)| ≤ 50) :
    |quarterConductorProfile663 s - (conductorApprox s : ℝ)| ≤ 1 / 10 ^ 14 := by
  have hqR : |(shiftedCoeff 0 |s| : ℝ)| ≤ 50 := by exact_mod_cast hq
  have hqEq : (shiftedCoeff 0 |s| : ℝ) = quarterAuxProfile656 (|s| : ℚ) := by
    simp only [shiftedCoeff, Matrix.cons_val_zero, Rat.cast_add, Rat.cast_mul, Rat.cast_div,
      Rat.cast_ofNat, Rat.cast_pow, quarterAuxProfile656]
    ring
  have he := profile_exp_error (-(11 / 10) * |s|) (by exact_mod_cast hx)
  rw [Rat.cast_mul] at he
  simp only [quarterConductorProfile663, conductorApprox, Rat.cast_mul, Rat.cast_ofNat, ← hqEq]
  rw [show ∀ a b q : ℝ, 2 * a * q - 2 * b * q = (2 * (a - b)) * q from fun a b q ↦ by ring, abs_mul,
    abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  have h₂ := mul_le_mul_of_nonneg_left he (by norm_num only : (0 : ℝ) ≤ 2)
  exact
    (mul_le_mul h₂ hqR (abs_nonneg _) (by norm_num only)).trans
      (by norm_num only : (2 * (1 / 10 ^ 16) * 50 : ℝ) ≤ 1 / 10 ^ 14)

private theorem weighted_error (i : Fin 6) {a b e : ℝ} (h : |a - b| ≤ e) :
    |(quarterCoeff663 i : ℝ) * a - (quarterCoeff663 i : ℝ) * b| ≤ e := by
  have hc : ∀ i : Fin 6, |quarterCoeff663 i| ≤ 1 := by decide +kernel
  have hcR : |(quarterCoeff663 i : ℝ)| ≤ 1 := by exact_mod_cast hc i
  rw [← mul_sub, abs_mul]
  exact (mul_le_of_le_one_left (abs_nonneg _) hcR).trans h

private theorem mix_error (f g : ℚ → ℝ) {e : ℝ}
    (hs : ∀ i, |f (quarterFreq663 i) - g (quarterFreq663 i)| ≤ e)
    (hp :
      ∀ i j,
        |f (quarterFreq663 i - quarterFreq663 j) - g (quarterFreq663 i - quarterFreq663 j)| ≤ e) :
    |quarterAuxMix663 f - quarterAuxMix663 g| ≤ 24 * e := by
  have hl := sum_six_error _ _ fun i ↦ weighted_error i (hs i)
  have hq :=
    sum_six_error _ _ fun i ↦ weighted_error i (sum_six_error _ _ fun j ↦ weighted_error j (hp i j))
  unfold quarterAuxMix663
  simp only [mul_assoc, ← Finset.mul_sum]
  rw [show ∀ a b c d : ℝ, a / 2 - b - (c / 2 - d) = (a - c) / 2 - (b - d) from fun a b c d ↦ by
      ring]
  exact
    (abs_sub _ _).trans
      (by
        rw [abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
        linarith only [hl, hq])

private def conductorMixRat : ℚ :=
  (∑ i,
        ∑ j,
          quarterCoeff663 i * quarterCoeff663 j *
            conductorApprox (quarterFreq663 i - quarterFreq663 j)) /
      2 -
    ∑ i, quarterCoeff663 i * conductorApprox (quarterFreq663 i)

private theorem conductor_mix_error :
    |quarterAuxMix663 quarterConductorProfile663 - (conductorMixRat : ℝ)| ≤ 24 / 10 ^ 14 := by
  have hs :
    ∀ i,
      let s := quarterFreq663 i
      |(-(11 / 10) * |s| : ℚ)| ≤ 11 ∧ |shiftedCoeff 0 (|s|)| ≤ 50 := by
    decide +kernel
  have hp :
    ∀ i j,
      let s := quarterFreq663 i - quarterFreq663 j
      |(-(11 / 10) * |s| : ℚ)| ≤ 11 ∧ |shiftedCoeff 0 (|s|)| ≤ 50 := by
    decide +kernel
  have h :=
    mix_error quarterConductorProfile663 (fun s ↦ (conductorApprox s : ℝ))
      (fun i ↦ conductor_error _ (hs i).1 (hs i).2)
      (fun i j ↦ conductor_error _ (hp i j).1 (hp i j).2)
  have hc : (conductorMixRat : ℝ) = quarterAuxMix663 (fun s ↦ (conductorApprox s : ℝ)) := by
    simp only [conductorMixRat, quarterAuxMix663, Rat.cast_sub, Rat.cast_div, Rat.cast_sum,
      Rat.cast_mul, Rat.cast_ofNat]
  simpa only [hc, div_eq_mul_inv, one_mul] using h

private def halfArg (i : Fin 6) : ℚ :=
  -(quarterFreq663 i - 21 / 8) / 2

/-- The coefficient of the positive half-point residue from the six shifts.
Multiplication by the radius gives the corresponding term in (137.20). -/
noncomputable def quarterAuxHalfCoeff663 : ℝ :=
  (3 * (11 / 10) ^ 5 / (8 / 5) ^ 6) * ∑ i, (quarterCoeff663 i : ℝ) * Real.exp (halfArg i : ℝ)

private def halfSumRat (v : Fin 6 → ℚ) : ℚ :=
  ∑ i, quarterCoeff663 i * profileExpTaylor (v i)

private theorem half_sum_error (v : Fin 6 → ℚ) (hv : ∀ i, |v i| ≤ 11) :
    |(∑ i, (quarterCoeff663 i : ℝ) * Real.exp (v i : ℝ)) - (halfSumRat v : ℝ)| ≤ 6 / 10 ^ 16 := by
  simpa only [halfSumRat, Rat.cast_sum, Rat.cast_mul, div_eq_mul_inv, one_mul] using
    sum_six_error _ _ (fun i ↦ weighted_error i (profile_exp_error (v i) (by exact_mod_cast hv i)))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 800000 in
-- Kernel evaluation reduces the Taylor sums at the 36 ordered frequency pairs.
/-- The conductor and positive half-point terms yield the strict linear gain
in (137.20), with rational Taylor errors accounted for at all six shifts. -/
theorem quarter_aux_delta_lower_663 :
    (0.0002205111 : ℝ) < -quarterAuxMix663 quarterConductorProfile663 - quarterAuxHalfCoeff663 := by
  have h :
    conductorMixRat + (3 * (11 / 10) ^ 5 / (8 / 5) ^ 6 : ℚ) * halfSumRat halfArg <
      -220511101 / 10 ^ 12 := by
    decide +kernel
  have hR := (Rat.cast_lt (K := ℝ)).mpr h
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_neg] at hR
  unfold quarterAuxHalfCoeff663
  have hs := half_sum_error halfArg (by decide +kernel)
  linarith only [hR, (abs_le.mp conductor_mix_error).2, (abs_le.mp hs).2]

set_option maxRecDepth 8192 in
/-- The positive half-point residue has a signed upper bound for K137. -/
theorem quarter_aux_half_upper_663 : quarterAuxHalfCoeff663 ≤ -0.006702 := by
  have h : (3 * (11 / 10) ^ 5 / (8 / 5) ^ 6 : ℚ) * halfSumRat halfArg ≤ -67021 / 10000000 := by
    decide +kernel
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg] at hr
  unfold quarterAuxHalfCoeff663
  linarith only [hr, (abs_le.mp (half_sum_error halfArg (by decide +kernel))).2]

/-- The deficit in the linear part of the final comparison is bounded by
the coefficient in (137.28) times a nonnegative radius. -/
theorem quarter_aux_deficit_663 {r : ℝ} (hr : 0 ≤ r) :
    (3 / 4 - 0.71780481 + quarterAuxMix663 quarterConductorProfile663 + quarterAuxHalfCoeff663) *
        r ≤
      0.0319746789 * r :=
  mul_le_mul_of_nonneg_right (by linarith only [quarter_aux_delta_lower_663]) hr

set_option maxRecDepth 8192 in
/-- For scales from zero to 26/25, the K137 conductor coefficient dominates
the scaled principal linear coefficient with the upper bound for its main term. -/
theorem k137_scaled_slope_le {scale : ℝ} (hs₀ : 0 ≤ scale) (hs₁ : scale ≤ 26 / 25) :
    (0.71780482 - quarterAuxHalfCoeff663) * scale ≤
      3 / 4 + quarterAuxMix663 quarterConductorProfile663 := by
  have hg : (6482 / 1000000 : ℚ) ≤ conductorMixRat := by decide +kernel
  have hh : (-6703 / 1000000 : ℚ) ≤ (3 * (11 / 10) ^ 5 / (8 / 5) ^ 6) * halfSumRat halfArg := by
    decide +kernel
  have hgR := (Rat.cast_le (K := ℝ)).mpr hg
  have hhR := (Rat.cast_le (K := ℝ)).mpr hh
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg] at hgR hhR
  have hs := (abs_le.mp (half_sum_error halfArg (by decide +kernel))).1
  have hlow : (-6704 / 1000000 : ℝ) ≤ quarterAuxHalfCoeff663 := by
    unfold quarterAuxHalfCoeff663
    linarith only [hhR, hs]
  have hm := mul_le_mul_of_nonneg_right (sub_le_sub_left hlow 0.71780482) hs₀
  have ht :=
    mul_le_mul_of_nonneg_left hs₁ (by norm_num only : (0 : ℝ) ≤ 0.71780482 - (-6704 / 1000000))
  linarith only [hm, ht, hgR, (abs_le.mp conductor_mix_error).1]

/-- The signed coefficient of the negative half-point residue in (137.31).
The residue contributes this coefficient divided by the radius. -/
noncomputable def quarterAuxNegPole663 : ℝ :=
  -(3 * (11 / 10) ^ 5 / (3 / 5) ^ 6) *
    ∑ i, (quarterCoeff663 i : ℝ) * Real.exp ((-halfArg i : ℚ) : ℝ)

set_option maxRecDepth 8192 in
-- Kernel evaluation reduces the six shifted Taylor polynomials.
/-- Rational Taylor bounds enclose the negative half-point coefficient
for the residual comparison on [656,663]. -/
theorem quarter_aux_neg_pole_box_663 : quarterAuxNegPole663 ∈ Set.Icc 18.29172549 18.29172550 := by
  let v : Fin 6 → ℚ := fun i ↦ -halfArg i
  have hs := half_sum_error v (by decide +kernel)
  have h :
    -(3 * (11 / 10) ^ 5 / (3 / 5) ^ 6 : ℚ) * halfSumRat v ∈
      Set.Icc (182917254992 / 10 ^ 10) (182917254993 / 10 ^ 10) := by
    decide +kernel
  have hlo := (Rat.cast_le (K := ℝ)).mpr h.1
  have hhi := (Rat.cast_le (K := ℝ)).mpr h.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_mul, Rat.cast_pow, Rat.cast_neg] at hlo hhi
  unfold quarterAuxNegPole663
  exact ⟨by linarith only [(abs_le.mp hs).2, hlo], by linarith only [(abs_le.mp hs).1, hhi]⟩

end PseudoPrime.PrimeTestBounds.MillerRabin
