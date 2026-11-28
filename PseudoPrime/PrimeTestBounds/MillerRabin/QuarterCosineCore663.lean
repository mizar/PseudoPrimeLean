/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterThetaPoly663
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineXi656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxSlope663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineSplit656
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterCosineXi656

/-! # Symmetric cosine core with the six section 137 frequencies -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def residueRat (s : ℚ) : ℚ :=
  profileExpTaylor (-|s| / 2) + profileExpTaylor (|s| / 2)

private theorem residue_error (s : ℚ) (hm : |(-|s| / 2 : ℚ)| ≤ 11) (hp : |(|s| / 2 : ℚ)| ≤ 11) :
    |quarterAuxResidue656 (s : ℝ) - (residueRat s : ℝ)| ≤ 2 / 10 ^ 16 := by
  have h₁ := profile_exp_error (-|s| / 2) (by exact_mod_cast hm)
  have h₂ := profile_exp_error (|s| / 2) (by exact_mod_cast hp)
  have h := (abs_add_le _ _).trans (add_le_add h₁ h₂)
  rw [← add_sub_add_comm] at h
  simp only [quarterAuxResidue656, residueRat, Rat.cast_add, Rat.cast_div, Rat.cast_neg,
    Rat.cast_abs, Rat.cast_ofNat] at h ⊢
  linarith only [h]

private def residueMixRat : ℚ :=
  (∑ i,
        ∑ j,
          quarterCoeff663 i * quarterCoeff663 j *
            residueRat (quarterFreq663 i - quarterFreq663 j)) /
      2 -
    ∑ i, quarterCoeff663 i * residueRat (quarterFreq663 i)

private theorem residue_mix_cast :
    (residueMixRat : ℝ) = quarterAuxMix663 (fun s ↦ (residueRat s : ℝ)) := by
  simp only [residueMixRat, quarterAuxMix663, Rat.cast_sub, Rat.cast_sum, Rat.cast_mul,
    Rat.cast_div, Rat.cast_ofNat]

set_option maxRecDepth 8192 in
-- The exact rational comparison evaluates the Taylor sums at the 36 ordered pairs.
/-- The six-frequency combination of symmetric half-point residues for
three characters contributes at least 3.64059393. -/
theorem quarter_aux_residue_lower_663 :
    (3.64059393 : ℝ) ≤
      3 * ((11 / 10 : ℝ) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3) *
        quarterAuxMix663 (fun s ↦ quarterAuxResidue656 (s : ℝ)) := by
  have hs :
    ∀ i,
      let s := quarterFreq663 i
      |(-|s| / 2 : ℚ)| ≤ 11 ∧ |(|s| / 2 : ℚ)| ≤ 11 := by
    decide +kernel
  have hp :
    ∀ i j,
      let s := quarterFreq663 i - quarterFreq663 j
      |(-|s| / 2 : ℚ)| ≤ 11 ∧ |(|s| / 2 : ℚ)| ≤ 11 := by
    decide +kernel
  have h :=
    mix_error (fun s ↦ quarterAuxResidue656 (s : ℝ)) (fun s ↦ (residueRat s : ℝ))
      (fun i ↦ residue_error _ (hs i).1 (hs i).2) (fun i j ↦ residue_error _ (hp i j).1 (hp i j).2)
  rw [← residue_mix_cast] at h
  have hq : (666655183 : ℚ) / 10 ^ 9 ≤ residueMixRat := by decide +kernel
  have hR := (Rat.cast_le (K := ℝ)).mpr hq
  norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat] at hR
  linarith only [(abs_le.mp h).1, hR]

/-- The signed contribution of the common xi terms is at most 72 millionths,
using the uniform one-millionth bound at each frequency. -/
theorem quarter_six_xi_cap_663 (hRH : RiemannHypothesis) :
    |3 * quarterAuxMix663 (fun s ↦ quarterCosineXi656 |(s : ℝ)|)| ≤ 0.000072 := by
  have h :=
    mix_error (fun s ↦ quarterCosineXi656 |(s : ℝ)|) (fun _ ↦ 0)
      (fun i ↦ by
        simpa only [sub_zero] using
          quarter_xi_cosine_abs_656 hRH (abs_nonneg (quarterFreq663 i : ℝ)))
      (fun i j ↦ by
        simpa only [sub_zero] using
          quarter_xi_cosine_abs_656 hRH
            (abs_nonneg ((quarterFreq663 i - quarterFreq663 j : ℚ) : ℝ)))
  simp only [quarterAuxMix663, mul_zero, Finset.sum_const_zero, zero_div, sub_zero] at h
  rw [abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 3)]
  unfold quarterAuxMix663
  linarith only [h]

private theorem mix_linear (f g k : ℚ → ℝ) (a b c : ℝ) :
    quarterAuxMix663 (fun s ↦ a * f s + b * g s + c * k s) =
      a * quarterAuxMix663 f + b * quarterAuxMix663 g + c * quarterAuxMix663 k := by
  unfold quarterAuxMix663
  simp only [mul_add, Finset.sum_add_distrib, mul_left_comm _ a, mul_left_comm _ b,
    mul_left_comm _ c]
  simp only [← Finset.mul_sum]
  ring

/-- The symmetric cosine core for six frequencies is bounded by its
conductor term minus the certified net residue gain, including the xi error. -/
theorem quarter_cosine_core_cap_663 (hRH : RiemannHypothesis) (r : ℝ) :
    quarterAuxMix663 (fun s ↦ quarterCosineCore656 (4 * r) (s : ℝ)) ≤
      quarterAuxMix663 quarterConductorProfile663 * r - 3.64052193 := by
  let M : ℝ := (11 / 10) ^ 5 / ((11 / 10 : ℝ) ^ 2 - 1 / 4) ^ 3
  have he (s : ℚ) :
    quarterCosineCore656 (4 * r) (s : ℝ) =
      3 * quarterCosineXi656 |(s : ℝ)| + (-3 * M) * quarterAuxResidue656 (s : ℝ) +
        r * quarterConductorProfile663 s := by
    have hp := quarter_cosine_pole_pair_656 |(s : ℝ)|
    dsimp only at hp
    unfold quarterCosineCore656 quarterAuxResidue656 M
    dsimp only
    rw [quarter_conductor_profile_eq_663, symmetric_profile_value (inv_pos.mpr (Real.exp_pos _)),
      symmetric_profile_value (inv_pos.mpr (Real.exp_pos _))]
    simp only [Real.log_inv, Real.log_exp, abs_neg, abs_abs]
    linear_combination -3 * hp
  rw [funext he, mix_linear]
  have hx := (abs_le.mp (quarter_six_xi_cap_663 hRH)).2
  have hp := quarter_aux_residue_lower_663
  dsimp only [M]
  linarith only [hx, hp]

end PseudoPrime.PrimeTestBounds.MillerRabin
