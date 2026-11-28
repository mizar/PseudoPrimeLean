/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main788
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main788
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main426
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Main354
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK137Later
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ReflectionEarly
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ReflectCredit
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterGammaEndpoints656
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197ConductorTail
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipalTail663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterReflectBox663
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterAuxReflectTail656
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Profile
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK197Conductor

/-! # Principal and reflected bounds for K197 through radius 1000 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- For radii from 332.15 to 1000, the combined K197 reflection
is at least -0.0011 by the common endpoint moment estimate. -/
theorem gaussian_joint_to1000 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc 332.15 1000)
    (α : ℕ → ℝ) (hα : ∀ n, 0 ≤ α n ∧ α n ≤ 4)
    (hprefix : ∀ n : ℕ, (n : ℝ) ≤ r ^ 2 → ArithmeticFunction.vonMangoldt n ≠ 0 → α n = 0) :
    (-0.0011 : ℝ) ≤
      ∑ i, (gaussianCoeff197 i : ℝ) * quarterAuxReflection656 α r (quarterShift663 i : ℝ) := by
  have hhi :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000) (j := 10) (n := 27) (lo := 5) (hi := 6.908)
        (by decide +kernel)).2
  norm_num only [Rat.cast_ofScientific] at hhi
  have hrU : r ≤ (1000 : ℝ) := by linarith only [hr.2]
  have hl := (Real.log_le_log ((by norm_num only : (0 : ℝ) < 332.15).trans_le hr.1) hrU).trans hhi
  have h :=
    joint_lower_box hRH (u := 16.132) (L := 13.816) (E := 0.0011)
      ⟨hr.1, hr.2.trans (by norm_num only)⟩
      (by
        norm_num only [Rat.cast_ofScientific]; linarith only [hl])
      (by norm_num only [Rat.cast_ofScientific]) (by decide +kernel) α hα hprefix
  norm_num only [Rat.cast_ofScientific] at h ⊢
  exact h

/-- The main reflected kernel costs at most 0.0012 on radii 328 through 1000. -/
theorem k197_main_reflect_to1000 {r : ℝ} (hr : r ∈ Set.Icc 328 1000) :
    quarterAuxReflectCap656 r (-(21 / 8)) 103684 ≤ 0.0012 := by
  have hr₁ : (1 : ℝ) ≤ r := (by norm_num only : (1 : ℝ) ≤ 328).trans hr.1
  have hh : -(21 / 8 : ℝ) ≤ 2 * Real.log r := by linarith only [Real.log_nonneg hr₁]
  have he := shift_exp_upper (-(21 / 8)) 0.0558 (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_ofScientific] at he
  have he' : Real.exp ((11 / 10 : ℝ) * -(21 / 8)) ≤ 0.0558 := by
    norm_num only
    exact he
  have hr₀ := zero_lt_one.trans_le hr₁
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000) (j := 10) (n := 27) (lo := 5) (hi := 6.908)
        (by decide +kernel)).2
  simp only [Rat.cast_ofScientific] at hlog
  have hcap : 2 * Real.log r ≤ 13.816 := cap_log_bound hr₀ hr.2 (by linarith only [hlog])
  refine (cap_rectangle_354 hr₀ hh he' hcap (cap_decay_328 hr.1)).trans ?_
  norm_num only [momentBox, Analysis.logPowerTailPoly, Finset.sum_range_succ, Finset.sum_range_zero,
    Nat.choose, Nat.reduceAdd, Nat.reduceSub, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one]

private theorem k197_reflect_to1000 {r : ℝ} (hr : r ∈ Set.Icc 328 1000) :
    14.21 ≤ 21 / 8 + Real.log (r ^ 2) ∧
      0.0000000138 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
  have h₀ := (by norm_num only : (0 : ℝ) < 328).trans_le hr.1
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 328) (j := 9) (n := 27) (lo := 5.793) (hi := 6)
        (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000) (j := 10) (n := 27) (lo := 5) (hi := 6.908)
        (by decide +kernel)).2
  have he :=
    (Analysis.rationalLogIntervalCheck_sound (N := 10000000000 / 138) (j := 26) (n := 32) (lo :=
        18.098) (hi := 19) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div, Rat.cast_ofScientific] at hl hu he
  have hz : 14.21 ≤ 21 / 8 + Real.log (r ^ 2) := by
    rw [Real.log_pow]
    linarith only [hl, Real.log_le_log (by norm_num only : (0 : ℝ) < 328) hr.1]
  have hru : r ≤ (1000 : ℝ) := by linarith only [hr.2]
  have hd : 0.0000000138 ≤ Real.exp (-(11 / 10) * (21 / 8 + Real.log (r ^ 2))) := by
    apply (Real.log_le_iff_le_exp (by norm_num only)).mp
    have hi : Real.log (0.0000000138 : ℝ)⁻¹ ≥ 18.098 := by
      norm_num only at he ⊢; exact he
    rw [Real.log_inv] at hi
    rw [Real.log_pow]
    linarith only [hi, hu, Real.log_le_log h₀ hru]
  exact ⟨hz, hd⟩

/-- The prefix through 2701 gives a uniform lower bound for three copies
of the principal reflected Euler series through radius 1000. -/
theorem gaussian_k197_reflect_credit_to1000 {r : ℝ} (hr : r ∈ Set.Icc 328 1000) :
    0.00082 ≤ 3 * quarterMainEuler656 (1 : DirichletCharacter ℂ 1) (r ^ 2) := by
  obtain ⟨hz, hd⟩ := k197_reflect_to1000 hr
  exact reflect_credit_of_exp hr.1 hz hd (by norm_num only)

private theorem first_rectangle_to1000 {z : ℝ} (hl : 14.232 ≤ z) (hu : z ≤ 16.441) :
    0.0075 ≤ quarterGammaFirst656 z := by
  have ht :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 196) (j := 13) (n := 48) (lo := 8)
        (hi := 8.538) (by decide +kernel)).2
  have hf :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000000 / 267) (j := 11) (n := 48) (lo := 8.227)
        (hi := 9) (by decide +kernel)).1
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at ht hf
  have htail : Real.exp (-(3 / 5 : ℝ) * 14.232) ≤ 0.000196 := by
    rw [neg_mul]
    apply exp_neg_le_of_log_inv (by norm_num only)
    norm_num only at ht ⊢
    linarith only [ht]
  have hfront : 0.000267 ≤ Real.exp (-(1 / 2 : ℝ) * 16.441) := by
    rw [neg_mul]
    apply le_exp_neg_of_log_inv (by norm_num only)
    norm_num only at hf ⊢
    linarith only [hf]
  have hm :=
    first_moment_lower_of_exp htail (m := 2194)
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
      (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, Nat.cast_one])
  exact
    first_rectangle_lower (c := 0.0075) (by norm_num only) hl hu hfront hm (by norm_num only)
      (by norm_num only)

/-- The first Gamma pole gives a uniform credit for radii between 663/2
and 1000, covering the middle K197 radii. -/
theorem quarter_gamma_k197_to1000 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 1000) :
    (centralGammaPair656 (1 : DirichletCharacter ℂ 1) (r ^ 2)).re ≤
      -2.16 * quarterWeight656 (r ^ 2) 1 - 0.0075 := by
  have hl :=
    (Analysis.rationalLogIntervalCheck_sound (N := 663 / 2) (j := 9) (n := 32) (lo := 5.8035) (hi :=
        6) (by decide +kernel)).1
  have hu :=
    (Analysis.rationalLogIntervalCheck_sound (N := 1000) (j := 10) (n := 32) (lo := 5) (hi := 6.908)
        (by decide +kernel)).2
  simp only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl hu
  have hr₀ : 0 < r := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  have hlo := Real.log_le_log (by norm_num only : (0 : ℝ) < 663 / 2) hr.1
  have hup := Real.log_le_log hr₀ hr.2
  have hfirst : 0.0075 ≤ quarterGammaFirst656 (Real.log (r ^ 2) + 21 / 8) := by
    rw [Real.log_pow]
    exact first_rectangle_to1000 (by linarith only [hl, hlo]) (by linarith only [hu, hup])
  exact
    (quarter_principal_gamma_upper_656 ((by norm_num only : (322 : ℝ) ≤ 663 / 2).trans hr.1)).trans
      (sub_le_sub_left hfirst _)

private theorem k197_log_credit_to1000 {r : ℝ} (hr : r ∈ Set.Icc (663 / 2) 1000) :
    0.00068 ≤ 4 * quarterWeight656 (r ^ 2) (r ^ 2) * Real.log (2 * Real.pi) := by
  have hp := (by norm_num only : (0 : ℝ) < 663 / 2).trans_le hr.1
  rw [quarter_cutoff_weight_656 (sq_pos_of_pos hp), Real.sqrt_sq hp.le]
  have hlog : (1.837 : ℝ) ≤ Real.log (2 * Real.pi) := by linarith only [Analysis.log_two_mul_pi_gt]
  have hW : (0.09319731 : ℝ) ≤ (quarterKernel656.transform 1).re := by
    linarith only [quarter_unit_weight_656.1]
  have hw :=
    (div_le_div_of_nonneg_left (by norm_num only : (0 : ℝ) ≤ 0.09319731) hp hr.2).trans
      (div_le_div_of_nonneg_right hW hp.le)
  have h :=
    mul_le_mul hw hlog (by norm_num only : (0 : ℝ) ≤ 1.837)
      ((by norm_num only : (0 : ℝ) ≤ 0.09319731 / 1000).trans hw)
  linarith only [h]

/-- On the middle K197 radii through 1000, any certified signed boundary
cost gives a principal-sum lower bound including the Gamma term. -/
theorem gaussian_k197_principal_to1000 (hRH : RiemannHypothesis) {r B : ℝ}
    (hr : r ∈ Set.Icc (663 / 2) 1000)
    (hb : -4 * (Chebyshev.psi (r ^ 2) - r ^ 2) * quarterWeight656 (r ^ 2) (r ^ 2) ≤ B) :
    let x := r ^ 2
    let W := fun n ↦ (quarterKernel656.summand (1 : DirichletCharacter ℂ 1) x n).re
    (0.71780481 : ℝ) * r - 0.004 - B <
      4 * (∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, W n) - (∑' n, W n) -
        3 * (centralGammaPair656 (1 : DirichletCharacter ℂ 1) x).re := by
  intro x W
  have h :=
    gaussian_principal_gamma_lower hRH ((by norm_num only : (331 : ℝ) ≤ 663 / 2).trans hr.1)
      (quarter_gamma_k197_to1000 hr) hb (k197_log_credit_to1000 hr)
  dsimp only [x, W] at h ⊢
  linarith only [h]

/-- At radii from 787.5, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7875 {r s : ℝ} (hr : (7875 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.693119 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.016855 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7875 / 10) (j := 10) (n := 27) (lo := 6.66876)
      (hi := 6.66888) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7875 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000334581) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.33776) (C := 1.037191) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 791.6, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7916 {r s : ℝ} (hr : (7916 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.686743 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.013830 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7916 / 10) (j := 10) (n := 27) (lo := 6.67396)
      (hi := 6.67407) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7916 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000332503) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.34814) (C := 1.034105) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 795.7, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7957 {r s : ℝ} (hr : (7957 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.680421 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.010829 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7957 / 10) (j := 10) (n := 27) (lo := 6.67912)
      (hi := 6.67924) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7957 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000330448) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.35848) (C := 1.031044) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 799.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from7998 {r s : ℝ} (hr : (7998 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.674144 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.007849 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 7998 / 10) (j := 10) (n := 27) (lo := 6.68426)
      (hi := 6.68438) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 7998 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000328416) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.36876) (C := 1.028004) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 804.2, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8042 {r s : ℝ} (hr : (8042 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.667459 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.004670 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8042 / 10) (j := 10) (n := 27) (lo := 6.68975)
      (hi := 6.68986) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8042 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000326261) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.37972) (C := 1.024762) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 806.2, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8062 {r s : ℝ} (hr : (8062 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.664446 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.003240 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8062 / 10) (j := 10) (n := 27) (lo := 6.69223)
      (hi := 6.69235) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8062 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000325290) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.38470) (C := 1.023303) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 808.3, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8083 {r s : ℝ} (hr : (8083 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.661287 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.001738 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8083 / 10) (j := 10) (n := 27) (lo := 6.69483)
      (hi := 6.69495) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8083 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000324276) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.38990) (C := 1.021771) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 810.3, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8103 {r s : ℝ} (hr : (8103 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.658293 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 1.000313 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8103 / 10) (j := 10) (n := 27) (lo := 6.69730)
      (hi := 6.69742) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8103 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000323316) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.39484) (C := 1.020318) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 812.3, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8123 {r s : ℝ} (hr : (8123 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.655306 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.998891 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8123 / 10) (j := 10) (n := 27) (lo := 6.69977)
      (hi := 6.69988) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8123 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000322361) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.39976) (C := 1.018867) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 814.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8144 {r s : ℝ} (hr : (8144 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.652193 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.997412 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8144 / 10) (j := 10) (n := 27) (lo := 6.70235)
      (hi := 6.70247) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8144 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000321364) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.40494) (C := 1.017359) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 816.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8164 {r s : ℝ} (hr : (8164 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.649229 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.996001 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8164 / 10) (j := 10) (n := 27) (lo := 6.70480)
      (hi := 6.70492) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8164 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000320419) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.40984) (C := 1.015919) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 818.5, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8185 {r s : ℝ} (hr : (8185 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.646135 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.994528 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8185 / 10) (j := 10) (n := 27) (lo := 6.70737)
      (hi := 6.70749) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8185 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000319433) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.41498) (C := 1.014417) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 820.8, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8208 {r s : ℝ} (hr : (8208 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.642752 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.992915 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8208 / 10) (j := 10) (n := 27) (lo := 6.71018)
      (hi := 6.71029) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8208 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000318359) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.42058) (C := 1.012772) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 837.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8374 {r s : ℝ} (hr : (8374 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.618812 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.981504 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8374 / 10) (j := 10) (n := 27) (lo := 6.73020)
      (hi := 6.73032) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8374 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000310801) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.46064) (C := 1.001133) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 854.1, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8541 {r s : ℝ} (hr : (8541 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.595448 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.970341 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8541 / 10) (j := 10) (n := 27) (lo := 6.74995)
      (hi := 6.75006) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8541 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000303523) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.50012) (C := 0.989746) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 870.7, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8707 {r s : ℝ} (hr : (8707 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.572922 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.959556 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8707 / 10) (j := 10) (n := 27) (lo := 6.76920)
      (hi := 6.76931) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8707 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000296592) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.53862) (C := 0.978746) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 887.4, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from8874 {r s : ℝ} (hr : (8874 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.550930 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.949006 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 8874 / 10) (j := 10) (n := 27) (lo := 6.78820)
      (hi := 6.78831) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 8874 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000289907) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.57662) (C := 0.967985) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 904, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from9040 {r s : ℝ} (hr : (9040 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.529701 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.938799 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 9040 / 10) (j := 10) (n := 27) (lo := 6.80673)
      (hi := 6.80684) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 9040 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000283531) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.61368) (C := 0.957573) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 920.7, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from9207 {r s : ℝ} (hr : (9207 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.508959 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.928804 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 9207 / 10) (j := 10) (n := 27) (lo := 6.82503)
      (hi := 6.82515) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 9207 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000277371) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.65030) (C := 0.947379) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 937.3, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from9373 {r s : ℝ} (hr : (9373 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.488915 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.919123 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 9373 / 10) (j := 10) (n := 27) (lo := 6.84290)
      (hi := 6.84302) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 9373 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000271486) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.68604) (C := 0.937504) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 953.9, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from9539 {r s : ℝ} (hr : (9539 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.469427 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.909690 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 9539 / 10) (j := 10) (n := 27) (lo := 6.86046)
      (hi := 6.86057) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 9539 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000265827) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.72114) (C := 0.927882) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 970.6, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from9706 {r s : ℝ} (hr : (9706 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.450362 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.900443 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 9706 / 10) (j := 10) (n := 27) (lo := 6.87781)
      (hi := 6.87793) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 9706 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000260348) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.75586) (C := 0.918450) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

/-- At radii from 987.2, bound the two K197 conductor terms
using the certified endpoint and the scale floor 1.02. -/
theorem conductors_from9872 {r s : ℝ} (hr : (9872 / 10 : ℝ) ≤ r) (hs : 1.02 ≤ s) :
    -1.431919 ≤ gaussianTheta197 r ∧
      4 * (r / s) * (quarterKernel656.transform (r ^ 2)⁻¹).re ≤ 0.891475 := by
  have hl :=
    Analysis.rationalLogIntervalCheck_sound (N := 9872 / 10) (j := 10) (n := 27) (lo := 6.89477)
      (hi := 6.89489) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific] at hl
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 9872 / 10) (p := 6)
        (d := 5) (lo := 0) (hi := 0.000255103) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_ofScientific, Nat.cast_ofNat, neg_div] at hp
  norm_num only at hr
  exact
    conductors_from_endpoint (z := 13.78978) (C := 0.909303) (by norm_num only) hr hs
      (by linarith only [hl.1]) (by linarith only [hl.2]) hp
      (by norm_num only [gaussianConductorPoly197]) (by norm_num only) (by norm_num only)
      (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
