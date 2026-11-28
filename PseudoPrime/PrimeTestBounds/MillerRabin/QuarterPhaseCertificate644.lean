/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseRotation644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseArithmetic644
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import all PseudoPrime.Analysis.LogTaylorBounds

/-! # Shared input certificates for the five section 122 phase endpoints -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def scale : ℤ :=
  100000000000000000000

private theorem scale_pos : 0 < scale := by decide

private def ordinates (i : Fin 29) : Analysis.IntegerInterval :=
  let l := AnalyticNumberTheory.RiemannZeta.lowZero100Lower i
  let a := Analysis.roundedConstant scale l.num l.den
  let b := Analysis.roundedConstant scale (l + 1 / 100).num (l + 1 / 100).den
  ⟨a.lower, b.upper⟩

private theorem rational_box (q : ℚ) :
    (Analysis.roundedConstant scale q.num q.den).Contains scale (q : ℝ) := by
  have hd : (0 : ℤ) < (q.den : ℤ) := Int.natCast_pos.mpr q.den_pos
  have h := Analysis.roundedConstant_contains (p := q.num) scale_pos hd
  simpa only [Int.cast_natCast, Rat.cast_def] using h

private theorem ordinates_sound {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    (ordinates i).Contains scale (g i) := by
  have h := (rational_box (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i)).1.trans (hl i)
  have h' := (rational_box (AnalyticNumberTheory.RiemannZeta.lowZero100Lower i + 1 / 100)).2
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at h'
  exact ⟨h, (hu i).trans h'⟩

private def halfBox : Analysis.IntegerInterval :=
  Analysis.roundedConstant scale 1 2

private def poleBox : Analysis.IntegerInterval :=
  Analysis.roundedConstant scale 107 100

private def reciprocalBox (A : Analysis.IntegerInterval) : Analysis.IntegerInterval :=
  ⟨scale * scale / A.upper, -(-(scale * scale) / A.lower)⟩

private def inverseHalf (i : Fin 29) : Analysis.IntegerInterval :=
  reciprocalBox (phaseInverseDenom scale halfBox (ordinates i))

private def inversePole (i : Fin 29) : Analysis.IntegerInterval :=
  reciprocalBox (phaseInverseDenom scale poleBox (ordinates i))

private theorem inverse_half_valid (i : Fin 29) :
    Analysis.integerReciprocalCheck scale (phaseInverseDenom scale halfBox (ordinates i)).lower
        (phaseInverseDenom scale halfBox (ordinates i)).upper (inverseHalf i).lower
        (inverseHalf i).upper =
      true := by
  have h :
    ∀ j : Fin 29,
      Analysis.integerReciprocalCheck scale (phaseInverseDenom scale halfBox (ordinates j)).lower
          (phaseInverseDenom scale halfBox (ordinates j)).upper (inverseHalf j).lower
          (inverseHalf j).upper =
        true := by
    decide +kernel
  exact h i

private theorem inverse_pole_valid (i : Fin 29) :
    Analysis.integerReciprocalCheck scale (phaseInverseDenom scale poleBox (ordinates i)).lower
        (phaseInverseDenom scale poleBox (ordinates i)).upper (inversePole i).lower
        (inversePole i).upper =
      true := by
  have h :
    ∀ j : Fin 29,
      Analysis.integerReciprocalCheck scale (phaseInverseDenom scale poleBox (ordinates j)).lower
          (phaseInverseDenom scale poleBox (ordinates j)).upper (inversePole j).lower
          (inversePole j).upper =
        true := by
    decide +kernel
  exact h i

private def coefficientRat (j : ℕ) : ℚ :=
  let c (k : ℕ) : ℚ := if k ≤ 5 then (120 / (5 - k).factorial) * (2687 / 1000) ^ (5 - k) else 0
  57 / 100 * c j - c (j + 1)

private theorem coefficient_cast (j : ℕ) : (coefficientRat j : ℝ) = quarterPhaseCoeff644 j := by
  unfold coefficientRat quarterPhaseCoeff644
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
  split <;> split <;>
    simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_zero]

private def coefficientBoxes (j : ℕ) : Analysis.IntegerInterval :=
  Analysis.roundedConstant scale (coefficientRat j).num (coefficientRat j).den

private theorem coefficientBoxes_sound (j : ℕ) :
    (coefficientBoxes j).Contains scale (quarterPhaseCoeff644 j) := by
  rw [← coefficient_cast]
  exact rational_box _

private def normalizationBox : Analysis.IntegerInterval :=
  ⟨263731443400000000, 263731443500000000⟩

private theorem normalization_sound :
    normalizationBox.Contains scale
      (4 * ((107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120)) := by
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (287509 / 100000 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 287509 / 100000) 26
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hu hl
  have h₁ := one_div_le_one_div_of_le (Real.exp_pos _) hu
  have h₂ := one_div_le_one_div_of_le (by norm_num only) hl
  rw [one_div (Real.exp _), ← Real.exp_neg] at h₁ h₂
  unfold normalizationBox scale Analysis.IntegerInterval.Contains
  norm_num only [Int.cast_ofNat]
  exact ⟨by linarith only [h₁], by linarith only [h₂]⟩

private def shiftedBoxes (i : Fin 29) :=
  phasePoleBox scale poleBox (ordinates i) (inversePole i)

private def unshiftedBoxes (i : Fin 29) :=
  let Q := (poleBox, ordinates i)
  let U := phaseInverseBox scale halfBox (ordinates i) (inverseHalf i)
  let V := phaseInverseBox scale poleBox (ordinates i) (inversePole i)
  Analysis.roundedComplexProduct scale (normalizationBox, ⟨0, 0⟩)
    (Analysis.roundedComplexProduct scale (phaseNumeratorBox scale Q coefficientBoxes)
      (Analysis.roundedComplexProduct scale U (phasePowBox scale V 6)))

private theorem line_box (a t : ℝ) {A T : Analysis.IntegerInterval} (ha : A.Contains scale a)
    (ht : T.Contains scale t) :
    Analysis.complexIntervalContains A T scale ((a : ℂ) + Complex.I * t) := by
  simp only [Analysis.complexIntervalContains, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
    mul_zero, sub_zero, add_zero, one_mul, zero_add]
  exact ⟨ha, ht⟩

private theorem shifted_boxes_sound {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    Analysis.complexIntervalContains (shiftedBoxes i).1 (shiftedBoxes i).2 scale
      (quarterPhasePole644 (g i)) := by
  have h :=
    line_box (107 / 100) (g i)
      (show poleBox.Contains scale (107 / 100 : ℝ) by
        simpa only [poleBox, Int.cast_ofNat] using
          Analysis.roundedConstant_contains (p := 107) scale_pos (by decide : (0 : ℤ) < 100))
      (ordinates_sound hl hu i)
  rw [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_ofNat] at h
  exact phase_pole_box_sound scale_pos h (inverse_pole_valid i)

private theorem unshifted_boxes_sound {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    Analysis.complexIntervalContains (unshiftedBoxes i).1 (unshiftedBoxes i).2 scale
      (quarterPhaseRational644 (g i)) := by
  have hp :=
    line_box (107 / 100) (g i)
      (show poleBox.Contains scale (107 / 100 : ℝ) by
        simpa only [poleBox, Int.cast_ofNat] using
          Analysis.roundedConstant_contains (p := 107) scale_pos (by decide : (0 : ℤ) < 100))
      (ordinates_sound hl hu i)
  have hh :=
    line_box (1 / 2) (g i)
      (show halfBox.Contains scale (1 / 2 : ℝ) by
        simpa only [halfBox, Int.cast_one, Int.cast_ofNat] using
          Analysis.roundedConstant_contains (p := 1) scale_pos (by decide : (0 : ℤ) < 2))
      (ordinates_sound hl hu i)
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hp hh
  exact
    phase_rational_box_sound scale_pos hp
      (phase_inverse_box_sound scale_pos hh (inverse_half_valid i))
      (phase_inverse_box_sound scale_pos hp (inverse_pole_valid i))
      (fun j _ ↦ coefficientBoxes_sound j) normalization_sound

private def piBox : Analysis.IntegerInterval :=
  ⟨314159265358979323846, 314159265358979323847⟩

private theorem pi_box_sound : piBox.Contains scale Real.pi := by
  unfold piBox scale Analysis.IntegerInterval.Contains
  norm_num only [Int.cast_ofNat]
  exact ⟨by linarith only [Real.pi_gt_d20], by linarith only [Real.pi_lt_d20]⟩

private def angle (A : Analysis.IntegerInterval) (i : Fin 29) (b : Bool) :=
  phaseAngle644 scale A (ordinates i) b

private def quarterTurn (A : Analysis.IntegerInterval) (i : Fin 29) (b : Bool) : ℤ :=
  let X := angle A i b
  (X.lower + X.upper + piBox.lower / 2) / piBox.lower

private def rotations (A : Analysis.IntegerInterval) (i : Fin 29) (b : Bool) :=
  phaseRotationBox644 scale (quarterTurn A i b) (angle A i b) piBox

private def endpointSum (A : Analysis.IntegerInterval) : Analysis.IntegerInterval :=
  Analysis.intervalFinsetSum Finset.univ
    (fun i ↦
      phaseTermBox scale (unshiftedBoxes i) (shiftedBoxes i) (rotations A i false)
        (rotations A i true))

private theorem endpoint_sound {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) {A : Analysis.IntegerInterval}
    {x : ℝ} (hA : A.Contains scale x)
    (hc : ∀ i b, |phaseCenter644 scale (quarterTurn A i b) (angle A i b) piBox| ≤ scale) :
    2 * ((endpointSum A).lower : ℝ) / (scale : ℝ) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) x := by
  rw [mul_div_assoc]
  exact
    phase_endpoint_rotations_lower_644 scale_pos hA pi_box_sound
      (by norm_num only [scale, Int.cast_ofNat]) g ordinates (ordinates_sound hl hu) (quarterTurn A)
      hc unshiftedBoxes shiftedBoxes (unshifted_boxes_sound hl hu) (shifted_boxes_sound hl hu)

private theorem radius_log_box {r lo hi : ℚ} {a b : ℤ}
    (h : Analysis.rationalLogIntervalCheck r 9 27 lo hi = true)
    (hlo : (a : ℚ) / (scale : ℚ) ≤ 2 * lo) (hhi : 2 * hi ≤ (b : ℚ) / (scale : ℚ)) :
    (⟨a, b⟩ : Analysis.IntegerInterval).Contains scale (2 * Real.log (r : ℝ)) := by
  have hlog := Analysis.rationalLogIntervalCheck_sound h
  have hl := (Rat.cast_le (K := ℝ)).2 hlo
  have hu := (Rat.cast_le (K := ℝ)).2 hhi
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast] at hl hu
  exact ⟨by linarith only [hl, hlog.1], by linarith only [hu, hlog.2]⟩

private theorem endpoint_rational_lower {g : Fin 29 → ℝ} {x : ℝ} {A : Analysis.IntegerInterval}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (hbox : A.Contains scale x)
    (hc : ∀ i b, |phaseCenter644 scale (quarterTurn A i b) (angle A i b) piBox| ≤ scale) {B : ℚ}
    (hb : B ≤ 2 * ((endpointSum A).lower : ℚ) / (scale : ℚ)) :
    (B : ℝ) ≤ pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) x := by
  have h := (Rat.cast_le (K := ℝ)).2 hb
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast] at h
  exact h.trans (endpoint_sound hl hu hbox hc)

/-- The paired low-zero phase at radius 316 is at least 1842/1000000. -/
theorem quarter_phase_endpoint_644_316 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    (1842 / 1000000 : ℝ) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) (2 * Real.log (316)) := by
  have h :=
    radius_log_box (r := 316) (lo := 11511484411173 / 2000000000000) (hi :=
      11511484443173 / 2000000000000) (a := 1151148441117300000000) (b := 1151148444317300000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    endpoint_rational_lower hl hu h (by decide +kernel) (B := 1842 / 1000000) (by decide +kernel)

/-- The paired low-zero phase at radius 320 is at least 3371/1000000. -/
theorem quarter_phase_endpoint_644_320 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    (3371 / 1000000 : ℝ) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) (2 * Real.log (320)) := by
  have h :=
    radius_log_box (r := 320) (lo := 11536641975587 / 2000000000000) (hi :=
      11536642007587 / 2000000000000) (a := 1153664197558700000000) (b := 1153664200758700000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    endpoint_rational_lower hl hu h (by decide +kernel) (B := 3371 / 1000000) (by decide +kernel)

/-- The paired low-zero phase at radius 1287 / 4 is at least 4133/1000000. -/
theorem quarter_phase_endpoint_644_32175 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    (4133 / 1000000 : ℝ) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) (2 * Real.log (1287 / 4)) := by
  have h :=
    radius_log_box (r := 1287 / 4) (lo := 11547549676952 / 2000000000000) (hi :=
      11547549708952 / 2000000000000) (a := 1154754967695200000000) (b := 1154754970895200000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    endpoint_rational_lower hl hu h (by decide +kernel) (B := 4133 / 1000000) (by decide +kernel)

/-- The paired low-zero phase at radius 1609 / 5 is at least 4152/1000000. -/
theorem quarter_phase_endpoint_644_3218 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    (4152 / 1000000 : ℝ) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) (2 * Real.log (1609 / 5)) := by
  have h :=
    radius_log_box (r := 1609 / 5) (lo := 11547860453116 / 2000000000000) (hi :=
      11547860485116 / 2000000000000) (a := 1154786045311600000000) (b := 1154786048511600000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    endpoint_rational_lower hl hu h (by decide +kernel) (B := 4152 / 1000000) (by decide +kernel)

/-- The paired low-zero phase at radius 322 is at least 4227/1000000. -/
theorem quarter_phase_endpoint_644_322 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    (4227 / 1000000 : ℝ) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) (2 * Real.log (322)) := by
  have h :=
    radius_log_box (r := 322) (lo := 11549103075088 / 2000000000000) (hi :=
      11549103107088 / 2000000000000) (a := 1154910307508800000000) (b := 1154910310708800000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  simpa only [Rat.cast_div, Rat.cast_ofNat] using
    endpoint_rational_lower hl hu h (by decide +kernel) (B := 4227 / 1000000) (by decide +kernel)

end PseudoPrime.PrimeTestBounds.MillerRabin
