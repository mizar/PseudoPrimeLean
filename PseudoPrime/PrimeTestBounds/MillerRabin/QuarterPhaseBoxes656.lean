/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseScalar656
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseArithmetic644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseCertificate644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseArithmetic644
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseRotation644
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.Analysis.ComputedScalarPhase

/-! # Fixed-point rectangles for the two section 132 phase coefficients -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The computed pole coefficient rectangle scales the sixth power of the
inverse linear factor by the rational number (107/100)^5. -/
def phasePoleBox656 (G : ℤ) (R I D : Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  Analysis.roundedComplexProduct G (Analysis.roundedConstant G 161051 100000, ⟨0, 0⟩)
    (phasePowBox G (phaseInverseBox G R I D) 6)

/-- Once the inverse denominator is checked, the computed pole rectangle
contains the shifted coefficient for every ordinate in the input interval. -/
theorem phase_pole_box_sound_656 {G : ℤ} (hG : 0 < G) {R I D : Analysis.IntegerInterval} {t : ℝ}
    (hz : Analysis.complexIntervalContains R I G ((11 / 10 : ℂ) + Complex.I * t))
    (hD :
      Analysis.integerReciprocalCheck G (phaseInverseDenom G R I).lower
          (phaseInverseDenom G R I).upper D.lower D.upper =
        true) :
    Analysis.complexIntervalContains (phasePoleBox656 G R I D).1 (phasePoleBox656 G R I D).2 G
      (quarterPhasePole656 t) := by
  have h := phase_pow_box_sound hG (phase_inverse_box_sound hG hz hD) 6
  have hc :
    Analysis.complexIntervalContains (Analysis.roundedConstant G 161051 100000) ⟨0, 0⟩ G
      ((11 / 10 : ℂ) ^ 5) := by
    have he : (11 / 10 : ℂ) ^ 5 = ((161051 / 100000 : ℝ) : ℂ) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [he]
    constructor
    · rw [Complex.ofReal_re]
      exact Analysis.roundedConstant_contains hG (by norm_num only)
    · simp only [Complex.ofReal_im, Analysis.IntegerInterval.Contains, Int.cast_zero, zero_div,
        le_refl, and_self]
  unfold quarterPhasePole656
  rw [div_eq_mul_inv, ← inv_pow]
  exact Analysis.roundedComplexProduct_contains hG hc h

/-- All six coefficient boxes and the linear factor box suffice to
certify the computed rectangle for the common numerator. -/
theorem phase_numerator_box_sound_656 {G : ℤ} (hG : 0 < G)
    {Q : Analysis.IntegerInterval × Analysis.IntegerInterval} {z : ℂ}
    {B : ℕ → Analysis.IntegerInterval} (hz : Analysis.complexIntervalContains Q.1 Q.2 G z)
    (hB : ∀ j ∈ Finset.range 6, (B j).Contains G (quarterPhaseCoeff656 j)) :
    Analysis.complexIntervalContains (phaseNumeratorBox G Q B).1 (phaseNumeratorBox G Q B).2 G
      (quarterPhaseNumerator656 z) := by
  unfold phaseNumeratorBox quarterPhaseNumerator656
  apply Analysis.complex_sum_contains
  intro j hj
  exact
    Analysis.roundedComplexProduct_contains hG (real_box (hB j hj))
      (phase_pow_box_sound hG hz (5 - j))

/-- Compose the common numerator, the two reciprocal factors, and the
real normalizing factor to enclose the unshifted coefficient. -/
theorem phase_rational_box_sound_656 {G : ℤ} (hG : 0 < G) {t : ℝ}
    {Q U V : Analysis.IntegerInterval × Analysis.IntegerInterval} {B : ℕ → Analysis.IntegerInterval}
    {K : Analysis.IntegerInterval}
    (hQ : Analysis.complexIntervalContains Q.1 Q.2 G ((11 / 10 : ℂ) + Complex.I * t))
    (hU : Analysis.complexIntervalContains U.1 U.2 G (((1 / 2 : ℂ) + Complex.I * t)⁻¹))
    (hV : Analysis.complexIntervalContains V.1 V.2 G (((11 / 10 : ℂ) + Complex.I * t)⁻¹))
    (hB : ∀ j ∈ Finset.range 6, (B j).Contains G (quarterPhaseCoeff656 j))
    (hK : K.Contains G (4 * ((11 / 10 : ℝ) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120))) :
    let A :=
      Analysis.roundedComplexProduct G (K, ⟨0, 0⟩)
        (Analysis.roundedComplexProduct G (phaseNumeratorBox G Q B)
          (Analysis.roundedComplexProduct G U (phasePowBox G V 6)))
    Analysis.complexIntervalContains A.1 A.2 G (quarterPhaseRational656 t) := by
  intro A
  unfold quarterPhaseRational656
  dsimp only
  rw [div_eq_mul_inv (quarterPhaseNumerator656 _), mul_inv_rev, ← inv_pow,
    mul_comm ((((11 / 10 : ℂ) + Complex.I * t)⁻¹) ^ 6)]
  exact
    Analysis.roundedComplexProduct_contains hG (real_box hK)
      (Analysis.roundedComplexProduct_contains hG (phase_numerator_box_sound_656 hG hQ hB)
        (Analysis.roundedComplexProduct_contains hG hU (phase_pow_box_sound hG hV 6)))

private theorem phase_term_split (x t : ℝ) :
    Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel656 t =
      quarterPhaseRational656 t * Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) +
        quarterPhasePole656 t * Complex.exp (Complex.I * (((x + 21 / 8) * t : ℝ) : ℂ)) := by
  rw [quarter_phase_split_656, mul_add, mul_left_comm (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))),
    ← Complex.exp_add]
  congr 1
  · rw [mul_comm]
  · congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_add]
    ring

private def poleBox656 : Analysis.IntegerInterval :=
  Analysis.roundedConstant scale 11 10

private def inversePole656 (i : Fin 29) : Analysis.IntegerInterval :=
  reciprocalBox (phaseInverseDenom scale poleBox656 (ordinates i))

private theorem inverse_pole_valid656 (i : Fin 29) :
    Analysis.integerReciprocalCheck scale (phaseInverseDenom scale poleBox656 (ordinates i)).lower
        (phaseInverseDenom scale poleBox656 (ordinates i)).upper (inversePole656 i).lower
        (inversePole656 i).upper =
      true := by
  have h :
    ∀ j : Fin 29,
      Analysis.integerReciprocalCheck scale (phaseInverseDenom scale poleBox656 (ordinates j)).lower
          (phaseInverseDenom scale poleBox656 (ordinates j)).upper (inversePole656 j).lower
          (inversePole656 j).upper =
        true := by
    decide +kernel
  exact h i

private def coefficientRat656 (j : ℕ) : ℚ :=
  let c (k : ℕ) : ℚ := if k ≤ 5 then (120 / (5 - k).factorial) * (21 / 8) ^ (5 - k) else 0
  3 / 5 * c j - c (j + 1)

private theorem coefficient_cast656 (j : ℕ) :
    (coefficientRat656 j : ℝ) = quarterPhaseCoeff656 j := by
  unfold coefficientRat656 quarterPhaseCoeff656
  simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat]
  split <;> split <;>
    simp only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, Rat.cast_pow,
      Rat.cast_zero]

private def coefficientBoxes656 (j : ℕ) : Analysis.IntegerInterval :=
  Analysis.roundedConstant scale (coefficientRat656 j).num (coefficientRat656 j).den

private theorem coefficientBoxes_sound656 (j : ℕ) :
    (coefficientBoxes656 j).Contains scale (quarterPhaseCoeff656 j) := by
  rw [← coefficient_cast656]
  exact rational_box _

private def normalizationBox656 : Analysis.IntegerInterval :=
  ⟨299100304093266000, 299100304093269000⟩

private theorem normalization_sound656 :
    normalizationBox656.Contains scale
      (4 * ((11 / 10 : ℝ) ^ 5 * Real.exp (-(11 / 10) * (21 / 8)) / 120)) := by
  unfold normalizationBox656 scale Analysis.IntegerInterval.Contains
  have hG : (10 : ℝ) ^ 20 = 100000000000000000000 := by norm_num only
  simpa only [Int.cast_ofNat, hG, Set.mem_Icc] using quarter_phase_normalization_656

private def shiftedBoxes656 (i : Fin 29) :=
  phasePoleBox656 scale poleBox656 (ordinates i) (inversePole656 i)

private def unshiftedBoxes656 (i : Fin 29) :=
  let Q := (poleBox656, ordinates i)
  let U := phaseInverseBox scale halfBox (ordinates i) (inverseHalf i)
  let V := phaseInverseBox scale poleBox656 (ordinates i) (inversePole656 i)
  Analysis.roundedComplexProduct scale (normalizationBox656, ⟨0, 0⟩)
    (Analysis.roundedComplexProduct scale (phaseNumeratorBox scale Q coefficientBoxes656)
      (Analysis.roundedComplexProduct scale U (phasePowBox scale V 6)))

private theorem shifted_boxes_sound656 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    Analysis.complexIntervalContains (shiftedBoxes656 i).1 (shiftedBoxes656 i).2 scale
      (quarterPhasePole656 (g i)) := by
  have h :=
    line_box (11 / 10) (g i)
      (show poleBox656.Contains scale (11 / 10 : ℝ) by
        simpa only [poleBox656, Int.cast_ofNat] using
          Analysis.roundedConstant_contains (p := 11) scale_pos (by decide : (0 : ℤ) < 10))
      (ordinates_sound hl hu i)
  rw [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_ofNat] at h
  exact phase_pole_box_sound_656 scale_pos h (inverse_pole_valid656 i)

private theorem unshifted_boxes_sound656 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    Analysis.complexIntervalContains (unshiftedBoxes656 i).1 (unshiftedBoxes656 i).2 scale
      (quarterPhaseRational656 (g i)) := by
  have hp :=
    line_box (11 / 10) (g i)
      (show poleBox656.Contains scale (11 / 10 : ℝ) by
        simpa only [poleBox656, Int.cast_ofNat] using
          Analysis.roundedConstant_contains (p := 11) scale_pos (by decide : (0 : ℤ) < 10))
      (ordinates_sound hl hu i)
  have hh :=
    line_box (1 / 2) (g i)
      (show halfBox.Contains scale (1 / 2 : ℝ) by
        simpa only [halfBox, Int.cast_one, Int.cast_ofNat] using
          Analysis.roundedConstant_contains (p := 1) scale_pos (by decide : (0 : ℤ) < 2))
      (ordinates_sound hl hu i)
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hp hh
  exact
    phase_rational_box_sound_656 scale_pos hp
      (phase_inverse_box_sound scale_pos hh (inverse_half_valid i))
      (phase_inverse_box_sound scale_pos hp (inverse_pole_valid656 i))
      (fun j _ ↦ coefficientBoxes_sound656 j) normalization_sound656

private theorem phase_term_split_656 (x t : ℝ) :
    Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel656 t =
      quarterPhaseRational656 t * Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) +
        quarterPhasePole656 t * Complex.exp (Complex.I * (((x + 21 / 8) * t : ℝ) : ℂ)) := by
  rw [quarter_phase_split_656, mul_add, mul_left_comm (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))),
    ← Complex.exp_add]
  congr 1
  · rw [mul_comm]
  · congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_add]
    ring

private theorem phase_term_box_sound_656 {G : ℤ} (hG : 0 < G) {x t : ℝ}
    {R P E F : Analysis.IntegerInterval × Analysis.IntegerInterval}
    (hR : Analysis.complexIntervalContains R.1 R.2 G (quarterPhaseRational656 t))
    (hP : Analysis.complexIntervalContains P.1 P.2 G (quarterPhasePole656 t))
    (hE : Analysis.complexIntervalContains E.1 E.2 G (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))))
    (hF :
      Analysis.complexIntervalContains F.1 F.2 G
        (Complex.exp (Complex.I * (((x + 21 / 8) * t : ℝ) : ℂ)))) :
    (phaseTermBox G R P E F).Contains G
      (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel656 t).re := by
  rw [phase_term_split_656, Complex.add_re]
  exact
    Analysis.IntegerInterval.add_contains (Analysis.roundedComplexProduct_contains hG hR hE).1
      (Analysis.roundedComplexProduct_contains hG hP hF).1

/-- Combine the 29 checked coefficient and phase rectangles at a fixed
logarithmic coordinate into a lower bound on the paired endpoint sum. -/
private theorem phase_endpoint_boxes_lower_656 {G : ℤ} (hG : 0 < G) (g : Fin 29 → ℝ) (x : ℝ)
    (R P E F : Fin 29 → Analysis.IntegerInterval × Analysis.IntegerInterval)
    (hR : ∀ i, Analysis.complexIntervalContains (R i).1 (R i).2 G (quarterPhaseRational656 (g i)))
    (hP : ∀ i, Analysis.complexIntervalContains (P i).1 (P i).2 G (quarterPhasePole656 (g i)))
    (hE :
      ∀ i,
        Analysis.complexIntervalContains (E i).1 (E i).2 G
          (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ))))
    (hF :
      ∀ i,
        Analysis.complexIntervalContains (F i).1 (F i).2 G
          (Complex.exp (Complex.I * (((x + 21 / 8) * g i : ℝ) : ℂ)))) :
    let W := Analysis.intervalFinsetSum Finset.univ (fun i ↦ phaseTermBox G (R i) (P i) (E i) (F i))
    2 * ((W.lower : ℝ) / G) ≤ pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) x := by
  intro W
  have h :=
    Analysis.intervalFinsetSum_contains Finset.univ (fun i ↦ phaseTermBox G (R i) (P i) (E i) (F i))
      (fun i ↦ (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) * quarterPhaseKernel656 (g i)).re) G
      (fun i _ ↦ phase_term_box_sound_656 hG (hR i) (hP i) (hE i) (hF i))
  exact mul_le_mul_of_nonneg_left h.1 (by norm_num only)

/-- At the common positive scale, an ordinate interval and an interval
for twice the radius logarithm determine both required angle intervals.
The shifted angle uses the exact rational displacement of the Mellin term. -/
private theorem phase_angle_boxes_656 {G : ℤ} (hG : 0 < G) {A T : Analysis.IntegerInterval}
    {x t : ℝ} (hx : A.Contains G x) (ht : T.Contains G t) :
    (Analysis.roundedProduct G A T).Contains G (x * t) ∧
      (Analysis.roundedProduct G (A.add (Analysis.roundedConstant G 21 8)) T).Contains G
        ((x + 21 / 8) * t) := by
  have hs : (Analysis.roundedConstant G 21 8).Contains G (21 / 8 : ℝ) := by
    simpa only [Int.cast_ofNat] using
      Analysis.roundedConstant_contains (p := 21) hG (by decide : (0 : ℤ) < 8)
  exact
    ⟨Analysis.roundedProduct_contains hG hx ht,
      Analysis.roundedProduct_contains hG (Analysis.IntegerInterval.add_contains hx hs) ht⟩

/-- Compute the angle box from a logarithm box and an ordinate box.
The Boolean selects the exact Mellin shift when it is true. -/
private def phaseAngle656 (G : ℤ) (A T : Analysis.IntegerInterval) (shifted : Bool) :
    Analysis.IntegerInterval :=
  Analysis.roundedProduct G (if shifted then A.add (Analysis.roundedConstant G 21 8) else A) T

/-- Combine the computed rotations and the two coefficient rectangles at
each of the 29 ordinate brackets. The only angle witnesses are the integer
quarter turns and the checks that their centers lie in the Taylor domain. -/
private theorem phase_endpoint_rotations_lower_656 {G : ℤ} (hG : 0 < G)
    {A P : Analysis.IntegerInterval} {x : ℝ} (hx : A.Contains G x) (hpi : P.Contains G Real.pi)
    (he : (1 / 2 ^ 120 : ℝ) ≤ 1 / (G : ℝ)) (g : Fin 29 → ℝ) (T : Fin 29 → Analysis.IntegerInterval)
    (ht : ∀ i, (T i).Contains G (g i)) (k : Fin 29 → Bool → ℤ)
    (hc : ∀ i f, |phaseCenter644 G (k i f) (phaseAngle656 G A (T i) f) P| ≤ G)
    (R S : Fin 29 → Analysis.IntegerInterval × Analysis.IntegerInterval)
    (hR : ∀ i, Analysis.complexIntervalContains (R i).1 (R i).2 G (quarterPhaseRational656 (g i)))
    (hS : ∀ i, Analysis.complexIntervalContains (S i).1 (S i).2 G (quarterPhasePole656 (g i))) :
    let E := fun i f ↦ phaseRotationBox644 G (k i f) (phaseAngle656 G A (T i) f) P
    let W :=
      Analysis.intervalFinsetSum Finset.univ
        (fun i ↦ phaseTermBox G (R i) (S i) (E i false) (E i true))
    2 * ((W.lower : ℝ) / G) ≤ pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) x := by
  intro E W
  have h (i : Fin 29) (f : Bool) :
    Analysis.complexIntervalContains (E i f).1 (E i f).2 G
      (Complex.exp (Complex.I * ((((if f then x + 21 / 8 else x) * g i : ℝ)) : ℂ))) := by
    have hA : (phaseAngle656 G A (T i) f).Contains G ((if f then x + 21 / 8 else x) * g i) := by
      cases f
      · exact (phase_angle_boxes_656 hG hx (ht i)).1
      · exact (phase_angle_boxes_656 hG hx (ht i)).2
    exact phase_rotation_box_sound hG hA hpi (abs_le.mp (hc i f)).1 (abs_le.mp (hc i f)).2 he
  exact
    phase_endpoint_boxes_lower_656 hG g x R S (fun i ↦ E i false) (fun i ↦ E i true) hR hS
      (fun i ↦ h i false) (fun i ↦ h i true)

private def angle656 (A : Analysis.IntegerInterval) (i : Fin 29) (b : Bool) :=
  phaseAngle656 scale A (ordinates i) b

private def quarterTurn656 (A : Analysis.IntegerInterval) (i : Fin 29) (b : Bool) : ℤ :=
  let X := angle656 A i b
  (X.lower + X.upper + piBox.lower / 2) / piBox.lower

private def rotations656 (A : Analysis.IntegerInterval) (i : Fin 29) (b : Bool) :=
  phaseRotationBox644 scale (quarterTurn656 A i b) (angle656 A i b) piBox

private def endpointSum656 (A : Analysis.IntegerInterval) : Analysis.IntegerInterval :=
  Analysis.intervalFinsetSum Finset.univ
    (fun i ↦
      phaseTermBox scale (unshiftedBoxes656 i) (shiftedBoxes656 i) (rotations656 A i false)
        (rotations656 A i true))

private theorem endpoint_sound656 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) {A : Analysis.IntegerInterval}
    {x : ℝ} (hA : A.Contains scale x)
    (hc : ∀ i b, |phaseCenter644 scale (quarterTurn656 A i b) (angle656 A i b) piBox| ≤ scale) :
    2 * ((endpointSum656 A).lower : ℝ) / (scale : ℝ) ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) x := by
  rw [mul_div_assoc]
  exact
    phase_endpoint_rotations_lower_656 scale_pos hA pi_box_sound
      (by norm_num only [scale, Int.cast_ofNat]) g ordinates (ordinates_sound hl hu)
      (quarterTurn656 A) hc unshiftedBoxes656 shiftedBoxes656 (unshifted_boxes_sound656 hl hu)
      (shifted_boxes_sound656 hl hu)

private theorem endpoint_rational_lower656 {g : Fin 29 → ℝ} {x : ℝ} {A : Analysis.IntegerInterval}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (hbox : A.Contains scale x)
    (hc : ∀ i b, |phaseCenter644 scale (quarterTurn656 A i b) (angle656 A i b) piBox| ≤ scale)
    {B : ℚ} (hb : B ≤ 2 * ((endpointSum656 A).lower : ℚ) / (scale : ℚ)) :
    (B : ℝ) ≤ pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) x := by
  have h := (Rat.cast_le (K := ℝ)).2 hb
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat, Rat.cast_intCast] at h
  exact h.trans (endpoint_sound656 hl hu hbox hc)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Check the rotations and the rounded sum at 29 positive ordinates.
/-- The paired low-zero phase at radius 322 is at least 4313522/10^9. -/
theorem quarter_phase_endpoint_656_322 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    4313522 / 1000000000 ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log (322)) := by
  have hx :=
    radius_log_box (r := 322) (lo := 5774551543203 / 1000000000000) (hi :=
      5774551547707 / 1000000000000) (a := 1154910308640600000000) (b := 1154910309541400000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_ofNat] at hx
  have h :=
    endpoint_rational_lower656 hl hu hx (by decide +kernel) (B := 4313522 / 1000000000)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Check the rotations and the rounded sum at 29 positive ordinates.
/-- The paired low-zero phase at radius 1291 / 4 is at least 4563762/10^9. -/
theorem quarter_phase_endpoint_656_32275 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    4563762 / 1000000000 ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log (1291 / 4)) := by
  have hx :=
    radius_log_box (r := 1291 / 4) (lo := 5776878027386 / 1000000000000) (hi :=
      5776878031889 / 1000000000000) (a := 1155375605477200000000) (b := 1155375606377800000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_div, Rat.cast_ofNat] at hx
  have h :=
    endpoint_rational_lower656 hl hu hx (by decide +kernel) (B := 4563762 / 1000000000)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Check the rotations and the rounded sum at 29 positive ordinates.
/-- The paired low-zero phase at radius 1297 / 4 is at least 4875145/10^9. -/
theorem quarter_phase_endpoint_656_32425 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    4875145 / 1000000000 ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log (1297 / 4)) := by
  have hx :=
    radius_log_box (r := 1297 / 4) (lo := 5781514820856 / 1000000000000) (hi :=
      5781514825359 / 1000000000000) (a := 1156302964171200000000) (b := 1156302965071800000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_div, Rat.cast_ofNat] at hx
  have h :=
    endpoint_rational_lower656 hl hu hx (by decide +kernel) (B := 4875145 / 1000000000)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Check the rotations and the rounded sum at 29 positive ordinates.
/-- The paired low-zero phase at radius 1305 / 4 is at least 4909557/10^9. -/
theorem quarter_phase_endpoint_656_32625 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    4909557 / 1000000000 ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log (1305 / 4)) := by
  have hx :=
    radius_log_box (r := 1305 / 4) (lo := 5787663956296 / 1000000000000) (hi :=
      5787663960799 / 1000000000000) (a := 1157532791259200000000) (b := 1157532792159800000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_div, Rat.cast_ofNat] at hx
  have h :=
    endpoint_rational_lower656 hl hu hx (by decide +kernel) (B := 4909557 / 1000000000)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Check the rotations and the rounded sum at 29 positive ordinates.
/-- The paired low-zero phase at radius 328 is at least 4706101/10^9. -/
theorem quarter_phase_endpoint_656_328 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    4706101 / 1000000000 ≤
      pairedPhase g (fun i ↦ quarterPhaseKernel656 (g i)) (2 * Real.log (328)) := by
  have hx :=
    radius_log_box (r := 328) (lo := 5793013606044 / 1000000000000) (hi :=
      5793013610546 / 1000000000000) (a := 1158602721208800000000) (b := 1158602722109200000000)
      (by decide +kernel) (by decide +kernel) (by decide +kernel)
  simp only [Rat.cast_ofNat] at hx
  have h :=
    endpoint_rational_lower656 hl hu hx (by decide +kernel) (B := 4706101 / 1000000000)
      (by decide +kernel)
  simpa only [Rat.cast_div, Rat.cast_ofNat] using h

/-- Bound the absolute values of both coordinates by their farthest endpoints. -/
private def phaseBoxAbs (P : Analysis.IntegerInterval × Analysis.IntegerInterval) : ℤ :=
  max |P.1.lower| |P.1.upper| + max |P.2.lower| |P.2.upper|

/-- The two coordinate bounds control the sum of absolute real coefficients. -/
private theorem phase_box_abs_le {P : Analysis.IntegerInterval × Analysis.IntegerInterval} {z : ℂ}
    (h : Analysis.complexIntervalContains P.1 P.2 scale z) :
    |z.re| + |z.im| ≤ (phaseBoxAbs P : ℝ) / scale := by
  unfold phaseBoxAbs
  rw [Int.cast_add, add_div]
  exact add_le_add (Analysis.interval_abs_le scale_pos h.1) (Analysis.interval_abs_le scale_pos h.2)

/-- The common fixed-point numerator for the squared-frequency bound. -/
private def phaseCurvTicks (i : Fin 29) : ℤ :=
  (max |(ordinates i).lower| |(ordinates i).upper|) ^ 2 *
    (phaseBoxAbs (unshiftedBoxes656 i) + phaseBoxAbs (shiftedBoxes656 i))

private theorem phase_curv_term {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    (g i) ^ 2 *
        ((|(quarterPhaseRational656 (g i)).re| + |(quarterPhaseRational656 (g i)).im|) +
          (|(quarterPhasePole656 (g i)).re| + |(quarterPhasePole656 (g i)).im|)) ≤
      (phaseCurvTicks i : ℝ) / (scale : ℝ) ^ 3 := by
  have ho := Analysis.interval_abs_le scale_pos (ordinates_sound hl hu i)
  have hsq := pow_le_pow_left₀ (abs_nonneg _) ho 2
  rw [sq_abs] at hsq
  have hA := phase_box_abs_le (unshifted_boxes_sound656 hl hu i)
  have hB := phase_box_abs_le (shifted_boxes_sound656 hl hu i)
  have hC := add_le_add hA hB
  rw [← add_div] at hC
  have hx :=
    mul_le_mul hsq hC
      (add_nonneg (add_nonneg (abs_nonneg _) (abs_nonneg _))
        (add_nonneg (abs_nonneg _) (abs_nonneg _)))
      (sq_nonneg _)
  refine hx.trans_eq ?_
  simp only [phaseCurvTicks, Int.cast_mul, Int.cast_pow, Int.cast_add, div_pow]
  rw [div_mul_div_comm, ← pow_succ]

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Evaluate the 29 rounded coefficient rectangles once for the curvature bound.
/-- All admissible heights satisfy the curvature budget of 29 for the
unshifted and shifted phases together, including both conjugate signs. -/
theorem quarter_phase_curvature_656 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    2 *
        ∑ i : Fin 29,
          (g i) ^ 2 *
            ((|(quarterPhaseRational656 (g i)).re| + |(quarterPhaseRational656 (g i)).im|) +
              (|(quarterPhasePole656 (g i)).re| + |(quarterPhasePole656 (g i)).im|)) ≤
      29 := by
  have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ ↦ phase_curv_term hl hu i)
  rw [← Finset.sum_div, ← Int.cast_sum] at h
  have ht : 2 * (∑ i : Fin 29, phaseCurvTicks i) ≤ 29 * scale ^ 3 := by decide +kernel
  have hs : (0 : ℝ) < scale := Int.cast_pos.mpr scale_pos
  have ht' : 2 * ((∑ i : Fin 29, phaseCurvTicks i : ℤ) : ℝ) ≤ 29 * (scale : ℝ) ^ 3 := by
    exact_mod_cast ht
  exact
    (mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ 2)).trans
      (by
        rw [← mul_div_assoc]; exact (div_le_iff₀ (pow_pos hs 3)).mpr ht')

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
-- Reuse the 29 rounded rectangles to check their unweighted absolute mass.
/-- The absolute coordinate mass of the 29 low pairs is at most 0.018.
This bound is independent of the logarithmic phase. -/
theorem quarter_low_phase_mass_656 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) :
    2 *
        ∑ i : Fin 29,
          ((|(quarterPhaseRational656 (g i)).re| + |(quarterPhaseRational656 (g i)).im|) +
            (|(quarterPhasePole656 (g i)).re| + |(quarterPhasePole656 (g i)).im|)) ≤
      0.018 := by
  let ticks (i : Fin 29) := phaseBoxAbs (unshiftedBoxes656 i) + phaseBoxAbs (shiftedBoxes656 i)
  have h :=
    Finset.sum_le_sum (s := Finset.univ)
      (fun i _ ↦
        (add_le_add (phase_box_abs_le (unshifted_boxes_sound656 hl hu i))
              (phase_box_abs_le (shifted_boxes_sound656 hl hu i))).trans_eq
          (by rw [← add_div, Int.cast_add] : _ = ((ticks i : ℤ) : ℝ) / (scale : ℝ)))
  rw [← Finset.sum_div, ← Int.cast_sum] at h
  have ht : 1000 * (2 * ∑ i : Fin 29, ticks i) ≤ 18 * scale := by decide +kernel
  have ht' : (1000 : ℝ) * (2 * ((∑ i : Fin 29, ticks i : ℤ) : ℝ)) ≤ 18 * scale := by
    exact_mod_cast ht
  refine (mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ 2)).trans ?_
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (Int.cast_pos.mpr scale_pos)).mpr
  linarith only [ht']

end PseudoPrime.PrimeTestBounds.MillerRabin
