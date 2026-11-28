/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseScalar644
public import PseudoPrime.Analysis.ComputedComplexIntervals
import PseudoPrime.Analysis.IntegerIntervalChecks

/-! # Interval arithmetic for the reciprocal factors of the section 122 phase -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Given intervals for the real and imaginary parts, this is their
rounded sum of squares at the common integer scale. It encloses the
denominator of the complex inverse. -/
def phaseInverseDenom (G : ℤ) (R I : Analysis.IntegerInterval) : Analysis.IntegerInterval :=
  (Analysis.roundedProduct G R R).add (Analysis.roundedProduct G I I)

/-- Given an interval for the reciprocal of the squared norm, multiply it
by the real coordinate and the negated imaginary coordinate of the input.
These computed intervals enclose the complex inverse when the check succeeds. -/
def phaseInverseBox (G : ℤ) (R I D : Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  (Analysis.roundedProduct G R D, Analysis.roundedProduct G I.neg D)

/-- Reflect a checked real reciprocal into a complex inverse enclosure.
This applies uniformly to both linear denominators of the phase kernel. -/
theorem phase_inverse_box_sound {G : ℤ} (hG : 0 < G) {R I D : Analysis.IntegerInterval} {z : ℂ}
    (hz : Analysis.complexIntervalContains R I G z)
    (hD :
      Analysis.integerReciprocalCheck G (phaseInverseDenom G R I).lower
          (phaseInverseDenom G R I).upper D.lower D.upper =
        true) :
    Analysis.complexIntervalContains (phaseInverseBox G R I D).1 (phaseInverseBox G R I D).2 G
      z⁻¹ := by
  have hn : (phaseInverseDenom G R I).Contains G (Complex.normSq z) := by
    rw [Complex.normSq_apply]
    exact
      Analysis.IntegerInterval.add_contains (Analysis.roundedProduct_contains hG hz.1 hz.1)
        (Analysis.roundedProduct_contains hG hz.2 hz.2)
  have hd : D.Contains G (Complex.normSq z)⁻¹ := Analysis.integerReciprocalCheck_sound hD hn
  constructor
  · simpa only [phaseInverseBox, Complex.inv_re, div_eq_mul_inv] using
      Analysis.roundedProduct_contains hG hz.1 hd
  · simpa only [phaseInverseBox, Complex.inv_im, div_eq_mul_inv] using
      Analysis.roundedProduct_contains hG (Analysis.IntegerInterval.neg_contains hz.2) hd

/-- Repeated rounded products enclose a natural power of a complex
interval. The zero power starts at the singleton rectangle for one. -/
def phasePowBox (G : ℤ) (Q : Analysis.IntegerInterval × Analysis.IntegerInterval) :
    ℕ → Analysis.IntegerInterval × Analysis.IntegerInterval
  | 0 => (⟨G, G⟩, ⟨0, 0⟩)
  | k + 1 => Analysis.roundedComplexProduct G (phasePowBox G Q k) Q

/-- At positive scale, the computed rectangle contains the actual power
of every complex number in the input rectangle. -/
theorem phase_pow_box_sound {G : ℤ} (hG : 0 < G)
    {Q : Analysis.IntegerInterval × Analysis.IntegerInterval} {z : ℂ}
    (hz : Analysis.complexIntervalContains Q.1 Q.2 G z) (k : ℕ) :
    Analysis.complexIntervalContains (phasePowBox G Q k).1 (phasePowBox G Q k).2 G (z ^ k) := by
  induction k with
  | zero =>
    have hp : (0 : ℝ) < (G : ℝ) := by exact_mod_cast hG
    simp only [phasePowBox, pow_zero, Analysis.complexIntervalContains,
      Analysis.IntegerInterval.Contains, Complex.one_re, Complex.one_im, Int.cast_zero,
      div_self hp.ne', zero_div, le_refl, and_self]
  | succ k ih =>
    rw [phasePowBox, pow_succ]
    exact Analysis.roundedComplexProduct_contains hG ih hz

/-- The computed pole coefficient rectangle scales the sixth power of the
inverse linear factor by the rational number (107/100)^5. -/
def phasePoleBox (G : ℤ) (R I D : Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  Analysis.roundedComplexProduct G (Analysis.roundedConstant G 14025517307 10000000000, ⟨0, 0⟩)
    (phasePowBox G (phaseInverseBox G R I D) 6)

/-- Once the inverse denominator is checked, the computed pole rectangle
contains the shifted coefficient for every ordinate in the input interval. -/
theorem phase_pole_box_sound {G : ℤ} (hG : 0 < G) {R I D : Analysis.IntegerInterval} {t : ℝ}
    (hz : Analysis.complexIntervalContains R I G ((107 / 100 : ℂ) + Complex.I * t))
    (hD :
      Analysis.integerReciprocalCheck G (phaseInverseDenom G R I).lower
          (phaseInverseDenom G R I).upper D.lower D.upper =
        true) :
    Analysis.complexIntervalContains (phasePoleBox G R I D).1 (phasePoleBox G R I D).2 G
      (quarterPhasePole644 t) := by
  have h := phase_pow_box_sound hG (phase_inverse_box_sound hG hz hD) 6
  have hc :
    Analysis.complexIntervalContains (Analysis.roundedConstant G 14025517307 10000000000) ⟨0, 0⟩ G
      ((107 / 100 : ℂ) ^ 5) := by
    have he : (107 / 100 : ℂ) ^ 5 = ((14025517307 / 10000000000 : ℝ) : ℂ) := by
      norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat]
    rw [he]
    constructor
    · rw [Complex.ofReal_re]
      exact Analysis.roundedConstant_contains hG (by norm_num only)
    · simp only [Complex.ofReal_im, Analysis.IntegerInterval.Contains, Int.cast_zero, zero_div,
        le_refl, and_self]
  unfold quarterPhasePole644
  rw [div_eq_mul_inv, ← inv_pow]
  exact Analysis.roundedComplexProduct_contains hG hc h

/-- Compute a rectangle for the unshifted numerator by enclosing the
six products of rational coefficients and powers of the linear factor. -/
def phaseNumeratorBox (G : ℤ) (Q : Analysis.IntegerInterval × Analysis.IntegerInterval)
    (B : ℕ → Analysis.IntegerInterval) : Analysis.IntegerInterval × Analysis.IntegerInterval :=
  let term := fun j ↦ Analysis.roundedComplexProduct G (B j, ⟨0, 0⟩) (phasePowBox G Q (5 - j))
  (Analysis.intervalFinsetSum (Finset.range 6) (fun j ↦ (term j).1),
    Analysis.intervalFinsetSum (Finset.range 6) (fun j ↦ (term j).2))

private theorem real_box {G : ℤ} {B : Analysis.IntegerInterval} {v : ℝ} (h : B.Contains G v) :
    Analysis.complexIntervalContains B ⟨0, 0⟩ G (v : ℂ) := by
  exact
    ⟨by simpa only [Complex.ofReal_re] using h, by
      simp only [Complex.ofReal_im, Analysis.IntegerInterval.Contains, Int.cast_zero, zero_div,
        le_refl, and_self]⟩

/-- All six coefficient boxes and the linear factor box suffice to
certify the computed rectangle for the common numerator. -/
theorem phase_numerator_box_sound {G : ℤ} (hG : 0 < G)
    {Q : Analysis.IntegerInterval × Analysis.IntegerInterval} {z : ℂ}
    {B : ℕ → Analysis.IntegerInterval} (hz : Analysis.complexIntervalContains Q.1 Q.2 G z)
    (hB : ∀ j ∈ Finset.range 6, (B j).Contains G (quarterPhaseCoeff644 j)) :
    Analysis.complexIntervalContains (phaseNumeratorBox G Q B).1 (phaseNumeratorBox G Q B).2 G
      (quarterPhaseNumerator644 z) := by
  unfold phaseNumeratorBox quarterPhaseNumerator644
  apply Analysis.complex_sum_contains
  intro j hj
  exact
    Analysis.roundedComplexProduct_contains hG (real_box (hB j hj))
      (phase_pow_box_sound hG hz (5 - j))

/-- Compose the common numerator, the two reciprocal factors, and the
real normalizing factor to enclose the unshifted coefficient. -/
theorem phase_rational_box_sound {G : ℤ} (hG : 0 < G) {t : ℝ}
    {Q U V : Analysis.IntegerInterval × Analysis.IntegerInterval} {B : ℕ → Analysis.IntegerInterval}
    {K : Analysis.IntegerInterval}
    (hQ : Analysis.complexIntervalContains Q.1 Q.2 G ((107 / 100 : ℂ) + Complex.I * t))
    (hU : Analysis.complexIntervalContains U.1 U.2 G (((1 / 2 : ℂ) + Complex.I * t)⁻¹))
    (hV : Analysis.complexIntervalContains V.1 V.2 G (((107 / 100 : ℂ) + Complex.I * t)⁻¹))
    (hB : ∀ j ∈ Finset.range 6, (B j).Contains G (quarterPhaseCoeff644 j))
    (hK :
      K.Contains G (4 * ((107 / 100 : ℝ) ^ 5 * Real.exp (-(107 / 100) * (2687 / 1000)) / 120))) :
    let A :=
      Analysis.roundedComplexProduct G (K, ⟨0, 0⟩)
        (Analysis.roundedComplexProduct G (phaseNumeratorBox G Q B)
          (Analysis.roundedComplexProduct G U (phasePowBox G V 6)))
    Analysis.complexIntervalContains A.1 A.2 G (quarterPhaseRational644 t) := by
  intro A
  unfold quarterPhaseRational644
  dsimp only
  rw [div_eq_mul_inv (quarterPhaseNumerator644 _), mul_inv_rev, ← inv_pow,
    mul_comm ((((107 / 100 : ℂ) + Complex.I * t)⁻¹) ^ 6)]
  exact
    Analysis.roundedComplexProduct_contains hG (real_box hK)
      (Analysis.roundedComplexProduct_contains hG (phase_numerator_box_sound hG hQ hB)
        (Analysis.roundedComplexProduct_contains hG hU (phase_pow_box_sound hG hV 6)))

private theorem phase_term_split (x t : ℝ) :
    Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel644 t =
      quarterPhaseRational644 t * Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) +
        quarterPhasePole644 t * Complex.exp (Complex.I * (((x + 2687 / 1000) * t : ℝ) : ℂ)) := by
  rw [quarter_phase_split_644, mul_add, mul_left_comm (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))),
    ← Complex.exp_add]
  congr 1
  · rw [mul_comm]
  · congr 2
    simp only [Complex.ofReal_mul, Complex.ofReal_add]
    ring

/-- Multiply each coefficient rectangle by its corresponding phase
rectangle, and add the real coordinates to enclose one ordinate's term. -/
def phaseTermBox (G : ℤ) (R P E F : Analysis.IntegerInterval × Analysis.IntegerInterval) :
    Analysis.IntegerInterval :=
  (Analysis.roundedComplexProduct G R E).1.add (Analysis.roundedComplexProduct G P F).1

private theorem phase_term_box_sound {G : ℤ} (hG : 0 < G) {x t : ℝ}
    {R P E F : Analysis.IntegerInterval × Analysis.IntegerInterval}
    (hR : Analysis.complexIntervalContains R.1 R.2 G (quarterPhaseRational644 t))
    (hP : Analysis.complexIntervalContains P.1 P.2 G (quarterPhasePole644 t))
    (hE : Analysis.complexIntervalContains E.1 E.2 G (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ))))
    (hF :
      Analysis.complexIntervalContains F.1 F.2 G
        (Complex.exp (Complex.I * (((x + 2687 / 1000) * t : ℝ) : ℂ)))) :
    (phaseTermBox G R P E F).Contains G
      (Complex.exp (Complex.I * ((x * t : ℝ) : ℂ)) * quarterPhaseKernel644 t).re := by
  rw [phase_term_split, Complex.add_re]
  exact
    Analysis.IntegerInterval.add_contains (Analysis.roundedComplexProduct_contains hG hR hE).1
      (Analysis.roundedComplexProduct_contains hG hP hF).1

/-- Combine the 29 checked coefficient and phase rectangles at a fixed
logarithmic coordinate into a lower bound on the paired endpoint sum. -/
theorem phase_endpoint_boxes_lower_644 {G : ℤ} (hG : 0 < G) (g : Fin 29 → ℝ) (x : ℝ)
    (R P E F : Fin 29 → Analysis.IntegerInterval × Analysis.IntegerInterval)
    (hR : ∀ i, Analysis.complexIntervalContains (R i).1 (R i).2 G (quarterPhaseRational644 (g i)))
    (hP : ∀ i, Analysis.complexIntervalContains (P i).1 (P i).2 G (quarterPhasePole644 (g i)))
    (hE :
      ∀ i,
        Analysis.complexIntervalContains (E i).1 (E i).2 G
          (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ))))
    (hF :
      ∀ i,
        Analysis.complexIntervalContains (F i).1 (F i).2 G
          (Complex.exp (Complex.I * (((x + 2687 / 1000) * g i : ℝ) : ℂ)))) :
    let W := Analysis.intervalFinsetSum Finset.univ (fun i ↦ phaseTermBox G (R i) (P i) (E i) (F i))
    2 * ((W.lower : ℝ) / G) ≤ pairedPhase g (fun i ↦ quarterPhaseKernel644 (g i)) x := by
  intro W
  have h :=
    Analysis.intervalFinsetSum_contains Finset.univ (fun i ↦ phaseTermBox G (R i) (P i) (E i) (F i))
      (fun i ↦ (Complex.exp (Complex.I * ((x * g i : ℝ) : ℂ)) * quarterPhaseKernel644 (g i)).re) G
      (fun i _ ↦ phase_term_box_sound hG (hR i) (hP i) (hE i) (hF i))
  exact mul_le_mul_of_nonneg_left h.1 (by norm_num only)

end PseudoPrime.PrimeTestBounds.MillerRabin
