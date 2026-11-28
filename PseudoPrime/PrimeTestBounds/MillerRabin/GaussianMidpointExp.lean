/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import Mathlib.Data.Nat.Sqrt
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMidpointRational
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianMidpointRational
public import PseudoPrime.Analysis.ComputedPhaseRotation
public import PseudoPrime.Analysis.IntegerIntervalHorner
import all PseudoPrime.PrimeTestBounds.MillerRabin.GaussianPrincipalLowZeros
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.Analysis.ExponentialTaylorCertificates
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.Linarith

/-! # Rational exponential enclosures for Gaussian midpoints -/

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The fixed-point grid used for midpoint phases. -/
private def midpointPhaseScale : ℤ :=
  10 ^ 18

/-- Enclose a rational on the fixed-point grid using its rounded-down coordinate. -/
private def midpointAngleInterval (q : ℚ) : Analysis.IntegerInterval :=
  let z := ⌊(midpointPhaseScale : ℚ) * q⌋
  ⟨z, z + 1⟩

/-- The rational angle lies between the neighboring integer grid points. -/
private theorem midpoint_angle_contains (q : ℚ) :
    (midpointAngleInterval q).Contains midpointPhaseScale (q : ℝ) := by
  have hG : (0 : ℝ) < (midpointPhaseScale : ℝ) := by
    norm_num only [midpointPhaseScale, Int.cast_pow, Int.cast_ofNat]
  let x := (midpointPhaseScale : ℝ) * (q : ℝ)
  have hf : ⌊x⌋ = ⌊(midpointPhaseScale : ℚ) * q⌋ := by
    simpa only [x, Rat.cast_mul, Rat.cast_intCast] using
      (Rat.floor_cast (α := ℝ) ((midpointPhaseScale : ℚ) * q))
  have hlo := Int.floor_le x
  have hhi := Int.lt_floor_add_one x
  rw [hf] at hlo hhi
  constructor
  · exact (div_le_iff₀ hG).2 (hlo.trans_eq (mul_comm _ _))
  · apply (le_div_iff₀ hG).2
    simpa only [midpointAngleInterval, Int.cast_add, Int.cast_one, x, mul_comm] using hhi.le

/-- Apply the certified complex squaring operation a fixed number of times. -/
private def midpointPhaseSquares (G : ℤ) :
    ℕ →
      Analysis.IntegerInterval × Analysis.IntegerInterval →
      Analysis.IntegerInterval × Analysis.IntegerInterval
  | 0, Z => Z
  | n + 1, Z =>
    let Y := midpointPhaseSquares G n Z
    Analysis.roundedPhaseDouble G Y.1 Y.2

/-- The result of repeated squaring encloses the phase at the corresponding doubled angle. -/
private theorem midpoint_squares_contains {G : ℤ} {x : ℝ}
    {Z : Analysis.IntegerInterval × Analysis.IntegerInterval} (n : ℕ) (hG : 0 < G)
    (hZ : Analysis.complexIntervalContains Z.1 Z.2 G (Complex.exp ((x : ℂ) * Complex.I))) :
    let Y := midpointPhaseSquares G n Z
    Analysis.complexIntervalContains Y.1 Y.2 G
      (Complex.exp (((2 ^ n * x : ℝ) : ℂ) * Complex.I)) := by
  induction n with
  | zero => simpa only [midpointPhaseSquares, pow_zero, one_mul] using hZ
  | succ n ih =>
    have h := Analysis.rounded_phase_double_contains hG ih
    have he : (2 : ℝ) ^ (n + 1) * x = 2 ^ n * x + 2 ^ n * x := by
      rw [pow_succ]
      ring
    simpa only [midpointPhaseSquares, he] using h

/-- The phase box at a height is computed from a reduced argument and eleven squares. -/
private def midpointPhaseBox (t : ℚ) : Analysis.IntegerInterval × Analysis.IntegerInterval :=
  let q := 5 * t / 2048
  let Z := Analysis.intervalPhaseHorner midpointPhaseScale (midpointAngleInterval q) 24 0
  midpointPhaseSquares midpointPhaseScale 11 (Z.1.widen 1, Z.2.widen 1)

/-- The phase box encloses the exact unit phase for heights of absolute value at most 100. -/
private theorem midpoint_phase_contains (t : ℚ) (ht : |t| ≤ 100) :
    let Z := midpointPhaseBox t
    Analysis.complexIntervalContains Z.1 Z.2 midpointPhaseScale
      (Complex.exp (5 * Complex.I * (t : ℂ))) := by
  let q : ℚ := 5 * t / 2048
  have hG : 0 < midpointPhaseScale := by decide +kernel
  have hq : |(q : ℝ)| ≤ 1 / 4 := by
    have htR := (Rat.cast_le (K := ℝ)).mpr ht
    simp only [Rat.cast_abs, Rat.cast_ofNat] at htR
    simp only [q, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, abs_div, abs_mul,
      abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 5),
      abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2048)]
    linarith only [htR]
  have hw : (1 / 2 ^ 120 : ℝ) ≤ (1 : ℝ) / (midpointPhaseScale : ℤ) := by
    norm_num only [midpointPhaseScale, Int.cast_pow, Int.cast_ofNat]
  have h :=
    Analysis.intervalHorner25_phase (r := 1) q hG (midpoint_angle_contains q) hq
      (by simpa only [Int.cast_one] using hw)
  let Z := Analysis.intervalPhaseHorner midpointPhaseScale (midpointAngleInterval q) 24 0
  have h' :=
    midpoint_squares_contains (x := (q : ℝ)) (Z := (Z.1.widen 1, Z.2.widen 1)) 11 hG
      (by simpa only [Z, Complex.ofReal_ratCast] using h)
  have he : ((((2 : ℝ) ^ 11 * (q : ℝ)) : ℝ) : ℂ) * Complex.I = 5 * Complex.I * (t : ℂ) := by
    simp only [q, Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Complex.ofReal_mul,
      Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_ratCast]
    ring
  change
    Analysis.complexIntervalContains (midpointPhaseBox t).1 (midpointPhaseBox t).2
      midpointPhaseScale (Complex.exp (((2 ^ 11 * (q : ℝ) : ℝ) : ℂ) * Complex.I)) at h'
  rwa [he] at h'

/-- A rational phase center obtained from the lower corner of the computed rectangle. -/
private def midpointPhaseCorner (Z : Analysis.IntegerInterval × Analysis.IntegerInterval) :
    Analysis.RatComplex :=
  ⟨(Z.1.lower : ℚ) / (midpointPhaseScale : ℚ), (Z.2.lower : ℚ) / (midpointPhaseScale : ℚ)⟩

/-- Evaluate the lower corner of the computed phase rectangle. -/
public def highMidpointPhase (t : ℚ) : Analysis.RatComplex :=
  midpointPhaseCorner (midpointPhaseBox t)

/-- The sum of the rectangle widths is a rational bound on distance from the corner. -/
private def midpointPhaseWidth (Z : Analysis.IntegerInterval × Analysis.IntegerInterval) : ℚ :=
  ((Z.1.upper - Z.1.lower : ℤ) : ℚ) / (midpointPhaseScale : ℚ) +
    ((Z.2.upper - Z.2.lower : ℤ) : ℚ) / (midpointPhaseScale : ℚ)

/-- Evaluate the sum of the widths of the computed phase rectangle. -/
public def highMidpointPhaseRadius (t : ℚ) : ℚ :=
  midpointPhaseWidth (midpointPhaseBox t)

/-- The computed rational center has the stated norm error throughout the phase rectangle. -/
public theorem high_midpoint_phase_error (t : ℚ) (ht : |t| ≤ 100) :
    ‖Complex.exp (5 * Complex.I * (t : ℂ)) - (highMidpointPhase t).val‖ ≤
      (highMidpointPhaseRadius t : ℝ) := by
  let Z := midpointPhaseBox t
  let z := Complex.exp (5 * Complex.I * (t : ℂ))
  have h : Analysis.complexIntervalContains Z.1 Z.2 midpointPhaseScale z :=
    midpoint_phase_contains t ht
  have hd (I : Analysis.IntegerInterval) {x : ℝ} (hx : I.Contains midpointPhaseScale x) :
    |x - (I.lower : ℝ) / (midpointPhaseScale : ℤ)| ≤
      ((I.upper : ℝ) - (I.lower : ℝ)) / (midpointPhaseScale : ℤ) := by
    rw [abs_of_nonneg (sub_nonneg.mpr hx.1), sub_div]
    exact sub_le_sub_right hx.2 _
  refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
  simpa only [z, Z, highMidpointPhase, highMidpointPhaseRadius, midpointPhaseCorner,
    midpointPhaseWidth, Analysis.RatComplex.val, Complex.sub_re, Complex.sub_im, Rat.cast_add,
    Rat.cast_sub, Rat.cast_div, Rat.cast_intCast, Int.cast_sub] using
    add_le_add (hd Z.1 h.1) (hd Z.2 h.2)

/-- A rational lower approximation to the real exponential scale of the centered moment. -/
public def highMidpointExp (K : HighGaussianKernel) : ℚ :=
  Analysis.gammaExpTaylorLower (5 * K.pole) 64

/-- The Taylor upper and lower enclosures give an explicit rational error. -/
public def highMidpointExpRadius (K : HighGaussianKernel) : ℚ :=
  headExpUpper (5 * K.pole) 64 - highMidpointExp K

/-- Both high kernels satisfy the geometric Taylor remainder condition. -/
private theorem high_midpoint_exp_inputs (K : HighGaussianKernel) :
    0 ≤ 5 * K.pole ∧ 5 * K.pole / ((64 + 1 : ℕ) : ℚ) ≤ 1 / 2 := by cases K <;> decide +kernel

/-- The real exponential is at a certified rational distance from its lower approximation. -/
public theorem high_midpoint_exp_error (K : HighGaussianKernel) :
    |Real.exp (-(5 * (K.pole : ℝ))) - (highMidpointExp K : ℝ)| ≤ (highMidpointExpRadius K : ℝ) := by
  obtain ⟨hlo, htail⟩ := high_midpoint_exp_inputs K
  have hl := Analysis.gamma_exp_taylor_lower_valid hlo htail
  have hu := head_exp_upper_sound hlo 64
  simp only [Rat.cast_mul, Rat.cast_ofNat] at hl hu
  rw [highMidpointExpRadius, Rat.cast_sub, highMidpointExp, abs_of_nonneg (sub_nonneg.mpr hl)]
  exact sub_le_sub_right hu _

/-- The two computed exponentials supply both errors for the midpoint norm calculation. -/
public theorem high_midpoint_computed_le (K : HighGaussianKernel) (t : ℚ) (ht : |t| ≤ 100) :
    let A := highMidpointSquareRat K t
    let B := highMidpointMomentRat K t
    let C :=
      ((highMidpointPhase t).mul A).add ((Analysis.RatComplex.real (4 * highMidpointExp K)).mul B)
    ‖highPrincipalMultiplier K (t : ℝ)‖ ≤
      ‖C.val‖ + (highMidpointPhaseRadius t : ℝ) * ‖A.val‖ +
        4 * (highMidpointExpRadius K : ℝ) * ‖B.val‖ := by
  exact
    high_midpoint_enclosure K t (highMidpointExp K) (highMidpointPhase t)
      (high_midpoint_phase_error t ht) (high_midpoint_exp_error K)

/-- Every certified midpoint lies inside the height range of the phase evaluator. -/
public theorem high_zero_midpoint_phase_range (i : Fin 29) : |highZeroBracketMid i| ≤ 100 := by
  exact (by decide +kernel : ∀ j : Fin 29, |highZeroBracketMid j| ≤ 100) i

/-- Combine the rational midpoint values before checking their squared norm. -/
public def highMidpointCombined (K : HighGaussianKernel) (t : ℚ) : Analysis.RatComplex :=
  ((highMidpointPhase t).mul (highMidpointSquareRat K t)).add
    ((Analysis.RatComplex.real (4 * highMidpointExp K)).mul (highMidpointMomentRat K t))

/-- Three squared-norm comparisons certify a rational upper bound for one midpoint. -/
public theorem high_zero_midpoint_of_squares (K : HighGaussianKernel) (i : Fin 29) {a b c : ℚ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hA : (highMidpointSquareRat K (highZeroBracketMid i)).normSq ≤ a ^ 2)
    (hB : (highMidpointMomentRat K (highZeroBracketMid i)).normSq ≤ b ^ 2)
    (hC : (highMidpointCombined K (highZeroBracketMid i)).normSq ≤ c ^ 2) :
    ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖ ≤
      ((c + highMidpointPhaseRadius (highZeroBracketMid i) * a + 4 * highMidpointExpRadius K * b :
          ℚ) :
        ℝ) := by
  let t := highZeroBracketMid i
  have ht := high_zero_midpoint_phase_range i
  have hp := (norm_nonneg _).trans (high_midpoint_phase_error t ht)
  have he := (abs_nonneg _).trans (high_midpoint_exp_error K)
  refine (high_midpoint_computed_le K t ht).trans ?_
  simp only [Rat.cast_add, Rat.cast_mul, Rat.cast_ofNat]
  exact
    add_le_add
      (add_le_add (Analysis.RatComplex.val_norm_le _ hc hC)
        (mul_le_mul_of_nonneg_left (Analysis.RatComplex.val_norm_le _ ha hA) hp))
      (mul_le_mul_of_nonneg_left (Analysis.RatComplex.val_norm_le _ hb hB)
        (mul_nonneg (by norm_num only) he))

/-- The real exponential scale is enclosed to twenty decimal places for both kernels. -/
public theorem high_midpoint_exp_radius_le (K : HighGaussianKernel) :
    highMidpointExpRadius K ≤ 1 / 10 ^ 20 := by cases K <;> decide +kernel

/-- Complex midpoint values and the phase radius used by the integer norm evaluator. -/
private structure MidpointNormData where
  square : HornerFraction
  moment : HornerFraction
  combined : HornerFraction
  radius : ℚ

/-- Compute each complex value with an unreduced common denominator. -/
private def midpointNormRow (K : HighGaussianKernel) (cf : Array ℚ) (t : ℚ) : MidpointNormData :=
  let A := hornerFraction (highMidpointSquareRat K t)
  let B := midpointMomentFraction K cf t
  let Z := midpointPhaseBox t
  let P := hornerFraction (midpointPhaseCorner Z)
  let E := hornerFraction (Analysis.RatComplex.real (4 * highMidpointExp K))
  ⟨A, B, (P.mul A).add (E.mul B), midpointPhaseWidth Z⟩

/-- Prepare one coefficient array for the 29 midpoint evaluations. -/
private def midpointNormTable (K : HighGaussianKernel) : Array MidpointNormData :=
  let cf := midpointMomentCoeffs K
  Array.ofFn fun i : Fin 29 ↦ midpointNormRow K cf (highZeroBracketMid i)

/-- The table lookup returns the row at the chosen midpoint. -/
private theorem midpoint_norm_at (K : HighGaussianKernel) (i : Fin 29) :
    (midpointNormTable K)[i.val]? =
      some (midpointNormRow K (midpointMomentCoeffs K) (highZeroBracketMid i)) := by
  simp only [midpointNormTable, Array.getElem?_ofFn, Fin.isLt, dite_true]

/-- Return a decimal upper bound on the norm without normalizing the complex coordinates. -/
private def roundedFractionNorm (a : HornerFraction) : ℚ :=
  let s : ℕ := 10 ^ 10
  let n := (a.re ^ 2 + a.im ^ 2).natAbs
  (Nat.succ (Nat.sqrt (n * s ^ 2 / a.den ^ 2)) : ℚ) / (s : ℚ)

/-- The integer square-root calculation bounds the quadratic norm of the represented value. -/
private theorem rounded_fraction_spec (a : HornerFraction) (ha : a.den ≠ 0) :
    0 ≤ roundedFractionNorm a ∧ a.value.normSq ≤ roundedFractionNorm a ^ 2 := by
  let s : ℕ := 10 ^ 10
  let n := (a.re ^ 2 + a.im ^ 2).natAbs
  let m := Nat.succ (Nat.sqrt (n * s ^ 2 / a.den ^ 2))
  have hd := Nat.pos_of_ne_zero ha
  have hs : (0 : ℚ) < (s : ℚ) := by
    norm_num only [s, Nat.cast_pow, Nat.cast_ofNat, pow_pos, Nat.ofNat_pos]
  have h := (Nat.div_lt_iff_lt_mul (pow_pos hd 2)).mp (Nat.lt_succ_sqrt' (n * s ^ 2 / a.den ^ 2))
  have hc : (n : ℚ) * (s : ℚ) ^ 2 < (m : ℚ) ^ 2 * (a.den : ℚ) ^ 2 := by exact_mod_cast h
  have hn : (n : ℚ) = (a.re : ℚ) ^ 2 + (a.im : ℚ) ^ 2 := by
    rw [← Rat.intCast_natCast, Int.natAbs_of_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _))]
    simp only [Int.cast_add, Int.cast_pow]
  change 0 ≤ (m : ℚ) / (s : ℚ) ∧ a.value.normSq ≤ ((m : ℚ) / (s : ℚ)) ^ 2
  refine ⟨div_nonneg (Nat.cast_nonneg _) hs.le, ?_⟩
  simp only [HornerFraction.value, Analysis.RatComplex.normSq, div_pow, ← add_div, ← hn]
  rw [le_div_iff₀ (pow_pos hs 2), div_mul_eq_mul_div, div_le_iff₀ (pow_pos (Nat.cast_pos.mpr hd) 2)]
  exact hc.le

/-- Convert a row into a rational upper bound including both enclosure errors. -/
private def midpointNormUpper (K : HighGaussianKernel) (row : MidpointNormData) : ℚ :=
  roundedFractionNorm row.combined + row.radius * roundedFractionNorm row.square +
    4 * highMidpointExpRadius K * roundedFractionNorm row.moment

/-- The integer bounds on the three squared norms certify the analytic midpoint estimate. -/
private theorem high_midpoint_le_rounded (K : HighGaussianKernel) (i : Fin 29) :
    ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖ ≤
      (midpointNormUpper K (midpointNormRow K (midpointMomentCoeffs K) (highZeroBracketMid i)) :
        ℝ) := by
  let t := highZeroBracketMid i
  let cf := midpointMomentCoeffs K
  let row := midpointNormRow K cf t
  have hA := horner_fraction_den (highMidpointSquareRat K t)
  have hB := midpoint_moment_fraction_den K cf t
  have hP := horner_fraction_den (highMidpointPhase t)
  have hE := horner_fraction_den (Analysis.RatComplex.real (4 * highMidpointExp K))
  have hC : row.combined.den ≠ 0 := Nat.mul_ne_zero (Nat.mul_ne_zero hP hA) (Nat.mul_ne_zero hE hB)
  have a := rounded_fraction_spec row.square hA
  have b := rounded_fraction_spec row.moment hB
  have c := rounded_fraction_spec row.combined hC
  have hCv : row.combined.value = highMidpointCombined K t := by
    let PA :=
      (hornerFraction (highMidpointPhase t)).mul (hornerFraction (highMidpointSquareRat K t))
    let EB :=
      (hornerFraction (Analysis.RatComplex.real (4 * highMidpointExp K))).mul
        (midpointMomentFraction K cf t)
    change (PA.add EB).value = highMidpointCombined K t
    rw [horner_fraction_add_value PA EB (Nat.mul_ne_zero hP hA) (Nat.mul_ne_zero hE hB)]
    simp only [PA, EB, horner_fraction_mul_value, horner_fraction_value,
      midpoint_moment_fraction_value, highMidpointCombined, highMidpointMomentRat, cf]
  rw [hCv] at c
  have ha : row.square.value = highMidpointSquareRat K t := horner_fraction_value _
  have hb : row.moment.value = highMidpointMomentRat K t := midpoint_moment_fraction_value K cf t
  rw [ha] at a
  rw [hb] at b
  exact high_zero_midpoint_of_squares K i a.1 b.1 c.1 a.2 b.2 c.2

/-- Read an upper bound from a row, with zero for a missing entry. -/
private def midpointLookupUpper (K : HighGaussianKernel) (o : Option MidpointNormData) : ℚ :=
  match o with
  | none => 0
  | some row => midpointNormUpper K row

/-- Sum the rational upper bounds for the 29 certified midpoints. -/
public def highMidpointNormSum (K : HighGaussianKernel) : ℚ :=
  let rows := midpointNormTable K
  (List.ofFn fun i : Fin 29 ↦ midpointLookupUpper K rows[i.val]?).sum

/-- Sum bounds supplied by the entries of an abstract rational table. -/
private theorem midpoint_sum_of_rows (K : HighGaussianKernel) (rows : Array MidpointNormData)
    (h :
      ∀ i : Fin 29,
        ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖ ≤
          (midpointLookupUpper K rows[i.val]? : ℚ)) :
    (∑ i : Fin 29, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) ≤
      ((List.ofFn fun i : Fin 29 ↦ midpointLookupUpper K rows[i.val]?).sum : ℝ) := by
  rw [List.sum_ofFn, Rat.cast_sum]
  exact Finset.sum_le_sum fun i _ ↦ h i

/-- Transport the bound through a successful lookup in the table. -/
private theorem midpoint_bound_of_lookup (K : HighGaussianKernel) {x : ℝ} {row : MidpointNormData}
    {o : Option MidpointNormData} (hr : o = some row) (h : x ≤ (midpointNormUpper K row : ℝ)) :
    x ≤ (midpointLookupUpper K o : ℝ) := by
  cases hr
  exact h

/-- The total midpoint contribution is bounded by the computed rational sum. -/
public theorem high_midpoint_sum_le (K : HighGaussianKernel) :
    (∑ i : Fin 29, ‖highPrincipalMultiplier K (highZeroBracketMid i : ℝ)‖) ≤
      (highMidpointNormSum K : ℝ) := by
  exact
    midpoint_sum_of_rows K (midpointNormTable K) fun i ↦
      midpoint_bound_of_lookup K (midpoint_norm_at K i) (high_midpoint_le_rounded K i)

end PseudoPrime.PrimeTestBounds.MillerRabin
