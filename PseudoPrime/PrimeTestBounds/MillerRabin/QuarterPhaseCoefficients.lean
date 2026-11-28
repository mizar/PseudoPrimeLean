/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPhaseTruncation
import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterZetaLedger
public import PseudoPrime.Analysis.ComputedComplexInverse
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import all PseudoPrime.AnalyticNumberTheory.RiemannZeta.LowZero100Bounds
import PseudoPrime.Analysis.ExponentialFixedPointBounds
import PseudoPrime.Analysis.ComputedPhaseCell
import PseudoPrime.Analysis.LogTaylorBounds
import Mathlib.Data.Fin.VecNotation
import all PseudoPrime.PrimeTestBounds.MillerRabin.QuarterPrincipal600

/-! # Rectangular certificates for the sixth-pole phase coefficients -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Evaluate the rational numerator divided by the sixth power in Horner form
at the reciprocal argument. This avoids computing an interval for `s^6`
before taking its complex inverse. -/
theorem section104_num_inv_horner {s : ℂ} (hs : s ≠ 0) :
    section104Numerator s / s ^ 6 =
      let v := s⁻¹
      v *
        (-(17018288 / 78125) +
          v *
            (-(872592 / 3125) +
              v * (-(151312 / 625) + v * (-(11424 / 125) + v * (1368 / 25 + v * (312 / 5)))))) := by
  dsimp only [section104Numerator]
  field_simp [hs]
  ring

/-- A computed rectangle for the pole coefficient, using the inverse of
the input box for the shifted critical-line argument. -/
def section99PoleBox (G : ℤ) (Q : Analysis.IntegerInterval × Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  let W := Analysis.roundedComplexPow6 G (Analysis.roundedComplexInv G Q)
  let A := Analysis.roundedConstant G (51 ^ 5) (50 ^ 5)
  (Analysis.roundedProduct G A W.1, Analysis.roundedProduct G A W.2)

/-- The computed pole coefficient encloses the coefficient throughout the
ordinate box. The denominator check applies to the shifted argument. -/
theorem section99_pole_box_contains {G : ℤ}
    {Q : Analysis.IntegerInterval × Analysis.IntegerInterval} {t : ℝ} (hg : 0 < G)
    (hq : Analysis.complexIntervalContains Q.1 Q.2 G ((51 / 50 : ℂ) + (t : ℂ) * Complex.I))
    (hd : 0 < (Analysis.complexNormSqInterval G Q).lower) :
    Analysis.complexIntervalContains (section99PoleBox G Q).1 (section99PoleBox G Q).2 G
      (section99PoleCoeff t) := by
  have hw := Analysis.roundedComplexPow6_contains hg (Analysis.roundedComplexInv_contains hg hq hd)
  have ha := Analysis.roundedConstant_contains (p := (51 ^ 5)) (d := (50 ^ 5)) hg (by decide)
  have hA : (Analysis.roundedConstant G (51 ^ 5) (50 ^ 5)).Contains G ((51 / 50 : ℝ) ^ 5) := by
    rw [div_pow]
    simpa only [Int.cast_pow, Int.cast_ofNat] using ha
  unfold section99PoleCoeff
  rw [div_eq_mul_inv, ← inv_pow]
  rw [show (51 / 50 : ℂ) ^ 5 = (((51 / 50 : ℝ) ^ 5 : ℝ) : ℂ) by
      simp only [Complex.ofReal_pow, Complex.ofReal_div, Complex.ofReal_ofNat]]
  constructor
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact Analysis.roundedProduct_contains hg hA hw.1
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact Analysis.roundedProduct_contains hg hA hw.2

/-- Evaluate a polynomial with rational real coefficients at a complex input
by Horner's rule. The list starts with the constant coefficient. -/
private noncomputable def hornerValue (z : ℂ) : List (ℤ × ℤ) → ℂ
  | [] => 0
  | (n, d) :: cs => (((n : ℝ) / d : ℝ) : ℂ) + z * hornerValue z cs

/-- Evaluate the same Horner expression with outward-rounded complex products
and real rational constants at a fixed positive integer scale. -/
def hornerBox (G : ℤ) (Q : Analysis.IntegerInterval × Analysis.IntegerInterval) :
    List (ℤ × ℤ) → Analysis.IntegerInterval × Analysis.IntegerInterval
  | [] => (⟨0, 0⟩, ⟨0, 0⟩)
  | (n, d) :: cs =>
      let T := Analysis.roundedComplexProduct G Q (hornerBox G Q cs)
      ((Analysis.roundedConstant G n d).add T.1, T.2)

/-- The Horner enclosure is sound for a contained input and a list of
rational coefficients with positive denominators. -/
private theorem hornerBox_contains {G : ℤ} {Q : Analysis.IntegerInterval × Analysis.IntegerInterval}
    {z : ℂ} (hg : 0 < G) (hz : Analysis.complexIntervalContains Q.1 Q.2 G z) (cs : List (ℤ × ℤ))
    (hd : ∀ p ∈ cs, 0 < p.2) :
    Analysis.complexIntervalContains (hornerBox G Q cs).1 (hornerBox G Q cs).2 G
      (hornerValue z cs) := by
  induction cs with
  | nil =>
    constructor <;>
      simp only [hornerBox, hornerValue, Analysis.IntegerInterval.Contains, Int.cast_zero, zero_div,
        Complex.zero_re, Complex.zero_im, le_refl, and_self]
  | cons p cs ih =>
    obtain ⟨n, d⟩ := p
    have hc := Analysis.roundedConstant_contains (p := n) hg (hd (n, d) List.mem_cons_self)
    have ht :=
      Analysis.roundedComplexProduct_contains hg hz
        (ih (fun q hq ↦ hd q (List.mem_cons_of_mem _ hq)))
    constructor
    · simpa only [hornerBox, hornerValue, Complex.add_re, Complex.ofReal_re] using
        Analysis.IntegerInterval.add_contains hc ht.1
    · simpa only [hornerBox, hornerValue, Complex.add_im, Complex.ofReal_im, zero_add] using ht.2

/-- Coefficients of the inverse-argument numerator, including its zero
constant term. They are shared across all zero ordinates. -/
def section99RatHorner : List (ℤ × ℤ) :=
  [(0, 1), (-17018288, 78125), (-872592, 3125), (-151312, 625), (-11424, 125), (1368, 25), (312, 5)]

/-- The inverse-argument evaluation gives exactly the numerator divided by
the sixth power in the rational phase coefficient. -/
private theorem section99_horner_eq {s : ℂ} (hs : s ≠ 0) :
    hornerValue s⁻¹ section99RatHorner = section104Numerator s / s ^ 6 := by
  rw [section104_num_inv_horner hs]
  norm_num only [section99RatHorner, hornerValue, Int.cast_zero, Int.cast_one, Int.cast_ofNat,
    Int.cast_neg, Complex.ofReal_div, Complex.ofReal_neg, Complex.ofReal_zero, Complex.ofReal_one,
    Complex.ofReal_ofNat, zero_div, zero_add, mul_zero, add_zero, div_one]

/-- Enclose the rational coefficient by inverting the two arguments,
evaluating the fixed Horner polynomial, and scaling the product by four
times the real kernel constant. -/
def section99RatBox (G : ℤ) (C : Analysis.IntegerInterval)
    (P Q : Analysis.IntegerInterval × Analysis.IntegerInterval) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  let V := hornerBox G (Analysis.roundedComplexInv G Q) section99RatHorner
  let W := Analysis.roundedComplexProduct G (Analysis.roundedComplexInv G P) V
  (Analysis.roundedProduct G C W.1, Analysis.roundedProduct G C W.2)

/-- The computed rational coefficient encloses the kernel coefficient on
the given critical-line rectangle. The only nonrational input is an interval
for four times the kernel's real normalization constant. -/
theorem section99_rat_box_contains {G : ℤ} {C : Analysis.IntegerInterval}
    {P Q : Analysis.IntegerInterval × Analysis.IntegerInterval} {t : ℝ} (hg : 0 < G)
    (hc : C.Contains G (4 * (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120))))
    (hp : Analysis.complexIntervalContains P.1 P.2 G ((1 / 2 : ℂ) + (t : ℂ) * Complex.I))
    (hq : Analysis.complexIntervalContains Q.1 Q.2 G ((51 / 50 : ℂ) + (t : ℂ) * Complex.I))
    (hdp : 0 < (Analysis.complexNormSqInterval G P).lower)
    (hdq : 0 < (Analysis.complexNormSqInterval G Q).lower) :
    Analysis.complexIntervalContains (section99RatBox G C P Q).1 (section99RatBox G C P Q).2 G
      (section99RatCoeff t) := by
  let s := (51 / 50 : ℂ) + (t : ℂ) * Complex.I
  let p := (1 / 2 : ℂ) + (t : ℂ) * Complex.I
  have hs : s ≠ 0 := by
    intro h
    have he := congrArg Complex.re h
    dsimp only [s] at he
    rw [← Complex.ofReal_ofNat (n := 51), ← Complex.ofReal_ofNat (n := 50), ←
      Complex.ofReal_div] at he
    norm_num only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, mul_zero, zero_mul, sub_zero, add_zero, Complex.zero_re] at he
  have hV :=
    hornerBox_contains hg (Analysis.roundedComplexInv_contains hg hq hdq) section99RatHorner
      (by decide)
  change Analysis.complexIntervalContains _ _ G (hornerValue s⁻¹ section99RatHorner) at hV
  rw [section99_horner_eq hs] at hV
  have hW :=
    Analysis.roundedComplexProduct_contains hg (Analysis.roundedComplexInv_contains hg hp hdp) hV
  have he :
    section99RatCoeff t =
      ((4 * (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120)) : ℝ) : ℂ) *
        (p⁻¹ * (section104Numerator s / s ^ 6)) := by
    dsimp only [section99RatCoeff, s, p]
    rw [Complex.ofReal_mul, Complex.ofReal_ofNat]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [he]
  constructor
  · rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    exact Analysis.roundedProduct_contains hg hc hW.1
  · rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    exact Analysis.roundedProduct_contains hg hc hW.2

/-- The fixed normalization interval for four times the real kernel factor.
The two endpoints are rounded outward at scale one trillion. -/
private theorem section99_scale_box :
    (⟨2116092089, 2116092091⟩ : Analysis.IntegerInterval).Contains 1000000000000
      (4 * (Real.exp (-(14 / 5 * (51 / 50))) / ((50 / 51) ^ 5 * 120))) := by
  have ht :=
    Analysis.exp_le_taylor_add_two_next (x := (357 / 125 : ℝ)) (n := 24) (by norm_num only)
      (by norm_num only)
  have hb := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 357 / 125) 22
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht hb
  have hl := one_div_le_one_div_of_le (Real.exp_pos _) ht
  have hu := one_div_le_one_div_of_le (by norm_num only) hb
  unfold Analysis.IntegerInterval.Contains
  rw [show -(14 / 5 * (51 / 50)) = -(357 / 125 : ℝ) by norm_num only, Real.exp_neg, ← one_div]
  norm_num only [Int.cast_ofNat]
  constructor <;> linarith only [hl, hu]

/-- The lower and upper endpoints enclose the complete certified ordinate
bracket at the common integer scale. -/
private def section99OrdinateBox (i : Fin 29) : Analysis.IntegerInterval :=
  let L := AnalyticNumberTheory.RiemannZeta.lowZero100Lower i
  let U := L + 1 / 100
  ⟨(Analysis.roundedConstant 1000000000000 L.num L.den).lower,
    (Analysis.roundedConstant 1000000000000 U.num U.den).upper⟩

/-- The fixed-point box contains any ordinate satisfying both ledger brackets. -/
private theorem section99_ordinate_box {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    (section99OrdinateBox i).Contains 1000000000000 (g i) := by
  let L := AnalyticNumberTheory.RiemannZeta.lowZero100Lower i
  let U : ℚ := L + 1 / 100
  have hb (x : ℚ) :
    (Analysis.roundedConstant 1000000000000 x.num x.den).Contains 1000000000000 (x : ℝ) := by
    rw [Rat.cast_def]
    have hd : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
    simpa only [Int.cast_natCast] using
      Analysis.roundedConstant_contains (G := 1000000000000) (p := x.num) (d := (x.den : ℤ))
        (by decide) hd
  have hU : g i ≤ (U : ℝ) := by
    simpa only [U, L, Rat.cast_add, Rat.cast_div, Rat.cast_ofNat, Rat.cast_one] using hu i
  exact ⟨(hb L).1.trans (hl i), hU.trans (hb U).2⟩

/-- Use the same ordinate interval for the critical-line and shifted arguments. -/
private def section99InputBox (i : Fin 29) (n d : ℤ) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  (Analysis.roundedConstant 1000000000000 n d, section99OrdinateBox i)

/-- The rectangular input for a rational real part contains the corresponding
vertical complex argument at any ordinate in its certified interval. -/
private theorem section99_input_box {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) {n d : ℤ}
    (hd : 0 < d) :
    Analysis.complexIntervalContains (section99InputBox i n d).1 (section99InputBox i n d).2
      1000000000000 ((((n : ℝ) / d : ℝ) : ℂ) + (g i : ℂ) * Complex.I) := by
  constructor
  · simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, Complex.I_re,
      mul_zero, zero_mul, sub_zero, add_zero]
    exact Analysis.roundedConstant_contains (by decide) hd
  · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re, Complex.I_im,
      Complex.I_re, mul_one, zero_mul, add_zero, zero_add]
    exact section99_ordinate_box hl hu i

/-- The denominator positivity checks for both arguments are shared by
all endpoint evaluations. -/
private theorem section99_input_positive :
    ∀ i : Fin 29,
      0 < (Analysis.complexNormSqInterval 1000000000000 (section99InputBox i 1 2)).lower ∧
        0 < (Analysis.complexNormSqInterval 1000000000000 (section99InputBox i 51 50)).lower := by
  decide +kernel

/-- A rectangle for the rational part of the phase at the indexed ordinate. -/
private def section99RatRow (i : Fin 29) : Analysis.IntegerInterval × Analysis.IntegerInterval :=
  section99RatBox 1000000000000 ⟨2116092089, 2116092091⟩ (section99InputBox i 1 2)
    (section99InputBox i 51 50)

/-- A rectangle for the pole part of the phase at the indexed ordinate. -/
private def section99PoleRow (i : Fin 29) : Analysis.IntegerInterval × Analysis.IntegerInterval :=
  section99PoleBox 1000000000000 (section99InputBox i 51 50)

/-- Both computed coefficient rectangles contain the actual complex
coefficients simultaneously for every ordinate in its ledger bracket. -/
private theorem section99_coeff_rows {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (i : Fin 29) :
    Analysis.complexIntervalContains (section99RatRow i).1 (section99RatRow i).2 1000000000000
        (section99RatCoeff (g i)) ∧
      Analysis.complexIntervalContains (section99PoleRow i).1 (section99PoleRow i).2 1000000000000
        (section99PoleCoeff (g i)) := by
  have hp := section99_input_box hl hu i (n := 1) (d := 2) (by decide)
  have hq := section99_input_box hl hu i (n := 51) (d := 50) (by decide)
  norm_num only [Int.cast_one, Int.cast_ofNat, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat] at hp hq
  have hn := section99_input_positive i
  exact
    ⟨section99_rat_box_contains (by decide) section99_scale_box hp hq hn.1 hn.2,
      section99_pole_box_contains (by decide) hq hn.2⟩

/-- Select the unshifted or shifted coefficient enclosure for an ordinate. -/
private def section99PhaseRow (j : Fin 29 × Fin 2) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  if j.2 = 0 then section99RatRow j.1 else section99PoleRow j.1

/-- The real weight used in the curvature calculation is bounded by
the larger of the absolute interval endpoints at the fixed scale. -/
private theorem section99_abs_of_box {x : ℝ} {Q : Analysis.IntegerInterval}
    (h : Q.Contains 1000000000000 x) :
    |x| ≤ ((max (-Q.lower) Q.upper : ℤ) : ℝ) / 1000000000000 := by
  apply abs_le.mpr
  constructor
  · have hh : (-Q.lower : ℤ) ≤ max (-Q.lower) Q.upper := le_max_left _ _
    have ht : (-(Q.lower : ℝ)) ≤ (max (-Q.lower) Q.upper : ℤ) := by exact_mod_cast hh
    have hd := div_le_div_of_nonneg_right ht (by norm_num only : (0 : ℝ) ≤ 1000000000000)
    rw [neg_div] at hd
    linarith only [hd, h.1]
  · exact
      h.2.trans (div_le_div_of_nonneg_right (Int.cast_le.mpr (le_max_right _ _)) (by norm_num only))

/-- Integer numerator of a curvature contribution at the cubed scale.
Both coordinate caps include the conjugate-pair factor of two. -/
private def section99CurvatureTicks (j : Fin 29 × Fin 2) : ℤ :=
  let Q := section99PhaseRow j
  (section99OrdinateBox j.1).upper ^ 2 *
    (2 * (max (-Q.1.lower) Q.1.upper + max (-Q.2.lower) Q.2.upper))

/-- The finite integer evaluation of the curvature cap uses the same
coefficient rectangles as the phase endpoint checks. -/
private theorem section99_curvature_ticks :
    (∑ j : Fin 29 × Fin 2, section99CurvatureTicks j) ≤ 27 * 1000000000000 ^ 3 := by decide +kernel

/-- The certified coefficient rectangles bound the curvature of the
complete low-phase sum uniformly for every ordinate in its ledger interval. -/
theorem quarter_phase_curvature_27 {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (hp : ∀ i, 0 ≤ g i) :
    (∑ j : Fin 29 × Fin 2,
        (g j.1) ^ 2 * (|(quarterLowPhaseCoeff g j).re| + |(quarterLowPhaseCoeff g j).im|)) ≤
      27 := by
  have hsum :
    (∑ j : Fin 29 × Fin 2,
        (g j.1) ^ 2 * (|(quarterLowPhaseCoeff g j).re| + |(quarterLowPhaseCoeff g j).im|)) ≤
      ∑ j : Fin 29 × Fin 2, (section99CurvatureTicks j : ℝ) / 1000000000000 ^ 3 := by
    apply Finset.sum_le_sum
    intro j _
    let Q := section99PhaseRow j
    let z := if j.2 = 0 then section99RatCoeff (g j.1) else section99PoleCoeff (g j.1)
    have hz : Analysis.complexIntervalContains Q.1 Q.2 1000000000000 z := by
      by_cases h : j.2 = 0
      · simpa only [Q, z, section99PhaseRow, ite_eq_left h] using (section99_coeff_rows hl hu j.1).1
      · simpa only [Q, z, section99PhaseRow, ite_eq_right h] using
          (section99_coeff_rows hl hu j.1).2
    have hA := section99_abs_of_box hz.1
    have hB := section99_abs_of_box hz.2
    have hAB := mul_le_mul_of_nonneg_left (add_le_add hA hB) (by norm_num only : (0 : ℝ) ≤ 2)
    have hg := (section99_ordinate_box hl hu j.1).2
    have hgg := pow_le_pow_left₀ (hp j.1) hg 2
    have hc :
      |(quarterLowPhaseCoeff g j).re| + |(quarterLowPhaseCoeff g j).im| =
        2 * (|z.re| + |z.im|) := by
      change |((2 : ℂ) * z).re| + |((2 : ℂ) * z).im| = _
      rw [← Complex.ofReal_ofNat]
      simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul,
        sub_zero, add_zero, abs_mul, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
      ring
    rw [hc]
    apply
      le_trans
        (mul_le_mul hgg hAB
          (mul_nonneg (by norm_num only) (add_nonneg (abs_nonneg _) (abs_nonneg _))) (sq_nonneg _))
    apply le_of_eq
    dsimp only [section99CurvatureTicks, Q]
    norm_num only [Int.cast_mul, Int.cast_add, Int.cast_pow, Int.cast_ofNat]
    ring
  have hN :
    ((∑ j : Fin 29 × Fin 2, section99CurvatureTicks j : ℤ) : ℝ) ≤ 27 * 1000000000000 ^ 3 := by
    exact_mod_cast section99_curvature_ticks
  apply hsum.trans
  rw [← Finset.sum_div, ← Int.cast_sum]
  exact (div_le_iff₀ (by norm_num only)).mpr hN

/-- Bounds for the two low-phase endpoint sums transfer across every positive
radius interval with the certified curvature loss. -/
theorem quarter_phase_lower_27 {g : Fin 29 → ℝ}
    (hgL : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hgU : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (hp : ∀ i, 0 ≤ g i)
    {l r u L U : ℝ} (hl : 0 < l) (hr : r ∈ Set.Icc l u) (hL : L ≤ quarterLowPhase g l)
    (hU : U ≤ quarterLowPhase g u) :
    min L U - 27 * (u - l) ^ 2 / (2 * l ^ 2) ≤ quarterLowPhase g r := by
  have hs := quarter_phase_curvature_27 hgL hgU hp
  simpa only [sq_abs] using
    quarter_low_phase_interval g (fun i ↦ |g i|) (fun j ↦ |(quarterLowPhaseCoeff g j).re|)
      (fun j ↦ |(quarterLowPhaseCoeff g j).im|) hl hr (fun _ ↦ le_rfl) (fun _ ↦ le_rfl)
      (fun _ ↦ le_rfl)
      (show
        (∑ j : Fin 29 × Fin 2,
            |g j.1| ^ 2 * (|(quarterLowPhaseCoeff g j).re| + |(quarterLowPhaseCoeff g j).im|)) ≤
          27
        by simpa only [sq_abs] using hs)
      hL hU

/-- The six radii at the ends of the five compressed comparisons. -/
private def section99Endpoint (e : Fin 6) : ℚ :=
  ![313, 1568 / 5, 314, 6289 / 20, 315, 316] e

/-- Outward fixed-point logarithm bounds for the six endpoint radii. -/
private def section99LogBox (e : Fin 6) : Analysis.IntegerInterval :=
  let l : ℤ :=
    ![5746203190540, 5748118288476, 5749392985908, 5750825080989, 5752572638825, 5755742213586] e
  ⟨l - 3000, l + 3000⟩

/-- The logarithm bounds follow from the shared rational logarithm checker. -/
private theorem section99_log_box (e : Fin 6) :
    (section99LogBox e).Contains 1000000000000 (Real.log (section99Endpoint e : ℝ)) := by
  have h :
    ∀ e : Fin 6,
      Analysis.rationalLogIntervalCheck (section99Endpoint e) 8 32
          ((section99LogBox e).lower / (1000000000000 : ℚ))
          ((section99LogBox e).upper / (1000000000000 : ℚ)) =
        true := by
    decide +kernel
  simpa only [Analysis.IntegerInterval.Contains, Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat,
    Int.cast_ofNat] using Analysis.rationalLogIntervalCheck_sound (h e)

/-- Form an angle interval from the ordinate bracket, endpoint logarithm, and
one of the two phase shifts. -/
private def section99AngleBox (e : Fin 6) (j : Fin 29 × Fin 2) : Analysis.IntegerInterval :=
  let L := section99LogBox e
  let T :=
    if j.2 = 0 then (⟨0, 0⟩ : Analysis.IntegerInterval)
    else Analysis.roundedConstant 1000000000000 14 5
  Analysis.roundedProduct 1000000000000 (section99OrdinateBox j.1) ((L.add L).add T)

/-- The computed angle contains the exact phase argument for every allowed ordinate. -/
private theorem section99_angle_box {g : Fin 29 → ℝ}
    (hgL : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hgU : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (e : Fin 6)
    (j : Fin 29 × Fin 2) :
    (section99AngleBox e j).Contains 1000000000000
      (g j.1 * (2 * Real.log (section99Endpoint e : ℝ) + quarterLowPhaseShift j)) := by
  have ht :
    (if j.2 = 0 then (⟨0, 0⟩ : Analysis.IntegerInterval)
        else Analysis.roundedConstant 1000000000000 14 5).Contains
      1000000000000 (quarterLowPhaseShift j) := by
    by_cases h : j.2 = 0
    · simp only [ite_eq_left h, quarterLowPhaseShift, Analysis.IntegerInterval.Contains,
        Int.cast_zero, zero_div, le_refl, and_self]
    · simpa only [ite_eq_right h, quarterLowPhaseShift, Int.cast_ofNat] using
        Analysis.roundedConstant_contains (G := 1000000000000) (p := 14) (d := 5) (by decide)
          (by decide)
  have hL := section99_log_box e
  rw [two_mul]
  exact
    Analysis.roundedProduct_contains (by decide) (section99_ordinate_box hgL hgU j.1)
      (Analysis.IntegerInterval.add_contains (Analysis.IntegerInterval.add_contains hL hL) ht)

/-- Center the angle interval on a fixed-point midpoint. -/
private def section99AngleCenter (e : Fin 6) (j : Fin 29 × Fin 2) : ℤ :=
  ((section99AngleBox e j).lower + (section99AngleBox e j).upper) / 2

/-- The signed displacement interval relative to that midpoint. -/
private def section99AngleDelta (e : Fin 6) (j : Fin 29 × Fin 2) : Analysis.IntegerInterval :=
  (section99AngleBox e j).add ⟨-section99AngleCenter e j, -section99AngleCenter e j⟩

/-- The Taylor argument is small and the displacement fits the common error
radius. Both checks are exact integer comparisons over the six endpoint rows. -/
private theorem section99_phase_guards :
    ∀ (e : Fin 6) (j : Fin 29 × Fin 2),
      |section99AngleCenter e j| ≤ 2048000000000000 ∧
        -73000000000 ≤ (section99AngleDelta e j).lower ∧
        (section99AngleDelta e j).upper ≤ 73000000000 := by
  decide +kernel

/-- Reduce the center angle before Taylor evaluation, restore it by doubling,
and transport the resulting rectangle over the certified displacement. -/
private def section99TrigBox (e : Fin 6) (j : Fin 29 × Fin 2) :
    Analysis.IntegerInterval × Analysis.IntegerInterval :=
  let q : ℚ := section99AngleCenter e j / (8192000000000000 : ℚ)
  let Q := Analysis.computedPhaseDouble 1000000000000 q 13
  Analysis.computedPhaseCell 1000000000000 Q (section99AngleDelta e j) 2700000000

/-- The phase rectangle is valid for the entire ordinate bracket at this
endpoint. The Taylor center, angle restoration, and linear error are all
checked at the same fixed-point scale. -/
private theorem section99_trig_box {g : Fin 29 → ℝ}
    (hgL : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hgU : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (e : Fin 6)
    (j : Fin 29 × Fin 2) :
    Analysis.complexIntervalContains (section99TrigBox e j).1 (section99TrigBox e j).2 1000000000000
      (Complex.exp
        ((((g j.1 * (2 * Real.log (section99Endpoint e : ℝ) + quarterLowPhaseShift j)) : ℝ) : ℂ) *
          Complex.I)) := by
  let c := section99AngleCenter e j
  let q : ℚ := c / (8192000000000000 : ℚ)
  have hg := section99_phase_guards e j
  have hc : |(q : ℝ)| ≤ 1 / 4 := by
    have h : (|c| : ℝ) ≤ 2048000000000000 := by exact_mod_cast hg.1
    dsimp only [q]
    rw [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat, abs_div,
      abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 8192000000000000)]
    exact (div_le_iff₀ (by norm_num only)).mpr (by linarith only [h])
  have hQ :=
    Analysis.computed_phase_double_contains (G := 1000000000000) (q := q) (by decide) hc
      (by norm_num only [Int.cast_ofNat]) 13
  have he : (2 : ℝ) ^ 13 * (q : ℝ) = (c : ℝ) / 1000000000000 := by
    dsimp only [q]
    norm_num only [Rat.cast_div, Rat.cast_intCast, Rat.cast_ofNat]
    ring
  rw [he] at hQ
  let x := g j.1 * (2 * Real.log (section99Endpoint e : ℝ) + quarterLowPhaseShift j)
  have hC :
    (⟨-c, -c⟩ : Analysis.IntegerInterval).Contains 1000000000000 (-((c : ℝ) / 1000000000000)) := by
    simp only [Analysis.IntegerInterval.Contains, Int.cast_neg, Int.cast_ofNat, neg_div, le_refl,
      and_self]
  have hD : (section99AngleDelta e j).Contains 1000000000000 (x - (c : ℝ) / 1000000000000) := by
    simpa only [sub_eq_add_neg, x, c, section99AngleDelta] using
      Analysis.IntegerInterval.add_contains (section99_angle_box hgL hgU e j) hC
  have hRad : |x - (c : ℝ) / 1000000000000| ≤ (73000000000 : ℝ) / 1000000000000 := by
    apply abs_le.mpr
    have he₁ : (-(73000000000 : ℝ)) ≤ ((section99AngleDelta e j).lower : ℝ) := by
      exact_mod_cast hg.2.1
    have he₂ : ((section99AngleDelta e j).upper : ℝ) ≤ 73000000000 := by exact_mod_cast hg.2.2
    exact
      ⟨(by
          rw [← neg_div]
          exact (div_le_div_of_nonneg_right he₁ (by norm_num only)).trans hD.1),
        hD.2.trans (div_le_div_of_nonneg_right he₂ (by norm_num only))⟩
  exact
    Analysis.computed_phase_cell_contains (by decide) hQ hD
      (Analysis.phaseRadiusCheck_sound
        (show Analysis.phaseRadiusCheck 1000000000000 73000000000 2700000000 = true by
          decide +kernel)
        hRad)

/-- Compute the integer lower endpoint for the doubled real phase term. -/
private def section99EndpointTerm (e : Fin 6) (j : Fin 29 × Fin 2) : ℤ :=
  2 *
    (Analysis.roundedComplexProduct 1000000000000 (section99PhaseRow j)
        (section99TrigBox e j)).1.lower

/-- The six lower bounds, in millionths, for the entire finite low phase. -/
private def section99EndpointTicks (e : Fin 6) : ℤ :=
  ![1000, 1280, 1450, 1620, 1820, 2150] e

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
-- One check evaluates all six endpoint sums, with 58 phase terms at each endpoint.
/-- The lower endpoints of the complex products certify the six scalar sums. -/
private theorem section99_endpoint_check :
    ∀ e : Fin 6,
      section99EndpointTicks e * 1000000 ≤ ∑ j : Fin 29 × Fin 2, section99EndpointTerm e j := by
  decide +kernel

/-- Soundness of the computed lower endpoint of each doubled phase term. -/
private theorem section99_endpoint_term {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (e : Fin 6)
    (j : Fin 29 × Fin 2) :
    (section99EndpointTerm e j : ℝ) / 1000000000000 ≤
      (quarterLowPhaseCoeff g j *
          Complex.exp
            (((g j.1 * (2 * Real.log (section99Endpoint e : ℝ) + quarterLowPhaseShift j) : ℝ) : ℂ) *
              Complex.I)).re := by
  let Q := section99PhaseRow j
  let z := if j.2 = 0 then section99RatCoeff (g j.1) else section99PoleCoeff (g j.1)
  have hz : Analysis.complexIntervalContains Q.1 Q.2 1000000000000 z := by
    by_cases h : j.2 = 0
    · simpa only [Q, z, section99PhaseRow, ite_eq_left h] using (section99_coeff_rows hl hu j.1).1
    · simpa only [Q, z, section99PhaseRow, ite_eq_right h] using (section99_coeff_rows hl hu j.1).2
  have h :=
    (Analysis.roundedComplexProduct_contains (by decide : (0 : ℤ) < 1000000000000) hz
        (section99_trig_box hl hu e j)).1
  dsimp only [Analysis.IntegerInterval.Contains] at h
  dsimp only [section99EndpointTerm]
  rw [Int.cast_mul, Int.cast_ofNat, mul_div_assoc]
  rw [quarterLowPhaseCoeff]
  change _ ≤ ((2 * z) * _).re
  rw [mul_assoc]
  conv_rhs => rw [two_mul, Complex.add_re]
  norm_num only [Int.cast_ofNat, Q] at h
  linarith only [h.1]

/-- Every ordinate list in the certified brackets satisfies the endpoint
lower bound obtained from the corresponding finite complex sum. -/
private theorem section99_certified_endpoint {g : Fin 29 → ℝ}
    (hl : AnalyticNumberTheory.RiemannZeta.LowZero100LowerBounds g)
    (hu : AnalyticNumberTheory.RiemannZeta.LowZero100UpperBounds g) (e : Fin 6) :
    (section99EndpointTicks e : ℝ) / 1000000 ≤ quarterLowPhase g (section99Endpoint e : ℝ) := by
  have hr : 0 < (section99Endpoint e : ℝ) :=
    Rat.cast_pos.mpr ((show ∀ i : Fin 6, 0 < section99Endpoint i by decide +kernel) e)
  rw [quarter_low_phase_sum hr]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) ↦ section99_endpoint_term hl hu e j)
  rw [← Finset.sum_div, ← Int.cast_sum] at h
  have hs :
    (section99EndpointTicks e : ℝ) * 1000000 ≤
      ((∑ j : Fin 29 × Fin 2, section99EndpointTerm e j : ℤ) : ℝ) := by
    exact_mod_cast section99_endpoint_check e
  linarith only [h, hs]

/-- Exact endpoint phases and the curvature cap transfer to the physical
Abel action by adding the already certified tail and cutoff losses. -/
private theorem section99_abel_endpoint_interval (hRH : RiemannHypothesis) {r B : ℝ} (a b : Fin 6)
    (ha : 292 ≤ (section99Endpoint a : ℝ))
    (hr : r ∈ Set.Icc (section99Endpoint a : ℝ) (section99Endpoint b : ℝ))
    (hB :
      B ≤
        min ((section99EndpointTicks a : ℝ) / 1000000) ((section99EndpointTicks b : ℝ) / 1000000) -
          27 * ((section99Endpoint b : ℝ) - (section99Endpoint a : ℝ)) ^ 2 /
            (2 * (section99Endpoint a : ℝ) ^ 2) -
          0.0064276) :
    B ≤
      section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  obtain ⟨g, hm, hp, hh, hz, hL, hU, hcover, hmul⟩ := quarter_low_zeros_complete hRH
  have hphase :=
    quarter_phase_lower_27 hL hU (fun i ↦ (hp i).le) (by linarith only [ha]) hr
      (section99_certified_endpoint hL hU a) (section99_certified_endpoint hL hU b)
  simp only [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] at hz hcover hmul
  have hab := quarter_abel_of_low_phase hRH (ha.trans hr.1) g hm hp hh hz hcover hmul
  linarith only [hB, hphase, hab]

/-- The phase certificate bounds the nontrivial-zero Abel action on the
radius interval [313, 1568 / 5]. -/
theorem section99_abel_to3136 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc (313) (1568 / 5)) :
    -0.00548 ≤
      section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have ha : section99Endpoint 0 = 313 := by decide +kernel
  have hb : section99Endpoint 1 = 1568 / 5 := by decide +kernel
  refine section99_abel_endpoint_interval hRH 0 1 ?_ ?_ ?_
  · norm_num only [ha, Rat.cast_div, Rat.cast_ofNat]
  · simpa only [ha, hb, Rat.cast_div, Rat.cast_ofNat] using hr
  · rw [show section99EndpointTicks 0 = 1000 by decide,
      show section99EndpointTicks 1 = 1280 by decide, ha, hb]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_ofNat, min_def, ite_true, ite_false]

/-- The phase certificate bounds the nontrivial-zero Abel action on the
radius interval [1568 / 5, 314]. -/
theorem section99_abel_to314 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc (1568 / 5) (314)) :
    -0.00517 ≤
      section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have ha : section99Endpoint 1 = 1568 / 5 := by decide +kernel
  have hb : section99Endpoint 2 = 314 := by decide +kernel
  refine section99_abel_endpoint_interval hRH 1 2 ?_ ?_ ?_
  · norm_num only [ha, Rat.cast_div, Rat.cast_ofNat]
  · simpa only [ha, hb, Rat.cast_div, Rat.cast_ofNat] using hr
  · rw [show section99EndpointTicks 1 = 1280 by decide,
      show section99EndpointTicks 2 = 1450 by decide, ha, hb]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_ofNat, min_def, ite_true, ite_false]

/-- The phase certificate bounds the nontrivial-zero Abel action on the
radius interval [314, 6289 / 20]. -/
theorem section99_abel_to31445 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc (314) (6289 / 20)) :
    -0.00501 ≤
      section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have ha : section99Endpoint 2 = 314 := by decide +kernel
  have hb : section99Endpoint 3 = 6289 / 20 := by decide +kernel
  refine section99_abel_endpoint_interval hRH 2 3 ?_ ?_ ?_
  · norm_num only [ha, Rat.cast_div, Rat.cast_ofNat]
  · simpa only [ha, hb, Rat.cast_div, Rat.cast_ofNat] using hr
  · rw [show section99EndpointTicks 2 = 1450 by decide,
      show section99EndpointTicks 3 = 1620 by decide, ha, hb]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_ofNat, min_def, ite_true, ite_false]

/-- The phase certificate bounds the nontrivial-zero Abel action on the
radius interval [6289 / 20, 315]. -/
theorem section99_abel_to315 (hRH : RiemannHypothesis) {r : ℝ}
    (hr : r ∈ Set.Icc (6289 / 20) (315)) :
    -0.00485 ≤
      section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have ha : section99Endpoint 3 = 6289 / 20 := by decide +kernel
  have hb : section99Endpoint 4 = 315 := by decide +kernel
  refine section99_abel_endpoint_interval hRH 3 4 ?_ ?_ ?_
  · norm_num only [ha, Rat.cast_div, Rat.cast_ofNat]
  · simpa only [ha, hb, Rat.cast_div, Rat.cast_ofNat] using hr
  · rw [show section99EndpointTicks 3 = 1620 by decide,
      show section99EndpointTicks 4 = 1820 by decide, ha, hb]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_ofNat, min_def, ite_true, ite_false]

/-- The phase certificate bounds the nontrivial-zero Abel action on the
radius interval [315, 316]. -/
theorem section99_abel_to316 (hRH : RiemannHypothesis) {r : ℝ} (hr : r ∈ Set.Icc (315) (316)) :
    -0.00475 ≤
      section99AbelAction (r ^ 2)
        (fun t ↦ (∑' ρ : ℂ, AnalyticNumberTheory.RiemannZeta.nontrivialLogZeroTerm t ρ).re) := by
  have ha : section99Endpoint 4 = 315 := by decide +kernel
  have hb : section99Endpoint 5 = 316 := by decide +kernel
  refine section99_abel_endpoint_interval hRH 4 5 ?_ ?_ ?_
  · norm_num only [ha, Rat.cast_div, Rat.cast_ofNat]
  · simpa only [ha, hb, Rat.cast_div, Rat.cast_ofNat] using hr
  · rw [show section99EndpointTicks 4 = 1820 by decide,
      show section99EndpointTicks 5 = 2150 by decide, ha, hb]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Int.cast_ofNat, min_def, ite_true, ite_false]

end PseudoPrime.PrimeTestBounds.MillerRabin
