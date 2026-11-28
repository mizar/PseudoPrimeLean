/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Arithmetic.NaturalTailLimit
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterEulerMoments570
public import PseudoPrime.AnalyticNumberTheory.RiemannZeta.ChebyshevBoundary43
public import PseudoPrime.AnalyticNumberTheory.Arithmetic.WeightedAbelInterval
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.EulerDerivatives
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuarterKernel570
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticTripleCharacters

/-! # Common Euler tail for the section 96 two-frequency comparison -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- Apply the symmetric exponential shift at frequency s to a polynomial f. -/
private noncomputable def shift (f : ℝ → ℝ) (s v : ℝ) : ℝ :=
  (Real.exp (-(51 / 50) * s) * f (v + s) + Real.exp (51 / 50 * s) * f (v - s)) / 2

/-- Combine the frequencies 3, 14/5, 0 and 1/5 with the square-completion
coefficients. All four Euler sums have the same trace deficit. -/
private noncomputable def combine (f : ℝ → ℝ) (v : ℝ) : ℝ :=
  (shift f 3 v - shift f (14 / 5) v) / 2 + (f v - shift f (1 / 5) v) / 4

/-- The unshifted quadratic in the Fourier weight of the sixth pole. -/
private noncomputable def poly (v : ℝ) : ℝ :=
  3 / 8 + 3 * (51 / 50) / 8 * v + (51 / 50 : ℝ) ^ 2 / 8 * v ^ 2

/-- The combined polynomial P in the common Euler tail. -/
noncomputable def twoShiftEulerPoly (v : ℝ) : ℝ :=
  combine poly v

/-- The common tail polynomial is the weighted difference of the averaged forward
and backward translates of the unshifted quadratic. -/
theorem twoShiftEulerPoly_eq_shifts (v : ℝ) :
    let P := fun t : ℝ ↦ 3 / 8 + 3 * (51 / 50 : ℝ) / 8 * t + (51 / 50 : ℝ) ^ 2 / 8 * t ^ 2
    let S := fun s : ℝ ↦
      (Real.exp (-(51 / 50) * s) * P (v + s) + Real.exp ((51 / 50) * s) * P (v - s)) / 2
    twoShiftEulerPoly v = (S 3 - S (14 / 5)) / 2 + (P v - S (1 / 5)) / 4 := by
  rfl

/-- Rational Taylor enclosure at the fixed positive frequency. -/
private theorem exp_t :
    2132755716 / 100000000 ≤ Real.exp ((51 / 50 : ℝ) * 3) ∧
      Real.exp ((51 / 50 : ℝ) * 3) ≤ 2132755717 / 100000000 := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (51 / 50 : ℝ) * 3) 32
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * 3) (n := 32) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hl hu
  constructor <;> linarith only [hl, hu]

/-- Rational Taylor enclosure at the fixed positive frequency. -/
private theorem exp_b :
    1739182033 / 100000000 ≤ Real.exp ((51 / 50 : ℝ) * (14 / 5)) ∧
      Real.exp ((51 / 50 : ℝ) * (14 / 5)) ≤ 1739182034 / 100000000 := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (51 / 50 : ℝ) * (14 / 5)) 32
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (14 / 5)) (n := 32) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hl hu
  constructor <;> linarith only [hl, hu]

/-- Rational Taylor enclosure at the fixed positive frequency. -/
private theorem exp_h :
    122629815 / 100000000 ≤ Real.exp ((51 / 50 : ℝ) * (1 / 5)) ∧
      Real.exp ((51 / 50 : ℝ) * (1 / 5)) ≤ 122629816 / 100000000 := by
  have hl := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (51 / 50 : ℝ) * (1 / 5)) 32
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (51 / 50 : ℝ) * (1 / 5)) (n := 32) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hl hu
  constructor <;> linarith only [hl, hu]

/-- Conductor difference (96.23) in the coordinate u = log X = 2 log r. -/
@[expose]
noncomputable def twoShiftConductor (u : ℝ) : ℝ :=
  (51 / 50 : ℝ) ^ 5 / 60 * Real.exp (-(13 / 25) * u) *
    (u ^ 5 - Real.exp ((51 / 50 : ℝ) * (1 / 5)) * (u - 1 / 5) ^ 5)

private noncomputable def conductorSlope (u : ℝ) : ℝ :=
  u ^ 4 * (26 / 25 * u - 10)

/-- After translation by 11.35 all coefficients of the rational lower polynomial
are positive. This proves the sign in (96.28) directly. -/
private theorem conductorSlope_gap {u : ℝ} (hu : 227 / 20 ≤ u) :
    0 ≤ Real.exp ((51 / 50 : ℝ) * (1 / 5)) * conductorSlope (u - 1 / 5) - conductorSlope u := by
  have hv : 0 ≤ conductorSlope (u - 1 / 5) :=
    mul_nonneg (pow_nonneg (by linarith only [hu]) _) (by linarith only [hu])
  have h := mul_le_mul_of_nonneg_right exp_h.1 hv
  have hy : 0 ≤ u - 227 / 20 := sub_nonneg.mpr hu
  generalize hz : u - 227 / 20 = y at hy
  have he : u = y + 227 / 20 := by linarith only [hz]
  have hp : 0 ≤ 122629815 / 100000000 * conductorSlope (u - 1 / 5) - conductorSlope u := by
    rw [he]
    unfold conductorSlope
    ring_nf
    positivity
  linarith only [h, hp]

/-- The conductor difference is increasing in the log-cutoff coordinate from 11.35
onward. Its derivative has the sign of the translated polynomial gap in (96.28). -/
theorem twoShiftConductor_monotone : MonotoneOn twoShiftConductor (Set.Ici (227 / 20)) := by
  let E := Real.exp ((51 / 50 : ℝ) * (1 / 5))
  have hd (u : ℝ) :
    HasDerivAt twoShiftConductor
      ((51 / 50 : ℝ) ^ 5 / 120 * Real.exp (-(13 / 25) * u) *
        (E * conductorSlope (u - 1 / 5) - conductorSlope u))
      u := by
    have h :=
      (((((hasDerivAt_id u).const_mul (-(13 / 25 : ℝ))).exp).const_mul ((51 / 50 : ℝ) ^ 5 / 60)).mul
        (((hasDerivAt_id u).pow 5).sub ((((hasDerivAt_id u).sub_const (1 / 5)).pow 5).const_mul E)))
    convert h using 1
    · funext v
      rfl
    dsimp only [conductorSlope, id_eq, Pi.sub_apply, Pi.pow_apply]
    ring
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · exact fun u _ ↦ (hd u).continuousAt.continuousWithinAt
  · exact fun u _ ↦ (hd u).differentiableAt.differentiableWithinAt
  · intro u hu
    rw [(hd u).deriv]
    exact
      mul_nonneg (mul_nonneg (by norm_num only) (Real.exp_pos _).le)
        (conductorSlope_gap (interior_subset hu))

/-- For every radius at least 292 the conductor difference is bounded below
by its value at the entrance radius, using the certified logarithm of 292. -/
theorem twoShiftConductor_at_radius {r : ℝ} (hr : 292 ≤ r) :
    twoShiftConductor (2 * Real.log 292) ≤ twoShiftConductor (2 * Real.log r) := by
  have h :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 227 / 40) (hi :=
        6) (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have he : 227 / 20 ≤ 2 * Real.log 292 := by linarith only [h]
  have hl := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num only) hr) zero_le_two
  exact twoShiftConductor_monotone he (he.trans hl) hl

/-- The conductor term stays above −1.156 throughout the high range. Evaluate its
two fifth powers at opposite endpoints enclosing twice the logarithm of 292,
then use monotonicity to transfer the entrance estimate. -/
theorem twoShiftConductor_lower {r : ℝ} (hr : 292 ≤ r) :
    -(1156 / 1000 : ℝ) < twoShiftConductor (2 * Real.log r) := by
  apply lt_of_lt_of_le _ (twoShiftConductor_at_radius hr)
  let u := 2 * Real.log 292
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo :=
      567675380 / 100000000) (hi := 567675381 / 100000000) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hl : (1135350760 / 100000000 : ℝ) ≤ u := by
    dsimp only [u]; linarith only [h.1]
  have hu : u ≤ 1135350762 / 100000000 := by
    dsimp only [u]; linarith only [h.2]
  have h₁ := pow_le_pow_left₀ (by norm_num only) hl 5
  have h₂ :=
    pow_le_pow_left₀ (show 0 ≤ u - 1 / 5 by linarith only [hl]) (sub_le_sub_right hu (1 / 5)) 5
  have h₃ :=
    mul_le_mul exp_h.2 h₂ (pow_nonneg (show 0 ≤ u - 1 / 5 by linarith only [hl]) _)
      (by norm_num only)
  have hx :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 292) (p := 26) (d := 25)
        (lo := 0) (hi := 272899 / 100000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hx
  rw [Real.rpow_def_of_pos (by norm_num only)] at hx
  have he : -(13 / 25) * u = Real.log 292 * (-(26 / 25 : ℝ)) := by
    dsimp only [u]; ring
  rw [← he] at hx
  have hd :
    -(2301998 / 100 : ℝ) ≤ u ^ 5 - Real.exp ((51 / 50 : ℝ) * (1 / 5)) * (u - 1 / 5) ^ 5 := by
    linarith only [h₁, h₃]
  unfold twoShiftConductor
  change _ < _ * Real.exp (-(13 / 25) * u) * _
  nlinarith only [mul_nonneg (Real.exp_pos (-(13 / 25) * u)).le (sub_nonneg.mpr hd), hx]

/-- For every radius at least 475, the conductor difference exceeds −1.1201.
Enclose its value at 475 and apply monotonicity on the logarithmic half-line. -/
theorem twoShiftConductor_lower_475 {r : ℝ} (hr : 475 ≤ r) :
    -(11201 / 10000 : ℝ) < twoShiftConductor (2 * Real.log r) := by
  let u := 2 * Real.log 475
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 475) (j := 9) (n := 24) (lo :=
      616331480 / 100000000) (hi := 616331481 / 100000000) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hl : (1232662960 / 100000000 : ℝ) ≤ u := by
    dsimp only [u]; linarith only [h.1]
  have hu : u ≤ 1232662962 / 100000000 := by
    dsimp only [u]; linarith only [h.2]
  have h₁ := pow_le_pow_left₀ (by norm_num only) hl 5
  have h₂ :=
    pow_le_pow_left₀ (show 0 ≤ u - 1 / 5 by linarith only [hl]) (sub_le_sub_right hu (1 / 5)) 5
  have h₃ :=
    mul_le_mul exp_h.2 h₂ (pow_nonneg (show 0 ≤ u - 1 / 5 by linarith only [hl]) _)
      (by norm_num only)
  have hx :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 475) (p := 26) (d := 25)
        (lo := 0) (hi := 1645276 / 1000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hx
  rw [Real.rpow_def_of_pos (by norm_num only)] at hx
  have he : -(13 / 25) * u = Real.log 475 * (-(26 / 25 : ℝ)) := by
    dsimp only [u]; ring
  rw [← he] at hx
  have hd :
    -(3699427 / 100 : ℝ) ≤ u ^ 5 - Real.exp ((51 / 50 : ℝ) * (1 / 5)) * (u - 1 / 5) ^ 5 := by
    linarith only [h₁, h₃]
  have hdom : 227 / 20 ≤ u := by linarith only [hl]
  have hmono := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num only) hr) zero_le_two
  apply lt_of_lt_of_le _ (twoShiftConductor_monotone hdom (hdom.trans hmono) hmono)
  unfold twoShiftConductor
  change _ < _ * Real.exp (-(13 / 25) * u) * _
  nlinarith only [mul_nonneg (Real.exp_pos (-(13 / 25) * u)).le (sub_nonneg.mpr hd), hx]

/-- For every radius at least 299, the conductor difference exceeds −1.15554.
Enclose its value at 299 and apply monotonicity on the logarithmic half-line. -/
theorem twoShiftConductor_lower_299 {r : ℝ} (hr : 299 ≤ r) :
    -(115554 / 100000 : ℝ) < twoShiftConductor (2 * Real.log r) := by
  let u := 2 * Real.log 299
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 299) (j := 8) (n := 24) (lo :=
      570044357 / 100000000) (hi := 570044358 / 100000000) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  have hl : (1140088714 / 100000000 : ℝ) ≤ u := by
    dsimp only [u]; linarith only [h.1]
  have hu : u ≤ 1140088716 / 100000000 := by
    dsimp only [u]; linarith only [h.2]
  have h₁ := pow_le_pow_left₀ (by norm_num only) hl 5
  have h₂ :=
    pow_le_pow_left₀ (show 0 ≤ u - 1 / 5 by linarith only [hl]) (sub_le_sub_right hu (1 / 5)) 5
  have h₃ :=
    mul_le_mul exp_h.2 h₂ (pow_nonneg (show 0 ≤ u - 1 / 5 by linarith only [hl]) _)
      (by norm_num only)
  have hx :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 299) (p := 26) (d := 25)
        (lo := 0) (hi := 266257571 / 100000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hx
  rw [Real.rpow_def_of_pos (by norm_num only)] at hx
  have he : -(13 / 25) * u = Real.log 299 * (-(26 / 25 : ℝ)) := by
    dsimp only [u]; ring
  rw [← he] at hx
  have hd :
    -(23584860 / 1000 : ℝ) ≤ u ^ 5 - Real.exp ((51 / 50 : ℝ) * (1 / 5)) * (u - 1 / 5) ^ 5 := by
    linarith only [h₁, h₃]
  have hdom : 227 / 20 ≤ u := by linarith only [hl]
  have hmono := mul_le_mul_of_nonneg_left (Real.log_le_log (by norm_num only) hr) zero_le_two
  apply lt_of_lt_of_le _ (twoShiftConductor_monotone hdom (hdom.trans hmono) hmono)
  unfold twoShiftConductor
  change _ < _ * Real.exp (-(13 / 25) * u) * _
  nlinarith only [mul_nonneg (Real.exp_pos (-(13 / 25) * u)).le (sub_nonneg.mpr hd), hx]

/-- The reciprocal-radius pole correction coefficient from (96.23). -/
@[expose]
noncomputable def twoShiftReciprocalCoeff : ℝ :=
  3 / 2 * (51 / 50 : ℝ) ^ 5 / (13 / 25 : ℝ) ^ 6 * (Real.exp (1 / 10) - 1)

/-- Four Taylor terms beyond the constant give a rational lower bound for the correction. -/
theorem twoShiftReciprocalCoeff_lower : 88098 / 10000 < twoShiftReciprocalCoeff := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num only : 0 ≤ (1 / 10 : ℝ)) 5
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat] at h
  unfold twoShiftReciprocalCoeff
  linarith only [h]

/-- The coefficient of the radius in the two-frequency phase recovery formula (96.19). -/
noncomputable def twoShiftPhaseCoeff : ℝ :=
  let B := fun s : ℝ ↦ 2 * Real.exp (-(51 / 50) * s) * poly s
  (B (14 / 5) - B 3 - 3 * (51 / 50 : ℝ) ^ 5 / (38 / 25 : ℝ) ^ 6 * (1 - Real.exp (-(1 / 10)))) / 2 -
    (B 0 - B (1 / 5)) / 4

/-- Express the leading phase coefficient using the symmetric conductor
profile and the loss at the positive half-pole. -/
theorem twoShift_phaseCoeff_formula :
    let P := fun s : ℝ ↦
      Real.exp (-(51 / 50) * s) * (3 / 16 + (3 * (51 / 50) / 16) * s + ((51 / 50) ^ 2 / 16) * s ^ 2)
    twoShiftPhaseCoeff =
      4 * ((P (14 / 5) - P 3) / 2 - (P 0 - P (1 / 5)) / 4) -
        (3 * (51 / 50 : ℝ) ^ 5 / (38 / 25) ^ 6 * (1 - Real.exp (-(1 / 10)))) / 2 := by
  dsimp only [twoShiftPhaseCoeff, poly]
  ring

/-- The leading gain in (96.19) exceeds 0.0014337. Bound each fixed exponential
on the side dictated by its coefficient. -/
theorem twoShiftPhaseCoeff_lower : 14337 / 10000000 < twoShiftPhaseCoeff := by
  have hu :=
    Analysis.exp_le_taylor_add_two_next (x := (1 / 10 : ℝ)) (n := 12) (by norm_num only)
      (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at hu
  have hsmall : Real.exp (1 / 10 : ℝ) ≤ 110517092 / 100000000 := by linarith only [hu]
  unfold twoShiftPhaseCoeff poly
  simp only [neg_mul, mul_zero, Real.exp_zero, Real.exp_neg, ← one_div]
  linarith only [one_div_le_one_div_of_le (Real.exp_pos _) exp_b.2,
    one_div_le_one_div_of_le (by norm_num only) exp_t.1,
    one_div_le_one_div_of_le (Real.exp_pos _) exp_h.2,
    one_div_le_one_div_of_le (Real.exp_pos _) hsmall]

/-- Fixed pole contribution after charging the zeta zero mass in (96.23). -/
@[expose]
noncomputable def twoShiftPoleConstant : ℝ :=
  6 * (51 / 50 : ℝ) ^ 5 / ((51 / 50 : ℝ) ^ 2 - 1 / 4) ^ 3 *
      ((Real.cosh (3 / 2) - Real.cosh (7 / 5)) / 2 + (1 - Real.cosh (1 / 10)) / 4) -
    3 / 5000

/-- Positive Taylor truncations and their geometric remainders enclose the
hyperbolic cosine at a nonnegative rational argument. -/
private theorem cosh_taylor_box (x : ℝ) (hx : 0 ≤ x) (hs : x / (17 : ℕ) ≤ 1 / 2) :
    let S := ∑ i ∈ Finset.range 16, x ^ i / i.factorial
    let U := S + x ^ 16 / ((16 : ℕ).factorial : ℝ) * 2
    (S + 1 / U) / 2 ≤ Real.cosh x ∧ Real.cosh x ≤ (U + 1 / S) / 2 := by
  intro S U
  have hl : S ≤ Real.exp x := Real.sum_le_exp_of_nonneg hx 16
  have hu : Real.exp x ≤ U := Analysis.exp_le_taylor_add_two_next hx hs
  have hS : 0 < S :=
    Finset.sum_pos' (fun i _ ↦ div_nonneg (pow_nonneg hx _) (Nat.cast_nonneg _))
      ⟨0, by decide, by norm_num only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one]⟩
  rw [Real.cosh_eq, Real.exp_neg, ← one_div]
  constructor <;>
    linarith only [hl, hu, one_div_le_one_div_of_le hS hl,
      one_div_le_one_div_of_le (Real.exp_pos _) hu]

/-- The fixed contribution in the two-frequency comparison exceeds 1.334316. -/
theorem twoShiftPoleConstant_lower : 1334316 / 1000000 < twoShiftPoleConstant := by
  have ht := (cosh_taylor_box (3 / 2) (by norm_num only) (by norm_num only)).1
  have hb := (cosh_taylor_box (7 / 5) (by norm_num only) (by norm_num only)).2
  have hh := (cosh_taylor_box (1 / 10) (by norm_num only) (by norm_num only)).2
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_zero,
    Nat.cast_one, Nat.cast_ofNat] at ht hb hh
  unfold twoShiftPoleConstant
  linarith only [ht, hb, hh]

/-- At v = 4 the constant, linear and quadratic Taylor coefficients of P are
strictly positive. Fixed-frequency exponential enclosures certify each sign. -/
private theorem coeff_pos :
    0 < combine poly 4 ∧
      0 < combine (fun v ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * v) 4 ∧
      0 < combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 4 := by
  unfold combine shift poly
  simp only [neg_mul, Real.exp_neg, ← one_div]
  constructor
  · linarith only [exp_t.1, exp_t.2, one_div_le_one_div_of_le (Real.exp_pos _) exp_t.2,
      one_div_le_one_div_of_le (by norm_num only) exp_t.1, exp_b.1, exp_b.2,
      one_div_le_one_div_of_le (Real.exp_pos _) exp_b.2,
      one_div_le_one_div_of_le (by norm_num only) exp_b.1, exp_h.1, exp_h.2,
      one_div_le_one_div_of_le (Real.exp_pos _) exp_h.2,
      one_div_le_one_div_of_le (by norm_num only) exp_h.1]
  constructor <;>
    linarith only [exp_t.1, exp_t.2, one_div_le_one_div_of_le (Real.exp_pos _) exp_t.2,
      one_div_le_one_div_of_le (by norm_num only) exp_t.1, exp_b.1, exp_b.2,
      one_div_le_one_div_of_le (Real.exp_pos _) exp_b.2,
      one_div_le_one_div_of_le (by norm_num only) exp_b.1, exp_h.1, exp_h.2,
      one_div_le_one_div_of_le (Real.exp_pos _) exp_h.2,
      one_div_le_one_div_of_le (by norm_num only) exp_h.1]

/-- The combined weight is positive for every logarithm v at least four.
Expand about four and use the three positive coefficients. -/
theorem twoShiftEulerPoly_pos {v : ℝ} (hv : 4 ≤ v) : 0 < twoShiftEulerPoly v := by
  obtain ⟨hc, hl, hq⟩ := coeff_pos
  have h :=
    add_pos_of_pos_of_nonneg (add_pos_of_pos_of_nonneg hc (mul_nonneg hl.le (sub_nonneg.mpr hv)))
      (mul_nonneg hq.le (sq_nonneg (v - 4)))
  convert h using 1
  unfold twoShiftEulerPoly combine shift poly
  ring

/-- A common trace deficit at most four bounds the combined negative Euler
tail from below. The nonnegative factor a includes the von Mangoldt and power
weights; the same deficit multiplies all four shifts. -/
theorem twoShiftEuler_tail_lower {ι : Type*} (a d v : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (hd : ∀ i, d i ≤ 4)
    (hv : ∀ i, 4 ≤ v i) (hs : Summable (fun i ↦ a i * twoShiftEulerPoly (v i)))
    (ht : Summable (fun i ↦ d i * (a i * twoShiftEulerPoly (v i)))) :
    -4 * (∑' i, a i * twoShiftEulerPoly (v i)) ≤
      -(∑' i, d i * (a i * twoShiftEulerPoly (v i))) := by
  have h :=
    hasSum_le
      (fun i ↦
        mul_le_mul_of_nonneg_right (hd i) (mul_nonneg (ha i) (twoShiftEulerPoly_pos (hv i)).le))
      ht.hasSum (hs.hasSum.mul_left 4)
  linarith only [h]

/-- Absolute convergence of the combined Euler weight follows from the
zeroth, first and second von Mangoldt logarithmic moments at 38/25. -/
theorem twoShiftEuler_summable :
    Summable
      (fun n : ℕ ↦
        ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
          twoShiftEulerPoly (Real.log n)) := by
  have hm :=
    AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.summable_mangoldt_log (σ := 38 / 25)
      (by norm_num only)
  have h :=
    (((hm 0).mul_left (combine poly 0)).add
          ((hm 1).mul_left
            (combine (fun v ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * v) 0))).add
      ((hm 2).mul_left (combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 0))
  apply h.congr
  intro n
  unfold twoShiftEulerPoly combine shift poly
  ring

/-- Above a cutoff with logarithm at least four, a three-character trace
at least minus one bounds the signed Euler tail by four times the positive
tail. Both series converge from the logarithmic moments and character norm bounds. -/
theorem three_trace_tail_lower {p q s : ℕ} (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) (X : ℕ) (hX : 4 ≤ Real.log X)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let A := fun n : { n : ℕ // X < n } ↦
      ArithmeticFunction.vonMangoldt n.val / (n.val : ℝ) ^ (38 / 25 : ℝ)
    let P := fun n : { n : ℕ // X < n } ↦ twoShiftEulerPoly (Real.log n.val)
    let D := fun n : { n : ℕ // X < n } ↦ 3 - ((a n.val).re + (b n.val).re + (c n.val).re)
    (-4 : ℝ) * (∑' n, A n * P n) ≤ -(∑' n, D n * (A n * P n)) := by
  intro A P D
  have hpos : 0 < (X : ℝ) := by
    by_contra! hz
    have he := le_antisymm hz (Nat.cast_nonneg X)
    rw [he, Real.log_zero] at hX
    norm_num only at hX
  have hv (i : { n : ℕ // X < n }) :=
    hX.trans (Real.log_le_log hpos (Nat.cast_le.mpr i.property.le))
  have ha (i : { n : ℕ // X < n }) : 0 ≤ A i :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hd (i : { n : ℕ // X < n }) : D i ≤ 4 := by
    dsimp only [D]; linarith only [ht i.val]
  have hs := twoShiftEuler_summable.subtype (fun n ↦ X < n)
  apply twoShiftEuler_tail_lower A D (fun i ↦ Real.log i.val) ha hd hv hs
  apply (hs.mul_left 4).of_norm_bounded
  intro i
  have hd0 : 0 ≤ D i := by
    dsimp only [D]
    linarith only [(Complex.re_le_norm _).trans (a.norm_le_one i.val),
      (Complex.re_le_norm _).trans (b.norm_le_one i.val),
      (Complex.re_le_norm _).trans (c.norm_le_one i.val)]
  have hw := mul_nonneg (ha i) (twoShiftEulerPoly_pos (hv i)).le
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hd0 hw)]
  exact mul_le_mul_of_nonneg_right (hd i) hw

/-- On logarithms at least four the combined weight times the decaying
exponential has negative derivative. The constant and linear coefficients
of (38/25)P-P' are certified by the fixed exponential enclosures. -/
theorem twoShiftEuler_deriv_neg {v : ℝ} (hv : 4 ≤ v) :
    deriv (fun u ↦ Real.exp (-(38 / 25 : ℝ) * u) * twoShiftEulerPoly u) v < 0 := by
  let C := combine poly 4
  let L := combine (fun u ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * u) 4
  let Q := combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 4
  have he (u : ℝ) : twoShiftEulerPoly u = C + L * (u - 4) + Q * (u - 4) ^ 2 := by
    unfold C L Q twoShiftEulerPoly combine shift poly
    ring
  have hcoeff : 0 < 38 / 25 * C - L ∧ 0 < 38 / 25 * L - 2 * Q := by
    unfold C L Q combine shift poly
    simp only [neg_mul, Real.exp_neg, ← one_div]
    constructor <;>
      linarith only [exp_t.1, exp_t.2, one_div_le_one_div_of_le (Real.exp_pos _) exp_t.2,
        one_div_le_one_div_of_le (by norm_num only) exp_t.1, exp_b.1, exp_b.2,
        one_div_le_one_div_of_le (Real.exp_pos _) exp_b.2,
        one_div_le_one_div_of_le (by norm_num only) exp_b.1, exp_h.1, exp_h.2,
        one_div_le_one_div_of_le (Real.exp_pos _) exp_h.2,
        one_div_le_one_div_of_le (by norm_num only) exp_h.1]
  have hQ : 0 < Q := coeff_pos.2.2
  have hsub := (hasDerivAt_id v).sub_const 4
  have hd :=
    (((hasDerivAt_id v).const_mul (-(38 / 25 : ℝ))).exp).mul
      ((((hsub.const_mul L).const_add C)).add ((hsub.pow 2).const_mul Q))
  simp_rw [he]
  change
    deriv
        ((fun x : ℝ ↦ Real.exp (-(38 / 25) * id x)) *
          ((fun x : ℝ ↦ C + L * (id x - 4)) + fun y ↦ Q * ((fun x : ℝ ↦ id x - 4) ^ 2) y))
        v <
      0
  rw [hd.deriv]
  simp only [id_eq, mul_one, Pi.add_apply, Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
  have hlin := mul_nonneg hcoeff.2.le (sub_nonneg.mpr hv)
  have hquad := mul_nonneg hQ.le (sq_nonneg (v - 4))
  have hneg : -(38 / 25) * (C + L * (v - 4) + Q * (v - 4) ^ 2) + (L + 2 * Q * (v - 4)) < 0 := by
    linarith only [hcoeff.1, hlin, hquad]
  linear_combination Real.exp (-(38 / 25 : ℝ) * v) * hneg

/-- The combined Euler density decreases throughout the logarithmic tail. -/
theorem twoShiftEuler_antitone :
    AntitoneOn (fun u : ℝ ↦ Real.exp (-(38 / 25 : ℝ) * u) * twoShiftEulerPoly u) (Set.Ici 4) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · unfold twoShiftEulerPoly combine shift poly
    fun_prop
  · unfold twoShiftEulerPoly combine shift poly
    fun_prop
  · intro v hv
    exact (twoShiftEuler_deriv_neg (interior_subset hv)).le

/-- Continuous-variable Euler weight used in centered Abel summation. -/
noncomputable def twoShiftEulerDensity (t : ℝ) : ℝ :=
  Real.exp (-(38 / 25 : ℝ) * Real.log t) * twoShiftEulerPoly (Real.log t)

/-- At positive arguments the two-shift weight is analytic, so its derivative
is continuous on every compact positive interval. -/
private theorem density_analytic {t : ℝ} (ht : 0 < t) : AnalyticAt ℝ twoShiftEulerDensity t := by
  unfold twoShiftEulerDensity twoShiftEulerPoly combine shift poly
  fun_prop (disch := exact ht.ne')

/-- Above log cutoff four, the derivative with respect to the original
positive argument is strictly negative by the logarithmic chain rule. -/
theorem twoShiftEulerDensity_deriv_neg {t : ℝ} (ht : 0 < t) (hl : 4 ≤ Real.log t) :
    deriv twoShiftEulerDensity t < 0 := by
  let F := fun u : ℝ ↦ Real.exp (-(38 / 25 : ℝ) * u) * twoShiftEulerPoly u
  have hd : DifferentiableAt ℝ F (Real.log t) := by
    unfold F twoShiftEulerPoly combine shift poly
    fun_prop
  have h := hd.hasDerivAt.comp t (Real.hasDerivAt_log ht.ne')
  exact h.deriv.trans_lt (mul_neg_of_neg_of_pos (twoShiftEuler_deriv_neg hl) (inv_pos.mpr ht))

/-- On a positive finite interval the signed difference between the Mangoldt
sum and its main integral equals the two endpoint errors minus the centered
psi integral against the derivative. -/
theorem twoShiftEuler_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) *
            twoShiftEulerPoly (Real.log n)) -
        (∫ t : ℝ in a..b, twoShiftEulerDensity t) =
      (Chebyshev.psi b - b) * twoShiftEulerDensity b -
        (Chebyshev.psi a - a) * twoShiftEulerDensity a -
        ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv twoShiftEulerDensity t := by
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := density_analytic (ha.trans_le ht.1)
  have h :=
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_interval ha.le hab
      (fun t ht ↦ (hd t ht).differentiableAt)
      (show ContinuousOn (deriv twoShiftEulerDensity) (Set.Icc a b) from fun t ht ↦
          (hd t ht).deriv.continuousAt.continuousWithinAt).integrableOn_Icc
  rw [← h]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hn0 : 0 < n := lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hn).1
  have hp : 0 < (n : ℝ) := Nat.cast_pos.mpr hn0
  rw [twoShiftEulerDensity, Real.rpow_def_of_pos hp, neg_mul, mul_comm (38 / 25 : ℝ), Real.exp_neg]
  ring

/-- The upper centered Abel boundary vanishes unconditionally: the Chebyshev
error grows at most linearly and each of the three logarithmic moments decays. -/
theorem twoShiftEuler_boundary_zero :
    Filter.Tendsto (fun x : ℝ ↦ (Chebyshev.psi x - x) * twoShiftEulerDensity x) Filter.atTop
      (nhds 0) := by
  let E := fun x : ℝ ↦ (Chebyshev.psi x - x) / 4
  have hE : ∀ᶠ x : ℝ in Filter.atTop, ‖E x‖ ≤ 2 * x := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 := zero_le_one.trans hx
    have hlog := Real.log_le_sub_one_of_pos (by norm_num only : (0 : ℝ) < 4)
    have hu :=
      (Chebyshev.psi_le_const_mul_self hx0).trans
        (mul_le_mul_of_nonneg_right (by linarith only [hlog] : Real.log 4 + 4 ≤ 7) hx0)
    rw [Real.norm_eq_abs, abs_le]
    dsimp only [E]
    constructor <;> linarith only [hu, Chebyshev.psi_nonneg (x := x), hx0]
  have hm (k : ℕ) :=
    AnalyticNumberTheory.RiemannZeta.moment_boundary_tendsto (by norm_num only : (1 : ℝ) < 38 / 25)
      k E hE
  let C := combine poly 0
  let L := combine (fun v ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * v) 0
  let Q := combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 0
  have hh :=
    ((((hm 0).const_mul (4 * C)).add ((hm 1).const_mul (4 * L))).add ((hm 2).const_mul (4 * Q)))
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  dsimp only [AnalyticNumberTheory.Arithmetic.mangoldtMomentWeight, E, twoShiftEulerDensity,
    twoShiftEulerPoly, C, L, Q, combine, shift, poly]
  rw [Real.rpow_def_of_pos hx]
  rw [show Real.log x * -(38 / 25 : ℝ) = -(38 / 25 : ℝ) * Real.log x by ring]
  ring

/-- Given limits for the main and centered error integrals, the combined
Mangoldt sums converge to the Abel expression with only the lower boundary. -/
theorem twoShiftEuler_abel_limit {a M E : ℝ} (ha : 0 < a)
    (hm :
      Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, twoShiftEulerDensity t) Filter.atTop (nhds M))
    (he :
      Filter.Tendsto
        (fun b : ℝ ↦ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv twoShiftEulerDensity t)
        Filter.atTop (nhds E)) :
    Filter.Tendsto
      (fun b : ℝ ↦
        ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, ArithmeticFunction.vonMangoldt n * twoShiftEulerDensity n)
      Filter.atTop (nhds (M - (Chebyshev.psi a - a) * twoShiftEulerDensity a - E)) := by
  apply
    AnalyticNumberTheory.Arithmetic.mangoldt_centered_abel_tendsto ha.le _ _ hm he
      twoShiftEuler_boundary_zero
  · exact fun _ _ _ ht ↦ (density_analytic (ha.trans_le ht.1)).differentiableAt
  · intro b _
    exact
      (show ContinuousOn (deriv twoShiftEulerDensity) (Set.Icc a b) from fun t ht ↦
          (density_analytic
              (ha.trans_le ht.1)).deriv.continuousAt.continuousWithinAt).integrableOn_Icc

/-- The three coefficients of the common Euler polynomial in increasing order. -/
private noncomputable def mainCoeff : Fin 3 → ℝ :=
  ![combine poly 0, combine (fun v ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * v) 0,
    combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 0]

/-- Closed main tail at a lower endpoint, using the three logarithmic moments
with decay exponent 13/25. -/
noncomputable def twoShiftEulerMain (a : ℝ) : ℝ :=
  ∑ j : Fin 3, mainCoeff j * eulerMomentValue570 (13 / 25) j.val a

/-- The integral between endpoints at least one equals the difference of their
closed main tails. Expand the weight and integrate its three monomials. -/
theorem twoShiftEuler_main_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, twoShiftEulerDensity t) = twoShiftEulerMain a - twoShiftEulerMain b := by
  unfold twoShiftEulerMain
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply euler570_polynomial_interval (k := 0) (by norm_num only) ha hab
  intro t ht
  have ht0 := zero_lt_one.trans_le (ha.trans ht.1)
  rw [Fin.sum_univ_three]
  change
    _ =
      combine poly 0 * eulerMoment570 _ 0 t +
        combine (fun v ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * v) 0 *
          eulerMoment570 _ 1 t +
        combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 0 * eulerMoment570 _ 2 t
  unfold eulerMoment570 twoShiftEulerDensity twoShiftEulerPoly combine shift poly
  rw [show -(13 / 25 : ℝ) - 1 = -(38 / 25 : ℝ) by norm_num only, Real.rpow_def_of_pos ht0,
    mul_comm (Real.log t) (-(38 / 25 : ℝ))]
  ring

/-- The main integral tends to the closed tail at its lower endpoint. Each
upper endpoint moment vanishes since the decay exponent is positive. -/
theorem twoShiftEuler_main_limit {a : ℝ} (ha : 1 ≤ a) :
    Filter.Tendsto (fun b : ℝ ↦ ∫ t : ℝ in a..b, twoShiftEulerDensity t) Filter.atTop
      (nhds (twoShiftEulerMain a)) := by
  have h (k : ℕ) : Filter.Tendsto (eulerMomentValue570 (13 / 25) k) Filter.atTop (nhds 0) := by
    change
      Filter.Tendsto
        (fun t : ℝ ↦ t ^ (-(13 / 25 : ℝ)) * Analysis.logPowerTailPoly (13 / 25) k (Real.log t)) _ _
    simpa only [eulerMomentValue570, neg_mul, neg_neg, neg_zero] using
      (Analysis.log_power_tail_primitive_tendsto (by norm_num only : (0 : ℝ) < 13 / 25) k).neg
  have hz :=
    (((h 0).const_mul (mainCoeff 0)).add ((h 1).const_mul (mainCoeff 1))).add
      ((h 2).const_mul (mainCoeff 2))
  simp only [mul_zero, add_zero] at hz
  have hz' : Filter.Tendsto twoShiftEulerMain Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t ↦ twoShiftEulerMain t) _ _
    simp only [twoShiftEulerMain, Fin.sum_univ_three]
    exact hz
  have hh := hz'.const_sub (twoShiftEulerMain a)
  rw [sub_zero] at hh
  apply hh.congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  exact (twoShiftEuler_main_interval ha hb).symm

/-- For every lower endpoint at least one the centered error integral
converges. Its value is the closed main tail less the lower boundary and
the actual Mangoldt tail, by finite Abel summation and absolute convergence. -/
theorem twoShiftEuler_error_limit {a : ℝ} (ha : 1 ≤ a) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    Filter.Tendsto
      (fun b : ℝ ↦ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv twoShiftEulerDensity t)
      Filter.atTop
      (nhds
        (twoShiftEulerMain a - (Chebyshev.psi a - a) * twoShiftEulerDensity a -
          ((∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n))) := by
  intro f
  have hf0 : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_div, zero_mul]
  have hnat := AnalyticNumberTheory.Arithmetic.tendsto_tail_prefix f hf0 twoShiftEuler_summable a
  have hs :=
    hnat.comp
      (show Filter.Tendsto (fun b : ℝ ↦ ⌊b⌋₊) Filter.atTop Filter.atTop from
        tendsto_nat_floor_atTop)
  have h :=
    ((((twoShiftEuler_main_limit ha).add twoShiftEuler_boundary_zero).sub_const
          ((Chebyshev.psi a - a) * twoShiftEulerDensity a)).sub
      hs)
  rw [add_zero] at h
  apply h.congr'
  filter_upwards [Filter.eventually_ge_atTop a] with b hb
  have he := twoShiftEuler_abel (zero_lt_one.trans_le ha) hb
  dsimp only [Function.comp_apply, f]
  linarith only [he]

/-- An eventual lower bound on the finite centered error integrals bounds
the infinite common Euler tail from above, with the exact lower boundary. -/
theorem twoShiftEuler_tail_of_error {a D : ℝ} (ha : 1 ≤ a)
    (hd :
      ∀ᶠ b : ℝ in Filter.atTop,
        -D ≤ ∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv twoShiftEulerDensity t) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      twoShiftEulerMain a - (Chebyshev.psi a - a) * twoShiftEulerDensity a + D := by
  intro f
  have h := ge_of_tendsto (twoShiftEuler_error_limit ha) hd
  dsimp only at h
  dsimp only [f]
  linarith only [h]

/-- On every interval above 101, RH bounds the centered Abel error by the
integral of the explicit square-root log-square envelope against the negative
slope of the common two-shift weight. -/
theorem twoShiftEuler_error_RH (hRH : RiemannHypothesis) {a b : ℝ} (ha : 101 ≤ a) (hab : a ≤ b) :
    |∫ t : ℝ in a..b, (Chebyshev.psi t - t) * deriv twoShiftEulerDensity t| ≤
      ∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv twoShiftEulerDensity t := by
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 101) (j := 7) (n := 16) (lo := 4) (hi := 5)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlo
  have hcont :
    ContinuousOn (fun t : ℝ ↦ Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv twoShiftEulerDensity t)
      (Set.Icc a b) := by
    intro t ht
    have hp : 0 < t := by linarith only [ha, ht.1]
    exact
      ((Real.continuous_sqrt.continuousAt.mul
              (((Real.continuousAt_log hp.ne').pow 2).div_const 24)).mul
          (density_analytic hp).deriv.continuousAt.neg).continuousWithinAt
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab, ← Real.norm_eq_abs]
  apply
    MeasureTheory.norm_integral_le_of_norm_le
      (hcont.integrableOn_Icc.mono_set Set.Ioc_subset_Icc_self)
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with t ht
  have ht' := ha.trans ht.1.le
  have hp : 0 < t := by linarith only [ht']
  have hn :=
    (twoShiftEulerDensity_deriv_neg hp (hlo.trans (Real.log_le_log (by norm_num only) ht'))).le
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonpos hn]
  exact mul_le_mul_of_nonneg_right (psi_log_sq_of_RH hRH ht') (neg_nonneg.mpr hn)

/-- A uniform upper bound on the explicit slope integral bounds the full
Mangoldt tail under RH, including the lower Chebyshev boundary term. -/
theorem twoShiftEuler_tail_RH (hRH : RiemannHypothesis) {a D : ℝ} (ha : 101 ≤ a)
    (hd :
      ∀ᶠ b : ℝ in Filter.atTop,
        (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv twoShiftEulerDensity t) ≤
          D) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      twoShiftEulerMain a + Real.sqrt a * (Real.log a ^ 2 / 24) * twoShiftEulerDensity a + D := by
  intro f
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 101) (j := 7) (n := 16) (lo := 4) (hi := 5)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlo
  have hw : 0 ≤ twoShiftEulerDensity a :=
    mul_nonneg (Real.exp_pos _).le
      (twoShiftEulerPoly_pos (hlo.trans (Real.log_le_log (by norm_num only) ha))).le
  have he := mul_le_mul_of_nonneg_right (abs_le.mp (psi_log_sq_of_RH hRH ha)).1 hw
  have h :=
    twoShiftEuler_tail_of_error (a := a) (D := D) (by linarith only [ha])
      (by
        filter_upwards [hd, Filter.eventually_ge_atTop a] with b hb hab
        exact (abs_le.mp ((twoShiftEuler_error_RH hRH ha hab).trans hb)).1)
  dsimp only at h
  dsimp only [f]
  linarith only [h, he]

/-- Coefficients of ((38/25)P-P')/24 in increasing powers of the logarithm. -/
private noncomputable def errorCoeff : Fin 3 → ℝ :=
  ![(38 / 25 * mainCoeff 0 - mainCoeff 1) / 24, (38 / 25 * mainCoeff 1 - 2 * mainCoeff 2) / 24,
    (38 / 25 * mainCoeff 2) / 24]

/-- Closed tail for the square-root log-square error majorant. -/
noncomputable def twoShiftEulerError (a : ℝ) : ℝ :=
  ∑ j : Fin 3, errorCoeff j * eulerMomentValue570 (51 / 50) (2 + j.val) a

/-- The RH error envelope integrates exactly to the difference of three
endpoint moments of degrees two, three and four. -/
theorem twoShiftEuler_error_interval {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (∫ t : ℝ in a..b, Real.sqrt t * (Real.log t ^ 2 / 24) * -deriv twoShiftEulerDensity t) =
      twoShiftEulerError a - twoShiftEulerError b := by
  unfold twoShiftEulerError
  rw [← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  apply euler570_polynomial_interval (by norm_num only) ha hab
  intro t ht
  have hp := zero_lt_one.trans_le (ha.trans ht.1)
  let C := mainCoeff 0
  let L := mainCoeff 1
  let Q := mainCoeff 2
  have he :
    twoShiftEulerDensity =ᶠ[nhds t] fun x : ℝ ↦
      x ^ (-(38 / 25 : ℝ)) * (C + L * Real.log x + Q * Real.log x ^ 2) := by
    filter_upwards [lt_mem_nhds hp] with x hx
    unfold twoShiftEulerDensity twoShiftEulerPoly
    rw [Real.rpow_def_of_pos hx, mul_comm (Real.log x)]
    congr 1
    change combine poly _ = combine poly 0 + combine _ 0 * _ + combine _ 0 * _
    unfold combine shift poly
    ring
  have hl := Real.hasDerivAt_log hp.ne'
  have hd :=
    (Real.hasDerivAt_rpow_const (p := -(38 / 25 : ℝ)) (Or.inl hp.ne')).mul
      (((hl.const_mul L).const_add C).add ((hl.pow 2).const_mul Q))
  rw [he.deriv_eq]
  change
    _ *
        -deriv
            ((fun x : ℝ ↦ x ^ (-(38 / 25 : ℝ))) *
              ((fun x ↦ C + L * Real.log x) + fun y ↦ Q * (Real.log ^ 2) y))
            t =
      _
  rw [hd.deriv, Fin.sum_univ_three]
  change
    _ =
      ((38 / 25 * C - L) / 24) * eulerMoment570 _ 2 t +
        ((38 / 25 * L - 2 * Q) / 24) * eulerMoment570 _ 3 t +
        ((38 / 25 * Q) / 24) * eulerMoment570 _ 4 t
  have hpow : t ^ (-(38 / 25 : ℝ)) * t⁻¹ = t ^ (-(38 / 25 : ℝ) - 1) := by
    rw [Real.rpow_sub hp, Real.rpow_one, div_eq_mul_inv (t ^ _) t]
  have hs : Real.sqrt t * t ^ (-(38 / 25 : ℝ) - 1) = t ^ (-(51 / 50 : ℝ) - 1) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hp]
    norm_num only
  unfold eulerMoment570
  simp only [Pi.add_apply, Pi.pow_apply, Nat.cast_ofNat, Nat.reduceSub, pow_one]
  rw [← hs, ← hpow]
  ring

/-- Under RH, the common Euler tail above a cutoff at least 101 is bounded
by its main tail, the lower endpoint error and the three explicit error
moments. No unknown integral or convergence assumption remains. -/
theorem twoShiftEuler_tail_closed {a : ℝ} (hRH : RiemannHypothesis) (ha : 101 ≤ a) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊a⌋₊, f n ≤
      twoShiftEulerMain a + Real.sqrt a * (Real.log a ^ 2 / 24) * twoShiftEulerDensity a +
        twoShiftEulerError a := by
  have ha1 : 1 ≤ a := by linarith only [ha]
  have hm (k : ℕ) : Filter.Tendsto (eulerMomentValue570 (51 / 50) k) Filter.atTop (nhds 0) := by
    change
      Filter.Tendsto
        (fun t : ℝ ↦ t ^ (-(51 / 50 : ℝ)) * Analysis.logPowerTailPoly (51 / 50) k (Real.log t)) _ _
    simpa only [neg_mul, neg_neg, neg_zero] using
      (Analysis.log_power_tail_primitive_tendsto (by norm_num only : (0 : ℝ) < 51 / 50) k).neg
  have hz :=
    (((hm 2).const_mul (errorCoeff 0)).add ((hm 3).const_mul (errorCoeff 1))).add
      ((hm 4).const_mul (errorCoeff 2))
  simp only [mul_zero, add_zero] at hz
  have he : Filter.Tendsto twoShiftEulerError Filter.atTop (nhds 0) := by
    change Filter.Tendsto (fun t ↦ twoShiftEulerError t) _ _
    simp only [twoShiftEulerError, Fin.sum_univ_three]
    exact hz
  intro f
  apply le_of_forall_pos_le_add
  intro ε hε
  have hh :=
    twoShiftEuler_tail_RH (D := twoShiftEulerError a + ε) hRH ha
      (by
        filter_upwards [he.eventually (lt_mem_nhds (neg_lt_zero.mpr hε)),
          Filter.eventually_ge_atTop a] with b hb hab
        rw [twoShiftEuler_error_interval ha1 hab]
        linarith only [hb])
  dsimp only at hh
  dsimp only [f]
  linarith only [hh]

/-- Bound the three-character tail by minus four times the unsigned residual after truncation. -/
theorem three_trace_tail_residual {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {X : ℝ} (hX : 101 ≤ X)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-4 : ℝ) * ((∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n) ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) := by
  intro f D
  have hx : 101 ≤ ⌊X⌋₊ := Nat.le_floor hX
  have hlo :=
    (Analysis.rationalLogIntervalCheck_sound (N := 101) (j := 7) (n := 16) (lo := 4) (hi := 5)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlo
  have hl :=
    three_trace_tail_lower a b c ⌊X⌋₊
      (hlo.trans (Real.log_le_log (by norm_num only) (by exact_mod_cast hx))) ht
  have hs : Summable f := twoShiftEuler_summable
  have hp := hs.sum_add_tsum_compl (s := Finset.Icc 0 ⌊X⌋₊)
  change
    (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, f n) + (∑' n : { n : ℕ // n ∉ Finset.Icc 0 ⌊X⌋₊ }, f n.val) =
      ∑' n, f n at hp
  have hpred : (fun n : ℕ ↦ n ∉ Finset.Icc 0 ⌊X⌋₊) = (fun n : ℕ ↦ ⌊X⌋₊ < n) := by
    funext n
    simp only [Finset.mem_Icc, Nat.zero_le, true_and, not_le]
  rw [hpred] at hp
  rw [← Finset.sum_Ioc_add_eq_sum_Icc (Nat.zero_le _)] at hp
  have hf0 : f 0 = 0 := by
    dsimp only [f]; rw [ArithmeticFunction.map_zero, zero_div, zero_mul]
  rw [hf0, add_zero] at hp
  change
    (-4 : ℝ) * (∑' n : { n : ℕ // ⌊X⌋₊ < n }, f n.val) ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) at hl
  linarith only [hp, hl]

/-- At any real cutoff at least 101, the three-character Euler correction is
bounded below by minus four times the explicit unsigned tail cap. Integer
indices strictly beyond the floor are exactly the omitted Euler terms. -/
theorem three_trace_tail_closed {p q s : ℕ} (a : DirichletCharacter ℂ p)
    (b : DirichletCharacter ℂ q) (c : DirichletCharacter ℂ s) {X : ℝ} (hX : 101 ≤ X)
    (hRH : RiemannHypothesis) (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-4 : ℝ) *
        (twoShiftEulerMain X + Real.sqrt X * (Real.log X ^ 2 / 24) * twoShiftEulerDensity X +
          twoShiftEulerError X) ≤
      -(∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) := by
  intro f D
  have htau := three_trace_tail_residual a b c hX ht
  have hc := twoShiftEuler_tail_closed hRH hX
  linarith only [htau, hc]

/-- Rational upper endpoints of the three coefficients after translation by four. -/
private theorem shifted_coeff_upper :
    combine poly 4 ≤ 26562 / 100000 ∧
      combine (fun u ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * u) 4 ≤ 39625 / 100000 ∧
      combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 4 ≤ 12694 / 100000 := by
  unfold combine shift poly
  simp only [neg_mul, Real.exp_neg, ← one_div]
  refine ⟨?_, ?_, ?_⟩ <;>
    linarith only [exp_t.1, exp_t.2, one_div_le_one_div_of_le (Real.exp_pos _) exp_t.2,
      one_div_le_one_div_of_le (by norm_num only) exp_t.1, exp_b.1, exp_b.2,
      one_div_le_one_div_of_le (Real.exp_pos _) exp_b.2,
      one_div_le_one_div_of_le (by norm_num only) exp_b.1, exp_h.1, exp_h.2,
      one_div_le_one_div_of_le (Real.exp_pos _) exp_h.2,
      one_div_le_one_div_of_le (by norm_num only) exp_h.1]

/-- Beyond shift four, the rational upper coefficients from section 96
bound the common Euler quadratic uniformly. -/
theorem twoShiftEulerPoly_upper {v : ℝ} (hv : 4 ≤ v) :
    twoShiftEulerPoly v ≤ (26562 + 39625 * (v - 4) + 12694 * (v - 4) ^ 2) / 100000 := by
  let C := combine poly 4
  let L := combine (fun u ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * u) 4
  let Q := combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 4
  have h : C ≤ 26562 / 100000 ∧ L ≤ 39625 / 100000 ∧ Q ≤ 12694 / 100000 := shifted_coeff_upper
  have he : twoShiftEulerPoly v = C + L * (v - 4) + Q * (v - 4) ^ 2 := by
    unfold C L Q twoShiftEulerPoly combine shift poly
    ring
  rw [he]
  linarith only [h.1, mul_le_mul_of_nonneg_right h.2.1 (sub_nonneg.mpr hv),
    mul_le_mul_of_nonneg_right h.2.2 (sq_nonneg (v - 4))]

/-- At the squared section 96 entrance radius the Euler polynomial is
below 10.1. Certify the logarithm before evaluating its quadratic majorant. -/
theorem twoShiftEulerPoly_at_292 : twoShiftEulerPoly (Real.log ((292 : ℝ) ^ 2)) < 101 / 10 := by
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 5) (hi :=
      56768 / 10000) (by decide +kernel)
  norm_num only [Rat.cast_ofNat, Rat.cast_div] at h
  rw [Real.log_pow, Nat.cast_ofNat]
  have hl : 4 ≤ 2 * Real.log 292 := by linarith only [h.1]
  have hu : 2 * Real.log 292 - 4 ≤ 73536 / 10000 := by linarith only [h.2]
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hl) hu 2
  linarith only [twoShiftEulerPoly_upper hl, hs, hu]

/-- The lower endpoint error in the RH tail cap at radius 292 is below
0.000508, using a rational enclosure of the negative power at 85264. -/
theorem twoShiftEuler_boundary_292 :
    let X := (292 : ℝ) ^ 2
    Real.sqrt X * (Real.log X ^ 2 / 24) * twoShiftEulerDensity X < 508 / 1000000 := by
  intro X
  have hx : 0 < X := by norm_num only [X]
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 85264) (p := 38) (d :=
        25) (lo := 0) (hi := 3201 / 100000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hp
  have he : Real.exp (-(38 / 25 : ℝ) * Real.log X) ≤ 3201 / 100000000000 := by
    rw [mul_comm, ← Real.rpow_def_of_pos hx]
    norm_num only [X]
    linarith only [hp]
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 5) (hi :=
        568 / 100) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hlog
  have hL : Real.log X ≤ 1136 / 100 := by
    rw [show X = (292 : ℝ) ^ 2 by rfl, Real.log_pow, Nat.cast_ofNat]
    linarith only [hlog]
  have hL0 := Real.log_nonneg (show 1 ≤ X by norm_num only [X])
  have hsq := pow_le_pow_left₀ hL0 hL 2
  have hd :=
    mul_le_mul_of_nonneg_left twoShiftEulerPoly_at_292.le
      (Real.exp_pos (-(38 / 25 : ℝ) * Real.log X)).le
  have hw : twoShiftEulerDensity X ≤ 3201 / 100000000000 * (101 / 10) := by
    unfold twoShiftEulerDensity
    linarith only [hd, he]
  have hs : Real.sqrt X = 292 := Real.sqrt_sq (by norm_num only)
  rw [hs]
  have hprod := mul_le_mul_of_nonneg_left hw (show 0 ≤ 292 * (Real.log X ^ 2 / 24) by positivity)
  linarith only [hprod, hsq]

/-- At the entrance radius 292 the main Euler tail is below 0.080480.
Translate the endpoint moments by four before applying the positive upper
coefficients and the rational power enclosure. -/
theorem twoShiftEuler_main_292 : twoShiftEulerMain ((292 : ℝ) ^ 2) < 80480 / 1000000 := by
  let C := combine poly 4
  let L := combine (fun u ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * u) 4
  let Q := combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 4
  have h : C ≤ 26562 / 100000 ∧ L ≤ 39625 / 100000 ∧ Q ≤ 12694 / 100000 := shifted_coeff_upper
  let X := (292 : ℝ) ^ 2
  let u := Real.log X - 4
  let d := (13 / 25 : ℝ)
  let T := fun j : ℕ ↦ Analysis.logPowerTailPoly d j u
  have hz :=
    Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 5) (hi :=
      56768 / 10000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hz
  have hu : 0 ≤ u ∧ u ≤ 73536 / 10000 := by
    dsimp only [u, X]
    rw [Real.log_pow, Nat.cast_ofNat]
    constructor <;> linarith only [hz.1, hz.2]
  have hm (j : ℕ) := Analysis.log_power_tail_poly_mono (by norm_num only : 0 < d) hu.1 hu.2 j
  have hp (j : ℕ) := Analysis.log_power_tail_poly_nonneg (by norm_num only : 0 < d) hu.1 j
  have hc := mul_le_mul h.1 (hm 0) (hp 0) (by norm_num only)
  have hl := mul_le_mul h.2.1 (hm 1) (hp 1) (by norm_num only)
  have hq := mul_le_mul h.2.2 (hm 2) (hp 2) (by norm_num only)
  have hsum : C * T 0 + L * T 1 + Q * T 2 ≤ 294904 / 10000 := by
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, d] at hc hl hq
    dsimp only [T, Analysis.logPowerTailPoly, d, Nat.cast_ofNat]
    linarith only [hc, hl, hq]
  have hx :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 85264) (p := 13) (d :=
        25) (lo := 0) (hi := 272899 / 100000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hx
  have he : twoShiftEulerMain X = X ^ (-d) * (C * T 0 + L * T 1 + Q * T 2) := by
    unfold twoShiftEulerMain
    rw [Fin.sum_univ_three]
    change
      combine poly 0 * eulerMomentValue570 d 0 X +
          combine (fun v ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * v) 0 *
            eulerMomentValue570 d 1 X +
          combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 0 * eulerMomentValue570 d 2 X =
        _
    unfold eulerMomentValue570 C L Q T u combine shift poly
    norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat, d]
    ring
  change twoShiftEulerMain X < _
  rw [he]
  have hxp : X ^ (-d) ≤ 272899 / 100000000 := by
    norm_num only [X, d]; linarith only [hx]
  have hh := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (sq_nonneg (292 : ℝ)) (-d))
  linarith only [hxp, hh]

/-- At radius 292 the three RH error moments contribute less than 0.001009.
The negative linear coefficient uses a lower enclosure of the third moment. -/
theorem twoShiftEuler_error_292 : twoShiftEulerError ((292 : ℝ) ^ 2) < 1009 / 1000000 := by
  let X := (292 : ℝ) ^ 2
  let d := (51 / 50 : ℝ)
  let z := Real.log X
  let T := fun j : ℕ ↦ Analysis.logPowerTailPoly d j z
  have hc :
    errorCoeff 0 ≤ 171 / 2400 ∧ errorCoeff 1 ≤ -(119 / 2400) ∧ errorCoeff 2 ≤ 193 / 24000 := by
    change
      (38 / 25 * combine poly 0 - combine _ 0) / 24 ≤ _ ∧
        (38 / 25 * combine _ 0 - 2 * combine _ 0) / 24 ≤ _ ∧ (38 / 25 * combine _ 0) / 24 ≤ _
    unfold combine shift poly
    simp only [neg_mul, Real.exp_neg, ← one_div]
    refine ⟨?_, ?_, ?_⟩ <;>
      linarith only [exp_t.1, exp_t.2, one_div_le_one_div_of_le (Real.exp_pos _) exp_t.2,
        one_div_le_one_div_of_le (by norm_num only) exp_t.1, exp_b.1, exp_b.2,
        one_div_le_one_div_of_le (Real.exp_pos _) exp_b.2,
        one_div_le_one_div_of_le (by norm_num only) exp_b.1, exp_h.1, exp_h.2,
        one_div_le_one_div_of_le (Real.exp_pos _) exp_h.2,
        one_div_le_one_div_of_le (by norm_num only) exp_h.1]
  have hz :=
    Analysis.rationalLogIntervalCheck_sound (N := 292) (j := 8) (n := 24) (lo := 5675 / 1000) (hi :=
      5677 / 1000) (by decide +kernel)
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hz
  have hz' : 11350 / 1000 ≤ z ∧ z ≤ 11354 / 1000 := by
    dsimp only [z, X]
    rw [Real.log_pow, Nat.cast_ofNat]
    constructor <;> linarith only [hz.1, hz.2]
  have hp (j : ℕ) :=
    Analysis.log_power_tail_poly_nonneg (by norm_num only : 0 < d)
      (by linarith only [hz'.1] : 0 ≤ z) j
  have hu (j : ℕ) :=
    Analysis.log_power_tail_poly_mono (by norm_num only : 0 < d) (by linarith only [hz'.1] : 0 ≤ z)
      hz'.2 j
  have hl := Analysis.log_power_tail_poly_mono (by norm_num only : 0 < d) (by norm_num only) hz'.1 3
  have h0 := mul_le_mul hc.1 (hu 2) (hp 2) (by norm_num only)
  have h1 := mul_le_mul_of_nonneg_right hc.2.1 (hp 3)
  have h2 := mul_le_mul hc.2.2 (hu 4) (hp 4) (by norm_num only)
  have hsum : errorCoeff 0 * T 2 + errorCoeff 1 * T 3 + errorCoeff 2 * T 4 ≤ 10794 / 100 := by
    dsimp only [T]
    norm_num only [Analysis.logPowerTailPoly, d, Nat.cast_ofNat] at h0 h1 h2 hl ⊢
    linarith only [h0, h1, h2, hl]
  have hx :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 85264) (p := 51) (d :=
        50) (lo := 0) (hi := 93459 / 10000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at hx
  have hxp : X ^ (-d) ≤ 93459 / 10000000000 := by
    norm_num only [X, d]; linarith only [hx]
  have hh := mul_le_mul_of_nonneg_left hsum (Real.rpow_nonneg (sq_nonneg (292 : ℝ)) (-d))
  unfold twoShiftEulerError
  rw [Fin.sum_univ_three]
  change
    errorCoeff 0 * (X ^ (-d) * T 2) + errorCoeff 1 * (X ^ (-d) * T 3) +
        errorCoeff 2 * (X ^ (-d) * T 4) <
      _
  linarith only [hh, hxp]

/-- At the section 96 entrance, the positive common Euler tail is below
0.081997 under RH, by adding the three rational endpoint bounds. -/
theorem twoShiftEuler_tail_292 (hRH : RiemannHypothesis) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 85264, f n < 81997 / 1000000 := by
  intro f
  have h := twoShiftEuler_tail_closed hRH (by norm_num only : (101 : ℝ) ≤ 292 ^ 2)
  dsimp only at h
  rw [show ⌊(292 : ℝ) ^ 2⌋₊ = 85264 by norm_num only [Nat.floor_ofNat]] at h
  dsimp only [f]
  linarith only [h, twoShiftEuler_main_292, twoShiftEuler_boundary_292, twoShiftEuler_error_292]

/-- The entrance bound holds for every larger cutoff: increasing the cutoff
removes only positive Euler weights. -/
theorem twoShiftEuler_tail_large {X : ℝ} (hX : 85264 ≤ X) (hRH : RiemannHypothesis) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n < 81997 / 1000000 := by
  intro f
  have hf : 85264 ≤ ⌊X⌋₊ := Nat.le_floor hX
  have hlog :=
    (Analysis.rationalLogIntervalCheck_sound (N := 101) (j := 7) (n := 16) (lo := 4) (hi := 5)
        (by decide +kernel)).1
  norm_num only [Rat.cast_ofNat] at hlog
  have hp : ∑ n ∈ Finset.Ioc 0 85264, f n ≤ ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, f n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.Ioc_subset_Ioc le_rfl hf)
    intro n hn hout
    have hgt : 85264 < n :=
      lt_of_not_ge (fun h ↦ hout (Finset.mem_Ioc.mpr ⟨(Finset.mem_Ioc.mp hn).1, h⟩))
    have hl : (101 : ℝ) ≤ n := Nat.cast_le.mpr ((by decide : 101 ≤ 85264).trans hgt.le)
    exact
      mul_nonneg
        (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _))
        (twoShiftEulerPoly_pos (hlog.trans (Real.log_le_log (by norm_num only) hl))).le
  have he := twoShiftEuler_tail_292 hRH
  change (∑' n, f n) - ∑ n ∈ Finset.Ioc 0 85264, f n < _ at he
  linarith only [hp, he]

/-- Above the squared radius 292, the three-character Euler tail exceeds −0.327988 under RH. -/
theorem three_trace_tail_large {p q s : ℕ} (a : DirichletCharacter ℂ p) (b : DirichletCharacter ℂ q)
    (c : DirichletCharacter ℂ s) {X : ℝ} (hX : 85264 ≤ X) (hRH : RiemannHypothesis)
    (ht : ∀ n : ℕ, -1 ≤ (a n).re + (b n).re + (c n).re) :
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-327988 / 1000000 : ℝ) < -(∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) := by
  intro f D
  have htau := three_trace_tail_residual a b c (show 101 ≤ X by linarith only [hX]) ht
  have hc := twoShiftEuler_tail_large hX hRH
  linarith only [htau, hc]

/-- For three odd levels and log input at least 584, the signed Jacobi tail at the
quarter-square cutoff exceeds −0.327988 under RH. Pair multiplicativity bounds the trace. -/
theorem pair_twoShift_tail_quarter (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {L X : ℝ} (hL : 584 ≤ L) (hX : L ^ 2 / 4 ≤ X)
    (hRH : RiemannHypothesis) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-327988 / 1000000 : ℝ) < -(∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) := by
  intro a b c f D
  apply three_trace_tail_large a b c (X := X) _ hRH
  · intro k
    simpa only [Int.cast_natCast] using
      pair_character_sum_ge_neg_one (k : ℤ) p q r (hp.mul hq) (hp.mul hr) (hq.mul hr)
  · nlinarith only [hX, hL, sq_nonneg (L - 584)]

/-- At radii at least 292, the fixed pole term and signed common Euler tail together
contribute more than 1.006328 to the finite remainder for the three Jacobi characters. -/
theorem pair_twoShift_fixed_lower (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {L X : ℝ} (hL : 584 ≤ L) (hX : L ^ 2 / 4 ≤ X)
    (hRH : RiemannHypothesis) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (1006328 / 1000000 : ℝ) <
      twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) := by
  intro a b c f D
  have h := pair_twoShift_tail_quarter p q r hp hq hr hL hX hRH
  change (-327988 / 1000000 : ℝ) < -(∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) at h
  linarith only [h, twoShiftPoleConstant_lower]

/-- For log input at least 584, combine the pole, signed Jacobi tail and conductor
terms of (96.25), retaining the positive reciprocal-radius correction. -/
theorem pair_twoShift_unreflected_lower (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {L X : ℝ} (hL : 584 ≤ L) (hX : L ^ 2 / 4 ≤ X)
    (hRH : RiemannHypothesis) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-149672 / 1000000 : ℝ) + (88098 / 10000) / (L / 2) <
      twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) +
        twoShiftConductor (2 * Real.log (L / 2)) +
        twoShiftReciprocalCoeff / (L / 2) := by
  intro a b c f D
  have h := pair_twoShift_fixed_lower p q r hp hq hr hL hX hRH
  change
    (1006328 / 1000000 : ℝ) <
      twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) at h
  have hc := twoShiftConductor_lower (show 292 ≤ L / 2 by linarith only [hL])
  have hpole :=
    div_lt_div_of_pos_right twoShiftReciprocalCoeff_lower (show 0 < L / 2 by linarith only [hL])
  linarith only [h, hc, hpole]

/-- Above radius 475, a reflected tail at most 0.0053 suffices for the −1/8 bound
on the remainder formed with the three actual Jacobi characters under RH. -/
theorem pair_twoShift_large_remainder (p q r : ℕ) [NeZero p] [NeZero q] [NeZero r] (hp : Odd p)
    (hq : Odd q) (hr : Odd r) {L X : ℝ} (hL : 950 ≤ L) (hX : L ^ 2 / 4 ≤ X)
    (hRH : RiemannHypothesis) {R : ℝ} (hR : R ≤ 53 / 10000) :
    let a := NumberTheory.complexJacobiNumeratorCharacter (p * q) (hp.mul hq)
    let b := NumberTheory.complexJacobiNumeratorCharacter (p * r) (hp.mul hr)
    let c := NumberTheory.complexJacobiNumeratorCharacter (q * r) (hq.mul hr)
    let f := fun n : ℕ ↦
      ArithmeticFunction.vonMangoldt n / (n : ℝ) ^ (38 / 25 : ℝ) * twoShiftEulerPoly (Real.log n)
    let D := fun n : ℕ ↦ 3 - ((a n).re + (b n).re + (c n).re)
    (-1 / 8 : ℝ) <
      twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) +
          twoShiftConductor (2 * Real.log (L / 2)) +
          twoShiftReciprocalCoeff / (L / 2) -
        2 * R := by
  intro a b c f D
  have hh := pair_twoShift_fixed_lower p q r hp hq hr (show 584 ≤ L by linarith only [hL]) hX hRH
  change
    (1006328 / 1000000 : ℝ) <
      twoShiftPoleConstant - (∑' n : { n : ℕ // ⌊X⌋₊ < n }, D n.val * f n.val) at hh
  have hc := twoShiftConductor_lower_475 (show 475 ≤ L / 2 by linarith only [hL])
  have hpole :=
    div_pos (show 0 < twoShiftReciprocalCoeff by linarith only [twoShiftReciprocalCoeff_lower])
      (show 0 < L / 2 by linarith only [hL])
  linarith only [hh, hc, hpole, hR]

/-- Bound three consecutive logarithmic moments using both ends of a log interval.
The negative linear coefficient requires a lower enclosure of the middle moment. -/
private theorem moment_triple_box {d x l u c₀ c₁ c₂ C₀ C₁ C₂ : ℝ} (hd : 0 < d) (hl : 0 ≤ l)
    (hlx : l ≤ x) (hxu : x ≤ u) (i : ℕ) (hc₀ : c₀ ≤ C₀) (hc₁ : c₁ ≤ C₁) (hc₂ : c₂ ≤ C₂)
    (h₀ : 0 ≤ C₀) (h₁ : C₁ ≤ 0) (h₂ : 0 ≤ C₂) :
    let T := Analysis.logPowerTailPoly d
    c₀ * T i x + c₁ * T (i + 1) x + c₂ * T (i + 2) x ≤
      C₀ * T i u + C₁ * T (i + 1) l + C₂ * T (i + 2) u := by
  intro T
  have hp (k : ℕ) := Analysis.log_power_tail_poly_nonneg hd (hl.trans hlx) k
  have hu (k : ℕ) := Analysis.log_power_tail_poly_mono hd (hl.trans hlx) hxu k
  have hm := Analysis.log_power_tail_poly_mono hd hl hlx (i + 1)
  exact
    add_le_add
      (add_le_add (mul_le_mul hc₀ (hu i) (hp i) h₀)
        ((mul_le_mul_of_nonneg_right hc₁ (hp _)).trans (mul_le_mul_of_nonpos_left hm h₁)))
      (mul_le_mul hc₂ (hu _) (hp _) h₂)

/-- Bound the main and error terms of the Euler envelope at any positive cutoff
from opposite endpoints of a rational logarithm enclosure. -/
theorem twoShiftEuler_moment_boxes {A l u : ℝ} (hA : 0 < A) (hl : 0 ≤ l) (hlA : l ≤ Real.log A)
    (hAu : Real.log A ≤ u) :
    let T := Analysis.logPowerTailPoly
    twoShiftEulerMain A ≤
        A ^ (-(13 / 25 : ℝ)) *
          ((711631 * T (13 / 25) 0 u - 619250 * T (13 / 25) 1 l + 126937 * T (13 / 25) 2 u) /
            1000000) ∧
      twoShiftEulerError A ≤
        A ^ (-(51 / 50 : ℝ)) *
          ((70873 * T (51 / 50) 2 u - 49797 * T (51 / 50) 3 l + 8040 * T (51 / 50) 4 u) /
            1000000) := by
  intro T
  have hc :
    mainCoeff 0 ≤ 711631 / 1000000 ∧
      mainCoeff 1 ≤ -(619250 / 1000000) ∧
      mainCoeff 2 ≤ 126937 / 1000000 ∧
      errorCoeff 0 ≤ 70873 / 1000000 ∧
      errorCoeff 1 ≤ -(49797 / 1000000) ∧ errorCoeff 2 ≤ 8040 / 1000000 := by
    let C := combine poly 0
    let L := combine (fun v ↦ 3 * (51 / 50) / 8 + 2 * (51 / 50 : ℝ) ^ 2 / 8 * v) 0
    let Q := combine (fun _ ↦ (51 / 50 : ℝ) ^ 2 / 8) 0
    change
      C ≤ _ ∧
        L ≤ _ ∧
        Q ≤ _ ∧ (38 / 25 * C - L) / 24 ≤ _ ∧ (38 / 25 * L - 2 * Q) / 24 ≤ _ ∧ 38 / 25 * Q / 24 ≤ _
    unfold C L Q combine shift poly
    simp only [neg_mul, Real.exp_neg, ← one_div]
    repeat' constructor
    all_goals
      linarith only [exp_t.1, exp_t.2, exp_b.1, exp_b.2, exp_h.1, exp_h.2,
        one_div_le_one_div_of_le (Real.exp_pos _) exp_t.2,
        one_div_le_one_div_of_le (by norm_num only) exp_t.1,
        one_div_le_one_div_of_le (Real.exp_pos _) exp_b.2,
        one_div_le_one_div_of_le (by norm_num only) exp_b.1,
        one_div_le_one_div_of_le (Real.exp_pos _) exp_h.2,
        one_div_le_one_div_of_le (by norm_num only) exp_h.1]
  obtain ⟨hc₀, hc₁, hc₂, he₀, he₁, he₂⟩ := hc
  have hm :=
    moment_triple_box (by norm_num only : (0 : ℝ) < 13 / 25) hl hlA hAu 0 hc₀ hc₁ hc₂
      (by norm_num only) (by norm_num only) (by norm_num only)
  have he :=
    moment_triple_box (by norm_num only : (0 : ℝ) < 51 / 50) hl hlA hAu 2 he₀ he₁ he₂
      (by norm_num only) (by norm_num only) (by norm_num only)
  constructor
  · unfold twoShiftEulerMain
    rw [Fin.sum_univ_three]
    have h := mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hA.le (-(13 / 25 : ℝ)))
    dsimp only [eulerMomentValue570, T, Fin.val_zero, Fin.val_one, Fin.val_two]
    linarith only [h]
  · unfold twoShiftEulerError
    rw [Fin.sum_univ_three]
    have h := mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hA.le (-(51 / 50 : ℝ)))
    dsimp only [eulerMomentValue570, T, Fin.val_zero, Fin.val_one, Fin.val_two]
    linarith only [h]

/-- At a log upper endpoint u the boundary contribution uses the same power
A ^ (-51 / 50) as the error moments. -/
theorem twoShiftEuler_boundary_box {A u : ℝ} (hA : 0 < A) (hl : 4 ≤ Real.log A)
    (hu : Real.log A ≤ u) :
    Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A ≤
      A ^ (-(51 / 50 : ℝ)) *
        (u ^ 2 / 24 * ((26562 + 39625 * (u - 4) + 12694 * (u - 4) ^ 2) / 100000)) := by
  have hv := sub_le_sub_right hu 4
  have hs := pow_le_pow_left₀ (sub_nonneg.mpr hl) hv 2
  have hp := twoShiftEulerPoly_upper hl
  have hq :
    twoShiftEulerPoly (Real.log A) ≤ (26562 + 39625 * (u - 4) + 12694 * (u - 4) ^ 2) / 100000 := by
    linarith only [hp, hv, hs]
  have hpow : Real.sqrt A * Real.exp (-(38 / 25) * Real.log A) = A ^ (-(51 / 50 : ℝ)) := by
    rw [mul_comm (-(38 / 25 : ℝ)), ← Real.rpow_def_of_pos hA, Real.sqrt_eq_rpow, ← Real.rpow_add hA]
    norm_num only
  have hw :=
    mul_le_mul
      (div_le_div_of_nonneg_right (pow_le_pow_left₀ (by linarith only [hl]) hu 2)
        (by norm_num only : (0 : ℝ) ≤ 24))
      hq (twoShiftEulerPoly_pos hl).le (div_nonneg (sq_nonneg _) (by norm_num only))
  unfold twoShiftEulerDensity
  rw [← hpow]
  linarith only [mul_le_mul_of_nonneg_left hw
      (mul_nonneg (Real.sqrt_nonneg A) (Real.exp_pos (-(38 / 25) * Real.log A)).le)]

/-- A rational endpoint test for the full Euler cap. Its three scalar inputs
bound the main, boundary and error polynomials after enclosing the logarithm. -/
theorem twoShiftEuler_cap_box {A l u P Q m b e : ℝ} (hA : 0 < A) (hl : 4 ≤ l) (hlA : l ≤ Real.log A)
    (hAu : Real.log A ≤ u) (hP : A ^ (-(13 / 25 : ℝ)) ≤ P) (hQ : A ^ (-(51 / 50 : ℝ)) ≤ Q)
    (hm :
      (711631 * Analysis.logPowerTailPoly (13 / 25) 0 u -
              619250 * Analysis.logPowerTailPoly (13 / 25) 1 l +
            126937 * Analysis.logPowerTailPoly (13 / 25) 2 u) /
          1000000 ≤
        m)
    (hb : u ^ 2 / 24 * ((26562 + 39625 * (u - 4) + 12694 * (u - 4) ^ 2) / 100000) ≤ b)
    (he :
      (70873 * Analysis.logPowerTailPoly (51 / 50) 2 u -
              49797 * Analysis.logPowerTailPoly (51 / 50) 3 l +
            8040 * Analysis.logPowerTailPoly (51 / 50) 4 u) /
          1000000 ≤
        e)
    (hm0 : 0 ≤ m) (hbe : 0 ≤ b + e) :
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      P * m + Q * (b + e) := by
  have h := twoShiftEuler_moment_boxes hA (by linarith only [hl]) hlA hAu
  have h₁ := h.1.trans (mul_le_mul_of_nonneg_left hm (Real.rpow_nonneg hA.le _))
  have h₂ :=
    (twoShiftEuler_boundary_box hA (hl.trans hlA) hAu).trans
      (mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hA.le _))
  have h₃ := h.2.trans (mul_le_mul_of_nonneg_left he (Real.rpow_nonneg hA.le _))
  linarith only [h₁, h₂, h₃, mul_le_mul_of_nonneg_right hP hm0, mul_le_mul_of_nonneg_right hQ hbe]

/-- The full Euler envelope at radius 292 is at most 0.0819835,
retaining enough precision for the interval ending at 292.25. -/
theorem twoShiftEuler_cap_292 :
    let A := (292 : ℝ) ^ 2
    twoShiftEulerMain A + Real.sqrt A * (Real.log A ^ 2 / 24) * twoShiftEulerDensity A +
        twoShiftEulerError A ≤
      819835 / 10000000 := by
  intro A
  have h :=
    Analysis.rationalLogIntervalCheck_sound (N := 85264) (j := 16) (n := 24) (lo :=
      113535076 / 10000000) (hi := 113535077 / 10000000) (by decide +kernel)
  have hp :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 85264) (p := 13) (d :=
        25) (lo := 0) (hi := 27289894 / 10000000000) (by decide +kernel)).2
  have hq :=
    (AnalyticNumberTheory.Arithmetic.rationalPowerIntervalCheck_sound (b := 85264) (p := 51) (d :=
        50) (lo := 0) (hi := 93458539 / 10000000000000) (by decide +kernel)).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Nat.cast_ofNat] at h hp hq
  have hA : A = 85264 := by norm_num only [A]
  rw [hA]
  apply
    (twoShiftEuler_cap_box (by norm_num only) (by norm_num only) h.1 h.2 hp hq (m :=
        2948931 / 100000) (b := 539435 / 10000) (e := 1073343 / 10000)
        (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]) (by norm_num only)
        (by norm_num only [Analysis.logPowerTailPoly, Nat.cast_ofNat]) (by norm_num only)
        (by norm_num only)).trans
  norm_num only

end PseudoPrime.PrimeTestBounds.MillerRabin
