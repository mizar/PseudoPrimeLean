/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Gamma.GammaNodeRationalCertificate
public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianGammaCoefficients

/-! # Rational bounds for the Gaussian gamma coefficient at order zero -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

/-- The zeroth coefficient of the even gamma expansion for a rational pole
rate, formed from the two shifted digamma arguments. -/
noncomputable def gammaZeroCoeff (a : ℚ) : ℝ :=
  ((Complex.digamma (((9 / 2 - a) / 2 : ℚ) : ℂ)).re +
        (Complex.digamma (((a + 1 / 2) / 2 : ℚ) : ℂ)).re) /
      2 -
    Real.log Real.pi

/-- Enclose the zeroth coefficient using two rational digamma prefixes
and the certified interval for the logarithm of pi. -/
@[expose]
def gammaZeroBounds (a : ℚ) : ℚ × ℚ :=
  let U := (9 / 2 - a) / 2
  let V := (a + 1 / 2) / 2
  let lo := AnalyticNumberTheory.Gamma.rationalDigammaLower
  let hi := AnalyticNumberTheory.Gamma.rationalDigammaUpper
  ((lo U 32 5 12 + lo V 32 5 12) / 2 - 35772809 / 31250000,
    (hi U 32 5 12 + hi V 32 5 12) / 2 - 286182471 / 250000000)

/-- The computed endpoints enclose the analytic zeroth coefficient
when the pole is between one half and seven halves. -/
theorem gamma_zero_bounds {a : ℚ} (ha₀ : 1 / 2 ≤ a) (ha₁ : a ≤ 7 / 2) :
    ((gammaZeroBounds a).1 : ℝ) ≤ gammaZeroCoeff a ∧
      gammaZeroCoeff a ≤ ((gammaZeroBounds a).2 : ℝ) := by
  let U : ℚ := (9 / 2 - a) / 2
  let V : ℚ := (a + 1 / 2) / 2
  have hu : (1 / 2 : ℚ) ≤ U := by
    dsimp only [U]; linarith only [ha₁]
  have hv : (1 / 2 : ℚ) ≤ V := by
    dsimp only [V]; linarith only [ha₀]
  have hU :=
    AnalyticNumberTheory.Gamma.rationalDigammaBounds_sound hu 32 5 12
      (by
        apply abs_lt.mpr; norm_num only [U]; constructor <;> linarith only [ha₀, ha₁])
  have hV :=
    AnalyticNumberTheory.Gamma.rationalDigammaBounds_sound hv 32 5 12
      (by
        apply abs_lt.mpr; norm_num only [V]; constructor <;> linarith only [ha₀, ha₁])
  have hpi := AnalyticNumberTheory.Gamma.gamma_log_pi_bounds
  simp only [gammaZeroBounds, gammaZeroCoeff, Rat.cast_sub, Rat.cast_div, Rat.cast_add,
    Rat.cast_ofNat]
  simp only [U, V, Rat.cast_sub, Rat.cast_div, Rat.cast_add, Rat.cast_ofNat] at hU hV hpi
  exact ⟨by linarith only [hU.1, hV.1, hpi.2], by linarith only [hU.2, hV.2, hpi.1]⟩

/-- The shared rational enclosure applies to both middle-kernel pole rates. -/
theorem middle_gamma_zero_bounds {a : ℚ} (ha : a = 2 ∨ a = 49 / 20) :
    ((gammaZeroBounds a).1 : ℝ) ≤ gammaZeroCoeff a ∧
      gammaZeroCoeff a ≤ ((gammaZeroBounds a).2 : ℝ) := by
  rcases ha with rfl | rfl <;> exact gamma_zero_bounds (by norm_num only) (by norm_num only)

/-- Recombine the forward and reflected reciprocal differences with their
digamma baselines. The forward baseline starts after the two isolated terms. -/
theorem gamma_zero_from_differences {a : ℚ} (ha : -(1 / 2) < a) (ha' : a < 9 / 2) :
    let b : ℝ := 17 / 32
    let f : ℝ := ((9 / 2 - a : ℚ) : ℝ)
    let r : ℝ := ((a + 1 / 2 : ℚ) : ℝ)
    ((Complex.digamma (((b + 2 : ℝ) : ℂ))).re + (Complex.digamma (b : ℂ)).re) / 2 -
          Real.log Real.pi +
        (∑' n : ℕ, (1 / (2 * (b + 2 + n)) - 1 / (f + 2 * n))) +
        (∑' n : ℕ, (1 / (2 * (b + n)) - 1 / (r + 2 * n))) =
      gammaZeroCoeff a := by
  intro b f r
  have hf : 0 < f := Rat.cast_pos.mpr (sub_pos.mpr ha')
  have hr : 0 < r := Rat.cast_pos.mpr (neg_lt_iff_pos_add.mp ha)
  have hb : 0 < b := by norm_num only [b]
  rw [gamma_pole_diff_tsum (add_pos hb (by norm_num only)) hf, gamma_pole_diff_tsum hb hr]
  simp only [gammaZeroCoeff, f, r, Rat.cast_div, Rat.cast_ofNat, Complex.ofReal_div,
    Complex.ofReal_ofNat, Complex.ofReal_ratCast]
  ring

/-- The exact width of the shifted rational digamma enclosure. The
reciprocal prefix and logarithmic polynomial cancel between the endpoints. -/
@[expose]
def gammaDigammaWidth (r : ℚ) : ℚ :=
  5 / 2000000000 + 2 * Analysis.rationalLogRemainder (1 - (r + 32) / 2 ^ 5) 12 +
    (1 / 8 : ℚ) * (r + 32)⁻¹ ^ 2

/-- The zeroth Gamma coefficient width consists of the two digamma
widths and the certified width for the logarithm of pi. -/
@[expose]
def gammaZeroWidth (a : ℚ) : ℚ :=
  (gammaDigammaWidth ((9 / 2 - a) / 2) + gammaDigammaWidth ((a + 1 / 2) / 2)) / 2 + 1 / 250000000

/-- Compute the zeroth coefficient width without replaying either prefix. -/
theorem gamma_zero_width_eq (a : ℚ) :
    (gammaZeroBounds a).2 - (gammaZeroBounds a).1 = gammaZeroWidth a := by
  simp only [gammaZeroBounds, gammaZeroWidth, gammaDigammaWidth,
    AnalyticNumberTheory.Gamma.rationalDigammaLower,
    AnalyticNumberTheory.Gamma.rationalDigammaUpper, Analysis.rationalLogLower,
    Analysis.rationalLogUpper, Nat.cast_ofNat]
  ring

end PseudoPrime.PrimeTestBounds.MillerRabin
