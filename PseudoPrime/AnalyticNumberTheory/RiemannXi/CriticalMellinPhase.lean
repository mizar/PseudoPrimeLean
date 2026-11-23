/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinQuadrature
import all PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinQuadrature
import all PseudoPrime.Analysis.ComplexCpowDerivatives
import PseudoPrime.Analysis.RationalPhaseTaylor
import PseudoPrime.Analysis.ScaledRationalPhase
import PseudoPrime.Analysis.ScaledRationalExp
import PseudoPrime.Analysis.PreciseLogTaylorBounds
import PseudoPrime.Analysis.PiFiftyInternal
import PseudoPrime.Analysis.RationalMellinWeight
import PseudoPrime.Analysis.RationalMellinWeightCheck
import PseudoPrime.Analysis.RationalMellinWeightTail
import PseudoPrime.Analysis.RationalMellinWeightAdaptive
import PseudoPrime.Analysis.RationalMellinWeightFast
import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinTerm
import PseudoPrime.AnalyticNumberTheory.RiemannXi.CriticalMellinPower

/-! # Rational phase certificates for critical-line quadrature -/

public section

namespace PseudoPrime.AnalyticNumberTheory.RiemannXi

/-- The 50-place rational interval for π, certified by internal nested
square-root inequalities. The computational certificate is not exported. -/
theorem pi_fifty_bounds :
    (314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℝ) < Real.pi ∧
      Real.pi < (314159265358979323846264338327950288419716939937511 / 10 ^ 50 : ℝ) := by
  exact ⟨Analysis.pi_lower_fifty, Analysis.pi_upper_fifty⟩

set_option maxRecDepth 8192 in
/-- A 256-term rational Taylor certificate encloses `log 2` to sixty
decimal places. Both endpoints are verified by the kernel using the series
for `log (1/2)`; no external numerical table is used. -/
theorem log_two_sixty_bounds :
    (693147180559945309417232121458176568075500134360255254120680 / 10 ^ 60 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤
        (693147180559945309417232121458176568075500134360255254120681 / 10 ^ 60 : ℝ) := by
  have hc :
    Analysis.rationalLogIntervalCheck (1 / 2) 0 256
        (-693147180559945309417232121458176568075500134360255254120681 / 10 ^ 60)
        (-693147180559945309417232121458176568075500134360255254120680 / 10 ^ 60) =
      true := by
    decide +kernel
  have h := Analysis.rationalLogIntervalCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_neg, Rat.cast_ofNat, Rat.cast_pow] at h
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num only, Real.log_inv] at h
  constructor <;> linarith only [h.1, h.2]

private def logSixtyLower (N : ℚ) (j : ℕ) : ℚ :=
  j * (693147180559945309417232121458176568075500134360255254120680 / 10 ^ 60) -
    Analysis.rationalLogSeries (1 - N / 2 ^ j) 256 -
    Analysis.rationalLogRemainder (1 - N / 2 ^ j) 256

private def logSixtyUpper (N : ℚ) (j : ℕ) : ℚ :=
  j * (693147180559945309417232121458176568075500134360255254120681 / 10 ^ 60) -
      Analysis.rationalLogSeries (1 - N / 2 ^ j) 256 +
    Analysis.rationalLogRemainder (1 - N / 2 ^ j) 256

/-- Positive rational inputs with convergent binary-scale displacement have
their logarithms enclosed by rational 256-term Taylor bounds. The bounds use
the kernel-certified sixty-place interval for `log 2`. -/
private theorem log_sixty_bounds {N : ℚ} (hN : 0 < N) (j : ℕ) (hx : |1 - N / 2 ^ j| < 1) :
    (logSixtyLower N j : ℝ) ≤ Real.log (N : ℝ) ∧ Real.log (N : ℝ) ≤ (logSixtyUpper N j : ℝ) := by
  have hxR : |1 - (N : ℝ) / 2 ^ j| < 1 := by
    have h := (Rat.cast_lt (K := ℝ)).mpr hx
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_one, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat] using h
  have ht :=
    Analysis.log_bounds_of_taylor_real ((Rat.cast_pos (K := ℝ)).mpr hN) j 256 (x :=
      1 - (N : ℝ) / 2 ^ j) rfl hxR
  have hl := mul_le_mul_of_nonneg_left log_two_sixty_bounds.1 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  have hu := mul_le_mul_of_nonneg_left log_two_sixty_bounds.2 (Nat.cast_nonneg j : (0 : ℝ) ≤ j)
  simp only [logSixtyLower, logSixtyUpper, Rat.cast_add, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_natCast, Rat.cast_div, Rat.cast_ofNat, Analysis.rationalLogSeries_cast,
    Analysis.rationalLogRemainder, Rat.cast_pow, Rat.cast_abs, Rat.cast_one]
  constructor <;> linarith only [ht.1, ht.2, hl, hu]

set_option maxRecDepth 8192 in
/-- The midpoint of the rational logarithm bounds has the uniform
high-precision error required by the fixed grid. -/
private theorem rational_log_midpoint_fifty {N : ℚ} (hN : 0 < N) (j : ℕ) (hj : j ≤ 6)
    (hd : |1 - N / 2 ^ j| ≤ 1 / 2) :
    |Real.log (N : ℝ) - (((logSixtyLower N j + logSixtyUpper N j) / 2 : ℚ) : ℝ)| ≤
      1 / (2 * 10 ^ 50) := by
  let d : ℚ := |1 - N / 2 ^ j|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hd1 : d ≤ 1 / 2 := hd
  have hdlt : d < 1 := lt_of_le_of_lt hd1 (by norm_num only)
  have hp : d ^ 257 ≤ (1 / 2 : ℚ) ^ 257 := pow_le_pow_left₀ hd0 hd1 257
  have hr : d ^ 257 / (1 - d) ≤ 1 / 10 ^ 60 := by
    apply (div_le_iff₀ (sub_pos.mpr hdlt)).2
    norm_num only [pow_succ] at hp ⊢
    linarith only [hp, hd1]
  have hjq : (j : ℚ) ≤ 6 := by exact_mod_cast hj
  have hw : logSixtyUpper N j - logSixtyLower N j ≤ 1 / 10 ^ 50 := by
    dsimp only [logSixtyUpper, logSixtyLower, Analysis.rationalLogRemainder]
    dsimp only [d] at hr
    norm_num only at hr ⊢
    linarith only [hr, hjq]
  have hb := log_sixty_bounds hN j hdlt
  have hwR : (logSixtyUpper N j : ℝ) - (logSixtyLower N j : ℝ) ≤ 1 / 10 ^ 50 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hw
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using h
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  rw [abs_le]
  constructor <;> linarith only [hb.1, hb.2, hwR]

/-- Under the same binary-scale hypotheses used by the fixed grid, a
256-term rational Taylor sum approximates the logarithm within `10⁻⁵⁰`.
This precision supports sign checks at high zero ordinates. -/
theorem rational_log_approx_fifty {N : ℚ} (hN : 0 < N) (j : ℕ) (hj : j ≤ 6)
    (hd : |1 - N / 2 ^ j| ≤ 1 / 2) : ∃ c : ℚ, |Real.log (N : ℝ) - (c : ℝ)| ≤ 1 / 10 ^ 50 := by
  refine ⟨(logSixtyLower N j + logSixtyUpper N j) / 2, ?_⟩
  exact (rational_log_midpoint_fifty hN j hj hd).trans (by norm_num only)

/-- A positive rational with binary-scale displacement at most one half and
scale at most six has a rational logarithm approximation with error at most
`10⁻¹²`. A uniform 48-term Taylor remainder proves the bound without
enumerating the rational inputs or using a numerical table. -/
theorem rational_log_approx_uniform {N : ℚ} (hN : 0 < N) (j : ℕ) (hj : j ≤ 6)
    (hd : |1 - N / 2 ^ j| ≤ 1 / 2) : ∃ c : ℚ, |Real.log (N : ℝ) - (c : ℝ)| ≤ 1 / 10 ^ 12 := by
  let d : ℚ := |1 - N / 2 ^ j|
  have hd0 : 0 ≤ d := abs_nonneg _
  have hd1 : d ≤ 1 / 2 := hd
  have hdlt : d < 1 := lt_of_le_of_lt hd1 (by norm_num only)
  have hp : d ^ 49 ≤ (1 / 2 : ℚ) ^ 49 := pow_le_pow_left₀ hd0 hd1 49
  have hr : d ^ 49 / (1 - d) ≤ 1 / 10 ^ 14 := by
    apply (div_le_iff₀ (sub_pos.mpr hdlt)).2
    norm_num only at hp ⊢
    linarith only [hp, hd1]
  have hjq : (j : ℚ) ≤ 6 := by exact_mod_cast hj
  have hw : Analysis.preciseLogUpper N j 48 - Analysis.preciseLogLower N j 48 ≤ 1 / 10 ^ 12 := by
    dsimp only [Analysis.preciseLogUpper, Analysis.preciseLogLower, Analysis.rationalLogRemainder]
    change _ ≤ _ at hr
    dsimp only [d] at hr
    norm_num only at hr ⊢
    linarith only [hr, hjq]
  have hb := Analysis.preciseLog_bounds hN j 48 hdlt
  let c : ℚ := (Analysis.preciseLogLower N j 48 + Analysis.preciseLogUpper N j 48) / 2
  refine ⟨c, ?_⟩
  have hwR :
    (Analysis.preciseLogUpper N j 48 : ℝ) - (Analysis.preciseLogLower N j 48 : ℝ) ≤
      1 / 10 ^ 12 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hw
    simpa only [Rat.cast_sub, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using h
  dsimp only [c]
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_ofNat]
  rw [abs_le]
  constructor <;> linarith only [hb.1, hb.2, hwR]

/-- The binary scale used for each node of the fixed sixteenth grid. The
six cases keep the normalized node between one half and one. -/
private def gridBinaryScale (i : ℕ) : ℕ :=
  if i ≤ 16 then 1
  else if i ≤ 48 then 2 else if i ≤ 112 then 3 else if i ≤ 240 then 4 else if i ≤ 496 then 5 else 6

/-- The rational midpoint of the high-precision logarithm enclosure at a
fixed-grid node. Its binary scale and Taylor sums are computed from the node. -/
private def gridLogMidpoint (i : ℕ) : ℚ :=
  (logSixtyLower (1 + (i : ℚ) / 16) (gridBinaryScale i) +
      logSixtyUpper (1 + (i : ℚ) / 16) (gridBinaryScale i)) /
    2

/-- The logarithm midpoint rounded down to a fixed rational grid.
The fixed denominator limits growth in the phase and amplitude polynomials. -/
private def gridLogRounded (i : ℕ) : ℚ :=
  Analysis.rationalGridFloor (10 ^ 55) (gridLogMidpoint i)

set_option maxRecDepth 8192 in
/-- Every node of the 944-cell grid, including the final endpoint, has a
rational logarithm approximation within `10⁻¹²`. The finite check selects
only a binary scale; the precision follows from one uniform Taylor theorem. -/
theorem critical_grid_log_approx (i : ℕ) (hi : i ≤ 944) :
    ∃ c : ℚ, |Real.log (criticalQuadratureGrid i) - (c : ℝ)| ≤ 1 / 10 ^ 12 := by
  have hc :
    ∀ i : Fin 945,
      0 < (1 + (i.val : ℚ) / 16) ∧
        gridBinaryScale i.val ≤ 6 ∧
        |1 - (1 + (i.val : ℚ) / 16) / 2 ^ gridBinaryScale i.val| ≤ 1 / 2 := by
    decide +kernel
  let k : Fin 945 := ⟨i, Nat.lt_succ_of_le hi⟩
  have hk := hc k
  obtain ⟨c, h⟩ := rational_log_approx_uniform hk.1 (gridBinaryScale i) hk.2.1 hk.2.2
  refine ⟨c, ?_⟩
  simpa only [criticalQuadratureGrid, Rat.cast_add, Rat.cast_one, Rat.cast_div, Rat.cast_natCast,
    Rat.cast_ofNat] using h

set_option maxRecDepth 8192 in
/-- The computed rational midpoint approximates the logarithm at every
node of the fixed grid, including the final endpoint. -/
private theorem grid_log_midpoint_fifty (i : ℕ) (hi : i ≤ 944) :
    |Real.log (criticalQuadratureGrid i) - (gridLogMidpoint i : ℝ)| ≤ 1 / (2 * 10 ^ 50) := by
  have hc :
    ∀ i : Fin 945,
      0 < (1 + (i.val : ℚ) / 16) ∧
        gridBinaryScale i.val ≤ 6 ∧
        |1 - (1 + (i.val : ℚ) / 16) / 2 ^ gridBinaryScale i.val| ≤ 1 / 2 := by
    decide +kernel
  let k : Fin 945 := ⟨i, Nat.lt_succ_of_le hi⟩
  have hk := hc k
  have h := rational_log_midpoint_fifty hk.1 (gridBinaryScale i) hk.2.1 hk.2.2
  simpa only [gridLogMidpoint, criticalQuadratureGrid, Rat.cast_add, Rat.cast_one, Rat.cast_div,
    Rat.cast_natCast, Rat.cast_ofNat] using h

/-- The fixed-grid rounded midpoint still approximates the node logarithm
within `10⁻⁵⁰`, including the final grid endpoint. -/
private theorem grid_log_rounded_fifty (i : ℕ) (hi : i ≤ 944) :
    |Real.log (criticalQuadratureGrid i) - (gridLogRounded i : ℝ)| ≤ 1 / 10 ^ 50 := by
  have hm := grid_log_midpoint_fifty i hi
  have hr : |(gridLogMidpoint i : ℝ) - (gridLogRounded i : ℝ)| ≤ 1 / 10 ^ 55 := by
    have h :=
      (Rat.cast_le (K := ℝ)).mpr
        (Analysis.rationalGridFloor_error (by norm_num only : 0 < 10 ^ 55) (gridLogMidpoint i))
    norm_num only [gridLogRounded, Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_one,
      Rat.cast_natCast, Nat.cast_pow, Nat.cast_ofNat] at h ⊢
    exact h
  have htri :=
    abs_sub_le (Real.log (criticalQuadratureGrid i)) (gridLogMidpoint i : ℝ) (gridLogRounded i : ℝ)
  linarith only [htri, hm, hr]

/-- Every node of the fixed grid, including the last endpoint, admits a
rational logarithm approximation with error at most `10⁻⁵⁰`. A uniform
Taylor estimate and the same finite binary-scale check cover all nodes. -/
theorem critical_grid_log_fifty (i : ℕ) (hi : i ≤ 944) :
    ∃ c : ℚ, |Real.log (criticalQuadratureGrid i) - (c : ℝ)| ≤ 1 / 10 ^ 50 := by
  exact ⟨gridLogRounded i, grid_log_rounded_fifty i hi⟩

/-- At every fixed-grid node and every rational height, the logarithmic
phase has a rational center with error at most `|t| / (2 * 10¹²)`. This
uniformly covers both endpoint heights and the final grid node. -/
theorem critical_grid_phase_approx (i : ℕ) (hi : i ≤ 944) (t : ℚ) :
    ∃ v : ℚ,
      |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (v : ℝ)| ≤
        |(t : ℝ)| / (2 * 10 ^ 12) := by
  obtain ⟨c, hc⟩ := critical_grid_log_approx i hi
  refine ⟨c * t / 2, ?_⟩
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  have he :
    Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (c : ℝ) * (t : ℝ) / 2 =
      (Real.log (criticalQuadratureGrid i) - c) * (t / 2) := by
    ring
  rw [he, abs_mul, abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  have h :=
    mul_le_mul_of_nonneg_right hc (div_nonneg (abs_nonneg (t : ℝ)) (by norm_num only : (0 : ℝ) ≤ 2))
  nlinarith only [h]

/-- The computed logarithm midpoint supplies an explicit phase center at
every fixed-grid node and rational height. -/
private theorem grid_phase_midpoint_fifty (i : ℕ) (hi : i ≤ 944) (t : ℚ) :
    |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - ((gridLogMidpoint i * t / 2 : ℚ) : ℝ)| ≤
      |(t : ℝ)| / (2 * 10 ^ 50) := by
  let c := gridLogMidpoint i
  have hc :=
    (grid_log_midpoint_fifty i hi).trans (by norm_num only : (1 : ℝ) / (2 * 10 ^ 50) ≤ 1 / 10 ^ 50)
  change |Real.log (criticalQuadratureGrid i) - (c : ℝ)| ≤ 1 / 10 ^ 50 at hc
  change |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - ((c * t / 2 : ℚ) : ℝ)| ≤ _
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  have he :
    Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (c : ℝ) * (t : ℝ) / 2 =
      (Real.log (criticalQuadratureGrid i) - c) * (t / 2) := by
    ring
  rw [he, abs_mul, abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  have h :=
    mul_le_mul_of_nonneg_right hc (div_nonneg (abs_nonneg (t : ℝ)) (by norm_num only : (0 : ℝ) ≤ 2))
  nlinarith only [h]

/-- The rounded logarithm gives a certified phase center. -/
private theorem grid_phase_rounded_fifty (i : ℕ) (hi : i ≤ 944) (t : ℚ) :
    |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - ((gridLogRounded i * t / 2 : ℚ) : ℝ)| ≤
      |(t : ℝ)| / (2 * 10 ^ 50) := by
  let c := gridLogRounded i
  have hc := grid_log_rounded_fifty i hi
  change |Real.log (criticalQuadratureGrid i) - (c : ℝ)| ≤ 1 / 10 ^ 50 at hc
  change |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - ((c * t / 2 : ℚ) : ℝ)| ≤ _
  simp only [Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]
  have he :
    Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (c : ℝ) * (t : ℝ) / 2 =
      (Real.log (criticalQuadratureGrid i) - c) * (t / 2) := by
    ring
  rw [he, abs_mul, abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  have h :=
    mul_le_mul_of_nonneg_right hc (div_nonneg (abs_nonneg (t : ℝ)) (by norm_num only : (0 : ℝ) ≤ 2))
  nlinarith only [h]

/-- Every fixed-grid node and rational height have a rational phase center
with error at most `|t| / (2 * 10⁵⁰)`. The common high-precision logarithm
estimate applies uniformly through the final node. -/
theorem critical_grid_phase_fifty (i : ℕ) (hi : i ≤ 944) (t : ℚ) :
    ∃ v : ℚ,
      |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (v : ℝ)| ≤
        |(t : ℝ)| / (2 * 10 ^ 50) := by
  exact ⟨gridLogMidpoint i * t / 2, grid_phase_midpoint_fifty i hi t⟩

/-- On the complete fixed grid, the node logarithm lies between zero and
five. The upper bound compares the last node with `64 = 2⁶` and uses the
elementary logarithm-of-two bound. -/
theorem critical_grid_log_le_five (i : ℕ) (hi : i ≤ 944) :
    0 ≤ Real.log (criticalQuadratureGrid i) ∧ Real.log (criticalQuadratureGrid i) ≤ 5 := by
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hiR : (i : ℝ) ≤ 944 := by exact_mod_cast hi
  have hg1 : 1 ≤ criticalQuadratureGrid i := by
    dsimp only [criticalQuadratureGrid]
    linarith only [div_nonneg hi0 (by norm_num only : (0 : ℝ) ≤ 16)]
  have hg64 : criticalQuadratureGrid i ≤ 64 := by
    dsimp only [criticalQuadratureGrid]
    linarith only [hiR]
  have hl64 : Real.log 64 ≤ 5 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num only, Real.log_pow]
    norm_num only [Nat.cast_ofNat]
    linarith only [Real.log_two_lt_d9]
  exact
    ⟨Real.log_nonneg hg1, (Real.log_le_log (lt_of_lt_of_le (by norm_num only) hg1) hg64).trans hl64⟩

/-- On the nonpositive real axis, a nearby rational exponent and a finite
Taylor sum approximate the exponential. The first error is controlled by a
local Lipschitz estimate and the second by the exponential-series remainder. -/
theorem exp_rational_taylor_error {x : ℝ} (hx : x ≤ 0) (q : ℚ) (m : ℕ) {δ : ℝ} (hδ : δ < 1)
    (hq : |x - (q : ℝ)| ≤ δ) (hm : |(q : ℝ)| / (m + 1 : ℕ) ≤ 1 / 2) :
    |Real.exp x - ∑ k ∈ Finset.range m, (q : ℝ) ^ k / (k.factorial : ℝ)| ≤
      2 * δ + |(q : ℝ)| ^ m / (m.factorial : ℝ) * 2 := by
  have hdist : ‖((q : ℝ) : ℂ) - (x : ℂ)‖ < 1 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    exact hq.trans_lt hδ
  have hlocal :=
    Complex.locally_lipschitz_exp (r := 1) (by norm_num only) le_rfl (x : ℂ) ((q : ℝ) : ℂ) hdist
  have hexp : ‖Complex.exp (x : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_exp, Complex.ofReal_re]
    exact Real.exp_le_one_iff.mpr hx
  have hlocal' : |Real.exp x - Real.exp (q : ℝ)| ≤ 2 * δ := by
    rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
      Real.norm_eq_abs] at hlocal
    rw [← Complex.ofReal_sub ((q : ℝ)) x, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_sub_comm (q : ℝ) x, abs_sub_comm (Real.exp (q : ℝ)) (Real.exp x),
      abs_of_pos (Real.exp_pos x)] at hlocal
    rw [Complex.norm_exp, Complex.ofReal_re] at hexp
    nlinarith only [hlocal, hexp, hq, abs_nonneg (x - (q : ℝ))]
  have hsize : ‖((q : ℝ) : ℂ)‖ / (m + 1 : ℕ) ≤ 1 / 2 := by
    simpa only [Complex.norm_real, Real.norm_eq_abs] using hm
  have hs := Complex.exp_bound' (n := m) hsize
  rw [Complex.norm_real, Real.norm_eq_abs] at hs
  have hs' :
    |Real.exp (q : ℝ) - ∑ k ∈ Finset.range m, (q : ℝ) ^ k / (k.factorial : ℝ)| ≤
      |(q : ℝ)| ^ m / (m.factorial : ℝ) * 2 := by
    convert hs using 1
    norm_cast
  exact (abs_sub_le _ _ _).trans (add_le_add hlocal' hs')

/-- Every fixed-grid amplitude has a rational Taylor exponent of magnitude
at most 46. The 512-term polynomial has an explicit remainder, uniformly
covering all nodes including the final endpoint. -/
theorem critical_grid_amplitude_taylor (i : ℕ) (hi : i ≤ 944) :
    ∃ q : ℚ,
      |(q : ℝ)| ≤ 46 ∧
        |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
              ∑ k ∈ Finset.range 512, (q : ℝ) ^ k / (k.factorial : ℝ)| ≤
          2 / 10 ^ 12 + |(q : ℝ)| ^ 512 / (Nat.factorial 512 : ℝ) * 2 := by
  have hiR : (i : ℝ) ≤ 944 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hg1 : 1 ≤ criticalQuadratureGrid i := by
    dsimp only [criticalQuadratureGrid]
    linarith only [div_nonneg hi0 (by norm_num only : (0 : ℝ) ≤ 16)]
  have hg60 : criticalQuadratureGrid i ≤ 60 := by
    dsimp only [criticalQuadratureGrid]
    linarith only [hiR]
  have hl0 : 0 ≤ Real.log (criticalQuadratureGrid i) := Real.log_nonneg hg1
  have hl60 : Real.log (criticalQuadratureGrid i) ≤ 60 :=
    (Real.log_le_self (le_trans (by norm_num only : (0 : ℝ) ≤ 1) hg1)).trans hg60
  obtain ⟨c, hc⟩ := critical_grid_log_approx i hi
  have hc' := abs_le.mp hc
  let q : ℚ := -(3 / 4) * c
  have hqclose :
    |Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ)) - (q : ℝ)| ≤ 1 / 10 ^ 12 := by
    dsimp only [q]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]
    rw [abs_le]
    constructor <;> linarith only [hc'.1, hc'.2]
  have hq : |(q : ℝ)| ≤ 46 := by
    dsimp only [q]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]
    rw [abs_le]
    constructor <;> linarith only [hc'.1, hc'.2, hl0, hl60]
  have hm : |(q : ℝ)| / (512 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith only [hq]
  have hx : Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ)) ≤ 0 := by linarith only [hl0]
  have he := exp_rational_taylor_error hx q 512 (by norm_num only) hqclose hm
  refine ⟨q, hq, ?_⟩
  convert he using 1
  ring

set_option maxRecDepth 8192 in
/-- The 512-term Taylor approximation of every grid amplitude has uniform
error at most `3 * 10⁻¹²`. The numerical comparison uses exact integer
arithmetic and the common exponent cap, not a table of node values. -/
theorem critical_grid_amplitude_approx (i : ℕ) (hi : i ≤ 944) :
    ∃ q : ℚ,
      |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
            ∑ k ∈ Finset.range 512, (q : ℝ) ^ k / (k.factorial : ℝ)| ≤
        3 / 10 ^ 12 := by
  obtain ⟨q, hq, h⟩ := critical_grid_amplitude_taylor i hi
  have hp : |(q : ℝ)| ^ 512 ≤ (46 : ℝ) ^ 512 := pow_le_pow_left₀ (abs_nonneg _) hq 512
  have hf : (0 : ℝ) < Nat.factorial 512 := by exact_mod_cast Nat.factorial_pos 512
  have hn : ((46 : ℝ) ^ 512 / (Nat.factorial 512 : ℝ)) * 2 ≤ 1 / 10 ^ 12 := by
    norm_num only [Nat.factorial, pow_succ]
  have hr : |(q : ℝ)| ^ 512 / (Nat.factorial 512 : ℝ) * 2 ≤ 1 / 10 ^ 12 :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp hf.le) (by norm_num only)).trans hn
  refine ⟨q, ?_⟩
  linarith only [h, hr]

/-- Every fixed-grid amplitude has a rational approximation within
`3 * 10⁻¹²`. Its rational witness is the finite Taylor sum supplied by the
uniform amplitude theorem, including at the last grid endpoint. -/
theorem critical_grid_amplitude_rational (i : ℕ) (hi : i ≤ 944) :
    ∃ a : ℚ,
      |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) - (a : ℝ)| ≤
        3 / 10 ^ 12 := by
  obtain ⟨q, hq⟩ := critical_grid_amplitude_approx i hi
  refine ⟨∑ k ∈ Finset.range 512, q ^ k / (k.factorial : ℚ), ?_⟩
  simpa only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using hq

/-- The explicit rational exponent used for the grid amplitude. -/
private def gridAmplitudeExponent (i : ℕ) : ℚ :=
  -(3 / 4) * gridLogMidpoint i

/-- The computed grid-amplitude exponent has a uniform size and Taylor error. -/
private theorem grid_amplitude_taylor_fifty (i : ℕ) (hi : i ≤ 944) :
    |(gridAmplitudeExponent i : ℝ)| ≤ 46 ∧
      |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
            ∑ k ∈ Finset.range 512, (gridAmplitudeExponent i : ℝ) ^ k / (k.factorial : ℝ)| ≤
        2 / 10 ^ 50 + |(gridAmplitudeExponent i : ℝ)| ^ 512 / (Nat.factorial 512 : ℝ) * 2 := by
  have hiR : (i : ℝ) ≤ 944 := by exact_mod_cast hi
  have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
  have hg1 : 1 ≤ criticalQuadratureGrid i := by
    dsimp only [criticalQuadratureGrid]
    linarith only [div_nonneg hi0 (by norm_num only : (0 : ℝ) ≤ 16)]
  have hg60 : criticalQuadratureGrid i ≤ 60 := by
    dsimp only [criticalQuadratureGrid]
    linarith only [hiR]
  have hl0 : 0 ≤ Real.log (criticalQuadratureGrid i) := Real.log_nonneg hg1
  have hl60 : Real.log (criticalQuadratureGrid i) ≤ 60 :=
    (Real.log_le_self (le_trans (by norm_num only : (0 : ℝ) ≤ 1) hg1)).trans hg60
  let c := gridLogMidpoint i
  have hc : |Real.log (criticalQuadratureGrid i) - (c : ℝ)| ≤ 1 / 10 ^ 50 :=
    (grid_log_midpoint_fifty i hi).trans (by norm_num only)
  have hc' := abs_le.mp hc
  let q : ℚ := -(3 / 4) * c
  have hqclose :
    |Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ)) - (q : ℝ)| ≤ 1 / 10 ^ 50 := by
    dsimp only [q]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]
    rw [abs_le]
    constructor <;> linarith only [hc'.1, hc'.2]
  have hq : |(q : ℝ)| ≤ 46 := by
    dsimp only [q]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]
    rw [abs_le]
    constructor <;> linarith only [hc'.1, hc'.2, hl0, hl60]
  have hm : |(q : ℝ)| / (512 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith only [hq]
  have hx : Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ)) ≤ 0 := by linarith only [hl0]
  have he := exp_rational_taylor_error hx q 512 (by norm_num only) hqclose hm
  change
    |(q : ℝ)| ≤ 46 ∧
      |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
            ∑ k ∈ Finset.range 512, (q : ℝ) ^ k / (k.factorial : ℝ)| ≤
        2 / 10 ^ 50 + |(q : ℝ)| ^ 512 / (Nat.factorial 512 : ℝ) * 2
  refine ⟨hq, ?_⟩
  convert he using 1
  ring

/-- Every fixed-grid amplitude has a rational Taylor exponent of magnitude
at most 46. The 512-term polynomial has an explicit remainder, uniformly
covering all nodes including the final endpoint. -/
theorem critical_grid_amplitude_taylor_fifty (i : ℕ) (hi : i ≤ 944) :
    ∃ q : ℚ,
      |(q : ℝ)| ≤ 46 ∧
        |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
              ∑ k ∈ Finset.range 512, (q : ℝ) ^ k / (k.factorial : ℝ)| ≤
          2 / 10 ^ 50 + |(q : ℝ)| ^ 512 / (Nat.factorial 512 : ℝ) * 2 := by
  exact ⟨gridAmplitudeExponent i, grid_amplitude_taylor_fifty i hi⟩

set_option maxRecDepth 8192 in
/-- The computed amplitude Taylor polynomial has the uniform error bound. -/
private theorem grid_amplitude_approx_fifty (i : ℕ) (hi : i ≤ 944) :
    |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
          ∑ k ∈ Finset.range 512, (gridAmplitudeExponent i : ℝ) ^ k / (k.factorial : ℝ)| ≤
      3 / 10 ^ 50 := by
  let q := gridAmplitudeExponent i
  have ⟨hq, h⟩ := grid_amplitude_taylor_fifty i hi
  change |(q : ℝ)| ≤ 46 at hq
  change
    |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
          ∑ k ∈ Finset.range 512, (q : ℝ) ^ k / (k.factorial : ℝ)| ≤
      _ at h
  have hp : |(q : ℝ)| ^ 512 ≤ (46 : ℝ) ^ 512 := pow_le_pow_left₀ (abs_nonneg _) hq 512
  have hf : (0 : ℝ) < Nat.factorial 512 := by exact_mod_cast Nat.factorial_pos 512
  have hn : ((46 : ℝ) ^ 512 / (Nat.factorial 512 : ℝ)) * 2 ≤ 1 / 10 ^ 50 := by
    norm_num only [Nat.factorial, pow_succ]
  have hr : |(q : ℝ)| ^ 512 / (Nat.factorial 512 : ℝ) * 2 ≤ 1 / 10 ^ 50 :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp hf.le) (by norm_num only)).trans hn
  linarith only [h, hr]

/-- The 512-term Taylor approximation of every grid amplitude has uniform
error at most `3 * 10⁻⁵⁰`. The numerical comparison uses exact integer
arithmetic and the common exponent cap, not a table of node values. -/
theorem critical_grid_amplitude_approx_fifty (i : ℕ) (hi : i ≤ 944) :
    ∃ q : ℚ,
      |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
            ∑ k ∈ Finset.range 512, (q : ℝ) ^ k / (k.factorial : ℝ)| ≤
        3 / 10 ^ 50 := by
  exact ⟨gridAmplitudeExponent i, grid_amplitude_approx_fifty i hi⟩

/-- The rational 512-term amplitude Taylor polynomial at a grid node. -/
private def gridAmplitudeTaylor (i : ℕ) : ℚ :=
  ∑ k ∈ Finset.range 512, gridAmplitudeExponent i ^ k / (k.factorial : ℚ)

/-- Casting the calculated amplitude to the reals preserves its error bound. -/
private theorem grid_amplitude_rational_fifty (i : ℕ) (hi : i ≤ 944) :
    |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
          (gridAmplitudeTaylor i : ℝ)| ≤
      3 / 10 ^ 50 := by
  simpa only [gridAmplitudeTaylor, Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast] using
    grid_amplitude_approx_fifty i hi

/-- Every fixed-grid amplitude has a rational approximation within
`3 * 10⁻⁵⁰`. Its rational witness is the finite Taylor sum supplied by the
uniform amplitude theorem, including at the last grid endpoint. -/
theorem critical_grid_amplitude_rational_fifty (i : ℕ) (hi : i ≤ 944) :
    ∃ a : ℚ,
      |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) - (a : ℝ)| ≤
        3 / 10 ^ 50 := by
  exact ⟨gridAmplitudeTaylor i, grid_amplitude_rational_fifty i hi⟩

/-- The amplitude exponent formed from the fixed-grid logarithm. -/
private def gridAmplitudeRoundedExponent (i : ℕ) : ℚ :=
  -(3 / 4) * gridLogRounded i

/-- The 64-term rational amplitude polynomial at a fixed grid node.
The node logarithm bound makes the shorter polynomial sufficient. -/
private def gridAmplitudeCompact (i : ℕ) : ℚ :=
  ∑ k ∈ Finset.range 64, gridAmplitudeRoundedExponent i ^ k / (k.factorial : ℚ)

/-- The 64-term amplitude polynomial has the same uniform error bound as
the longer polynomial at all 945 grid nodes. -/
private theorem grid_amplitude_compact_error (i : ℕ) (hi : i ≤ 944) :
    |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
          (gridAmplitudeCompact i : ℝ)| ≤
      3 / 10 ^ 50 := by
  let c := gridLogRounded i
  let q := gridAmplitudeRoundedExponent i
  have hc : |Real.log (criticalQuadratureGrid i) - (c : ℝ)| ≤ 1 / 10 ^ 50 :=
    grid_log_rounded_fifty i hi
  have hc' := abs_le.mp hc
  have hl := critical_grid_log_le_five i hi
  have hqclose :
    |Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ)) - (q : ℝ)| ≤ 1 / 10 ^ 50 := by
    dsimp only [q, gridAmplitudeRoundedExponent, c]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]
    rw [abs_le]
    constructor <;> linarith only [hc'.1, hc'.2]
  have hq : |(q : ℝ)| ≤ 4 := by
    dsimp only [q, gridAmplitudeRoundedExponent, c]
    simp only [Rat.cast_mul, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat]
    rw [abs_le]
    constructor <;> linarith only [hc'.1, hc'.2, hl.1, hl.2]
  have hm : |(q : ℝ)| / (64 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith only [hq]
  have hx : Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ)) ≤ 0 := by linarith only [hl.1]
  have he := exp_rational_taylor_error hx q 64 (by norm_num only) hqclose hm
  have hp : |(q : ℝ)| ^ 64 ≤ (4 : ℝ) ^ 64 := pow_le_pow_left₀ (abs_nonneg _) hq 64
  have hf : (0 : ℝ) < Nat.factorial 64 := by exact_mod_cast Nat.factorial_pos 64
  have hn : (4 : ℝ) ^ 64 / (Nat.factorial 64 : ℝ) * 2 ≤ 1 / 10 ^ 50 := by
    norm_num only [Nat.factorial, pow_succ]
  have hr : |(q : ℝ)| ^ 64 / (Nat.factorial 64 : ℝ) * 2 ≤ 1 / 10 ^ 50 :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hp hf.le) (by norm_num only)).trans hn
  change
    |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) -
          ((∑ k ∈ Finset.range 64, q ^ k / (k.factorial : ℚ) : ℚ) : ℝ)| ≤
      _
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
  linarith only [he, hr]

/-- A Gaussian exponential with exponent at most `-64` is below `10⁻¹²`.
The proof uses `exp 1 ≥ 2` and exact integer comparison. It supplies a
uniform cutoff for large nodes and Gaussian indices. -/
theorem exp_neg_large_le {u : ℝ} (hu : 64 ≤ u) : Real.exp (-u) ≤ 1 / 10 ^ 12 := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith only [h]
  have hpow : (2 : ℝ) ^ 64 ≤ Real.exp 64 := by
    have h := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2) hbase 64
    rw [← Real.exp_natCast_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h ⊢
    exact h
  have hsmall : Real.exp (-64) ≤ 1 / 10 ^ 12 := by
    rw [Real.exp_neg]
    have h := inv_le_inv₀ (Real.exp_pos 64) (by norm_num only : (0 : ℝ) < (2 : ℝ) ^ 64)
    have h' := h.mpr hpow
    norm_num only [one_div] at h' ⊢
    linarith only [h']
  exact (Real.exp_le_exp.mpr (neg_le_neg hu)).trans hsmall

/-- A Gaussian exponential with exponent at most `-160` is below `10⁻⁴⁷`.
The proof uses `exp 1 ≥ 2` and exact integer comparison. It supplies a
uniform cutoff for large nodes and Gaussian indices. -/
theorem exp_neg_large_fortyseven {u : ℝ} (hu : 160 ≤ u) : Real.exp (-u) ≤ 1 / 10 ^ 47 := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith only [h]
  have hpow : (2 : ℝ) ^ 160 ≤ Real.exp 160 := by
    have h := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2) hbase 160
    rw [← Real.exp_natCast_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h ⊢
    exact h
  have hsmall : Real.exp (-160) ≤ 1 / 10 ^ 47 := by
    rw [Real.exp_neg]
    have h := inv_le_inv₀ (Real.exp_pos 160) (by norm_num only : (0 : ℝ) < (2 : ℝ) ^ 160)
    have h' := h.mpr hpow
    norm_num only [one_div] at h' ⊢
    linarith only [h']
  exact (Real.exp_le_exp.mpr (neg_le_neg hu)).trans hsmall

/-- The same cutoff gives the sharper uniform exponential estimate. -/
private theorem exp_neg_large_fortyeight {u : ℝ} (hu : 160 ≤ u) : Real.exp (-u) ≤ 1 / 10 ^ 48 := by
  have hbase : (2 : ℝ) ≤ Real.exp 1 := by
    have h := Real.add_one_le_exp 1
    linarith only [h]
  have hpow : (2 : ℝ) ^ 160 ≤ Real.exp 160 := by
    have h := pow_le_pow_left₀ (by norm_num only : (0 : ℝ) ≤ 2) hbase 160
    rw [← Real.exp_natCast_mul] at h
    norm_num only [Nat.cast_ofNat, mul_one] at h ⊢
    exact h
  have hsmall : Real.exp (-160) ≤ 1 / 10 ^ 48 := by
    rw [Real.exp_neg]
    have h := inv_le_inv₀ (Real.exp_pos 160) (by norm_num only : (0 : ℝ) < (2 : ℝ) ^ 160)
    have h' := h.mpr hpow
    norm_num only [one_div] at h' ⊢
    linarith only [h']
  exact (Real.exp_le_exp.mpr (neg_le_neg hu)).trans hsmall

set_option maxRecDepth 8192 in
/-- For every nonnegative rational Gaussian argument, the real exponential
`exp (-π y)` has a rational approximation within `3 * 10⁻¹²`. Small
arguments use the certified 20-digit π interval and 512 Taylor terms;
large arguments use a common exponential cutoff. -/
theorem gaussian_rational_approx (y : ℚ) (hy : 0 ≤ y) :
    ∃ r : ℚ, |Real.exp (-Real.pi * (y : ℝ)) - (r : ℝ)| ≤ 3 / 10 ^ 12 := by
  have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
  by_cases hlarge : (22 : ℝ) ≤ y
  · have hlarge' : 64 ≤ Real.pi * (y : ℝ) := by nlinarith only [Real.pi_gt_d4, hlarge, hyR]
    refine ⟨0, ?_⟩
    simp only [Rat.cast_zero, sub_zero, abs_of_pos (Real.exp_pos _)]
    have hs := exp_neg_large_le hlarge'
    rw [← neg_mul] at hs
    linarith only [hs]
  · have hy22 : (y : ℝ) ≤ 22 := le_of_lt (not_le.mp hlarge)
    let p : ℚ := 314159265358979323846 / 100000000000000000000
    let q : ℚ := -p * y
    have hp0 : (0 : ℝ) ≤ p := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hpi : |Real.pi - (p : ℝ)| ≤ 1 / 10 ^ 20 := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      rw [abs_le]
      constructor <;> linarith only [Real.pi_gt_d20, Real.pi_lt_d20]
    have hp4 : (p : ℝ) ≤ 3.2 := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hq : |(q : ℝ)| ≤ 71 := by
      dsimp only [q]
      simp only [Rat.cast_mul, Rat.cast_neg]
      rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hp0 hyR)]
      have hm := mul_le_mul hp4 hy22 hyR (by norm_num only : (0 : ℝ) ≤ 3.2)
      norm_num only at hm ⊢
      linarith only [hm]
    have hclose : |-Real.pi * (y : ℝ) - (q : ℝ)| ≤ 1 / 10 ^ 12 := by
      dsimp only [q]
      simp only [Rat.cast_mul, Rat.cast_neg]
      have he : -Real.pi * (y : ℝ) - -(p : ℝ) * (y : ℝ) = -((Real.pi - (p : ℝ)) * (y : ℝ)) := by
        ring
      rw [he, abs_neg, abs_mul, abs_of_nonneg hyR]
      have hm := mul_le_mul hpi hy22 hyR (by norm_num only : (0 : ℝ) ≤ 1 / 10 ^ 20)
      nlinarith only [hm]
    have hx : -Real.pi * (y : ℝ) ≤ 0 := by
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hyR)
    have hm : |(q : ℝ)| / (512 + 1 : ℕ) ≤ 1 / 2 := by
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
      linarith only [hq]
    have h := exp_rational_taylor_error hx q 512 (by norm_num only) hclose hm
    have hpow : |(q : ℝ)| ^ 512 ≤ (71 : ℝ) ^ 512 := pow_le_pow_left₀ (abs_nonneg _) hq 512
    have hf : (0 : ℝ) < Nat.factorial 512 := by exact_mod_cast Nat.factorial_pos 512
    have hn : (71 : ℝ) ^ 512 / (Nat.factorial 512 : ℝ) * 2 ≤ 1 / 10 ^ 12 := by
      norm_num only [Nat.factorial, pow_succ]
    have hr : |(q : ℝ)| ^ 512 / (Nat.factorial 512 : ℝ) * 2 ≤ 1 / 10 ^ 12 :=
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow hf.le) (by norm_num only)).trans
        hn
    refine ⟨∑ k ∈ Finset.range 512, q ^ k / (k.factorial : ℚ), ?_⟩
    simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    linarith only [h, hr]

private def gaussianApproxFortyseven (y : ℚ) : ℚ :=
  if 54 ≤ y then 0
  else
    let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
    let q : ℚ := -p * y
    ∑ k ∈ Finset.range 1024, q ^ k / (k.factorial : ℚ)

set_option maxRecDepth 16384 in
/-- The explicit rational Gaussian calculation has the uniform error bound
used in the fixed grid, including the large-argument cutoff. -/
private theorem gaussian_approx_fortyseven (y : ℚ) (hy : 0 ≤ y) :
    |Real.exp (-Real.pi * (y : ℝ)) - (gaussianApproxFortyseven y : ℝ)| ≤ 3 / 10 ^ 48 := by
  have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
  by_cases hlarge : (54 : ℝ) ≤ y
  · have hlargeQ : (54 : ℚ) ≤ y := by exact_mod_cast hlarge
    rw [gaussianApproxFortyseven, ite_eq_left hlargeQ]
    have hlarge' : 160 ≤ Real.pi * (y : ℝ) := by nlinarith only [Real.pi_gt_d4, hlarge, hyR]
    simp only [Rat.cast_zero, sub_zero, abs_of_pos (Real.exp_pos _)]
    have hs := exp_neg_large_fortyeight hlarge'
    rw [← neg_mul] at hs
    linarith only [hs]
  · have hsmallQ : ¬(54 : ℚ) ≤ y := by exact_mod_cast hlarge
    rw [gaussianApproxFortyseven, ite_eq_right hsmallQ]
    have hy54 : (y : ℝ) ≤ 54 := le_of_lt (not_le.mp hlarge)
    let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
    let q : ℚ := -p * y
    have hp0 : (0 : ℝ) ≤ p := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hpi : |Real.pi - (p : ℝ)| ≤ 1 / 10 ^ 50 := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      rw [abs_le]
      constructor <;> linarith only [pi_fifty_bounds.1, pi_fifty_bounds.2]
    have hp4 : (p : ℝ) ≤ 3.2 := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hq : |(q : ℝ)| ≤ 173 := by
      dsimp only [q]
      simp only [Rat.cast_mul, Rat.cast_neg]
      rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hp0 hyR)]
      have hm := mul_le_mul hp4 hy54 hyR (by norm_num only : (0 : ℝ) ≤ 3.2)
      norm_num only at hm ⊢
      linarith only [hm]
    have hclose : |-Real.pi * (y : ℝ) - (q : ℝ)| ≤ 1 / 10 ^ 48 := by
      dsimp only [q]
      simp only [Rat.cast_mul, Rat.cast_neg]
      have he : -Real.pi * (y : ℝ) - -(p : ℝ) * (y : ℝ) = -((Real.pi - (p : ℝ)) * (y : ℝ)) := by
        ring
      rw [he, abs_neg, abs_mul, abs_of_nonneg hyR]
      have hm := mul_le_mul hpi hy54 hyR (by norm_num only : (0 : ℝ) ≤ 1 / 10 ^ 50)
      nlinarith only [hm]
    have hx : -Real.pi * (y : ℝ) ≤ 0 := by
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hyR)
    have hm : |(q : ℝ)| / (1024 + 1 : ℕ) ≤ 1 / 2 := by
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
      linarith only [hq]
    have h := exp_rational_taylor_error hx q 1024 (by norm_num only) hclose hm
    have hpow : |(q : ℝ)| ^ 1024 ≤ (173 : ℝ) ^ 1024 := pow_le_pow_left₀ (abs_nonneg _) hq 1024
    have hf : (0 : ℝ) < Nat.factorial 1024 := by exact_mod_cast Nat.factorial_pos 1024
    have hn : (173 : ℝ) ^ 1024 / (Nat.factorial 1024 : ℝ) * 2 ≤ 1 / 10 ^ 48 := by
      norm_num only [Nat.factorial, pow_succ]
    have hr : |(q : ℝ)| ^ 1024 / (Nat.factorial 1024 : ℝ) * 2 ≤ 1 / 10 ^ 48 :=
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow hf.le) (by norm_num only)).trans
        hn
    change
      |Real.exp (-Real.pi * (y : ℝ)) -
            ((∑ k ∈ Finset.range 1024, q ^ k / (k.factorial : ℚ) : ℚ) : ℝ)| ≤
        _
    simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    linarith only [h, hr]

private def gaussianApproxCompact (y : ℚ) : ℚ :=
  if 54 ≤ y then 0
  else
    let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
    let q : ℚ := -p * y
    ∑ k ∈ Finset.range 576, q ^ k / (k.factorial : ℚ)

set_option maxRecDepth 16384 in
/-- The shorter rational Gaussian calculation has the uniform error bound
used in the fixed grid, including the large-argument cutoff. -/
private theorem gaussian_approx_compact (y : ℚ) (hy : 0 ≤ y) :
    |Real.exp (-Real.pi * (y : ℝ)) - (gaussianApproxCompact y : ℝ)| ≤ 3 / 10 ^ 48 := by
  have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
  by_cases hlarge : (54 : ℝ) ≤ y
  · have hlargeQ : (54 : ℚ) ≤ y := by exact_mod_cast hlarge
    rw [gaussianApproxCompact, ite_eq_left hlargeQ]
    have hlarge' : 160 ≤ Real.pi * (y : ℝ) := by nlinarith only [Real.pi_gt_d4, hlarge, hyR]
    simp only [Rat.cast_zero, sub_zero, abs_of_pos (Real.exp_pos _)]
    have hs := exp_neg_large_fortyeight hlarge'
    rw [← neg_mul] at hs
    linarith only [hs]
  · have hsmallQ : ¬(54 : ℚ) ≤ y := by exact_mod_cast hlarge
    rw [gaussianApproxCompact, ite_eq_right hsmallQ]
    have hy54 : (y : ℝ) ≤ 54 := le_of_lt (not_le.mp hlarge)
    let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
    let q : ℚ := -p * y
    have hp0 : (0 : ℝ) ≤ p := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hpi : |Real.pi - (p : ℝ)| ≤ 1 / 10 ^ 50 := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      rw [abs_le]
      constructor <;> linarith only [pi_fifty_bounds.1, pi_fifty_bounds.2]
    have hp4 : (p : ℝ) ≤ 3.2 := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hq : |(q : ℝ)| ≤ 173 := by
      dsimp only [q]
      simp only [Rat.cast_mul, Rat.cast_neg]
      rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hp0 hyR)]
      have hm := mul_le_mul hp4 hy54 hyR (by norm_num only : (0 : ℝ) ≤ 3.2)
      norm_num only at hm ⊢
      linarith only [hm]
    have hclose : |-Real.pi * (y : ℝ) - (q : ℝ)| ≤ 1 / 10 ^ 48 := by
      dsimp only [q]
      simp only [Rat.cast_mul, Rat.cast_neg]
      have he : -Real.pi * (y : ℝ) - -(p : ℝ) * (y : ℝ) = -((Real.pi - (p : ℝ)) * (y : ℝ)) := by
        ring
      rw [he, abs_neg, abs_mul, abs_of_nonneg hyR]
      have hm := mul_le_mul hpi hy54 hyR (by norm_num only : (0 : ℝ) ≤ 1 / 10 ^ 50)
      nlinarith only [hm]
    have hx : -Real.pi * (y : ℝ) ≤ 0 := by
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hyR)
    have hm : |(q : ℝ)| / (576 + 1 : ℕ) ≤ 1 / 2 := by
      norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
      linarith only [hq]
    have h := exp_rational_taylor_error hx q 576 (by norm_num only) hclose hm
    have hpow : |(q : ℝ)| ^ 576 ≤ (173 : ℝ) ^ 576 := pow_le_pow_left₀ (abs_nonneg _) hq 576
    have hf : (0 : ℝ) < Nat.factorial 576 := by exact_mod_cast Nat.factorial_pos 576
    have hn : (173 : ℝ) ^ 576 / (Nat.factorial 576 : ℝ) * 2 ≤ 1 / 10 ^ 48 := by
      norm_num only [Nat.factorial, pow_succ]
    have hr : |(q : ℝ)| ^ 576 / (Nat.factorial 576 : ℝ) * 2 ≤ 1 / 10 ^ 48 :=
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow hf.le) (by norm_num only)).trans
        hn
    change
      |Real.exp (-Real.pi * (y : ℝ)) -
            ((∑ k ∈ Finset.range 576, q ^ k / (k.factorial : ℚ) : ℚ) : ℝ)| ≤
        _
    simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast]
    linarith only [h, hr]

private def gaussianApproxScaled (y : ℚ) : ℚ :=
  if 54 ≤ y then 0
  else
    let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
    let q : ℚ := -p * y
    (Analysis.rationalScaledRealExp (10 ^ 60) q 64 8).1

set_option maxRecDepth 16384 in
/-- The range-reduced rational Gaussian calculation has the uniform error bound
used in the fixed grid, including the large-argument cutoff. -/
private theorem gaussian_approx_scaled (y : ℚ) (hy : 0 ≤ y) :
    |Real.exp (-Real.pi * (y : ℝ)) - (gaussianApproxScaled y : ℝ)| ≤ 3 / 10 ^ 48 := by
  have hyR : (0 : ℝ) ≤ y := by exact_mod_cast hy
  by_cases hlarge : (54 : ℝ) ≤ y
  · have hlargeQ : (54 : ℚ) ≤ y := by exact_mod_cast hlarge
    rw [gaussianApproxScaled, ite_eq_left hlargeQ]
    have hlarge' : 160 ≤ Real.pi * (y : ℝ) := by nlinarith only [Real.pi_gt_d4, hlarge, hyR]
    simp only [Rat.cast_zero, sub_zero, abs_of_pos (Real.exp_pos _)]
    have hs := exp_neg_large_fortyeight hlarge'
    rw [← neg_mul] at hs
    linarith only [hs]
  · have hsmallQ : ¬(54 : ℚ) ≤ y := by exact_mod_cast hlarge
    rw [gaussianApproxScaled, ite_eq_right hsmallQ]
    have hy54 : (y : ℝ) ≤ 54 := le_of_lt (not_le.mp hlarge)
    let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
    let q : ℚ := -p * y
    have hp0 : (0 : ℝ) ≤ p := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hpi : |Real.pi - (p : ℝ)| ≤ 1 / 10 ^ 50 := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
      rw [abs_le]
      constructor <;> linarith only [pi_fifty_bounds.1, pi_fifty_bounds.2]
    have hp4 : (p : ℝ) ≤ 3.2 := by
      dsimp only [p]
      norm_num only [Rat.cast_div, Rat.cast_ofNat]
    have hq : |(q : ℝ)| ≤ 173 := by
      dsimp only [q]
      simp only [Rat.cast_mul, Rat.cast_neg]
      rw [neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hp0 hyR)]
      have hm := mul_le_mul hp4 hy54 hyR (by norm_num only : (0 : ℝ) ≤ 3.2)
      norm_num only at hm ⊢
      linarith only [hm]
    have hclose : |-Real.pi * (y : ℝ) - (q : ℝ)| ≤ 1 / 10 ^ 48 := by
      dsimp only [q]
      simp only [Rat.cast_mul, Rat.cast_neg]
      have he : -Real.pi * (y : ℝ) - -(p : ℝ) * (y : ℝ) = -((Real.pi - (p : ℝ)) * (y : ℝ)) := by
        ring
      rw [he, abs_neg, abs_mul, abs_of_nonneg hyR]
      have hm := mul_le_mul hpi hy54 hyR (by norm_num only : (0 : ℝ) ≤ 1 / 10 ^ 50)
      nlinarith only [hm]
    have hx : -Real.pi * (y : ℝ) ≤ 0 := by
      simpa only [neg_mul] using neg_nonpos.mpr (mul_nonneg Real.pi_pos.le hyR)
    have hq0 : q ≤ 0 := by
      dsimp only [q]
      have hpq : 0 ≤ p := by
        dsimp only [p]; norm_num only
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hpq) hy
    have hred : |((q / (2 : ℚ) ^ 8 : ℚ) : ℝ)| ≤ 1 := by
      norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
      linarith only [hq]
    have hpow := pow_le_pow_left₀ (abs_nonneg ((q / (2 : ℚ) ^ 8 : ℚ) : ℝ)) hred 64
    have hs :=
      Analysis.norm_scaled_real_exp_error (by norm_num only : 0 < 10 ^ 60) q hq0 64 8
        (by
          norm_num only; linarith only [hred])
        (by
          norm_num only [Nat.factorial] at hpow ⊢; nlinarith only [hpow])
        (by
          intro j hj
          interval_cases j <;>
            norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
              Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast])
    have hbudget : (Analysis.roundedSquareBudget (10 ^ 60) 8 : ℝ) ≤ 1 / 10 ^ 48 := by
      norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
        Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast]
    have hs' := hs.trans hbudget
    have hre :=
      Complex.abs_re_le_norm
        (Complex.exp (q : ℂ) -
          Analysis.rationalComplexCast (Analysis.rationalScaledRealExp (10 ^ 60) q 64 8))
    simp only [Complex.sub_re, ← Complex.ofReal_ratCast, Complex.exp_ofReal_re,
      Analysis.rationalComplexCast] at hre
    rw [Complex.ofReal_ratCast] at hre
    change
      |Real.exp (q : ℝ) - (((Analysis.rationalScaledRealExp (10 ^ 60) q 64 8).1 : ℚ) : ℝ)| ≤
        ‖Complex.exp (q : ℂ) -
            Analysis.rationalComplexCast (Analysis.rationalScaledRealExp (10 ^ 60) q 64 8)‖ at hre
    have hdist : ‖((q : ℝ) : ℂ) - ((-Real.pi * (y : ℝ) : ℝ) : ℂ)‖ < 1 := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
      exact hclose.trans_lt (by norm_num only)
    have hlocal :=
      Complex.locally_lipschitz_exp (r := 1) (by norm_num only) le_rfl
        ((-Real.pi * (y : ℝ) : ℝ) : ℂ) ((q : ℝ) : ℂ) hdist
    have hexp : ‖Complex.exp ((-Real.pi * (y : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_exp, Complex.ofReal_re]
      exact Real.exp_le_one_iff.mpr hx
    have hlocal' : |Real.exp (-Real.pi * (y : ℝ)) - Real.exp (q : ℝ)| ≤ 2 / 10 ^ 48 := by
      rw [← Complex.ofReal_exp, ← Complex.ofReal_exp, ← Complex.ofReal_sub, Complex.norm_real,
        Real.norm_eq_abs] at hlocal
      rw [← Complex.ofReal_sub ((q : ℝ)) (-Real.pi * (y : ℝ)), Complex.norm_real, Complex.norm_real,
        Real.norm_eq_abs, Real.norm_eq_abs, abs_sub_comm (q : ℝ), abs_sub_comm (Real.exp (q : ℝ)),
        abs_of_pos (Real.exp_pos _)] at hlocal
      rw [Complex.norm_exp, Complex.ofReal_re] at hexp
      nlinarith only [hlocal, hexp, hclose, abs_nonneg (-Real.pi * (y : ℝ) - (q : ℝ))]
    change
      |Real.exp (-Real.pi * (y : ℝ)) -
            (((Analysis.rationalScaledRealExp (10 ^ 60) q 64 8).1 : ℚ) : ℝ)| ≤
        _
    have htri :=
      abs_sub_le (Real.exp (-Real.pi * (y : ℝ))) (Real.exp (q : ℝ))
        (((Analysis.rationalScaledRealExp (10 ^ 60) q 64 8).1 : ℚ) : ℝ)
    exact htri.trans ((add_le_add hlocal' (hre.trans hs')).trans_eq (by ring))

set_option maxRecDepth 16384 in
/-- For every nonnegative rational Gaussian argument, the real exponential
`exp (-π y)` has a rational approximation within `3 * 10⁻⁴⁷`. Small
arguments use the certified 50-digit π interval and 1024 Taylor terms;
large arguments use a common exponential cutoff. -/
theorem gaussian_rational_approx_fortyseven (y : ℚ) (hy : 0 ≤ y) :
    ∃ r : ℚ, |Real.exp (-Real.pi * (y : ℝ)) - (r : ℝ)| ≤ 3 / 10 ^ 47 := by
  refine ⟨gaussianApproxFortyseven y, ?_⟩
  exact (gaussian_approx_fortyseven y hy).trans (by norm_num only)

/-- Every Gaussian factor in every fixed-grid cell admits the same rational
error bound. The natural index is arbitrary, so the theorem also covers all
eight terms used in the critical Mellin quadrature. -/
theorem critical_grid_gaussian_rational (i k : ℕ) :
    ∃ r : ℚ,
      |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) - (r : ℝ)| ≤
        3 / 10 ^ 12 := by
  let y : ℚ := ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16)
  have hy : 0 ≤ y := by
    dsimp only [y]
    exact
      mul_nonneg (sq_nonneg _)
        (add_nonneg (by norm_num only) (div_nonneg (Nat.cast_nonneg i) (by norm_num only)))
  obtain ⟨r, hr⟩ := gaussian_rational_approx y hy
  refine ⟨r, ?_⟩
  dsimp only [y] at hr
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_ofNat] at hr
  dsimp only [criticalQuadratureGrid]
  convert hr using 1
  ring_nf

/-- Every Gaussian factor in every fixed-grid cell admits the same rational
error bound. The natural index is arbitrary, so the theorem also covers all
eight terms used in the critical Mellin quadrature. -/
theorem critical_grid_gaussian_fortyseven (i k : ℕ) :
    ∃ r : ℚ,
      |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) - (r : ℝ)| ≤
        3 / 10 ^ 47 := by
  let y : ℚ := ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16)
  have hy : 0 ≤ y := by
    dsimp only [y]
    exact
      mul_nonneg (sq_nonneg _)
        (add_nonneg (by norm_num only) (div_nonneg (Nat.cast_nonneg i) (by norm_num only)))
  obtain ⟨r, hr⟩ := gaussian_rational_approx_fortyseven y hy
  refine ⟨r, ?_⟩
  dsimp only [y] at hr
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_ofNat] at hr
  dsimp only [criticalQuadratureGrid]
  convert hr using 1
  ring_nf

/-- The explicit Gaussian calculation applies at every grid node and
Gaussian index, with the same error bound as the existential estimate. -/
private theorem critical_grid_gaussian_calculated (i k : ℕ) :
    |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) -
          (gaussianApproxFortyseven (((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16)) : ℝ)| ≤
      3 / 10 ^ 48 := by
  have hy : 0 ≤ ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16) :=
    mul_nonneg (sq_nonneg _)
      (add_nonneg (by norm_num only) (div_nonneg (Nat.cast_nonneg i) (by norm_num only)))
  have h := gaussian_approx_fortyseven _ hy
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_ofNat] at h
  dsimp only [criticalQuadratureGrid]
  convert h using 1
  ring_nf

private theorem critical_grid_gaussian_compact (i k : ℕ) :
    |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) -
          (gaussianApproxCompact (((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16)) : ℝ)| ≤
      3 / 10 ^ 48 := by
  have hy : 0 ≤ ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16) :=
    mul_nonneg (sq_nonneg _)
      (add_nonneg (by norm_num only) (div_nonneg (Nat.cast_nonneg i) (by norm_num only)))
  have h := gaussian_approx_compact _ hy
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_ofNat] at h
  dsimp only [criticalQuadratureGrid]
  convert h using 1
  ring_nf

private theorem critical_grid_gaussian_scaled (i k : ℕ) :
    |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) -
          (gaussianApproxScaled (((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16)) : ℝ)| ≤
      3 / 10 ^ 48 := by
  have hy : 0 ≤ ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16) :=
    mul_nonneg (sq_nonneg _)
      (add_nonneg (by norm_num only) (div_nonneg (Nat.cast_nonneg i) (by norm_num only)))
  have h := gaussian_approx_scaled _ hy
  simp only [Rat.cast_mul, Rat.cast_pow, Rat.cast_add, Rat.cast_one, Rat.cast_natCast, Rat.cast_div,
    Rat.cast_ofNat] at h
  dsimp only [criticalQuadratureGrid]
  convert h using 1
  ring_nf

/-- The rational Gaussian approximation at a grid node and term index. -/
private def gridGaussianTaylor (i k : ℕ) : ℚ :=
  gaussianApproxScaled (((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16))

/-- The calculated Gaussian factor has a uniform error and magnitude bound. -/
private theorem grid_gaussian_bounded (i : ℕ) :
    ∀ k : ℕ,
      |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) -
              (gridGaussianTaylor i k : ℝ)| ≤
          3 / 10 ^ 48 ∧
        |(gridGaussianTaylor i k : ℝ)| ≤ 2 := by
  let r : ℕ → ℚ := fun k ↦ gaussianApproxScaled (((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16))
  have hr :
    ∀ k : ℕ,
      |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) - (r k : ℝ)| ≤
        3 / 10 ^ 48 :=
    critical_grid_gaussian_scaled i
  intro k
  change
    |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) - (r k : ℝ)| ≤ 3 / 10 ^ 48 ∧
      |(r k : ℝ)| ≤ 2
  refine ⟨hr k, ?_⟩
  have hg : 0 ≤ criticalQuadratureGrid i := by
    dsimp only [criticalQuadratureGrid]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    exact add_nonneg (by norm_num only) (div_nonneg hi (by norm_num only))
  have hx : -Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i ≤ 0 := by
    exact
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr Real.pi_pos.le) (sq_nonneg _)) hg
  have he : Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) ≤ 1 :=
    Real.exp_le_one_iff.mpr hx
  have htri :=
    abs_add_le ((r k : ℝ) - Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i))
      (Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i))
  rw [sub_add_cancel, abs_sub_comm, abs_of_pos (Real.exp_pos _)] at htri
  linarith only [htri, hr k, he]

/-- Every fixed-grid Gaussian term has a rational approximation with error
at most `3 * 10⁻⁴⁷` and magnitude at most two. A single function supplies
the approximations for all indices without list indexing. -/
theorem critical_grid_gaussian_bounded (i : ℕ) :
    ∃ r : ℕ → ℚ,
      ∀ k : ℕ,
        |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) - (r k : ℝ)| ≤
            3 / 10 ^ 47 ∧
          |(r k : ℝ)| ≤ 2 := by
  refine ⟨gridGaussianTaylor i, ?_⟩
  intro k
  exact ⟨((grid_gaussian_bounded i k).1).trans (by norm_num only), (grid_gaussian_bounded i k).2⟩

/-- The polynomial multiplying the `k`-th Gaussian in a derivative
coefficient. It contains no transcendental exponential and uses only a
finite sum of falling products and integer powers. -/
noncomputable def thetaGaussianPoly (s : ℂ) (n k : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j) *
      (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j))

/-- A finite geometric sum controls the perturbation of an integer power.
The bound is valid for arbitrary complex inputs and does not divide by their
difference, so it also covers coincident inputs and the zero-th power. -/
theorem complex_pow_perturbation (z w : ℂ) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ ‖z - w‖ * ∑ j ∈ Finset.range n, ‖z‖ ^ j * ‖w‖ ^ (n - 1 - j) := by
  rw [← (Commute.all z w).mul_geom_sum₂ n, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  calc
    ‖∑ j ∈ Finset.range n, z ^ j * w ^ (n - 1 - j)‖ ≤
        ∑ j ∈ Finset.range n, ‖z ^ j * w ^ (n - 1 - j)‖ :=
      norm_sum_le _ _
    _ = ∑ j ∈ Finset.range n, ‖z‖ ^ j * ‖w‖ ^ (n - 1 - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [norm_mul, norm_pow, norm_pow]

/-- A norm cap for both bases and a cap for their difference turn the
complex power perturbation into a finite real polynomial in those caps. -/
theorem complex_pow_perturbation_bound (z w : ℂ) (n : ℕ) {B D : ℝ} (hz : ‖z‖ ≤ B) (hw : ‖w‖ ≤ B)
    (hd : ‖z - w‖ ≤ D) : ‖z ^ n - w ^ n‖ ≤ D * ∑ j ∈ Finset.range n, B ^ j * B ^ (n - 1 - j) := by
  have hB : 0 ≤ B := (norm_nonneg z).trans hz
  have hsum :
    (∑ j ∈ Finset.range n, ‖z‖ ^ j * ‖w‖ ^ (n - 1 - j)) ≤
      ∑ j ∈ Finset.range n, B ^ j * B ^ (n - 1 - j) := by
    apply Finset.sum_le_sum
    intro j hj
    exact
      mul_le_mul (pow_le_pow_left₀ (norm_nonneg z) hz j)
        (pow_le_pow_left₀ (norm_nonneg w) hw (n - 1 - j)) (pow_nonneg (norm_nonneg w) _)
        (pow_nonneg hB _)
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range n, ‖z‖ ^ j * ‖w‖ ^ (n - 1 - j) := by
    apply Finset.sum_nonneg
    intro j hj
    exact mul_nonneg (pow_nonneg (norm_nonneg z) _) (pow_nonneg (norm_nonneg w) _)
  have hD : 0 ≤ D := (norm_nonneg _).trans hd
  exact (complex_pow_perturbation z w n).trans (mul_le_mul hd hsum hsum0 hD)

/-- The polynomial part of one Gaussian derivative coefficient with an
explicit real parameter in place of π. For rational parameter, node and
height, this expression can be evaluated using rational complex arithmetic. -/
noncomputable def thetaGaussianPolyAt (s : ℂ) (n k : ℕ) (x p : ℝ) : ℂ :=
  ∑ j ∈ Finset.range (n + 1),
    (n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j) *
      (((-p * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j))

/-- Substituting π in the parameterized polynomial recovers the original
Gaussian derivative coefficient exactly. -/
theorem theta_gaussian_poly_at_pi (s : ℂ) (n k : ℕ) (x : ℝ) :
    thetaGaussianPolyAt s n k x Real.pi = thetaGaussianPoly s n k x := by rfl

/-- Replacing π by a real parameter changes the Gaussian derivative
polynomial by at most the explicit finite sum of power perturbations. The
bound retains all coefficient magnitudes for later rational certification. -/
theorem theta_gaussian_poly_perturb (s : ℂ) (n k : ℕ) (x p : ℝ) :
    ‖thetaGaussianPoly s n k x - thetaGaussianPolyAt s n k x p‖ ≤
      ∑ j ∈ Finset.range (n + 1),
        ‖(n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j)‖ *
          (‖((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) - ((-p * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ)‖ *
            ∑ h ∈ Finset.range (n - j),
              ‖((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ)‖ ^ h *
                ‖((-p * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ)‖ ^ (n - j - 1 - h)) := by
  simp only [thetaGaussianPoly, thetaGaussianPolyAt, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j ∈ Finset.range (n + 1),
            ((n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j) *
                (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j)) -
              (n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j) *
                (((-p * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j)))‖ ≤
        ∑ j ∈ Finset.range (n + 1),
          ‖(n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j) *
                (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j)) -
              (n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j) *
                (((-p * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) ^ (n - j))‖ :=
      norm_sum_le _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro j hj
      rw [← mul_sub, norm_mul]
      exact mul_le_mul_of_nonneg_left (complex_pow_perturbation _ _ _) (norm_nonneg _)

/-- The explicit nonnegative error budget for replacing π in one Gaussian
derivative polynomial. It is a finite sum of coefficient norms and geometric
power-difference bounds. -/
noncomputable def thetaGaussianPolyError (s : ℂ) (n k : ℕ) (x p : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1),
    ‖(n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j)‖ *
      (‖((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) - ((-p * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ)‖ *
        ∑ h ∈ Finset.range (n - j),
          ‖((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ)‖ ^ h *
            ‖((-p * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ)‖ ^ (n - j - 1 - h))

/-- The polynomial error is bounded by its explicit finite error budget. -/
theorem theta_gaussian_poly_error (s : ℂ) (n k : ℕ) (x p : ℝ) :
    ‖thetaGaussianPoly s n k x - thetaGaussianPolyAt s n k x p‖ ≤
      thetaGaussianPolyError s n k x p := by
  exact theta_gaussian_poly_perturb s n k x p

/-- The Gaussian polynomial base changes by at most `(k+1)² / 10⁵⁰` when
π is replaced by the certified lower endpoint. This converts the only
transcendental input in the base difference to an explicit rational bound. -/
theorem gaussian_base_pi_error (k : ℕ) :
    ‖((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) -
          ((-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℝ) *
                ((k : ℝ) + 1) ^ 2 :
              ℝ) :
            ℂ)‖ ≤
      ((k : ℝ) + 1) ^ 2 / 10 ^ 50 := by
  have hp :
    |Real.pi - (314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℝ)| ≤
      1 / 10 ^ 50 := by
    rw [abs_le]
    constructor <;> linarith only [pi_fifty_bounds.1, pi_fifty_bounds.2]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have he :
    -Real.pi * ((k : ℝ) + 1) ^ 2 -
        -(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℝ) * ((k : ℝ) + 1) ^ 2 =
      -(Real.pi - (314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℝ)) *
        ((k : ℝ) + 1) ^ 2 := by
    ring
  rw [he, abs_mul, abs_neg, abs_of_nonneg (sq_nonneg ((k : ℝ) + 1))]
  have hm := mul_le_mul_of_nonneg_right hp (sq_nonneg ((k : ℝ) + 1))
  nlinarith only [hm]

/-- Both the true Gaussian polynomial base and the base obtained from the
certified rational π endpoint have norm at most `4 * (k+1)²`. The bound is
uniform in the derivative order and contains only rational operations. -/
theorem gaussian_base_pi_norm (k : ℕ) :
    ‖((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ)‖ ≤ 4 * ((k : ℝ) + 1) ^ 2 ∧
      ‖((-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℝ) * ((k : ℝ) + 1) ^ 2 :
              ℝ) :
            ℂ)‖ ≤
        4 * ((k : ℝ) + 1) ^ 2 := by
  have hp0 : (0 : ℝ) ≤ 314159265358979323846264338327950288419716939937510 / 10 ^ 50 := by
    norm_num only
  have hp4 : (314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℝ) ≤ 4 := by
    norm_num only
  have hs : 0 ≤ ((k : ℝ) + 1) ^ 2 := sq_nonneg _
  constructor
  · rw [Complex.norm_real, Real.norm_eq_abs, neg_mul, abs_neg,
      abs_of_nonneg (mul_nonneg Real.pi_pos.le hs)]
    exact mul_le_mul_of_nonneg_right Real.pi_le_four hs
  · rw [Complex.norm_real, Real.norm_eq_abs, neg_mul, abs_neg, abs_of_nonneg (mul_nonneg hp0 hs)]
    exact mul_le_mul_of_nonneg_right hp4 hs

/-- A π-free error budget for one Gaussian derivative polynomial. Complex
coefficient norms are bounded by the sum of the absolute values of their
real and imaginary parts; all remaining operations are finite arithmetic. -/
noncomputable def thetaGaussianRationalError (s : ℂ) (n k : ℕ) (x : ℝ) : ℝ :=
  let B : ℝ := 4 * ((k : ℝ) + 1) ^ 2
  let D : ℝ := ((k : ℝ) + 1) ^ 2 / 10 ^ 50
  ∑ j ∈ Finset.range (n + 1),
    let c : ℂ := (n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / (x : ℂ) ^ j)
    (|c.re| + |c.im|) * (D * ∑ h ∈ Finset.range (n - j), B ^ h * B ^ (n - j - 1 - h))

/-- Replacing π by its certified rational lower endpoint in a Gaussian
polynomial has an explicit error bound containing no π and no complex norm.
For rational input data its right side reduces to rational arithmetic. -/
theorem theta_gaussian_poly_rational_bound (s : ℂ) (n k : ℕ) (x : ℝ) :
    ‖thetaGaussianPoly s n k x -
          thetaGaussianPolyAt s n k x
            (314159265358979323846264338327950288419716939937510 / 10 ^ 50)‖ ≤
      thetaGaussianRationalError s n k x := by
  let B : ℝ := 4 * ((k : ℝ) + 1) ^ 2
  let D : ℝ := ((k : ℝ) + 1) ^ 2 / 10 ^ 50
  let z : ℂ := ((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ)
  let w : ℂ :=
    ((-(314159265358979323846264338327950288419716939937510 / 10 ^ 50 : ℝ) * ((k : ℝ) + 1) ^ 2 :
        ℝ) :
      ℂ)
  have hz : ‖z‖ ≤ B := (gaussian_base_pi_norm k).1
  have hw : ‖w‖ ≤ B := (gaussian_base_pi_norm k).2
  have hd : ‖z - w‖ ≤ D := gaussian_base_pi_error k
  simp only [thetaGaussianPoly, thetaGaussianPolyAt, thetaGaussianRationalError,
    ← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro j hj
  rw [← mul_sub, norm_mul]
  have he := complex_pow_perturbation_bound z w (n - j) hz hw hd
  exact
    mul_le_mul (Complex.norm_le_abs_re_add_abs_im _) he (norm_nonneg _)
      (add_nonneg (abs_nonneg _) (abs_nonneg _))

/-- The derivative coefficient is linear in its Gaussian values. Each
Gaussian exponential is factored out of its inner polynomial sum so that a
single approximation can be reused for all inner terms. -/
theorem theta_poly_gaussian (s : ℂ) (N n : ℕ) (x : ℝ) :
    thetaMellinPolyCoeff s N n x =
      2 *
        ∑ k ∈ Finset.range N,
          thetaGaussianPoly s n k x *
            Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * x) := by
  simp only [thetaMellinPolyCoeff, thetaGaussianPoly, Finset.sum_mul, mul_assoc]

/-- The `k`-th Gaussian weight in a Taylor cell. It sums the polynomial
coefficients over all derivative orders using the cell's exact integration
weights; the value is independent of the Gaussian exponential. -/
noncomputable def thetaGaussianWeight (s : ℂ) (n k : ℕ) (a b : ℝ) : ℂ :=
  2 *
    ∑ l ∈ Finset.range (n + 1),
      ((((l.factorial : ℝ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))) : ℝ) : ℂ) * thetaGaussianPoly s l k a

/-- The Taylor-cell Gaussian weight with π replaced by a real parameter.
It is a finite algebraic expression in that parameter, the node, the height
and the integration weights. -/
noncomputable def thetaGaussianWeightAt (s : ℂ) (n k : ℕ) (a b p : ℝ) : ℂ :=
  2 *
    ∑ l ∈ Finset.range (n + 1),
      ((((l.factorial : ℝ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))) : ℝ) : ℂ) *
        thetaGaussianPolyAt s l k a p

private theorem rational_gaussian_poly_cast (t x p : ℚ) (n k : ℕ) :
    Analysis.rationalComplexCast (Analysis.rationalGaussianPoly t x p n k) =
      thetaGaussianPolyAt (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k x p := by
  rw [Analysis.rationalGaussianPoly, Analysis.rationalComplexCast_sum, thetaGaussianPolyAt]
  apply Finset.sum_congr rfl
  intro j hj
  rw [Analysis.rationalComplexCast_scale, Analysis.rational_mellin_falling_cast]
  push_cast
  ring

private theorem rational_gaussian_weight_cast (t a b p : ℚ) (n k : ℕ) :
    Analysis.rationalComplexCast (Analysis.rationalGaussianWeight t a b p n k) =
      thetaGaussianWeightAt (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b p := by
  rw [Analysis.rationalGaussianWeight, Analysis.rationalComplexCast_scale,
    Analysis.rationalComplexCast_sum, thetaGaussianWeightAt]
  norm_num only [Rat.cast_ofNat]
  apply congrArg (fun z : ℂ ↦ 2 * z)
  apply Finset.sum_congr rfl
  intro l hl
  rw [Analysis.rationalComplexCast_scale, rational_gaussian_poly_cast]
  push_cast
  rfl

private theorem rational_gaussian_weight_cast_norm (t a b p : ℚ) (n k : ℕ) :
    ‖thetaGaussianWeightAt (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b p‖ ≤
      (Analysis.rationalComplexOneNorm (Analysis.rationalGaussianWeight t a b p n k) : ℝ) := by
  rw [← rational_gaussian_weight_cast t a b p n k]
  have h :=
    Complex.norm_le_abs_re_add_abs_im
      (Analysis.rationalComplexCast (Analysis.rationalGaussianWeight t a b p n k))
  simpa only [Analysis.rationalComplexOneNorm, Analysis.rationalComplexCast, Rat.cast_add,
    Rat.cast_abs] using h

/-- For rational heights of magnitude at most 100, nodes at least one, and
cells of width `1/16`, each rationalized 200th-order Gaussian weight in the
eight-term range has norm less than two million. -/
theorem theta_gaussian_weight_at_uniform_norm (t a b p : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) (hp : |p| ≤ 4) {k : ℕ} (hk : k < 8) :
    ‖thetaGaussianWeightAt (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b p‖ < 2000000 := by
  have hr :=
    (Rat.cast_lt (K := ℝ)).mpr
      (Analysis.rational_gaussian_norm_full_uniform t a b p ht ha hab hp hk)
  norm_num only [Rat.cast_ofNat] at hr
  exact (rational_gaussian_weight_cast_norm t a b p 200 k).trans_lt hr

private theorem rational_gaussian_coeff_cast (t x : ℚ) (n j : ℕ) :
    Analysis.rationalComplexCast (Analysis.rationalGaussianCoeff t x n j) =
      (n.choose j : ℂ) *
        (Analysis.complexFalling (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1) j /
          ((x : ℝ) : ℂ) ^ j) := by
  rw [Analysis.rationalGaussianCoeff, Analysis.rationalComplexCast_scale,
    Analysis.rational_mellin_falling_cast]
  push_cast
  ring

private theorem rational_gaussian_poly_error_cast (t x : ℚ) (n k : ℕ) :
    (Analysis.rationalGaussianPolyError t x n k : ℝ) =
      thetaGaussianRationalError (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k x := by
  simp only [Analysis.rationalGaussianPolyError, thetaGaussianRationalError, Rat.cast_sum,
    Rat.cast_mul, Rat.cast_add, Rat.cast_abs, Rat.cast_div, Rat.cast_pow, Rat.cast_natCast,
    Rat.cast_ofNat, Rat.cast_one]
  apply Finset.sum_congr rfl
  intro j hj
  have hc := rational_gaussian_coeff_cast t x n j
  have hre := congrArg Complex.re hc
  have him := congrArg Complex.im hc
  simp only [Analysis.rationalComplexCast] at hre him
  rw [hre, him]

/-- A complex number represented by an exact pair of rational components. -/
private def IsRationalComplex (z : ℂ) : Prop :=
  ∃ q : ℚ × ℚ, z = Analysis.rationalComplexCast q

private theorem rational_complex_rat (q : ℚ) : IsRationalComplex (q : ℂ) := by
  refine ⟨(q, 0), ?_⟩
  apply Complex.ext
  · simp only [Analysis.rationalComplexCast, Complex.ratCast_re]
  · simp only [Analysis.rationalComplexCast, Complex.ratCast_im, Rat.cast_zero]

private theorem rational_complex_i : IsRationalComplex Complex.I := by
  refine ⟨(0, 1), ?_⟩
  apply Complex.ext
  · simp only [Analysis.rationalComplexCast, Complex.I_re, Rat.cast_zero]
  · simp only [Analysis.rationalComplexCast, Complex.I_im, Rat.cast_one]

private theorem rational_complex_add {z w : ℂ} (hz : IsRationalComplex z)
    (hw : IsRationalComplex w) : IsRationalComplex (z + w) := by
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := hw
  exact ⟨Analysis.rationalComplexAdd a b, (Analysis.rationalComplexCast_add a b).symm⟩

private theorem rational_complex_mul {z w : ℂ} (hz : IsRationalComplex z)
    (hw : IsRationalComplex w) : IsRationalComplex (z * w) := by
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨b, rfl⟩ := hw
  exact ⟨Analysis.rationalComplexMul a b, (Analysis.rationalComplexCast_mul a b).symm⟩

private theorem rational_complex_neg {z : ℂ} (hz : IsRationalComplex z) :
    IsRationalComplex (-z) := by
  have h := rational_complex_mul (rational_complex_rat (-1)) hz
  simpa only [Rat.cast_neg, Rat.cast_one, neg_one_mul] using h

private theorem rational_complex_sub {z w : ℂ} (hz : IsRationalComplex z)
    (hw : IsRationalComplex w) : IsRationalComplex (z - w) := by
  simpa only [sub_eq_add_neg] using rational_complex_add hz (rational_complex_neg hw)

private theorem rational_complex_pow {z : ℂ} (hz : IsRationalComplex z) (n : ℕ) :
    IsRationalComplex (z ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, Rat.cast_one] using rational_complex_rat 1
  | succ n ih => simpa only [pow_succ] using rational_complex_mul ih hz

private theorem rational_complex_sum {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ S, IsRationalComplex (f i)) : IsRationalComplex (∑ i ∈ S, f i) := by
  classical
    induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Rat.cast_zero] using rational_complex_rat 0
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact
      rational_complex_add (hf i (Finset.mem_insert_self i S))
        (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

private theorem rational_complex_prod {ι : Type*} (S : Finset ι) (f : ι → ℂ)
    (hf : ∀ i ∈ S, IsRationalComplex (f i)) : IsRationalComplex (∏ i ∈ S, f i) := by
  classical
    induction S using Finset.induction_on with
  | empty => simpa only [Finset.prod_empty, Rat.cast_one] using rational_complex_rat 1
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    exact
      rational_complex_mul (hf i (Finset.mem_insert_self i S))
        (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

private theorem rational_complex_falling {w : ℂ} (hw : IsRationalComplex w) (n : ℕ) :
    IsRationalComplex (Analysis.complexFalling w n) := by
  rw [Analysis.complexFalling]
  apply rational_complex_prod
  intro j hj
  apply rational_complex_sub hw
  simpa only [Rat.cast_natCast] using rational_complex_rat (j : ℚ)

/-- A real number represented by an exact rational value. -/
private def IsRationalReal (x : ℝ) : Prop :=
  ∃ q : ℚ, x = (q : ℝ)

private theorem rational_real_rat (q : ℚ) : IsRationalReal (q : ℝ) :=
  ⟨q, rfl⟩

private theorem rational_real_add {x y : ℝ} (hx : IsRationalReal x) (hy : IsRationalReal y) :
    IsRationalReal (x + y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a + b, (Rat.cast_add a b).symm⟩

private theorem rational_real_mul {x y : ℝ} (hx : IsRationalReal x) (hy : IsRationalReal y) :
    IsRationalReal (x * y) := by
  obtain ⟨a, rfl⟩ := hx
  obtain ⟨b, rfl⟩ := hy
  exact ⟨a * b, (Rat.cast_mul a b).symm⟩

private theorem rational_real_abs {x : ℝ} (hx : IsRationalReal x) : IsRationalReal |x| := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨|a|, (Rat.cast_abs a).symm⟩

private theorem rational_real_pow {x : ℝ} (hx : IsRationalReal x) (n : ℕ) :
    IsRationalReal (x ^ n) := by
  obtain ⟨a, rfl⟩ := hx
  exact ⟨a ^ n, (Rat.cast_pow a n).symm⟩

private theorem rational_real_sum {ι : Type*} (S : Finset ι) (f : ι → ℝ)
    (hf : ∀ i ∈ S, IsRationalReal (f i)) : IsRationalReal (∑ i ∈ S, f i) := by
  classical
    induction S using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Rat.cast_zero] using rational_real_rat 0
  | @insert i S hi ih =>
    rw [Finset.sum_insert hi]
    exact
      rational_real_add (hf i (Finset.mem_insert_self i S))
        (ih (fun j hj ↦ hf j (Finset.mem_insert_of_mem hj)))

private theorem rational_complex_re {z : ℂ} (hz : IsRationalComplex z) : IsRationalReal z.re := by
  obtain ⟨q, rfl⟩ := hz
  exact ⟨q.1, rfl⟩

private theorem rational_complex_im {z : ℂ} (hz : IsRationalComplex z) : IsRationalReal z.im := by
  obtain ⟨q, rfl⟩ := hz
  exact ⟨q.2, rfl⟩

private theorem rational_complex_critical (t : ℚ) :
    IsRationalComplex (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
  apply rational_complex_add
  · simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, Complex.ofReal_div, Complex.ofReal_one,
      Complex.ofReal_ofNat] using rational_complex_rat (1 / 2)
  · exact rational_complex_mul (rational_complex_rat t) rational_complex_i

private theorem rational_complex_coefficient (s : ℂ) (hs : IsRationalComplex s) (n j : ℕ) (x : ℚ) :
    IsRationalComplex
      ((n.choose j : ℂ) * (Analysis.complexFalling (s / 2 - 1) j / ((x : ℝ) : ℂ) ^ j)) := by
  have hhalf : IsRationalComplex ((2 : ℂ)⁻¹) := by
    simpa only [Rat.cast_inv, Rat.cast_ofNat] using rational_complex_rat ((2 : ℚ)⁻¹)
  have hw : IsRationalComplex (s / 2 - 1) := by
    apply rational_complex_sub
    · simpa only [div_eq_mul_inv] using rational_complex_mul hs hhalf
    · simpa only [Rat.cast_one] using rational_complex_rat 1
  apply rational_complex_mul
  · simpa only [Rat.cast_natCast] using rational_complex_rat (n.choose j : ℚ)
  · rw [div_eq_mul_inv]
    apply rational_complex_mul (rational_complex_falling hw j)
    simpa only [Rat.cast_inv, Rat.cast_pow, Complex.ofReal_ratCast] using
      rational_complex_rat ((x ^ j)⁻¹)

/-- At rational heights and nodes, the π-free Gaussian polynomial error
budget itself is a rational number. Its real and imaginary components, power
bounds and finite sums are all closed under exact rational arithmetic. -/
theorem theta_gaussian_error_is_rational (t x : ℚ) (n k : ℕ) :
    ∃ q : ℚ,
      thetaGaussianRationalError (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k x = (q : ℝ) := by
  have hB : IsRationalReal (4 * ((k : ℝ) + 1) ^ 2) := by
    have h := rational_real_rat (4 * ((k : ℚ) + 1) ^ 2)
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one] using h
  have hD : IsRationalReal (((k : ℝ) + 1) ^ 2 / 10 ^ 50) := by
    have h := rational_real_rat (((k : ℚ) + 1) ^ 2 / 10 ^ 50)
    simpa only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one] using h
  unfold thetaGaussianRationalError
  apply rational_real_sum
  intro j hj
  apply rational_real_mul
  · apply rational_real_add
    · exact
        rational_real_abs
          (rational_complex_re (rational_complex_coefficient _ (rational_complex_critical t) n j x))
    · exact
        rational_real_abs
          (rational_complex_im (rational_complex_coefficient _ (rational_complex_critical t) n j x))
  · apply rational_real_mul hD
    apply rational_real_sum
    intro h hh
    exact rational_real_mul (rational_real_pow hB h) (rational_real_pow hB (n - j - 1 - h))

private theorem rational_complex_poly_at (s : ℂ) (hs : IsRationalComplex s) (n k : ℕ) (x p : ℚ) :
    IsRationalComplex (thetaGaussianPolyAt s n k x p) := by
  have hhalf : IsRationalComplex ((2 : ℂ)⁻¹) := by
    simpa only [Rat.cast_inv, Rat.cast_ofNat] using rational_complex_rat ((2 : ℚ)⁻¹)
  have hw : IsRationalComplex (s / 2 - 1) := by
    apply rational_complex_sub
    · simpa only [div_eq_mul_inv] using rational_complex_mul hs hhalf
    · simpa only [Rat.cast_one] using rational_complex_rat 1
  rw [thetaGaussianPolyAt]
  apply rational_complex_sum
  intro j hj
  apply rational_complex_mul
  · apply rational_complex_mul
    · simpa only [Rat.cast_natCast] using rational_complex_rat (n.choose j : ℚ)
    · rw [div_eq_mul_inv]
      apply rational_complex_mul (rational_complex_falling hw j)
      simpa only [Rat.cast_inv, Rat.cast_pow, Complex.ofReal_ratCast] using
        rational_complex_rat ((x ^ j)⁻¹)
  · have h := rational_complex_rat ((-p * ((k : ℚ) + 1) ^ 2) ^ (n - j))
    simpa only [Rat.cast_pow, Rat.cast_mul, Rat.cast_neg, Rat.cast_add, Rat.cast_natCast,
      Rat.cast_one, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_pow, Complex.ofReal_add,
      Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ratCast] using h

/-- At rational heights, nodes, endpoints and π parameters, a Gaussian cell
weight has rational real and imaginary parts. Its finite products and sums
are closed under exact rational complex arithmetic. -/
theorem theta_gaussian_weight_at_rational (t a b p : ℚ) (n k : ℕ) :
    ∃ r im : ℚ,
      thetaGaussianWeightAt (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b p =
        (r : ℂ) + (im : ℂ) * Complex.I := by
  let q := Analysis.rationalGaussianWeight t a b p n k
  refine ⟨q.1, q.2, ?_⟩
  rw [← rational_gaussian_weight_cast t a b p n k]
  dsimp only [q]
  apply Complex.ext
  · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

/-- Replacing π by a parameter in an entire cell weight has the finite
error bound obtained by summing its derivative-polynomial error budgets. -/
theorem theta_gaussian_weight_error (s : ℂ) (n k : ℕ) (a b p : ℝ) :
    ‖thetaGaussianWeight s n k a b - thetaGaussianWeightAt s n k a b p‖ ≤
      2 *
        ∑ l ∈ Finset.range (n + 1),
          ‖((((l.factorial : ℝ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))) : ℝ) : ℂ)‖ *
            thetaGaussianPolyError s l k a p := by
  simp only [thetaGaussianWeight, thetaGaussianWeightAt, ← mul_sub, norm_mul, Complex.norm_ofNat,
    ← Finset.sum_sub_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro l hl
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (theta_gaussian_poly_error s l k a p) (norm_nonneg _)

/-- The complete Gaussian cell weight has a π-free error budget when π is
replaced by its certified rational lower endpoint. Only absolute values of
real algebraic expressions and finite sums remain in the bound. -/
theorem theta_gaussian_weight_rational_bound (s : ℂ) (n k : ℕ) (a b : ℝ) :
    ‖thetaGaussianWeight s n k a b -
          thetaGaussianWeightAt s n k a b
            (314159265358979323846264338327950288419716939937510 / 10 ^ 50)‖ ≤
      2 *
        ∑ l ∈ Finset.range (n + 1),
          |(l.factorial : ℝ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))| *
            thetaGaussianRationalError s l k a := by
  simp only [thetaGaussianWeight, thetaGaussianWeightAt, ← mul_sub, norm_mul, Complex.norm_ofNat,
    ← Finset.sum_sub_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num only)
  refine (norm_sum_le _ _).trans ?_
  apply Finset.sum_le_sum
  intro l hl
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (theta_gaussian_poly_rational_bound s l k a) (abs_nonneg _)

/-- Rational cell data give a rational complex Gaussian weight approximation
with a finite π-free error budget. This combines the exact rationality of
the substituted weight with the uniform π perturbation estimate. -/
theorem theta_gaussian_weight_rational_fifty (t a b : ℚ) (n k : ℕ) :
    ∃ r im : ℚ,
      ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b -
            ((r : ℂ) + (im : ℂ) * Complex.I)‖ ≤
        2 *
          ∑ l ∈ Finset.range (n + 1),
            |(l.factorial : ℝ)⁻¹ * (((b : ℝ) - a) ^ (l + 1) / (l + 1))| *
              thetaGaussianRationalError (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) l k a := by
  obtain ⟨r, im, hr⟩ :=
    theta_gaussian_weight_at_rational t a b
      (314159265358979323846264338327950288419716939937510 / 10 ^ 50) n k
  refine ⟨r, im, ?_⟩
  rw [← hr]
  have h :=
    theta_gaussian_weight_rational_bound (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k (a : ℝ)
      (b : ℝ)
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at h ⊢
  exact h

/-- The π-free error budget for replacing one complete Gaussian cell
weight by its rational-parameter value. It is a finite sum of absolute
integration weights and polynomial perturbation budgets. -/
noncomputable def thetaGaussianWeightRationalError (s : ℂ) (n k : ℕ) (a b : ℝ) : ℝ :=
  2 *
    ∑ l ∈ Finset.range (n + 1),
      |(l.factorial : ℝ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))| * thetaGaussianRationalError s l k a

private theorem rational_gaussian_weight_error_cast (t a b : ℚ) (n k : ℕ) :
    (Analysis.rationalGaussianWeightError t a b n k : ℝ) =
      thetaGaussianWeightRationalError (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b := by
  simp only [Analysis.rationalGaussianWeightError, thetaGaussianWeightRationalError, Rat.cast_mul,
    Rat.cast_sum, Rat.cast_abs, Rat.cast_inv, Rat.cast_natCast, Rat.cast_div, Rat.cast_sub,
    Rat.cast_pow, Rat.cast_add, Rat.cast_one, Rat.cast_ofNat]
  apply congrArg (fun z : ℝ ↦ 2 * z)
  apply Finset.sum_congr rfl
  intro l hl
  rw [rational_gaussian_poly_error_cast]

private theorem rational_gaussian_weight_error_fast_cast (t a b : ℚ) (n k : ℕ) :
    (Analysis.rationalGaussianWeightErrorFast t a b n k : ℝ) =
      thetaGaussianWeightRationalError (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b := by
  rw [Analysis.rational_gaussian_weight_error_fast]
  exact rational_gaussian_weight_error_cast t a b n k

/-- For rational heights and cell endpoints, the entire π-free weight error
budget is rational. Each Taylor integration weight and polynomial budget is
rational, and the finite sum preserves rationality. -/
theorem theta_gaussian_weight_error_is_rational (t a b : ℚ) (n k : ℕ) :
    ∃ q : ℚ,
      thetaGaussianWeightRationalError (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b =
        (q : ℝ) := by
  exact
    ⟨Analysis.rationalGaussianWeightErrorFast t a b n k,
      (rational_gaussian_weight_error_fast_cast t a b n k).symm⟩

/-- Rational cell data therefore give a rational complex weight and a
rational error bound for it. This theorem combines the finite perturbation
estimate with rationality of the complete error budget. -/
theorem theta_gaussian_weight_cert_exists (t a b : ℚ) (n k : ℕ) :
    ∃ r im e : ℚ,
      ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b -
            ((r : ℂ) + (im : ℂ) * Complex.I)‖ ≤
        (e : ℝ) := by
  obtain ⟨r, im, hr⟩ := theta_gaussian_weight_rational_fifty t a b n k
  obtain ⟨e, he⟩ := theta_gaussian_weight_error_is_rational t a b n k
  refine ⟨r, im, e, ?_⟩
  rw [← he]
  exact hr

/-- Every 200th-order Gaussian cell weight with rational `|t| ≤ 100`, node
at least one, width `1/16`, and index below eight has a rational complex
approximation with error below `10⁻⁴²`. The common finite majorant is
checked once and applies to every cell and all eight Gaussian terms. -/
theorem theta_gaussian_weight_uniform (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) {k : ℕ} (hk : k < 8) :
    ∃ r im : ℚ,
      ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b -
            ((r : ℂ) + (im : ℂ) * Complex.I)‖ <
        1 / 10 ^ 42 := by
  obtain ⟨r, im, he⟩ :=
    theta_gaussian_weight_at_rational t a b
      (314159265358979323846264338327950288419716939937510 / 10 ^ 50) 200 k
  refine ⟨r, im, ?_⟩
  rw [← he]
  have hw :=
    theta_gaussian_weight_rational_bound (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k (a : ℝ)
      (b : ℝ)
  have hr :=
    (Rat.cast_lt (K := ℝ)).mpr (Analysis.rational_gaussian_error_full_uniform t a b ht ha hab hk)
  have hs := rational_gaussian_weight_error_fast_cast t a b 200 k
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hw ⊢
  change (Analysis.rationalGaussianWeightErrorFast t a b 200 k : ℝ) < _ at hr
  rw [hs] at hr
  dsimp only [thetaGaussianWeightRationalError] at hr
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hr
  exact hw.trans_lt hr

/-- Replacing π by its rational lower endpoint changes each admissible
200th-order Gaussian cell weight by less than `10⁻⁴²`. This version names
the substituted algebraic weight directly for finite computation. -/
theorem theta_gaussian_weight_pi_close (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) {k : ℕ} (hk : k < 8) :
    ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b -
          thetaGaussianWeightAt (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b
            (314159265358979323846264338327950288419716939937510 / 10 ^ 50)‖ <
      1 / 10 ^ 42 := by
  have hw :=
    theta_gaussian_weight_rational_bound (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k (a : ℝ)
      (b : ℝ)
  have hr :=
    (Rat.cast_lt (K := ℝ)).mpr (Analysis.rational_gaussian_error_full_uniform t a b ht ha hab hk)
  have hs := rational_gaussian_weight_error_fast_cast t a b 200 k
  change (Analysis.rationalGaussianWeightErrorFast t a b 200 k : ℝ) < _ at hr
  rw [hs] at hr
  dsimp only [thetaGaussianWeightRationalError] at hr
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hw hr ⊢
  exact hw.trans_lt hr

/-- The calculated rational weight for a cell and a Gaussian index. -/
private def gridWeightTaylor (t a b : ℚ) (k : ℕ) : ℚ × ℚ :=
  Analysis.rationalGaussianWeight t a b
    (314159265358979323846264338327950288419716939937510 / 10 ^ 50) 200 k

/-- The calculated weights satisfy the uniform error and norm bounds. -/
private theorem grid_weights_bounded (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) :
    ∀ k < 8,
      ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b -
              (((gridWeightTaylor t a b k).1 : ℂ) +
                ((gridWeightTaylor t a b k).2 : ℂ) * Complex.I)‖ <
          1 / 10 ^ 42 ∧
        ‖((gridWeightTaylor t a b k).1 : ℂ) + ((gridWeightTaylor t a b k).2 : ℂ) * Complex.I‖ <
          2000000 := by
  let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
  let q : ℕ → ℚ × ℚ := fun k ↦ Analysis.rationalGaussianWeight t a b p 200 k
  intro k hk
  change
    ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b -
            (((q k).1 : ℂ) + ((q k).2 : ℂ) * Complex.I)‖ <
        1 / 10 ^ 42 ∧
      ‖((q k).1 : ℂ) + ((q k).2 : ℂ) * Complex.I‖ < 2000000
  have he :
    ((q k).1 : ℂ) + ((q k).2 : ℂ) * Complex.I =
      thetaGaussianWeightAt (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b p := by
    rw [← rational_gaussian_weight_cast t a b p 200 k]
    dsimp only [q]
    apply Complex.ext
    · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [he]
  constructor
  · have h := theta_gaussian_weight_pi_close t a b ht ha hab hk
    dsimp only [p]
    norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow]
    norm_num only at h
    exact h
  · apply theta_gaussian_weight_at_uniform_norm t a b p ht ha hab _ hk
    dsimp only [p]
    norm_num only

/-- Every admissible cell has a single pair of rational functions giving
all eight Gaussian weight approximations. Each has error below `10⁻⁴²` and
norm below two million. -/
theorem theta_gaussian_weights_bounded (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) :
    ∃ r im : ℕ → ℚ,
      ∀ k < 8,
        ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b -
                ((r k : ℂ) + (im k : ℂ) * Complex.I)‖ <
            1 / 10 ^ 42 ∧
          ‖(r k : ℂ) + (im k : ℂ) * Complex.I‖ < 2000000 := by
  exact
    ⟨fun k ↦ (gridWeightTaylor t a b k).1, fun k ↦ (gridWeightTaylor t a b k).2,
      grid_weights_bounded t a b ht ha hab⟩

/-- The rational Gaussian weight truncated after the 128th Taylor term. -/
private def gridWeightCompact (t a b : ℚ) (k : ℕ) : ℚ × ℚ :=
  Analysis.rationalGaussianWeight t a b
    (314159265358979323846264338327950288419716939937510 / 10 ^ 50) 127 k

/-- The shorter rational weight retains the π-substitution error and adds
the uniform bound for its discarded Taylor tail. -/
private theorem grid_weights_compact_error (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) {k : ℕ} (hk : k < 8) :
    ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b -
          (((gridWeightCompact t a b k).1 : ℂ) + ((gridWeightCompact t a b k).2 : ℂ) * Complex.I)‖ <
      1 / 10 ^ 42 + 1 / 10 ^ 49 := by
  let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
  have hp : |p| ≤ 4 := by
    dsimp only [p]; norm_num only
  have htq := Analysis.rational_gaussian_weight_tail_small t a b p ht ha hab hp hk
  have hc := (Rat.cast_lt (K := ℝ)).mpr htq
  let z : ℂ := ((gridWeightTaylor t a b k).1 : ℂ) + ((gridWeightTaylor t a b k).2 : ℂ) * Complex.I
  let w : ℂ := ((gridWeightCompact t a b k).1 : ℂ) + ((gridWeightCompact t a b k).2 : ℂ) * Complex.I
  have hn := Complex.norm_le_abs_re_add_abs_im (z - w)
  dsimp only [z, w, gridWeightTaylor, gridWeightCompact, p,
    Analysis.rationalComplexOneNorm] at hn hc
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, mul_one, zero_add, Prod.fst_sub, Prod.snd_sub, Rat.cast_add, Rat.cast_abs,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at hn hc
  have htail : ‖z - w‖ < 1 / 10 ^ 49 := lt_of_le_of_lt hn hc
  have hfull := (grid_weights_bounded t a b ht ha hab k hk).1
  change
    ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b - z‖ <
      1 / 10 ^ 42 at hfull
  have htri :=
    norm_sub_le_norm_sub_add_norm_sub
      (thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b) z w
  change ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b - w‖ < _
  linarith only [htri, hfull, htail]

/-- The rational Gaussian weight at the order selected by its Gaussian index. -/
private def gridWeightAdaptive (t a b : ℚ) (k : ℕ) : ℚ × ℚ :=
  Analysis.rationalGaussianWeight t a b
    (314159265358979323846264338327950288419716939937510 / 10 ^ 50)
    (Analysis.rationalGaussianOrder k) k

/-- The shorter rational weight retains the π-substitution error and adds
the uniform bound for its discarded Taylor tail. -/
private theorem grid_weights_adaptive_error (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) {k : ℕ} (hk : k < 8) :
    ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b -
          (((gridWeightAdaptive t a b k).1 : ℂ) +
            ((gridWeightAdaptive t a b k).2 : ℂ) * Complex.I)‖ <
      1 / 10 ^ 42 + 1 / 10 ^ 49 := by
  let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
  have hp : |p| ≤ 4 := by
    dsimp only [p]; norm_num only
  have htq := Analysis.rational_gaussian_adaptive_tail t a b p ht ha hab hp hk
  have hc := (Rat.cast_lt (K := ℝ)).mpr htq
  let z : ℂ := ((gridWeightTaylor t a b k).1 : ℂ) + ((gridWeightTaylor t a b k).2 : ℂ) * Complex.I
  let w : ℂ :=
    ((gridWeightAdaptive t a b k).1 : ℂ) + ((gridWeightAdaptive t a b k).2 : ℂ) * Complex.I
  have hn := Complex.norm_le_abs_re_add_abs_im (z - w)
  dsimp only [z, w, gridWeightTaylor, gridWeightAdaptive, p,
    Analysis.rationalComplexOneNorm] at hn hc
  simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero,
    sub_zero, add_zero, mul_one, zero_add, Prod.fst_sub, Prod.snd_sub, Rat.cast_add, Rat.cast_abs,
    Rat.cast_sub, Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] at hn hc
  have htail : ‖z - w‖ < 1 / 10 ^ 49 := lt_of_le_of_lt hn hc
  have hfull := (grid_weights_bounded t a b ht ha hab k hk).1
  change
    ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b - z‖ <
      1 / 10 ^ 42 at hfull
  have htri :=
    norm_sub_le_norm_sub_add_norm_sub
      (thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b) z w
  change ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b - w‖ < _
  linarith only [htri, hfull, htail]

/-- The adaptive rational weight with its finite triangular sum transposed. -/
private def gridWeightFast (t a b : ℚ) (k : ℕ) : ℚ × ℚ :=
  Analysis.rationalGaussianWeightFast t a b
    (314159265358979323846264338327950288419716939937510 / 10 ^ 50)
    (Analysis.rationalGaussianOrder k) k

/-- The transposed weight is exactly the previously certified adaptive weight. -/
private theorem grid_weight_fast_eq (t a b : ℚ) (k : ℕ) :
    gridWeightFast t a b k = gridWeightAdaptive t a b k := by
  exact Analysis.rational_gaussian_weight_fast_eq t a b _ _ k

/-- Each exact 200th-order Gaussian weight in the eight-term range has
norm below `2000001`. The rationalized weight is below two million, and the
uniform π-substitution error is below `10⁻⁴²`. -/
theorem theta_gaussian_weight_uniform_norm (t a b : ℚ) (ht : |t| ≤ 100) (ha : 1 ≤ a)
    (hab : b - a = 1 / 16) {k : ℕ} (hk : k < 8) :
    ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b‖ < 2000001 := by
  let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
  have hp : |p| ≤ 4 := by
    dsimp only [p]
    norm_num only
  have hnorm := theta_gaussian_weight_at_uniform_norm t a b p ht ha hab hp hk
  have hw :=
    theta_gaussian_weight_rational_bound (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k (a : ℝ)
      (b : ℝ)
  have hr :=
    (Rat.cast_lt (K := ℝ)).mpr (Analysis.rational_gaussian_error_full_uniform t a b ht ha hab hk)
  have hs := rational_gaussian_weight_error_fast_cast t a b 200 k
  change (Analysis.rationalGaussianWeightErrorFast t a b 200 k : ℝ) < _ at hr
  rw [hs] at hr
  dsimp only [thetaGaussianWeightRationalError] at hr
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hw hr
  have hdiff := hw.trans_lt hr
  have hn :=
    norm_sub_norm_le (thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b)
      (thetaGaussianWeightAt (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b p)
  dsimp only [p] at hn hnorm
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hn hnorm
  linarith only [hn, hnorm, hdiff]

/-- For rational height and cell endpoints, each exact Gaussian weight has
a rational complex approximation obtained by replacing π with any rational
parameter. Its error is bounded by the explicit finite perturbation sum. -/
theorem theta_gaussian_weight_rational_error (t a b p : ℚ) (n k : ℕ) :
    ∃ r im : ℚ,
      ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k a b -
            ((r : ℂ) + (im : ℂ) * Complex.I)‖ ≤
        2 *
          ∑ l ∈ Finset.range (n + 1),
            ‖((((l.factorial : ℝ)⁻¹ * (((b : ℝ) - a) ^ (l + 1) / (l + 1))) : ℝ) : ℂ)‖ *
              thetaGaussianPolyError (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) l k a p := by
  obtain ⟨r, im, hr⟩ := theta_gaussian_weight_at_rational t a b p n k
  refine ⟨r, im, ?_⟩
  rw [← hr]
  exact theta_gaussian_weight_error _ _ _ _ _ _

/-- The finite cell coefficient sum can be transposed into one Gaussian
value per index times its accumulated polynomial weight. This identity is
valid for arbitrary cell endpoints and Taylor order. -/
theorem theta_cell_gaussian_sum (s : ℂ) (N n : ℕ) (a b : ℝ) :
    (∑ l ∈ Finset.range (n + 1),
        (((l.factorial : ℝ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))) : ℝ) •
          thetaMellinPolyCoeff s N l a) =
      ∑ k ∈ Finset.range N,
        thetaGaussianWeight s n k a b *
          Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * a) := by
  simp only [theta_poly_gaussian, thetaGaussianWeight, Complex.real_smul, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro l hl
  ring

/-- A two-sided logarithm enclosure gives a phase enclosure around the
midpoint. The factor `|t| / 2` makes this valid for either sign of the
height and can be used uniformly over every rational grid node. -/
theorem log_interval_phase_error {a t lo hi : ℝ} (hlo : lo ≤ Real.log a) (hhi : Real.log a ≤ hi) :
    |Real.log a * (t / 2) - ((lo + hi) / 2) * (t / 2)| ≤ ((hi - lo) / 2) * (|t| / 2) := by
  have hm : |Real.log a - (lo + hi) / 2| ≤ (hi - lo) / 2 := by
    rw [abs_le]
    constructor <;> linarith only [hlo, hhi]
  have heq :
    Real.log a * (t / 2) - ((lo + hi) / 2) * (t / 2) = (Real.log a - (lo + hi) / 2) * (t / 2) := by
    ring
  rw [heq, abs_mul, abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
  exact mul_le_mul_of_nonneg_right hm (div_nonneg (abs_nonneg t) (by norm_num only))

/-- The first noninitial sixteenth-grid node has this certified logarithm
interval. The rational Taylor check is performed by the kernel and the
calculation module remains a private import. -/
theorem grid_one_log_interval :
    (606246218164 / 10000000000000 : ℝ) ≤ Real.log (17 / 16) ∧
      Real.log (17 / 16) ≤ (606246218165 / 10000000000000 : ℝ) := by
  have hc :
    Analysis.preciseLogCheck (17 / 16) 1 64 (606246218164 / 10000000000000)
        (606246218165 / 10000000000000) =
      true := by
    decide +kernel
  have h := Analysis.preciseLogCheck_sound hc
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h
  constructor <;> linarith only [h.1, h.2]

/-- At the first noninitial grid node, the logarithmic phase is within a
specified rational multiple of `|t|` of its rational-center expression.
The statement is uniform in the height and applies to both reflected signs. -/
theorem grid_one_phase_interval (t : ℝ) :
    |Real.log (17 / 16) * (t / 2) - (1212492436329 / 20000000000000 : ℝ) * (t / 2)| ≤
      |t| / 40000000000000 := by
  have h := log_interval_phase_error (t := t) grid_one_log_interval.1 grid_one_log_interval.2
  convert h using 1 <;> ring_nf

/-- The rational Taylor pair approximates the critical logarithmic phase
with the input interval and Taylor remainder included in the error. -/
private theorem critical_phase_taylor_error {a t : ℝ} (v : ℚ) (m : ℕ) {ε : ℝ}
    (hv : |(v : ℝ)| / (m + 1 : ℕ) ≤ 1 / 2) (hε : |Real.log a * (t / 2) - (v : ℝ)| ≤ ε) :
    ‖Complex.exp (Complex.I * (Real.log a * (t / 2))) -
          (((Analysis.rationalPhaseTaylor v m).1 : ℂ) +
            ((Analysis.rationalPhaseTaylor v m).2 : ℂ) * Complex.I)‖ ≤
      ε + |(v : ℝ)| ^ m / (m.factorial : ℝ) * 2 := by
  let q := Analysis.rationalPhaseTaylor v m
  change
    ‖Complex.exp (Complex.I * (Real.log a * (t / 2))) - ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)‖ ≤ _
  have h := Analysis.norm_phaseTaylor_interval_error v m hv hε
  convert h using 1
  rw [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  apply congrArg (fun z : ℂ ↦ ‖Complex.exp (Complex.I * (Real.log a * (t / 2))) - z‖)
  dsimp only [q]
  apply Complex.ext
  · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
  · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]

/-- A rational center and a Taylor length give rational real and imaginary
parts approximating the critical logarithmic phase. The error combines the
input phase interval with the exponential Taylor remainder; the executable
construction is kept behind the private calculation import. -/
theorem critical_phase_rational_exists {a t : ℝ} (v : ℚ) (m : ℕ) {ε : ℝ}
    (hv : |(v : ℝ)| / (m + 1 : ℕ) ≤ 1 / 2) (hε : |Real.log a * (t / 2) - (v : ℝ)| ≤ ε) :
    ∃ r i : ℚ,
      ‖Complex.exp (Complex.I * (Real.log a * (t / 2))) - ((r : ℂ) + (i : ℂ) * Complex.I)‖ ≤
        ε + |(v : ℝ)| ^ m / (m.factorial : ℝ) * 2 := by
  exact
    ⟨(Analysis.rationalPhaseTaylor v m).1, (Analysis.rationalPhaseTaylor v m).2,
      critical_phase_taylor_error v m hv hε⟩

/-- The rational Taylor pair computed from the grid logarithm midpoint. -/
private def gridPhaseTaylor (i : ℕ) (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalPhaseTaylor (gridLogMidpoint i * t / 2) 1024

set_option maxRecDepth 16384 in
/-- The computed phase pair has the uniform error bound on the complete grid. -/
private theorem grid_phase_taylor_error (i : ℕ) (hi : i ≤ 944) (t : ℚ) (ht : |(t : ℝ)| ≤ 100) :
    ‖Complex.exp (Complex.I * ((Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) : ℝ) : ℂ)) -
          (((gridPhaseTaylor i t).1 : ℂ) + ((gridPhaseTaylor i t).2 : ℂ) * Complex.I)‖ ≤
      3 / 10 ^ 48 := by
  let v : ℚ := gridLogMidpoint i * t / 2
  have hv :
    |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (v : ℝ)| ≤ |(t : ℝ)| / (2 * 10 ^ 50) :=
    grid_phase_midpoint_fifty i hi t
  have he : |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (v : ℝ)| ≤ 1 / 10 ^ 48 := by
    nlinarith only [hv, ht]
  have hl := critical_grid_log_le_five i hi
  have hp : |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2)| ≤ 250 := by
    rw [abs_mul, abs_of_nonneg hl.1, abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
    have h := mul_le_mul hl.2 ht (abs_nonneg (t : ℝ)) (by norm_num only : (0 : ℝ) ≤ 5)
    nlinarith only [h]
  have hvb : |(v : ℝ)| ≤ 251 := by
    have h :=
      abs_add_le ((v : ℝ) - Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2))
        (Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2))
    rw [sub_add_cancel, abs_sub_comm] at h
    linarith only [h, he, hp]
  have hm : |(v : ℝ)| / (1024 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only [Nat.cast_ofNat, Nat.reduceAdd]
    linarith only [hvb]
  have h := critical_phase_taylor_error (a := criticalQuadratureGrid i) (t := t) v 1024 hm he
  have hpow : |(v : ℝ)| ^ 1024 ≤ (251 : ℝ) ^ 1024 := pow_le_pow_left₀ (abs_nonneg _) hvb 1024
  have hf : (0 : ℝ) < Nat.factorial 1024 := by exact_mod_cast Nat.factorial_pos 1024
  have hn : (251 : ℝ) ^ 1024 / (Nat.factorial 1024 : ℝ) * 2 ≤ 1 / 10 ^ 48 := by
    norm_num only [Nat.factorial, pow_succ]
  have hr : |(v : ℝ)| ^ 1024 / (Nat.factorial 1024 : ℝ) * 2 ≤ 1 / 10 ^ 48 :=
    (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hpow hf.le) (by norm_num only)).trans hn
  change
    ‖Complex.exp (Complex.I * ((Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) : ℝ) : ℂ)) -
          (((Analysis.rationalPhaseTaylor v 1024).1 : ℂ) +
            ((Analysis.rationalPhaseTaylor v 1024).2 : ℂ) * Complex.I)‖ ≤
      _
  simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
  linarith only [h, hr]

/-- Every fixed-grid node and rational height with `|t| ≤ 100` admit a
rational complex phase approximation within `3 * 10⁻⁴⁸`. A common
1024-term Taylor bound covers all 945 nodes and all such heights. -/
theorem critical_grid_phase_complex (i : ℕ) (hi : i ≤ 944) (t : ℚ) (ht : |(t : ℝ)| ≤ 100) :
    ∃ r im : ℚ,
      ‖Complex.exp (Complex.I * ((Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) : ℝ) : ℂ)) -
            ((r : ℂ) + (im : ℂ) * Complex.I)‖ ≤
        3 / 10 ^ 48 := by
  exact ⟨(gridPhaseTaylor i t).1, (gridPhaseTaylor i t).2, grid_phase_taylor_error i hi t ht⟩

/-- The reduced phase polynomial followed by eight rounded squarings.
The fixed grid bounds denominator growth during phase reconstruction. -/
private def gridPhaseScaled (i : ℕ) (t : ℚ) : ℚ × ℚ :=
  Analysis.rationalScaledPhase (10 ^ 60) (gridLogRounded i * t / 2) 64 8

/-- The range-reduced phase calculation meets the same uniform error bound
as the original phase polynomial on every grid node and admissible height. -/
private theorem grid_phase_scaled_error (i : ℕ) (hi : i ≤ 944) (t : ℚ) (ht : |(t : ℝ)| ≤ 100) :
    ‖Complex.exp (Complex.I * ((Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) : ℝ) : ℂ)) -
          (((gridPhaseScaled i t).1 : ℂ) + ((gridPhaseScaled i t).2 : ℂ) * Complex.I)‖ ≤
      3 / 10 ^ 48 := by
  let v : ℚ := gridLogRounded i * t / 2
  have hv := grid_phase_rounded_fifty i hi t
  change |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (v : ℝ)| ≤ _ at hv
  have he : |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) - (v : ℝ)| ≤ 1 / 10 ^ 48 := by
    nlinarith only [hv, ht]
  have hl := critical_grid_log_le_five i hi
  have hp : |Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2)| ≤ 250 := by
    rw [abs_mul, abs_of_nonneg hl.1, abs_div, abs_of_nonneg (by norm_num only : (0 : ℝ) ≤ 2)]
    have h := mul_le_mul hl.2 ht (abs_nonneg (t : ℝ)) (by norm_num only : (0 : ℝ) ≤ 5)
    nlinarith only [h]
  have hvb : |(v : ℝ)| ≤ 251 := by
    have h :=
      abs_add_le ((v : ℝ) - Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2))
        (Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2))
    rw [sub_add_cancel, abs_sub_comm] at h
    linarith only [h, he, hp]
  have hq : |((v / (2 : ℚ) ^ 8 : ℚ) : ℝ)| ≤ 1 := by
    norm_num only [Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat, abs_div, abs_of_pos]
    linarith only [hvb]
  have hpow := pow_le_pow_left₀ (abs_nonneg ((v / (2 : ℚ) ^ 8 : ℚ) : ℝ)) hq 64
  have hc :=
    Analysis.norm_scaled_phase_error (by norm_num only : 0 < 10 ^ 60) v 64 8
      (by
        norm_num only; linarith only [hq])
      (by
        norm_num only [Nat.factorial] at hpow ⊢; nlinarith only [hpow])
      (by
        intro j hj
        interval_cases j <;>
          norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
            Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast])
  norm_num only [Analysis.roundedSquareBudget, Rat.cast_div, Rat.cast_sub, Rat.cast_mul,
    Rat.cast_pow, Rat.cast_ofNat, Rat.cast_natCast] at hc
  have hphase :=
    Analysis.norm_phase_exp_sub_le (Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2)) (v : ℝ)
  rw [Complex.ofReal_ratCast] at hphase
  change
    ‖Complex.exp (Complex.I * (v : ℂ)) - Analysis.rationalComplexCast (gridPhaseScaled i t)‖ ≤
      _ at hc
  have htri :=
    norm_sub_le_norm_sub_add_norm_sub
      (Complex.exp (Complex.I * ((Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) : ℝ) : ℂ)))
      (Complex.exp (Complex.I * (v : ℂ))) (Analysis.rationalComplexCast (gridPhaseScaled i t))
  have heq :
    Analysis.rationalComplexCast (gridPhaseScaled i t) =
      (((gridPhaseScaled i t).1 : ℂ) + ((gridPhaseScaled i t).2 : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [← heq]
  change
    ‖Complex.exp (Complex.I * ((Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) : ℝ) : ℂ)) -
          Analysis.rationalComplexCast (gridPhaseScaled i t)‖ ≤
      _
  nlinarith only [htri, hphase, he, hc]

/-- The rational amplitude and phase approximations multiplied componentwise. -/
private def gridPowerTaylor (i : ℕ) (t : ℚ) : ℚ × ℚ :=
  let c := gridLogRounded i
  let q : ℚ := -(3 / 4) * c
  let a : ℚ := ∑ k ∈ Finset.range 64, q ^ k / (k.factorial : ℚ)
  let z := Analysis.rationalScaledPhase (10 ^ 60) (c * t / 2) 64 8
  (a * z.1, a * z.2)

/-- The importable rational grid power is definitionally equal to the
approximation used in the analytic cell error proof. -/
private theorem grid_power_certificate_eq (i : ℕ) (t : ℚ) :
    gridPowerTaylor i t = certificateGridPower i t := by rfl

/-- The computed rational pair approximates the complex grid power uniformly. -/
private theorem grid_power_taylor_error (i : ℕ) (hi : i ≤ 944) (t : ℚ) (ht : |(t : ℝ)| ≤ 100) :
    ‖(criticalQuadratureGrid i : ℂ) ^ (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1) -
          (((gridPowerTaylor i t).1 : ℂ) + ((gridPowerTaylor i t).2 : ℂ) * Complex.I)‖ ≤
      4 / 10 ^ 48 := by
  let a := gridAmplitudeCompact i
  have ha :
    |Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ))) - (a : ℝ)| ≤ 3 / 10 ^ 50 :=
    grid_amplitude_compact_error i hi
  let r := (gridPhaseScaled i t).1
  let im := (gridPhaseScaled i t).2
  have hp :
    ‖Complex.exp (Complex.I * ((Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) : ℝ) : ℂ)) -
          ((r : ℂ) + (im : ℂ) * Complex.I)‖ ≤
      3 / 10 ^ 48 :=
    grid_phase_scaled_error i hi t ht
  let A : ℝ := Real.exp (Real.log (criticalQuadratureGrid i) * (-(3 / 4 : ℝ)))
  let P : ℂ :=
    Complex.exp (Complex.I * ((Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2) : ℝ) : ℂ))
  let Q : ℂ := (r : ℂ) + (im : ℂ) * Complex.I
  have hl := critical_grid_log_le_five i hi
  have hA0 : 0 ≤ A := (Real.exp_pos _).le
  have hA1 : A ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    linarith only [hl.1]
  have hP : ‖P‖ = 1 := Complex.norm_exp_I_mul_ofReal _
  have hQ : ‖Q‖ ≤ 1 + 3 / 10 ^ 48 := by
    have h := norm_sub_norm_le Q P
    rw [hP, norm_sub_rev] at h
    linarith only [h, hp]
  have ha' : ‖(A : ℂ) - (a : ℂ)‖ ≤ 3 / 10 ^ 50 := by
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    exact ha
  have hbound := mul_le_mul ha' hQ (norm_nonneg Q) (by norm_num only : (0 : ℝ) ≤ 3 / 10 ^ 50)
  have hphase := mul_le_mul_of_nonneg_left hp hA0
  have hPexp :
    (Real.cos (Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2)) : ℂ) +
        (Real.sin (Real.log (criticalQuadratureGrid i) * ((t : ℝ) / 2)) : ℂ) * Complex.I =
      P := by
    dsimp only [P]
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hg : 0 < criticalQuadratureGrid i := by
    dsimp only [criticalQuadratureGrid]
    have hi0 : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    exact add_pos_of_pos_of_nonneg (by norm_num only) (div_nonneg hi0 (by norm_num only))
  change
    ‖(criticalQuadratureGrid i : ℂ) ^ (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1) -
          (((a * r : ℚ) : ℂ) + ((a * im : ℚ) : ℂ) * Complex.I)‖ ≤
      _
  have hc := critical_cpow_exp_phase hg (t : ℝ)
  rw [Complex.ofReal_ratCast] at hc
  rw [hc, hPexp]
  have heq : ((a * r : ℚ) : ℂ) + ((a * im : ℚ) : ℂ) * Complex.I = (a : ℂ) * Q := by
    simp only [Rat.cast_mul]
    dsimp only [Q]
    ring
  rw [heq]
  change ‖(A : ℂ) * P - (a : ℂ) * Q‖ ≤ _
  have heq' : (A : ℂ) * P - (a : ℂ) * Q = (A : ℂ) * (P - Q) + ((A : ℂ) - (a : ℂ)) * Q := by ring
  rw [heq']
  have htri := norm_add_le ((A : ℂ) * (P - Q)) (((A : ℂ) - (a : ℂ)) * Q)
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hA0] at htri
  nlinarith only [htri, hphase, hbound, hA1, hp, norm_nonneg (P - Q)]

/-- On the fixed grid and for rational `|t| ≤ 100`, the common complex power
factor has a rational complex approximation within `4 * 10⁻⁴⁸`. The proof
combines the separately certified amplitude and phase errors. -/
theorem critical_grid_power_rational (i : ℕ) (hi : i ≤ 944) (t : ℚ) (ht : |(t : ℝ)| ≤ 100) :
    ∃ r im : ℚ,
      ‖(criticalQuadratureGrid i : ℂ) ^ (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1) -
            ((r : ℂ) + (im : ℂ) * Complex.I)‖ ≤
        4 / 10 ^ 48 := by
  exact ⟨(gridPowerTaylor i t).1, (gridPowerTaylor i t).2, grid_power_taylor_error i hi t ht⟩

/-- At the first noninitial node and height `1413/100`, a 32-term rational
phase polynomial gives a complex approximation with error at most `10⁻¹²`.
The logarithm interval and Taylor remainder are checked without a table. -/
theorem grid_one_phase_1413 :
    ∃ r i : ℚ,
      ‖Complex.exp (Complex.I * (Real.log (17 / 16) * (1413 / 200))) -
            ((r : ℂ) + (i : ℂ) * Complex.I)‖ ≤
        1 / 10 ^ 12 := by
  have hp := grid_one_phase_interval (1413 / 100)
  have he :
    |Real.log (17 / 16) * (1413 / 200) - (1713251812532877 / 4000000000000000 : ℝ)| ≤
      (1413 / 4000000000000000 : ℝ) := by
    convert hp using 1 <;> norm_num only
  have hv : |((1713251812532877 / 4000000000000000 : ℚ) : ℝ)| / (32 + 1 : ℕ) ≤ 1 / 2 := by
    norm_num only
  have he' :
    |Real.log (17 / 16) * ((1413 / 100 : ℝ) / 2) -
          ((1713251812532877 / 4000000000000000 : ℚ) : ℝ)| ≤
      (1413 / 4000000000000000 : ℝ) := by
    norm_num only [Rat.cast_div, Rat.cast_ofNat]
    convert he using 1
  obtain ⟨r, i, hi⟩ :=
    critical_phase_rational_exists (a := 17 / 16) (t := 1413 / 100)
      (1713251812532877 / 4000000000000000) 32 hv he'
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hi
  refine ⟨r, i, hi.trans ?_⟩
  norm_num only

/-- A rational Taylor approximation to the logarithmic phase bounds the
error in one critical-line quadrature cell. The coefficient norm cap and
phase interval are supplied explicitly; the proof uses the exact cell
factorization and the certified complex exponential remainder. -/
theorem critical_cell_phase_error (t : ℝ) (N n : ℕ) {a b : ℝ} (ha : 0 < a) (q : ℂ) {D K : ℝ}
    (hphase : ‖Complex.exp (Complex.I * (Real.log a * (t / 2))) - q‖ ≤ D)
    (hK :
      ‖∑ k ∈ Finset.range (n + 1),
            (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
              thetaMellinPolyCoeff (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N k a‖ ≤
        K) :
    ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N n a b -
          (Real.exp (Real.log a * (-(3 / 4 : ℝ))) : ℂ) * q *
            (∑ k ∈ Finset.range (n + 1),
              (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
                thetaMellinPolyCoeff (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N k a)‖ ≤
      Real.exp (Real.log a * (-(3 / 4 : ℝ))) * K * D := by
  let θ : ℝ := Real.log a * (t / 2)
  let P : ℂ :=
    ∑ k ∈ Finset.range (n + 1),
      (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
        thetaMellinPolyCoeff (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N k a
  let A : ℝ := Real.exp (Real.log a * (-(3 / 4 : ℝ)))
  have heq : (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I = Complex.exp (Complex.I * θ) := by
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [critical_explicit_cell_phase t N n ha, heq]
  change ‖((A : ℂ) * Complex.exp (Complex.I * θ)) * P - (A : ℂ) * q * P‖ ≤ _
  have hid :
    ((A : ℂ) * Complex.exp (Complex.I * θ)) * P - (A : ℂ) * q * P =
      (A : ℂ) * (Complex.exp (Complex.I * θ) - q) * P := by
    ring
  rw [hid, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hD : 0 ≤ D := (norm_nonneg _).trans hphase
  have h := mul_le_mul hphase hK (norm_nonneg _) hD
  have hm := mul_le_mul_of_nonneg_left h (Real.exp_pos (Real.log a * (-(3 / 4 : ℝ)))).le
  dsimp only [θ, P]
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat, mul_assoc, mul_comm,
    mul_left_comm] using hm

/-- A rational phase center and a finite coefficient norm cap produce
rational phase components approximating the whole critical-line cell.
The bound includes both the phase interval and Taylor truncation errors. -/
theorem critical_cell_rational_phase (t : ℝ) (N n : ℕ) {a b : ℝ} (ha : 0 < a) (v : ℚ) (m : ℕ)
    {ε K : ℝ} (hv : |(v : ℝ)| / (m + 1 : ℕ) ≤ 1 / 2) (hε : |Real.log a * (t / 2) - (v : ℝ)| ≤ ε)
    (hK :
      ‖∑ k ∈ Finset.range (n + 1),
            (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
              thetaMellinPolyCoeff (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N k a‖ ≤
        K) :
    ∃ r i : ℚ,
      ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N n a b -
            (Real.exp (Real.log a * (-(3 / 4 : ℝ))) : ℂ) * ((r : ℂ) + (i : ℂ) * Complex.I) *
              (∑ k ∈ Finset.range (n + 1),
                (((k.factorial : ℝ)⁻¹ * ((b - a) ^ (k + 1) / (k + 1))) : ℝ) •
                  thetaMellinPolyCoeff (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N k a)‖ ≤
        Real.exp (Real.log a * (-(3 / 4 : ℝ))) * K *
          (ε + |(v : ℝ)| ^ m / (m.factorial : ℝ) * 2) := by
  obtain ⟨r, i, hq⟩ := critical_phase_rational_exists v m hv hε
  exact ⟨r, i, critical_cell_phase_error t N n ha ((r : ℂ) + (i : ℂ) * Complex.I) hq hK⟩

/-- The error in a finite sum of complex approximations is bounded by the
sum of their individual norm errors. This supports arbitrary cell partitions
and does not require indexing a list. -/
theorem finite_sum_approx_error {ι : Type*} (s : Finset ι) (f q : ι → ℂ) (E : ι → ℝ)
    (h : ∀ j ∈ s, ‖f j - q j‖ ≤ E j) : ‖(∑ j ∈ s, f j) - ∑ j ∈ s, q j‖ ≤ ∑ j ∈ s, E j := by
  rw [← Finset.sum_sub_distrib]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum h)

/-- Uniform bounds on coefficient errors and multiplier norms control the
error in a finite sum of products. The cardinality accounts for all terms
without requiring any indexed list of approximations. -/
theorem finite_weighted_sum_error {ι : Type*} (S : Finset ι) (w q z : ι → ℂ) {E M : ℝ}
    (hw : ∀ i ∈ S, ‖w i - q i‖ ≤ E) (hz : ∀ i ∈ S, ‖z i‖ ≤ M) :
    ‖(∑ i ∈ S, w i * z i) - ∑ i ∈ S, q i * z i‖ ≤ (S.card : ℝ) * (E * M) := by
  have hterm : ∀ i ∈ S, ‖w i * z i - q i * z i‖ ≤ E * M := by
    intro i hi
    rw [← sub_mul, norm_mul]
    exact mul_le_mul (hw i hi) (hz i hi) (norm_nonneg _) ((norm_nonneg _).trans (hw i hi))
  have h := finite_sum_approx_error S (fun i ↦ w i * z i) (fun i ↦ q i * z i) (fun _ ↦ E * M) hterm
  simpa only [Finset.sum_const, nsmul_eq_mul] using h

/-- Uniform norm caps on both factors bound a finite sum of their products. -/
theorem finite_product_sum_norm {ι : Type*} (S : Finset ι) (w z : ι → ℂ) {K M : ℝ}
    (hw : ∀ i ∈ S, ‖w i‖ ≤ K) (hz : ∀ i ∈ S, ‖z i‖ ≤ M) :
    ‖∑ i ∈ S, w i * z i‖ ≤ (S.card : ℝ) * (K * M) := by
  have hterm : ∀ i ∈ S, ‖w i * z i‖ ≤ K * M := by
    intro i hi
    rw [norm_mul]
    exact mul_le_mul (hw i hi) (hz i hi) (norm_nonneg _) ((norm_nonneg _).trans (hw i hi))
  have h := (norm_sum_le S (fun i ↦ w i * z i)).trans (Finset.sum_le_sum hterm)
  simpa only [Finset.sum_const, nsmul_eq_mul] using h

/-- Rational Gaussian enclosures propagate through the complete finite cell
coefficient sum. Each error is weighted by the norm of its accumulated
polynomial coefficient, with no repeated error for derivative terms. -/
theorem theta_cell_gaussian_error (s : ℂ) (N n : ℕ) (a b : ℝ) (r : ℕ → ℚ) (E : ℕ → ℝ)
    (hE : ∀ k < N, |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * a) - (r k : ℝ)| ≤ E k) :
    ‖(∑ l ∈ Finset.range (n + 1),
            (((l.factorial : ℝ)⁻¹ * ((b - a) ^ (l + 1) / (l + 1))) : ℝ) •
              thetaMellinPolyCoeff s N l a) -
          ∑ k ∈ Finset.range N, thetaGaussianWeight s n k a b * (r k : ℂ)‖ ≤
      ∑ k ∈ Finset.range N, ‖thetaGaussianWeight s n k a b‖ * E k := by
  rw [theta_cell_gaussian_sum]
  apply finite_sum_approx_error
  intro k hk
  have hg : ‖Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * a) - (r k : ℂ)‖ ≤ E k := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, ← Complex.ofReal_ratCast, ← Complex.ofReal_sub,
      Complex.norm_real, Real.norm_eq_abs]
    exact hE k (Finset.mem_range.mp hk)
  rw [← mul_sub, norm_mul]
  exact mul_le_mul_of_nonneg_left hg (norm_nonneg _)

/-- At every fixed-grid node, all Gaussian values in a cell can be replaced
simultaneously by rational approximations. Their total coefficient error is
bounded by the sum of the polynomial-weight norms times `3 * 10⁻¹²`. -/
theorem critical_grid_gaussian_cell (s : ℂ) (N n i : ℕ) (b : ℝ) :
    ∃ r : ℕ → ℚ,
      ‖(∑ l ∈ Finset.range (n + 1),
              (((l.factorial : ℝ)⁻¹ * ((b - criticalQuadratureGrid i) ^ (l + 1) / (l + 1))) : ℝ) •
                thetaMellinPolyCoeff s N l (criticalQuadratureGrid i)) -
            ∑ k ∈ Finset.range N,
              thetaGaussianWeight s n k (criticalQuadratureGrid i) b * (r k : ℂ)‖ ≤
        (∑ k ∈ Finset.range N, ‖thetaGaussianWeight s n k (criticalQuadratureGrid i) b‖) *
          (3 / 10 ^ 12) := by
  classical
  choose r hr using critical_grid_gaussian_rational i
  refine ⟨r, ?_⟩
  have h :=
    theta_cell_gaussian_error s N n (criticalQuadratureGrid i) b r (fun _ ↦ 3 / 10 ^ 12)
      (fun k _ ↦ hr k)
  simpa only [Finset.sum_mul] using h

/-- At every fixed-grid node, all Gaussian values in a cell can be replaced
simultaneously by rational approximations. Their total coefficient error is
bounded by the sum of the polynomial-weight norms times `3 * 10⁻⁴⁷`. -/
theorem critical_grid_gaussian_cell_fortyseven (s : ℂ) (N n i : ℕ) (b : ℝ) :
    ∃ r : ℕ → ℚ,
      ‖(∑ l ∈ Finset.range (n + 1),
              (((l.factorial : ℝ)⁻¹ * ((b - criticalQuadratureGrid i) ^ (l + 1) / (l + 1))) : ℝ) •
                thetaMellinPolyCoeff s N l (criticalQuadratureGrid i)) -
            ∑ k ∈ Finset.range N,
              thetaGaussianWeight s n k (criticalQuadratureGrid i) b * (r k : ℂ)‖ ≤
        (∑ k ∈ Finset.range N, ‖thetaGaussianWeight s n k (criticalQuadratureGrid i) b‖) *
          (3 / 10 ^ 47) := by
  classical
  choose r hr using critical_grid_gaussian_fortyseven i
  refine ⟨r, ?_⟩
  have h :=
    theta_cell_gaussian_error s N n (criticalQuadratureGrid i) b r (fun _ ↦ 3 / 10 ^ 47)
      (fun k _ ↦ hr k)
  simpa only [Finset.sum_mul] using h

/-- On nodes at least one, the norm of the critical-line complex-power
factor is at most one. Its oscillatory factor has norm one and its real
exponential amplitude is at most one. -/
theorem critical_power_norm_le_one {a t : ℝ} (ha : 1 ≤ a) :
    ‖(a : ℂ) ^ ((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2 - 1)‖ ≤ 1 := by
  have ha0 : 0 < a := lt_of_lt_of_le (by norm_num only) ha
  have hl : 0 ≤ Real.log a := Real.log_nonneg ha
  have he :
    (Real.cos (Real.log a * (t / 2)) : ℂ) + (Real.sin (Real.log a * (t / 2)) : ℂ) * Complex.I =
      Complex.exp (Complex.I * ((Real.log a * (t / 2) : ℝ) : ℂ)) := by
    rw [mul_comm Complex.I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  rw [critical_cpow_exp_phase ha0, he, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), Complex.norm_exp_I_mul_ofReal, mul_one]
  apply Real.exp_le_one_iff.mpr
  linarith only [hl]

/-- On every fixed-grid cell, rational Gaussian approximations give a bound
for the complete complex Taylor cell itself. The common critical-line power
factor has norm at most one, so it does not enlarge the accumulated error. -/
theorem critical_grid_cell_gaussian (t : ℝ) (N n i : ℕ) (b : ℝ) :
    ∃ r : ℕ → ℚ,
      ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N n
              (criticalQuadratureGrid i) b -
            (criticalQuadratureGrid i : ℂ) ^ (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1) *
              ∑ k ∈ Finset.range N,
                thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k
                    (criticalQuadratureGrid i) b *
                  (r k : ℂ)‖ ≤
        (∑ k ∈ Finset.range N,
            ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k
                (criticalQuadratureGrid i) b‖) *
          (3 / 10 ^ 12) := by
  have ha : 1 ≤ criticalQuadratureGrid i := by
    dsimp only [criticalQuadratureGrid]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith only [div_nonneg hi (by norm_num only : (0 : ℝ) ≤ 16)]
  obtain ⟨r, hr⟩ := critical_grid_gaussian_cell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N n i b
  refine ⟨r, ?_⟩
  rw [theta_mellin_explicit_cell_factor _ _ _ (lt_of_lt_of_le (by norm_num only) ha), ← mul_sub,
    norm_mul]
  have hp := critical_power_norm_le_one (t := t) ha
  have hn :=
    norm_nonneg
      ((∑ l ∈ Finset.range (n + 1),
          (((l.factorial : ℝ)⁻¹ * ((b - criticalQuadratureGrid i) ^ (l + 1) / (l + 1))) : ℝ) •
            thetaMellinPolyCoeff (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N l
              (criticalQuadratureGrid i)) -
        ∑ k ∈ Finset.range N,
          thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k
              (criticalQuadratureGrid i) b *
            (r k : ℂ))
  have hm := mul_le_mul_of_nonneg_right hp hn
  linarith only [hm, hr]

/-- On every fixed-grid cell, rational Gaussian approximations give a bound
for the complete complex Taylor cell itself. The common critical-line power
factor has norm at most one, so it does not enlarge the accumulated error. -/
theorem critical_grid_cell_gaussian_fortyseven (t : ℝ) (N n i : ℕ) (b : ℝ) :
    ∃ r : ℕ → ℚ,
      ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N n
              (criticalQuadratureGrid i) b -
            (criticalQuadratureGrid i : ℂ) ^ (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1) *
              ∑ k ∈ Finset.range N,
                thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k
                    (criticalQuadratureGrid i) b *
                  (r k : ℂ)‖ ≤
        (∑ k ∈ Finset.range N,
            ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k
                (criticalQuadratureGrid i) b‖) *
          (3 / 10 ^ 47) := by
  have ha : 1 ≤ criticalQuadratureGrid i := by
    dsimp only [criticalQuadratureGrid]
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg i
    linarith only [div_nonneg hi (by norm_num only : (0 : ℝ) ≤ 16)]
  obtain ⟨r, hr⟩ :=
    critical_grid_gaussian_cell_fortyseven (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N n i b
  refine ⟨r, ?_⟩
  rw [theta_mellin_explicit_cell_factor _ _ _ (lt_of_lt_of_le (by norm_num only) ha), ← mul_sub,
    norm_mul]
  have hp := critical_power_norm_le_one (t := t) ha
  have hn :=
    norm_nonneg
      ((∑ l ∈ Finset.range (n + 1),
          (((l.factorial : ℝ)⁻¹ * ((b - criticalQuadratureGrid i) ^ (l + 1) / (l + 1))) : ℝ) •
            thetaMellinPolyCoeff (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N l
              (criticalQuadratureGrid i)) -
        ∑ k ∈ Finset.range N,
          thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) n k
              (criticalQuadratureGrid i) b *
            (r k : ℂ))
  have hm := mul_le_mul_of_nonneg_right hp hn
  linarith only [hm, hr]

/-- In every one of the 944 fixed-grid cells and for every rational height
of magnitude at most 100, rationally approximating all eight Gaussian
factors changes the 200th-order complex cell by less than `10⁻³⁸`. The
common weight norm bound avoids any per-cell numerical table. -/
theorem critical_grid_cell_gaussian_numeric (t : ℚ) (ht : |t| ≤ 100) (i : ℕ) (_hi : i < 944) :
    ∃ r : ℕ → ℚ,
      ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 8 200
              (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1)) -
            (criticalQuadratureGrid i : ℂ) ^ (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1) *
              ∑ k ∈ Finset.range 8,
                thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k
                    (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1)) *
                  (r k : ℂ)‖ <
        1 / 10 ^ 38 := by
  let a : ℚ := 1 + (i : ℚ) / 16
  let b : ℚ := 1 + ((i + 1 : ℕ) : ℚ) / 16
  have ha : 1 ≤ a := by
    dsimp only [a]
    linarith only [div_nonneg (Nat.cast_nonneg i) (by norm_num only : (0 : ℚ) ≤ 16)]
  have hab : b - a = 1 / 16 := by
    dsimp only [a, b]
    push_cast
    ring
  have haR : (a : ℝ) = criticalQuadratureGrid i := by
    simp only [a, criticalQuadratureGrid, Rat.cast_add, Rat.cast_one, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat]
  have hbR : (b : ℝ) = criticalQuadratureGrid (i + 1) := by
    simp only [b, criticalQuadratureGrid, Rat.cast_add, Rat.cast_one, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat]
  have hsum :
    (∑ k ∈ Finset.range 8,
        ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k
            (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1))‖) ≤
      8 * 2000001 := by
    calc
      _ ≤ ∑ _k ∈ Finset.range 8, (2000001 : ℝ) := by
        apply Finset.sum_le_sum
        intro k hk
        rw [← haR, ← hbR]
        exact (theta_gaussian_weight_uniform_norm t a b ht ha hab (Finset.mem_range.mp hk)).le
      _ = 8 * 2000001 := by norm_num only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  obtain ⟨r, hr⟩ :=
    critical_grid_cell_gaussian_fortyseven (t : ℝ) 8 200 i (criticalQuadratureGrid (i + 1))
  simp only [Complex.ofReal_ratCast] at hr
  refine ⟨r, ?_⟩
  have hm := mul_le_mul_of_nonneg_right hsum (by norm_num only : (0 : ℝ) ≤ 3 / 10 ^ 47)
  nlinarith only [hr, hm]

/-- A Gaussian-weight contribution, skipping weight evaluation when the
Gaussian approximation is zero by its large-argument cutoff. -/
private def gridCellTerm (t : ℚ) (i k : ℕ) : ℚ × ℚ :=
  if 54 ≤ ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16) then (0, 0)
  else
    Analysis.rationalComplexScale (gridGaussianTaylor i k)
      (gridWeightFast t (1 + (i : ℚ) / 16) (1 + ((i + 1 : ℕ) : ℚ) / 16) k)

/-- The independently importable certificate term is definitionally equal to
the term used by the analytic cell approximation. -/
private theorem grid_cell_certificate_eq (t : ℚ) (i k : ℕ) :
    gridCellTerm t i k = certificateCellTerm t i k := by rfl

/-- The cutoff-aware term equals the product for every index and height. -/
private theorem grid_cell_term_eq (t : ℚ) (i k : ℕ) :
    gridCellTerm t i k =
      Analysis.rationalComplexScale (gridGaussianTaylor i k)
        (gridWeightFast t (1 + (i : ℚ) / 16) (1 + ((i + 1 : ℕ) : ℚ) / 16) k) := by
  by_cases h : (54 : ℚ) ≤ ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16)
  · simp only [gridCellTerm, ite_eq_left h, gridGaussianTaylor, gaussianApproxScaled,
      Analysis.rationalComplexScale, zero_mul]
  · rw [gridCellTerm, ite_eq_right h]

/-- A rational complex cell value assembled from its calculated power,
Gaussian factors, and eight calculated Gaussian weights. -/
private def gridCellTaylor (t : ℚ) (i : ℕ) : ℚ × ℚ :=
  if 54 ≤ 1 + (i : ℚ) / 16 then (0, 0)
  else Analysis.rationalComplexMul (gridPowerTaylor i t) (∑ k ∈ Finset.range 8, gridCellTerm t i k)

/-- If the first Gaussian is beyond the cutoff, every Gaussian term is zero;
otherwise the cell is the usual rational power times the finite sum. -/
private theorem grid_cell_taylor_eq (t : ℚ) (i : ℕ) :
    gridCellTaylor t i =
      Analysis.rationalComplexMul (gridPowerTaylor i t)
        (∑ k ∈ Finset.range 8, gridCellTerm t i k) := by
  by_cases h : (54 : ℚ) ≤ 1 + (i : ℚ) / 16
  · have hterm : ∀ k : ℕ, gridCellTerm t i k = 0 := by
      intro k
      have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg k
      have hk' : (1 : ℚ) ≤ ((k : ℚ) + 1) ^ 2 := by nlinarith only [hk, sq_nonneg (k : ℚ)]
      have ha : (0 : ℚ) ≤ 1 + (i : ℚ) / 16 := le_trans (by norm_num only) h
      have hm := mul_le_mul_of_nonneg_right hk' ha
      have hc : (54 : ℚ) ≤ ((k : ℚ) + 1) ^ 2 * (1 + (i : ℚ) / 16) := by nlinarith only [h, hm]
      simp only [gridCellTerm, ite_eq_left hc, Prod.mk_zero_zero]
    have hs : (∑ k ∈ Finset.range 8, gridCellTerm t i k) = 0 := by
      exact Finset.sum_eq_zero (fun k _ ↦ hterm k)
    rw [gridCellTaylor, ite_eq_left h, hs]
    simp only [Analysis.rationalComplexMul, Prod.fst_zero, Prod.snd_zero, mul_zero, sub_zero,
      add_zero, Prod.mk_zero_zero]
  · rw [gridCellTaylor, ite_eq_right h]

/-- From cell 848 onward the first Gaussian is beyond the cutoff, so the
computed cell value vanishes, including the final cell of the partition. -/
private theorem grid_cell_tail_zero (t : ℚ) {i : ℕ} (hi : 848 ≤ i) : gridCellTaylor t i = 0 := by
  have hiq : (848 : ℚ) ≤ i := by exact_mod_cast hi
  have hc : (54 : ℚ) ≤ 1 + (i : ℚ) / 16 := by linarith only [hiq]
  simp only [gridCellTaylor, ite_eq_left hc, Prod.mk_zero_zero]

/-- The calculated rational cell value has the uniform cell error bound. -/
private theorem grid_cell_taylor_error (t : ℚ) (ht : |t| ≤ 100) (i : ℕ) (hi : i < 944) :
    ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 8 200
            (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1)) -
          (((gridCellTaylor t i).1 : ℂ) + ((gridCellTaylor t i).2 : ℂ) * Complex.I)‖ <
      35 / 10 ^ 42 := by
  let a : ℚ := 1 + (i : ℚ) / 16
  let b : ℚ := 1 + ((i + 1 : ℕ) : ℚ) / 16
  have ha : 1 ≤ a := by
    dsimp only [a]
    linarith only [div_nonneg (Nat.cast_nonneg i) (by norm_num only : (0 : ℚ) ≤ 16)]
  have hab : b - a = 1 / 16 := by
    dsimp only [a, b]
    push_cast
    ring
  have haR : (a : ℝ) = criticalQuadratureGrid i := by
    simp only [a, criticalQuadratureGrid, Rat.cast_add, Rat.cast_one, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat]
  have hbR : (b : ℝ) = criticalQuadratureGrid (i + 1) := by
    simp only [b, criticalQuadratureGrid, Rat.cast_add, Rat.cast_one, Rat.cast_div,
      Rat.cast_natCast, Rat.cast_ofNat]
  let g := gridGaussianTaylor i
  have hg :
    ∀ k : ℕ,
      |Real.exp (-Real.pi * ((k : ℝ) + 1) ^ 2 * criticalQuadratureGrid i) - (g k : ℝ)| ≤
          3 / 10 ^ 48 ∧
        |(g k : ℝ)| ≤ 2 :=
    grid_gaussian_bounded i
  let wr : ℕ → ℚ := fun k ↦ (gridWeightFast t a b k).1
  let wi : ℕ → ℚ := fun k ↦ (gridWeightFast t a b k).2
  have hw :
    ∀ k < 8,
      ‖thetaGaussianWeight (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 200 k a b -
            ((wr k : ℂ) + (wi k : ℂ) * Complex.I)‖ <
        1 / 10 ^ 42 + 1 / 10 ^ 49 :=
    fun _ hk ↦ by
    simpa only [wr, wi, grid_weight_fast_eq] using grid_weights_adaptive_error t a b ht ha hab hk
  have htR : |(t : ℝ)| ≤ 100 := by exact_mod_cast ht
  let pr := (gridPowerTaylor i t).1
  let pi := (gridPowerTaylor i t).2
  have hp :
    ‖(criticalQuadratureGrid i : ℂ) ^ (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1) -
          ((pr : ℂ) + (pi : ℂ) * Complex.I)‖ ≤
      4 / 10 ^ 48 :=
    grid_power_taylor_error i (Nat.le_of_lt hi) t htR
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let P : ℂ := (criticalQuadratureGrid i : ℂ) ^ (s / 2 - 1)
  let Q : ℂ := (pr : ℂ) + (pi : ℂ) * Complex.I
  let W : ℕ → ℂ := fun k ↦
    thetaGaussianWeight s 200 k (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1))
  let V : ℕ → ℂ := fun k ↦ (wr k : ℂ) + (wi k : ℂ) * Complex.I
  let Z : ℕ → ℂ := fun k ↦ (g k : ℂ)
  let S : ℂ :=
    ∑ k ∈ Finset.range 8,
      W k * Complex.exp (((-Real.pi * ((k : ℝ) + 1) ^ 2 : ℝ) : ℂ) * criticalQuadratureGrid i)
  let T : ℂ := ∑ k ∈ Finset.range 8, W k * Z k
  let U : ℂ := ∑ k ∈ Finset.range 8, V k * Z k
  have hWV : ∀ k ∈ Finset.range 8, ‖W k - V k‖ ≤ 1 / 10 ^ 42 + 1 / 10 ^ 49 := by
    intro k hk
    dsimp only [W, V, s]
    rw [← haR, ← hbR]
    exact (hw k (Finset.mem_range.mp hk)).le
  have hZ : ∀ k ∈ Finset.range 8, ‖Z k‖ ≤ 2 := by
    intro k hk
    dsimp only [Z]
    rw [← Complex.ofReal_ratCast, Complex.norm_real, Real.norm_eq_abs]
    exact (hg k).2
  have hsumV : (∑ k ∈ Finset.range 8, ‖V k‖) ≤ 1700000 := by
    let p : ℚ := 314159265358979323846264338327950288419716939937510 / 10 ^ 50
    have hp : |p| ≤ 4 := by
      dsimp only [p]
      norm_num only
    have hterm :
      ∀ k ∈ Finset.range 8, ‖V k‖ ≤ (Analysis.rationalGaussianWeightBound 200 k : ℝ) := by
      intro k hk
      have h :=
        Analysis.rational_gaussian_weight_norm_le t a b p ht ha hab hp
          (Analysis.rationalGaussianOrder k) k
      have htail :=
        Analysis.rational_gaussian_weight_tail_le t a b p ht ha hab hp (m :=
          Analysis.rationalGaussianOrder k) (n := 200) (k := k)
          (Analysis.rational_gaussian_order_le k)
      have hnonneg :
        0 ≤
          Analysis.rationalComplexOneNorm
            (Analysis.rationalGaussianWeight t a b p 200 k -
              Analysis.rationalGaussianWeight t a b p (Analysis.rationalGaussianOrder k) k) := by
        exact add_nonneg (abs_nonneg _) (abs_nonneg _)
      have hmono :
        Analysis.rationalGaussianWeightBound (Analysis.rationalGaussianOrder k) k ≤
          Analysis.rationalGaussianWeightBound 200 k := by
        linarith only [htail, hnonneg]
      have h := h.trans hmono
      have hc := (Rat.cast_le (K := ℝ)).mpr h
      have hn := Complex.norm_le_abs_re_add_abs_im (V k)
      dsimp only [V, wr, wi] at hn
      simp only [grid_weight_fast_eq] at hn
      dsimp only [gridWeightAdaptive, p, Analysis.rationalComplexOneNorm] at hn hc
      simp only [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, sub_zero, add_zero, mul_one,
        zero_add, Rat.cast_add, Rat.cast_abs] at hn hc
      simpa only [V, wr, wi, grid_weight_fast_eq, gridWeightAdaptive] using hn.trans hc
    have hs := Finset.sum_le_sum hterm
    have hb := (Rat.cast_lt (K := ℝ)).mpr Analysis.rational_gaussian_norm_sum_bound
    simp only [Rat.cast_sum, Rat.cast_ofNat] at hb
    linarith only [hs, hb]
  have hsumW : (∑ k ∈ Finset.range 8, ‖W k‖) ≤ 1700001 := by
    have hterm : ∀ k ∈ Finset.range 8, ‖W k‖ ≤ ‖W k - V k‖ + ‖V k‖ := by
      intro k hk
      have h := norm_add_le (W k - V k) (V k)
      simpa only [sub_add_cancel] using h
    have hs := Finset.sum_le_sum hterm
    have he : (∑ k ∈ Finset.range 8, ‖W k - V k‖) ≤ 8 * (1 / 10 ^ 42 + 1 / 10 ^ 49) := by
      calc
        _ ≤ ∑ _k ∈ Finset.range 8, (1 / 10 ^ 42 + 1 / 10 ^ 49 : ℝ) := Finset.sum_le_sum hWV
        _ = 8 * (1 / 10 ^ 42 + 1 / 10 ^ 49) := by
          norm_num only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Finset.sum_add_distrib] at hs
    linarith only [hs, he, hsumV]
  have hST : ‖S - T‖ ≤ 1700001 * (3 / 10 ^ 48) := by
    have h :=
      theta_cell_gaussian_error s 8 200 (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1))
        g (fun _ ↦ 3 / 10 ^ 48) (fun k _ ↦ (hg k).1)
    rw [theta_cell_gaussian_sum] at h
    change ‖S - T‖ ≤ _ at h
    have hm := mul_le_mul_of_nonneg_right hsumW (by norm_num only : (0 : ℝ) ≤ 3 / 10 ^ 48)
    exact h.trans (by simpa only [Finset.sum_mul] using hm)
  have hTU : ‖T - U‖ ≤ 8 * ((1 / 10 ^ 42 + 1 / 10 ^ 49) * 2) := by
    have h := finite_weighted_sum_error (Finset.range 8) W V Z hWV hZ
    simpa only [Finset.card_range, Nat.cast_ofNat] using h
  have hU : ‖U‖ ≤ 1700000 * 2 := by
    have hterm : ∀ k ∈ Finset.range 8, ‖V k * Z k‖ ≤ ‖V k‖ * 2 := by
      intro k hk
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (hZ k hk) (norm_nonneg _)
    have hs := (norm_sum_le (Finset.range 8) (fun k ↦ V k * Z k)).trans (Finset.sum_le_sum hterm)
    rw [← Finset.sum_mul] at hs
    exact hs.trans (mul_le_mul_of_nonneg_right hsumV (by norm_num only))
  have hP : ‖P‖ ≤ 1 := by
    have h :=
      critical_power_norm_le_one (t := (t : ℝ)) (a := criticalQuadratureGrid i)
        (by
          rw [← haR]
          exact_mod_cast ha)
    simpa only [Complex.ofReal_ratCast] using h
  have hPQ : ‖P - Q‖ ≤ 4 / 10 ^ 48 := hp
  have hz : Analysis.rationalComplexCast (gridCellTaylor t i) = Q * U := by
    rw [grid_cell_taylor_eq, Analysis.rationalComplexCast_mul, Analysis.rationalComplexCast_sum]
    have hp' : Analysis.rationalComplexCast (gridPowerTaylor i t) = Q := by
      dsimp only [Q, pr, pi]
      apply Complex.ext
      · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
          Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
          Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [hp']
    congr 1
    dsimp only [U]
    apply Finset.sum_congr rfl
    intro k hk
    rw [grid_cell_term_eq]
    rw [Analysis.rationalComplexCast_scale]
    change (g k : ℂ) * Analysis.rationalComplexCast (gridWeightFast t a b k) = V k * Z k
    dsimp only [V, Z, wr, wi]
    have hw' :
      Analysis.rationalComplexCast (gridWeightFast t a b k) =
        (((gridWeightFast t a b k).1 : ℂ) + ((gridWeightFast t a b k).2 : ℂ) * Complex.I) := by
      apply Complex.ext
      · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
          Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
          Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    rw [hw', mul_comm]
  have hz' : Q * U = (((gridCellTaylor t i).1 : ℂ) + ((gridCellTaylor t i).2 : ℂ) * Complex.I) := by
    rw [← hz]
    apply Complex.ext
    · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [← hz']
  have ha0 : 0 < criticalQuadratureGrid i := by
    rw [← haR]
    exact_mod_cast (lt_of_lt_of_le (by norm_num only : (0 : ℚ) < 1) ha)
  have hcell :
    thetaMellinExplicitCell s 8 200 (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1)) =
      P * S := by
    rw [theta_mellin_explicit_cell_factor _ _ _ ha0, theta_cell_gaussian_sum]
  change
    ‖thetaMellinExplicitCell s 8 200 (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1)) -
          Q * U‖ <
      _
  rw [hcell]
  have hid : P * S - Q * U = P * (S - T) + P * (T - U) + (P - Q) * U := by ring
  rw [hid]
  have htri :=
    (norm_add_le (P * (S - T) + P * (T - U)) ((P - Q) * U)).trans
      (add_le_add (norm_add_le (P * (S - T)) (P * (T - U))) le_rfl)
  simp only [norm_mul] at htri
  have h1 := mul_le_mul hP hST (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 1)
  have h2 := mul_le_mul hP hTU (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 1)
  have h3 := mul_le_mul hPQ hU (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 4 / 10 ^ 48)
  nlinarith only [htri, h1, h2, h3]

/-- The cell approximation with each Gaussian-weight product rounded to a
fixed grid before summation. The large-node cutoff avoids all tail work. -/
private def gridCellRounded (t : ℚ) (i : ℕ) : ℚ × ℚ :=
  if 54 ≤ 1 + (i : ℚ) / 16 then (0, 0)
  else
    Analysis.rationalComplexMul (gridPowerTaylor i t)
      (∑ k ∈ Finset.range 8, Analysis.rationalComplexRound (10 ^ 60) (gridCellTerm t i k))

/-- Rounding the eight individual cell terms changes the rational complex
cell value by at most `32 * 10⁻⁶⁰` on the certified height and node range. -/
private theorem grid_cell_round_error (t : ℚ) (ht : |t| ≤ 100) (i : ℕ) (hi : i < 944) :
    ‖Analysis.rationalComplexCast (gridCellRounded t i) -
          Analysis.rationalComplexCast (gridCellTaylor t i)‖ ≤
      32 / 10 ^ 60 := by
  by_cases hc : (54 : ℚ) ≤ 1 + (i : ℚ) / 16
  · simp only [gridCellRounded, gridCellTaylor, ite_eq_left hc, sub_self, norm_zero]
    norm_num only
  · have ha : 1 ≤ criticalQuadratureGrid i := by
      dsimp only [criticalQuadratureGrid]
      linarith only [div_nonneg (Nat.cast_nonneg i) (by norm_num only : (0 : ℝ) ≤ 16)]
    have htR : |(t : ℝ)| ≤ 100 := by exact_mod_cast ht
    let P : ℂ :=
      (criticalQuadratureGrid i : ℂ) ^ (((((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) / 2) - 1)
    let Q : ℂ := Analysis.rationalComplexCast (gridPowerTaylor i t)
    have hp : ‖P‖ ≤ 1 := by
      simpa only [P, Complex.ofReal_ratCast] using critical_power_norm_le_one (t := (t : ℝ)) ha
    have heq : Q = (((gridPowerTaylor i t).1 : ℂ) + ((gridPowerTaylor i t).2 : ℂ) * Complex.I) := by
      dsimp only [Q]
      apply Complex.ext
      · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
          Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
      · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
          Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
    have hpq : ‖P - Q‖ ≤ 4 / 10 ^ 48 := by
      rw [heq]
      exact grid_power_taylor_error i (Nat.le_of_lt hi) t htR
    have hQ : ‖Q‖ ≤ 2 := by
      have h := norm_le_norm_sub_add Q P
      rw [norm_sub_rev] at h
      linarith only [h, hp, hpq]
    have hsum :
      ‖(∑ k ∈ Finset.range 8,
              Analysis.rationalComplexCast
                (Analysis.rationalComplexRound (10 ^ 60) (gridCellTerm t i k))) -
            ∑ k ∈ Finset.range 8, Analysis.rationalComplexCast (gridCellTerm t i k)‖ ≤
        8 * (2 / 10 ^ 60) := by
      have h :=
        finite_sum_approx_error (Finset.range 8)
          (fun k ↦
            Analysis.rationalComplexCast
              (Analysis.rationalComplexRound (10 ^ 60) (gridCellTerm t i k)))
          (fun k ↦ Analysis.rationalComplexCast (gridCellTerm t i k)) (fun _ ↦ 2 / 10 ^ 60)
          (fun k _ ↦ by
            have he :=
              Analysis.norm_rationalComplexRound_error (G := 10 ^ 60) (by norm_num only)
                (gridCellTerm t i k)
            norm_num only [Nat.cast_pow, Nat.cast_ofNat] at he ⊢
            exact he)
      norm_num only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h ⊢
      exact h
    rw [gridCellRounded, ite_eq_right hc, grid_cell_taylor_eq, Analysis.rationalComplexCast_mul,
      Analysis.rationalComplexCast_mul, Analysis.rationalComplexCast_sum,
      Analysis.rationalComplexCast_sum, ← mul_sub, norm_mul]
    have hm := mul_le_mul hQ hsum (norm_nonneg _) (by norm_num only : (0 : ℝ) ≤ 2)
    nlinarith only [hm]

/-- The term-rounded cell approximation has a uniform error below
`36 * 10⁻⁴²`; the bound includes the original cell and rounding errors. -/
private theorem grid_cell_rounded_error (t : ℚ) (ht : |t| ≤ 100) (i : ℕ) (hi : i < 944) :
    ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 8 200
            (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1)) -
          (((gridCellRounded t i).1 : ℂ) + ((gridCellRounded t i).2 : ℂ) * Complex.I)‖ <
      36 / 10 ^ 42 := by
  have h := grid_cell_taylor_error t ht i hi
  have hr := grid_cell_round_error t ht i hi
  have he (z : ℚ × ℚ) : Analysis.rationalComplexCast z = ((z.1 : ℂ) + (z.2 : ℂ) * Complex.I) := by
    apply Complex.ext
    · simp only [Analysis.rationalComplexCast, Complex.add_re, Complex.mul_re, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]
    · simp only [Analysis.rationalComplexCast, Complex.add_im, Complex.mul_im, Complex.ratCast_re,
        Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero]
  rw [he, he, norm_sub_rev] at hr
  have htri :=
    norm_sub_le_norm_sub_add_norm_sub
      (thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 8 200
        (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1)))
      (((gridCellTaylor t i).1 : ℂ) + ((gridCellTaylor t i).2 : ℂ) * Complex.I)
      (((gridCellRounded t i).1 : ℂ) + ((gridCellRounded t i).2 : ℂ) * Complex.I)
  nlinarith only [htri, h, hr]

/-- Every fixed-grid 200th-order critical cell at a rational height
`|t| ≤ 100` has a rational complex approximation within `10⁻³⁸`. The
proof combines the uniform Gaussian, weight and complex-power certificates. -/
theorem critical_grid_cell_rational (t : ℚ) (ht : |t| ≤ 100) (i : ℕ) (hi : i < 944) :
    ∃ re im : ℚ,
      ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 8 200
              (criticalQuadratureGrid i) (criticalQuadratureGrid (i + 1)) -
            ((re : ℂ) + (im : ℂ) * Complex.I)‖ <
        1 / 10 ^ 38 := by
  refine ⟨(gridCellTaylor t i).1, (gridCellTaylor t i).2, ?_⟩
  exact (grid_cell_taylor_error t ht i hi).trans (by norm_num only)

/-- Cellwise norm certificates for both reflected integrands give an
explicit real error bound for the complete critical-line quadrature. The
finite sums use the same partition through the final cell. -/
theorem critical_quadrature_cell_error (t : ℝ) (N n m : ℕ) (p : ℕ → ℝ) (q r : ℕ → ℂ) (E F : ℕ → ℝ)
    (hq :
      ∀ j < m,
        ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) N n (p j) (p (j + 1)) -
              q j‖ ≤
          E j)
    (hr :
      ∀ j < m,
        ‖thetaMellinExplicitCell (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) N n (p j)
                (p (j + 1)) -
              r j‖ ≤
          F j) :
    |criticalExplicitQuadrature t N n m p -
          (((∑ j ∈ Finset.range m, q j) + ∑ j ∈ Finset.range m, r j) / 2).re| ≤
      ((∑ j ∈ Finset.range m, E j) + ∑ j ∈ Finset.range m, F j) / 2 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let u : ℂ := ∑ j ∈ Finset.range m, thetaMellinExplicitCell s N n (p j) (p (j + 1))
  let v : ℂ := ∑ j ∈ Finset.range m, thetaMellinExplicitCell (1 - s) N n (p j) (p (j + 1))
  let U : ℂ := ∑ j ∈ Finset.range m, q j
  let V : ℂ := ∑ j ∈ Finset.range m, r j
  have hu : ‖u - U‖ ≤ ∑ j ∈ Finset.range m, E j :=
    finite_sum_approx_error _ _ _ _ (fun j hj ↦ hq j (Finset.mem_range.mp hj))
  have hv : ‖v - V‖ ≤ ∑ j ∈ Finset.range m, F j :=
    finite_sum_approx_error _ _ _ _ (fun j hj ↦ hr j (Finset.mem_range.mp hj))
  have hm : ‖(u - U) + (v - V)‖ ≤ (∑ j ∈ Finset.range m, E j) + ∑ j ∈ Finset.range m, F j :=
    (norm_add_le _ _).trans (add_le_add hu hv)
  have hreal := Complex.abs_re_le_norm (((u - U) + (v - V)) / 2)
  rw [norm_div, Complex.norm_ofNat] at hreal
  have heq :
    criticalExplicitQuadrature t N n m p - ((U + V) / 2).re = (((u - U) + (v - V)) / 2).re := by
    simp only [criticalExplicitQuadrature, ← Complex.sub_re]
    congr 1
    ring
  rw [heq]
  exact hreal.trans (div_le_div_of_nonneg_right hm (by norm_num only))

/-- At heights of absolute value at most 100, cellwise approximation
errors and the fixed Mellin and quadrature budgets bound the completed-zeta
value itself. This is the finite-sum interface for endpoint sign checks. -/
theorem critical_completed_cell_error {t : ℝ} (ht : |t| ≤ 100) (q r : ℕ → ℂ) (E F : ℕ → ℝ)
    (hq :
      ∀ j < 944,
        ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 8 200
                (criticalQuadratureGrid j) (criticalQuadratureGrid (j + 1)) -
              q j‖ ≤
          E j)
    (hr :
      ∀ j < 944,
        ‖thetaMellinExplicitCell (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) 8 200
                (criticalQuadratureGrid j) (criticalQuadratureGrid (j + 1)) -
              r j‖ ≤
          F j) :
    |criticalCompletedZeta t -
          (((∑ j ∈ Finset.range 944, q j) + ∑ j ∈ Finset.range 944, r j) / 2).re| ≤
      (1 / 10 ^ 52 + 1 / 10 ^ 60) +
        ((∑ j ∈ Finset.range 944, E j) + ∑ j ∈ Finset.range 944, F j) / 2 := by
  have hqf := critical_quadrature_cell_error t 8 200 944 criticalQuadratureGrid q r E F hq hr
  have hza := critical_explicit_quadrature_error ht
  exact (abs_sub_le _ _ _).trans (add_le_add hza hqf)

/-- Complex conjugation commutes with the finite falling product. -/
private theorem falling_conj (w : ℂ) (n : ℕ) :
    (starRingEnd ℂ) (Analysis.complexFalling w n) =
      Analysis.complexFalling ((starRingEnd ℂ) w) n := by
  simp only [Analysis.complexFalling, map_prod, map_sub, map_natCast]

/-- The polynomial part of a Mellin cell coefficient respects complex
conjugation; all Gaussian factors and real cell nodes remain fixed. -/
private theorem theta_poly_conj (s : ℂ) (N n : ℕ) (x : ℝ) :
    (starRingEnd ℂ) (thetaMellinPolyCoeff s N n x) =
      thetaMellinPolyCoeff ((starRingEnd ℂ) s) N n x := by
  simp only [thetaMellinPolyCoeff, map_mul, map_sum, map_div₀, map_sub, map_pow, map_natCast,
    map_ofNat, map_one, Complex.conj_ofReal, ← Complex.exp_conj, falling_conj]

/-- At a positive real node, the explicit Mellin cell at the conjugate
parameter is the conjugate of the original cell. -/
private theorem theta_explicit_cell_conj (s : ℂ) (N n : ℕ) (a b : ℝ) (ha : 0 < a) :
    (starRingEnd ℂ) (thetaMellinExplicitCell s N n a b) =
      thetaMellinExplicitCell ((starRingEnd ℂ) s) N n a b := by
  have harg : (a : ℂ).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg ha.le]
    exact Ne.symm Real.pi_ne_zero
  have hp := Complex.cpow_conj (a : ℂ) (s / 2 - 1) harg
  simp only [Complex.conj_ofReal, map_div₀, map_sub, map_ofNat, map_one] at hp
  rw [theta_mellin_explicit_cell_factor s N n ha,
    theta_mellin_explicit_cell_factor ((starRingEnd ℂ) s) N n ha]
  simp only [Complex.real_smul, map_mul, map_sum, Complex.conj_ofReal, hp, theta_poly_conj]

/-- The rounded sum of the real parts of the positive-height cell values.
Conjugate symmetry supplies the reflected half without a second evaluation. -/
private def gridCompletedHalf (t : ℚ) : ℚ :=
  ∑ j ∈ Finset.range 944, Analysis.rationalGridFloor (10 ^ 50) (gridCellRounded t j).1

set_option maxRecDepth 8192 in
-- The complete 944-cell cardinality is normalized in the rounding budget.
/-- Rounding each real cell component changes the complete rational sum
by at most one grid unit per cell, including the final block. -/
private theorem grid_completed_half_round_error (t : ℚ) :
    |(∑ j ∈ Finset.range 944, (gridCellRounded t j).1) - gridCompletedHalf t| ≤ 944 / 10 ^ 50 := by
  have ht :
    ∀ j ∈ Finset.range 944,
      |(gridCellRounded t j).1 - Analysis.rationalGridFloor (10 ^ 50) (gridCellRounded t j).1| ≤
        1 / 10 ^ 50 := by
    intro j hj
    exact Analysis.rationalGridFloor_error (by norm_num only) _
  have hs :
    |∑ j ∈ Finset.range 944,
          ((gridCellRounded t j).1 -
            Analysis.rationalGridFloor (10 ^ 50) (gridCellRounded t j).1)| ≤
      944 / 10 ^ 50 := by
    calc
      _ ≤
          ∑ j ∈ Finset.range 944,
            |(gridCellRounded t j).1 -
                Analysis.rationalGridFloor (10 ^ 50) (gridCellRounded t j).1| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range 944, (1 / 10 ^ 50 : ℚ) := Finset.sum_le_sum ht
      _ = 944 / 10 ^ 50 := by norm_num only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simpa only [Finset.sum_sub_distrib, gridCompletedHalf] using hs

set_option maxRecDepth 8192 in
-- The explicit 944-cell sums contribute the uniform cell-error budget.
/-- The single-sided rounded cell sum approximates the completed-zeta value
at any rational height of magnitude at most 100 with error below `4 * 10⁻³⁸`. -/
private theorem grid_completed_half_error (t : ℚ) (ht : |t| ≤ 100) :
    |criticalCompletedZeta t - (gridCompletedHalf t : ℝ)| < 4 / 10 ^ 38 := by
  let s : ℂ := ((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I
  let Q : ℕ → ℂ := fun j ↦ ((gridCellRounded t j).1 : ℂ) + ((gridCellRounded t j).2 : ℂ) * Complex.I
  let R : ℕ → ℂ := fun j ↦ (starRingEnd ℂ) (Q j)
  have hq :
    ∀ j < 944,
      ‖thetaMellinExplicitCell s 8 200 (criticalQuadratureGrid j) (criticalQuadratureGrid (j + 1)) -
            Q j‖ ≤
        36 / 10 ^ 42 := by
    intro j hj
    exact (grid_cell_rounded_error t ht j hj).le
  have hconj : (starRingEnd ℂ) s = 1 - s := by
    dsimp only [s]
    simp only [map_add, map_mul, Complex.conj_ofReal, map_ratCast, Complex.conj_I]
    norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat, Complex.ofReal_one]
    ring
  have hr :
    ∀ j < 944,
      ‖thetaMellinExplicitCell (1 - s) 8 200 (criticalQuadratureGrid j)
              (criticalQuadratureGrid (j + 1)) -
            R j‖ ≤
        36 / 10 ^ 42 := by
    intro j hj
    have ha : 0 < criticalQuadratureGrid j := by
      dsimp only [criticalQuadratureGrid]
      exact
        add_pos_of_pos_of_nonneg (by norm_num only)
          (div_nonneg (Nat.cast_nonneg j) (by norm_num only))
    rw [← hconj, ← theta_explicit_cell_conj s 8 200 _ _ ha]
    change
      ‖(starRingEnd ℂ)
              (thetaMellinExplicitCell s 8 200 (criticalQuadratureGrid j)
                (criticalQuadratureGrid (j + 1))) -
            (starRingEnd ℂ) (Q j)‖ ≤
        _
    rw [← map_sub, Complex.norm_conj]
    exact hq j hj
  have htR : |(t : ℝ)| ≤ 100 := by exact_mod_cast ht
  have h :=
    critical_completed_cell_error htR Q R (fun _ ↦ 36 / 10 ^ 42) (fun _ ↦ 36 / 10 ^ 42)
      (by simpa only [s, Complex.ofReal_ratCast] using hq)
      (by simpa only [s, Complex.ofReal_ratCast] using hr)
  have hQ := map_sum Complex.reCLM Q (Finset.range 944)
  have hR := map_sum Complex.reCLM R (Finset.range 944)
  change (∑ j ∈ Finset.range 944, Q j).re = ∑ j ∈ Finset.range 944, (Q j).re at hQ
  change (∑ j ∈ Finset.range 944, R j).re = ∑ j ∈ Finset.range 944, (R j).re at hR
  have hreal :
    (((∑ j ∈ Finset.range 944, Q j) + ∑ j ∈ Finset.range 944, R j) / 2).re =
      ((∑ j ∈ Finset.range 944, (gridCellRounded t j).1 : ℚ) : ℝ) := by
    simp only [Complex.div_ofNat_re, Complex.add_re, hQ, hR, R, Complex.conj_re, Q, Complex.mul_re,
      Complex.add_re, Complex.ratCast_re, Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero,
      zero_mul, sub_zero, add_zero, Rat.cast_sum]
    ring
  rw [hreal] at h
  have hrnd :
    |((∑ j ∈ Finset.range 944, (gridCellRounded t j).1 : ℚ) : ℝ) - (gridCompletedHalf t : ℝ)| ≤
      944 / 10 ^ 50 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr (grid_completed_half_round_error t)
    norm_num only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] at hc ⊢
    exact hc
  have htri :=
    abs_sub_le (criticalCompletedZeta t) ((∑ j ∈ Finset.range 944, (gridCellRounded t j).1 : ℚ) : ℝ)
      (gridCompletedHalf t : ℝ)
  norm_num only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  linarith only [htri, h, hrnd]

/-- The rational real part of the two reflected grid-cell sums. -/
private def gridCompletedTaylor (t : ℚ) : ℚ :=
  ((∑ j ∈ Finset.range 944, (gridCellTaylor t j).1) +
      ∑ j ∈ Finset.range 944, (gridCellTaylor (-t) j).1) /
    2

/-- The reflected real cell contributions rounded to a common decimal grid
before their finite sum. The common denominator limits sum denominator growth. -/
private def gridCompletedRounded (t : ℚ) : ℚ :=
  (∑ j ∈ Finset.range 944,
      Analysis.rationalGridFloor (10 ^ 50) ((gridCellTaylor t j).1 + (gridCellTaylor (-t) j).1)) /
    2

set_option maxRecDepth 8192 in
-- Normalizing the 944-cell cardinality requires deeper reduction.
/-- Componentwise rounding changes the reflected cell sum by at most one
grid unit per cell. This holds for every rational height without a table. -/
private theorem grid_completed_round_error (t : ℚ) :
    |gridCompletedTaylor t - gridCompletedRounded t| ≤ 472 / 10 ^ 50 := by
  let f : ℕ → ℚ := fun j ↦ (gridCellTaylor t j).1 + (gridCellTaylor (-t) j).1
  have hterm :
    ∀ j ∈ Finset.range 944, |f j - Analysis.rationalGridFloor (10 ^ 50) (f j)| ≤ 1 / 10 ^ 50 := by
    intro j hj
    exact Analysis.rationalGridFloor_error (by norm_num only) (f j)
  have hs :
    |∑ j ∈ Finset.range 944, (f j - Analysis.rationalGridFloor (10 ^ 50) (f j))| ≤
      944 / 10 ^ 50 := by
    calc
      _ ≤ ∑ j ∈ Finset.range 944, |f j - Analysis.rationalGridFloor (10 ^ 50) (f j)| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j ∈ Finset.range 944, (1 / 10 ^ 50 : ℚ) := Finset.sum_le_sum hterm
      _ = 944 / 10 ^ 50 := by norm_num only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  simp only [Finset.sum_sub_distrib, f, Finset.sum_add_distrib] at hs
  have he :
    gridCompletedTaylor t - gridCompletedRounded t =
      (((∑ j ∈ Finset.range 944, (gridCellTaylor t j).1) +
            ∑ j ∈ Finset.range 944, (gridCellTaylor (-t) j).1) -
          ∑ j ∈ Finset.range 944,
            Analysis.rationalGridFloor (10 ^ 50)
              ((gridCellTaylor t j).1 + (gridCellTaylor (-t) j).1)) /
        2 := by
    dsimp only [gridCompletedTaylor, gridCompletedRounded]
    ring
  rw [he, abs_div, abs_of_nonneg (by norm_num only : (0 : ℚ) ≤ 2)]
  linarith only [hs]

set_option maxRecDepth 8192 in
-- The 944-cell finite-sum cardinality is normalized in the final error bound.
/-- The rational reflected-cell sum approximates the completed zeta value. -/
private theorem grid_completed_taylor_error (t : ℚ) (ht : |t| ≤ 100) :
    |criticalCompletedZeta t - (gridCompletedTaylor t : ℝ)| < 34 / 10 ^ 39 := by
  classical
  have hneg : |(-t : ℚ)| ≤ 100 := by simpa only [abs_neg] using ht
  let qr : ℕ → ℚ := fun j ↦ (gridCellTaylor t j).1
  let qi : ℕ → ℚ := fun j ↦ (gridCellTaylor t j).2
  let rr : ℕ → ℚ := fun j ↦ (gridCellTaylor (-t) j).1
  let ri : ℕ → ℚ := fun j ↦ (gridCellTaylor (-t) j).2
  let Q : ℕ → ℂ := fun j ↦ (qr j : ℂ) + (qi j : ℂ) * Complex.I
  let R : ℕ → ℂ := fun j ↦ (rr j : ℂ) + (ri j : ℂ) * Complex.I
  have hq' :
    ∀ j < 944,
      ‖thetaMellinExplicitCell (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) 8 200
              (criticalQuadratureGrid j) (criticalQuadratureGrid (j + 1)) -
            Q j‖ ≤
        35 / 10 ^ 42 := by
    intro j hj
    exact (grid_cell_taylor_error t ht j hj).le
  have hr' :
    ∀ j < 944,
      ‖thetaMellinExplicitCell (1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) 8 200
              (criticalQuadratureGrid j) (criticalQuadratureGrid (j + 1)) -
            R j‖ ≤
        35 / 10 ^ 42 := by
    intro j hj
    have he :
      1 - (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (((1 / 2 : ℝ) : ℂ) + ((-t : ℚ) : ℂ) * Complex.I) := by
      push_cast
      ring
    rw [he]
    exact (grid_cell_taylor_error (-t) hneg j hj).le
  have htR : |(t : ℝ)| ≤ 100 := by exact_mod_cast ht
  have h :=
    critical_completed_cell_error htR Q R (fun _ ↦ 35 / 10 ^ 42) (fun _ ↦ 35 / 10 ^ 42)
      (by simpa only [Complex.ofReal_ratCast] using hq')
      (by simpa only [Complex.ofReal_ratCast] using hr')
  have hreal :
    (((∑ j ∈ Finset.range 944, Q j) + ∑ j ∈ Finset.range 944, R j) / 2).re =
      (gridCompletedTaylor t : ℝ) := by
    have hQ := map_sum Complex.reCLM Q (Finset.range 944)
    have hR := map_sum Complex.reCLM R (Finset.range 944)
    change (∑ j ∈ Finset.range 944, Q j).re = ∑ j ∈ Finset.range 944, (Q j).re at hQ
    change (∑ j ∈ Finset.range 944, R j).re = ∑ j ∈ Finset.range 944, (R j).re at hR
    simp only [gridCompletedTaylor, Rat.cast_div, Rat.cast_add, Rat.cast_sum, Rat.cast_ofNat,
      Complex.div_ofNat_re, Complex.add_re, hQ, hR, Q, R, Complex.mul_re, Complex.ratCast_re,
      Complex.ratCast_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero, qr,
      rr]
  rw [hreal] at h
  norm_num only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h
  linarith only [h]

/-- The rounded rational cell sum retains a uniform `4 * 10⁻³⁸` error
bound for the completed-zeta value on the rational height range. -/
private theorem grid_completed_rounded_error (t : ℚ) (ht : |t| ≤ 100) :
    |criticalCompletedZeta t - (gridCompletedRounded t : ℝ)| < 4 / 10 ^ 38 := by
  have hr : |(gridCompletedTaylor t : ℝ) - (gridCompletedRounded t : ℝ)| ≤ 472 / 10 ^ 50 := by
    have hc := (Rat.cast_le (K := ℝ)).mpr (grid_completed_round_error t)
    simpa only [Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow] using hc
  have htaylor := grid_completed_taylor_error t ht
  have htri :=
    abs_sub_le (criticalCompletedZeta t) (gridCompletedTaylor t : ℝ) (gridCompletedRounded t : ℝ)
  linarith only [htri, htaylor, hr]

/-- A strict rational upper test for the computed grid value proves that
the corresponding critical-line xi value is positive. -/
private theorem grid_xi_pos (t : ℚ) (ht : |t| ≤ 100)
    (h : (t ^ 2 + 1 / 4) * (gridCompletedHalf t + 4 / 10 ^ 38) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  apply (xi_critical_pos_iff (t : ℝ)).2
  have he := (abs_lt.mp (grid_completed_half_error t ht)).2
  have hq : ((t : ℝ) ^ 2 + 1 / 4) * ((gridCompletedHalf t : ℝ) + 4 / 10 ^ 38) < 1 := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr h
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_div, Rat.cast_pow, Rat.cast_ofNat,
      Rat.cast_one] using hc
  have hp : 0 ≤ (t : ℝ) ^ 2 + 1 / 4 := by positivity
  have hm := mul_le_mul_of_nonneg_left (le_of_lt he) hp
  nlinarith only [hq, hm]

/-- A strict rational lower test for the computed grid value proves that
the corresponding critical-line xi value is negative. -/
private theorem grid_xi_neg (t : ℚ) (ht : |t| ≤ 100)
    (h : 1 < (t ^ 2 + 1 / 4) * (gridCompletedHalf t - 4 / 10 ^ 38)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  apply (xi_critical_neg_iff (t : ℝ)).2
  have he := (abs_lt.mp (grid_completed_half_error t ht)).1
  have hq : 1 < ((t : ℝ) ^ 2 + 1 / 4) * ((gridCompletedHalf t : ℝ) - 4 / 10 ^ 38) := by
    have hc := (Rat.cast_lt (K := ℝ)).mpr h
    simpa only [Rat.cast_mul, Rat.cast_add, Rat.cast_sub, Rat.cast_div, Rat.cast_pow,
      Rat.cast_ofNat, Rat.cast_one] using hc
  have hp : 0 ≤ (t : ℝ) ^ 2 + 1 / 4 := by positivity
  have hm := mul_le_mul_of_nonneg_left (le_of_lt he) hp
  nlinarith only [hq, hm]

/-- Below the large-node cutoff, eight separately certified rounded terms
determine a cell value. This avoids reducing all eight terms simultaneously. -/
private theorem grid_cell_eq_term_sum (t : ℚ) (i : ℕ) (w : ℕ → ℚ × ℚ) (hc : ¬54 ≤ 1 + (i : ℚ) / 16)
    (hw : ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (gridCellTerm t i k) = w k) :
    gridCellRounded t i =
      Analysis.rationalComplexMul (gridPowerTaylor i t) (∑ k ∈ Finset.range 8, w k) := by
  rw [gridCellRounded, ite_eq_right hc]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  exact hw k (Finset.mem_range.mp hk)

/-- Cellwise rational certificates replace the complete 944-cell sum without
unfolding its computations together. The final cell is included. -/
private theorem grid_half_eq_cell_sum (t : ℚ) (v : ℕ → ℚ)
    (h : ∀ j < 944, Analysis.rationalGridFloor (10 ^ 50) (gridCellRounded t j).1 = v j) :
    gridCompletedHalf t = ∑ j ∈ Finset.range 944, v j := by
  unfold gridCompletedHalf
  apply Finset.sum_congr rfl
  intro j hj
  exact h j (Finset.mem_range.mp hj)

/-- Termwise certificates and the resulting inexpensive cell comparisons
determine the complete half sum, including cutoff cells and the final cell. -/
private theorem grid_half_eq_term_sum (t : ℚ) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 944,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 944 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (gridPowerTaylor j t)
                    (∑ k ∈ Finset.range 8, w j k)).1 =
            v j) :
    gridCompletedHalf t = ∑ j ∈ Finset.range 944, v j := by
  apply grid_half_eq_cell_sum t v
  intro j hj
  by_cases hc : (54 : ℚ) ≤ 1 + (j : ℚ) / 16
  · rw [gridCellRounded, ite_eq_left hc]
    simpa only [ite_eq_left hc] using hv j hj
  · have hterms :
      ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (gridCellTerm t j k) = w j k := by
      intro k hk
      rw [grid_cell_certificate_eq]
      exact hw j hj k hk
    rw [grid_cell_eq_term_sum t j (w j) hc hterms]
    simpa only [ite_eq_right hc] using hv j hj

/-- Extend term values by zero from cell 848 onward. This preserves the
computed prefix while representing the entire cutoff tail uniformly. -/
private def gridPrefixTerms (w : ℕ → ℕ → ℚ × ℚ) (j k : ℕ) : ℚ × ℚ :=
  if j < 848 then w j k else 0

/-- A certificate for the first 848 cells determines all rounded terms.
The remaining cells vanish uniformly, so no tail table or per-cell proof is needed. -/
private theorem grid_prefix_terms_cert (t : ℚ) (w : ℕ → ℕ → ℚ × ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k) :
    ∀ j < 944,
      ∀ k < 8,
        Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) =
          gridPrefixTerms w j k := by
  intro j _ k hk
  by_cases hc : j < 848
  · simpa only [gridPrefixTerms, ite_eq_left hc] using hw j hc k hk
  · have hi : 848 ≤ j := Nat.le_of_not_gt hc
    simp only [gridPrefixTerms, ite_eq_right hc, certificate_round_tail_zero t hi k]

/-- Certified term values for the first 848 cells and cellwise arithmetic
determine the complete 944-cell half sum; the tail is supplied uniformly. -/
private theorem grid_half_eq_prefix_sum (t : ℚ) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 944 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (gridPowerTaylor j t)
                    (∑ k ∈ Finset.range 8, gridPrefixTerms w j k)).1 =
            v j) :
    gridCompletedHalf t = ∑ j ∈ Finset.range 944, v j := by
  exact grid_half_eq_term_sum t (gridPrefixTerms w) v (grid_prefix_terms_cert t w hw) hv

/-- Extend cell values by zero from cell 848 onward, matching the uniform
cutoff of the cell approximation without storing a tail table. -/
private def gridPrefixCells (v : ℕ → ℚ) (j : ℕ) : ℚ :=
  if j < 848 then v j else 0

/-- The complete 944-cell sum of zero-extended values is exactly the sum
over the first 848 cells, so the final comparison has no tail entries. -/
private theorem grid_prefix_cells_sum (v : ℕ → ℚ) :
    (∑ j ∈ Finset.range 944, gridPrefixCells v j) = ∑ j ∈ Finset.range 848, v j := by
  have hsub : Finset.range 848 ⊆ Finset.range 944 := Finset.range_mono (by norm_num only)
  calc
    _ = ∑ j ∈ Finset.range 848, gridPrefixCells v j := by
      symm
      apply Finset.sum_subset hsub
      intro j hj hnot
      have hc : ¬j < 848 := by simpa only [Finset.mem_range] using hnot
      simp only [gridPrefixCells, ite_eq_right hc]
    _ = ∑ j ∈ Finset.range 848, v j := by
      apply Finset.sum_congr rfl
      intro j hj
      simp only [gridPrefixCells, ite_eq_left (Finset.mem_range.mp hj)]

/-- Prefix term and cell certificates determine the full half sum. Both
term and cell values in the remaining 96 cells are supplied by the cutoff. -/
private theorem grid_half_eq_prefix_cells (t : ℚ) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 848 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (certificateGridPower j t)
                    (∑ k ∈ Finset.range 8, gridPrefixTerms w j k)).1 =
            v j) :
    gridCompletedHalf t = ∑ j ∈ Finset.range 944, gridPrefixCells v j := by
  apply grid_half_eq_prefix_sum t w (gridPrefixCells v) hw
  intro j _
  by_cases hc : j < 848
  · simpa only [gridPrefixCells, ite_eq_left hc, grid_power_certificate_eq] using hv j hc
  · have hi : 848 ≤ j := Nat.le_of_not_gt hc
    have hiq : (848 : ℚ) ≤ j := by exact_mod_cast hi
    have hcut : (54 : ℚ) ≤ 1 + (j : ℚ) / 16 := by linarith only [hiq]
    simp only [ite_eq_left hcut, gridPrefixCells, ite_eq_right hc, Analysis.rationalGridFloor,
      zero_mul, Int.floor_zero, Int.cast_zero, zero_div]

/-- Prefix term and cell certificates with a strict upper comparison imply
a positive critical-line xi value. Both cutoff tails are automatic. -/
private theorem grid_xi_pos_of_prefix_cells (t : ℚ) (ht : |t| ≤ 100) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 848 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (certificateGridPower j t)
                    (∑ k ∈ Finset.range 8, gridPrefixTerms w j k)).1 =
            v j)
    (h : (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 848, v j) + 4 / 10 ^ 38) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  apply grid_xi_pos t ht
  rw [grid_half_eq_prefix_cells t w v hw hv, grid_prefix_cells_sum]
  exact h

/-- Prefix term and cell certificates with a strict lower comparison imply
a negative critical-line xi value. Both cutoff tails are automatic. -/
private theorem grid_xi_neg_of_prefix_cells (t : ℚ) (ht : |t| ≤ 100) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 848 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (certificateGridPower j t)
                    (∑ k ∈ Finset.range 8, gridPrefixTerms w j k)).1 =
            v j)
    (h : 1 < (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 848, v j) - 4 / 10 ^ 38)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  apply grid_xi_neg t ht
  rw [grid_half_eq_prefix_cells t w v hw hv, grid_prefix_cells_sum]
  exact h

/-- Arithmetic certificates stated directly with the prefix term values also
apply to their zero extension on every cell below the cutoff. -/
private theorem grid_prefix_arithmetic (t : ℚ) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hv :
      ∀ (j : ℕ),
        j < 848 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (certificateGridPower j t)
                    (∑ k ∈ Finset.range 8, w j k)).1 =
            v j) :
    ∀ (j : ℕ),
      j < 848 →
        Analysis.rationalGridFloor (10 ^ 50)
            (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
              else
                Analysis.rationalComplexMul (certificateGridPower j t)
                  (∑ k ∈ Finset.range 8, gridPrefixTerms w j k)).1 =
          v j := by
  intro j hj
  simpa only [gridPrefixTerms, ite_eq_left hj] using hv j hj

/-- Term and arithmetic prefix certificates with a strict upper comparison
imply positivity of xi at a rational height of magnitude at most 100. -/
private theorem grid_xi_pos_of_certificates (t : ℚ) (ht : |t| ≤ 100) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 848 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (certificateGridPower j t)
                    (∑ k ∈ Finset.range 8, w j k)).1 =
            v j)
    (h : (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 848, v j) + 4 / 10 ^ 38) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  exact grid_xi_pos_of_prefix_cells t ht w v hw (grid_prefix_arithmetic t w v hv) h

/-- Term and arithmetic prefix certificates with a strict lower comparison
imply negativity of xi at a rational height of magnitude at most 100. -/
private theorem grid_xi_neg_of_certificates (t : ℚ) (ht : |t| ≤ 100) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 848 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (certificateGridPower j t)
                    (∑ k ∈ Finset.range 8, w j k)).1 =
            v j)
    (h : 1 < (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 848, v j) - 4 / 10 ^ 38)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  exact grid_xi_neg_of_prefix_cells t ht w v hw (grid_prefix_arithmetic t w v hv) h

/-- A prefix certificate, cell arithmetic and a strict rational upper test
give a positive critical-line xi value without individual tail certificates. -/
private theorem grid_xi_pos_of_prefix (t : ℚ) (ht : |t| ≤ 100) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 944 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (gridPowerTaylor j t)
                    (∑ k ∈ Finset.range 8, gridPrefixTerms w j k)).1 =
            v j)
    (h : (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 944, v j) + 4 / 10 ^ 38) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  apply grid_xi_pos t ht
  rw [grid_half_eq_prefix_sum t w v hw hv]
  exact h

/-- A prefix certificate, cell arithmetic and a strict rational lower test
give a negative critical-line xi value without individual tail certificates. -/
private theorem grid_xi_neg_of_prefix (t : ℚ) (ht : |t| ≤ 100) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 848,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 944 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (gridPowerTaylor j t)
                    (∑ k ∈ Finset.range 8, gridPrefixTerms w j k)).1 =
            v j)
    (h : 1 < (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 944, v j) - 4 / 10 ^ 38)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  apply grid_xi_neg t ht
  rw [grid_half_eq_prefix_sum t w v hw hv]
  exact h

/-- Term and cell certificates supply the rational upper test for a
positive critical-line xi value, without one large kernel reduction. -/
private theorem grid_xi_pos_of_terms (t : ℚ) (ht : |t| ≤ 100) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 944,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 944 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (gridPowerTaylor j t)
                    (∑ k ∈ Finset.range 8, w j k)).1 =
            v j)
    (h : (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 944, v j) + 4 / 10 ^ 38) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  apply grid_xi_pos t ht
  rw [grid_half_eq_term_sum t w v hw hv]
  exact h

/-- Term and cell certificates supply the rational lower test for a
negative critical-line xi value, without one large kernel reduction. -/
private theorem grid_xi_neg_of_terms (t : ℚ) (ht : |t| ≤ 100) (w : ℕ → ℕ → ℚ × ℚ) (v : ℕ → ℚ)
    (hw :
      ∀ j < 944,
        ∀ k < 8, Analysis.rationalComplexRound (10 ^ 60) (certificateCellTerm t j k) = w j k)
    (hv :
      ∀ (j : ℕ),
        j < 944 →
          Analysis.rationalGridFloor (10 ^ 50)
              (if 54 ≤ 1 + (j : ℚ) / 16 then (0, 0)
                else
                  Analysis.rationalComplexMul (gridPowerTaylor j t)
                    (∑ k ∈ Finset.range 8, w j k)).1 =
            v j)
    (h : 1 < (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 944, v j) - 4 / 10 ^ 38)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  apply grid_xi_neg t ht
  rw [grid_half_eq_term_sum t w v hw hv]
  exact h

/-- Individually certified cells and a rational upper comparison establish
the positive xi sign at a rational height of magnitude at most 100. -/
private theorem grid_xi_pos_of_cells (t : ℚ) (ht : |t| ≤ 100) (v : ℕ → ℚ)
    (hv : ∀ j < 944, Analysis.rationalGridFloor (10 ^ 50) (gridCellRounded t j).1 = v j)
    (h : (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 944, v j) + 4 / 10 ^ 38) < 1) :
    0 < (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re := by
  apply grid_xi_pos t ht
  rw [grid_half_eq_cell_sum t v hv]
  exact h

/-- Individually certified cells and a rational lower comparison establish
the negative xi sign at a rational height of magnitude at most 100. -/
private theorem grid_xi_neg_of_cells (t : ℚ) (ht : |t| ≤ 100) (v : ℕ → ℚ)
    (hv : ∀ j < 944, Analysis.rationalGridFloor (10 ^ 50) (gridCellRounded t j).1 = v j)
    (h : 1 < (t ^ 2 + 1 / 4) * ((∑ j ∈ Finset.range 944, v j) - 4 / 10 ^ 38)) :
    (riemannXi (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re < 0 := by
  apply grid_xi_neg t ht
  rw [grid_half_eq_cell_sum t v hv]
  exact h

/-- For every rational height of magnitude at most 100, the regularized
completed-zeta value has a rational approximation with error below `10⁻³⁵`.
Both reflected 944-cell sums use the same uniform rational-cell certificate,
and the analytic truncation and quadrature errors are included. -/
theorem critical_completed_rational (t : ℚ) (ht : |t| ≤ 100) :
    ∃ q : ℚ, |criticalCompletedZeta t - (q : ℝ)| < 1 / 10 ^ 35 := by
  refine ⟨gridCompletedTaylor t, ?_⟩
  exact (grid_completed_taylor_error t ht).trans (by norm_num only)

/-- At every rational height of magnitude at most 100, the completed-zeta
value has a rational approximation within `7 * 10⁻³⁷`. The proof combines
the uniform cell bounds with the Mellin and quadrature remainders. -/
theorem critical_completed_rational_fine (t : ℚ) (ht : |t| ≤ 100) :
    ∃ q : ℚ, |criticalCompletedZeta t - (q : ℝ)| < 7 / 10 ^ 37 := by
  refine ⟨gridCompletedTaylor t, ?_⟩
  exact (grid_completed_taylor_error t ht).trans (by norm_num only)

/-- At every rational height of magnitude at most 100, the completed-zeta
value has a rational approximation within `2 * 10⁻³⁷`. The bound uses the
improved Gaussian cutoff together with the uniform cell and quadrature errors. -/
theorem critical_completed_rational_sharp (t : ℚ) (ht : |t| ≤ 100) :
    ∃ q : ℚ, |criticalCompletedZeta t - (q : ℝ)| < 2 / 10 ^ 37 := by
  refine ⟨gridCompletedTaylor t, ?_⟩
  exact (grid_completed_taylor_error t ht).trans (by norm_num only)

/-- For rational heights of magnitude at most 100, a rational approximation
to the completed-zeta value has error below `4 * 10⁻³⁸`. The proof sums the
individual Gaussian weight bounds before estimating the quadrature error. -/
theorem critical_completed_rational_small (t : ℚ) (ht : |t| ≤ 100) :
    ∃ q : ℚ, |criticalCompletedZeta t - (q : ℝ)| < 4 / 10 ^ 38 := by
  refine ⟨gridCompletedTaylor t, ?_⟩
  exact (grid_completed_taylor_error t ht).trans (by norm_num only)

end PseudoPrime.AnalyticNumberTheory.RiemannXi
