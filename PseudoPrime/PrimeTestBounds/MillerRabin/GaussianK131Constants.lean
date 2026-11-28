/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.GaussianK131Remainder
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-! # Principal and square-recovery constants of K131 -/

public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

private def gammaCoeffs : Fin 9 → ℚ :=
  ![17419183802523 / 8388608, -20468426139 / 16384, 17095088187 / 65536, -14682681 / 512,
    26979 / 16, -24, 48053 / 128, -29, 1]

private def fourierTerm (j : Fin 9) (k : ℕ) : ℚ :=
  let m := 9 - j.val
  gammaCoeffs j * ((2 * m - k).factorial : ℚ) * (27 / 16 : ℚ) ^ k /
    ((k.factorial : ℚ) * ((m - k).factorial : ℚ) * 2 ^ (2 * m - k) * (m.factorial : ℚ) *
      (27 / 16 : ℚ) ^ (19 - 2 * j.val))

private def fourierConstant : ℚ :=
  ∑ j : Fin 9, fourierTerm j 0

/-- The K131 amplitude normalizes the constant Fourier coefficient to 3/8.
The rational reciprocal is computed from the nine coefficients of the kernel. -/
def gaussianK131Amplitude : ℚ :=
  (3 / 8) / fourierConstant

private theorem k131_amplitude_eq :
    gaussianK131Amplitude = 6461081889226673298932241 / 45165044758708203983355904 := by
  decide +kernel

/-- The normalized K131 Fourier polynomial, generated from the nine
partial-fraction coefficients and their factorial transforms. -/
noncomputable def gaussianK131Fourier : Polynomial ℝ :=
  Polynomial.C (gaussianK131Amplitude : ℝ) *
    ∑ j : Fin 9, ∑ k ∈ Finset.range (10 - j.val), Polynomial.monomial k (fourierTerm j k : ℝ)

/-- The generator gives the normalized constant term 3/8. -/
theorem gaussian_k131_fourier_zero : gaussianK131Fourier.eval 0 = 3 / 8 := by
  have hg (j : Fin 9) :
    ∑ k ∈ Finset.range (10 - j.val), (fourierTerm j k : ℝ) * 0 ^ k = (fourierTerm j 0 : ℝ) := by
    have hj : 0 < 10 - j.val := Nat.sub_pos_of_lt (j.isLt.trans (by decide : 9 < 10))
    rw [Finset.sum_eq_single 0]
    · rw [pow_zero, mul_one]
    · intro k _ hk
      rw [zero_pow hk, mul_zero]
    · exact fun h ↦ (h (Finset.mem_range.mpr hj)).elim
  simp only [gaussianK131Fourier, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial, hg, ← Rat.cast_sum, ← Rat.cast_mul]
  have h : gaussianK131Amplitude * fourierConstant = (3 / 8 : ℚ) := by decide +kernel
  simpa only [fourierConstant, Rat.cast_div, Rat.cast_ofNat] using congrArg (fun q : ℚ ↦ (q : ℝ)) h

private def inverseCoeffs : Fin 9 → ℚ :=
  ![1 / 6, 29 / 120, 841 / 20160, 1 / 15120, 19 / 1663200, 29 / 115315200, 1 / 9081072000,
    1 / 274450176000, 1 / 41716426752000]

/-- The inverse Mellin polynomial of K131. The odd-degree coefficients
are those of the squared kernel numerator in reversed factorial order. -/
noncomputable def gaussianK131Inverse (x : ℝ) : ℝ :=
  ∑ j : Fin 9, (inverseCoeffs j : ℝ) * x ^ (2 * j.val + 3)

private theorem inverse_at_edge :
    gaussianK131Inverse (9 / 4) = 3266928989636743463788179 / 115827515866388365312000 := by
  have h :
    (∑ j : Fin 9, inverseCoeffs j * (9 / 4 : ℚ) ^ (2 * j.val + 3)) =
      3266928989636743463788179 / 115827515866388365312000 := by
    decide +kernel
  simpa only [gaussianK131Inverse, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow, Rat.cast_div,
    Rat.cast_ofNat] using congrArg (fun q : ℚ ↦ (q : ℝ)) h

/-- The K131 inverse Mellin weight as a polynomial, for symbolic
differentiation and shifts of its logarithmic coordinate. -/
noncomputable def gaussianK131InversePoly : Polynomial ℝ :=
  ∑ j : Fin 9, Polynomial.monomial (2 * j.val + 3) (inverseCoeffs j : ℝ)

/-- Evaluation of the inverse polynomial gives the inverse Mellin weight. -/
theorem gaussian_k131_inverse_eval (x : ℝ) :
    gaussianK131InversePoly.eval x = gaussianK131Inverse x := by
  simp only [gaussianK131InversePoly, gaussianK131Inverse, Polynomial.eval_finsetSum,
    Polynomial.eval_monomial]

private theorem inverse_derivative_at_edge :
    gaussianK131InversePoly.derivative.eval (9 / 4) =
      1211257253192871331747593 / 16764508875398316032000 := by
  have h :
    (∑ j : Fin 9,
        (inverseCoeffs j * ((2 * j.val + 3 : ℕ) : ℚ)) * (9 / 4 : ℚ) ^ (2 * j.val + 3 - 1)) =
      1211257253192871331747593 / 16764508875398316032000 := by
    decide +kernel
  simpa only [gaussianK131InversePoly, Polynomial.derivative_sum, Polynomial.derivative_monomial,
    Polynomial.eval_finsetSum, Polynomial.eval_monomial, Rat.cast_sum, Rat.cast_mul, Rat.cast_pow,
    Rat.cast_div, Rat.cast_ofNat, Rat.cast_natCast, mul_comm] using congrArg (fun q : ℚ ↦ (q : ℝ)) h

/-- The inverse fifth-power loss coefficient from the principal K131
remainder, computed from the inverse Mellin weight and its slope at the edge. -/
@[expose]
noncomputable def gaussianK131EdgeLoss : ℝ :=
  (5 / 3 : ℝ) * ((gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4))) *
    |(19 / 16 : ℝ) * gaussianK131Inverse (9 / 4) - gaussianK131InversePoly.derivative.eval (9 / 4)|

/-- The K131 inverse fifth-power loss supplies a strictly negative
normalized curvature term at every positive radius. -/
theorem gaussian_k131_edge_curvature_lt {y : ℝ} (hy : 0 < y) :
    logPowerPoly (-(5 : ℝ)) (logPowerCurvature 5 (Polynomial.C (-gaussianK131EdgeLoss))) y < 0 := by
  have h : 0 < gaussianK131EdgeLoss := by
    unfold gaussianK131EdgeLoss
    rw [k131_amplitude_eq, inverse_at_edge, inverse_derivative_at_edge]
    apply mul_pos
    · positivity
    · apply abs_pos.mpr
      norm_num only
  simp only [logPowerPoly, logPowerCurvature, Polynomial.derivative_C, Polynomial.derivative_zero,
    mul_zero, sub_zero, add_zero, Polynomial.eval_mul, Polynomial.eval_C]
  exact
    mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hy _)
      (mul_neg_of_pos_of_neg (by norm_num only) (neg_lt_zero.mpr h))

/-- The K131 weight at normalized radius one, before dividing by the
physical radius. -/
@[expose]
noncomputable def gaussianK131UnitWeight : ℝ :=
  (gaussianK131Amplitude : ℝ) * Real.exp (-(27 / 16 : ℝ) * (9 / 4)) * gaussianK131Inverse (9 / 4)

/-- The actual coefficient of the principal RH error in the bundle,
using its rational lower bound for pi. -/
@[expose]
noncomputable def gaussianK131RhCoeff : ℝ :=
  gaussianK131UnitWeight / (2 * (314159 / 100000 : ℝ))

/-- The fixed K131 principal coefficient satisfies the curvature budget. -/
theorem gaussian_k131_rh_coeff_mem : gaussianK131RhCoeff ∈ Set.Icc 0 (7 / 480) := by
  rw [gaussianK131RhCoeff, gaussianK131UnitWeight, k131_amplitude_eq, inverse_at_edge]
  have hp := Real.exp_pos (-(27 / 16 : ℝ) * (9 / 4))
  refine ⟨by positivity, ?_⟩
  have hx : (0 : ℝ) ≤ (27 / 16) * (9 / 4) := by norm_num only
  have ht := Real.sum_le_exp_of_nonneg hx 13
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  have he : Real.exp (-(27 / 16 : ℝ) * (9 / 4)) ≤ 9 / 400 := by
    rw [neg_mul, Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith only [ht]
  norm_num only [Rat.cast_div, Rat.cast_ofNat]
  linarith only [he]

/-- On the K131 bridge the actual principal RH error has normalized
curvature bounded by 4/5. -/
theorem gaussian_k131_rh_curvature {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    y ^ 2 * deriv (deriv (k131PrincipalError gaussianK131RhCoeff)) y ≤ 4 / 5 := by
  intro y
  have hy := gaussian_bridge_scale_mem hL
  exact
    k131_principal_curvature_le gaussian_k131_rh_coeff_mem
      ((by norm_num only : (1 : ℝ) < 465644807 / 400000).trans_le hy.1) (k131_radius_log_mem hL)

/-- The truncated exponential moment of the K131 inverse Mellin polynomial.
The square-recovery coefficients use rates 27/16 and 23/16. -/
@[expose]
noncomputable def gaussianK131Moment (a : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..9 / 4, Real.exp (-a * t) * gaussianK131Inverse t

private theorem inverse_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gaussianK131Inverse x := by
  unfold gaussianK131Inverse
  apply Finset.sum_nonneg
  intro j _
  have h : 0 ≤ inverseCoeffs j := by
    have hc : ∀ k : Fin 9, 0 ≤ inverseCoeffs k := by decide +kernel
    exact hc j
  exact mul_nonneg (Rat.cast_nonneg.mpr h) (pow_nonneg hx _)

private theorem moment_nonneg (a : ℝ) : 0 ≤ gaussianK131Moment a := by
  unfold gaussianK131Moment
  apply intervalIntegral.integral_nonneg (by norm_num only)
  intro t ht
  exact mul_nonneg (Real.exp_pos _).le (inverse_nonneg ht.1)

/-- The K131 coefficient multiplying the inverse square-root loss in the
finite Chebyshev square recovery. -/
@[expose]
noncomputable def gaussianK131RecoveryVariation : ℝ :=
  8 * gaussianK131UnitWeight +
    (gaussianK131Amplitude : ℝ) * Real.exp (-(9 / 16 : ℝ)) * gaussianK131Moment (23 / 16)

/-- The square-recovery variation is nonnegative, using the nonnegative
inverse Mellin polynomial on the moment support. -/
theorem gaussian_k131_recovery_nonneg : 0 ≤ gaussianK131RecoveryVariation := by
  have hw : 0 ≤ gaussianK131UnitWeight := by
    dsimp only [gaussianK131UnitWeight]
    rw [k131_amplitude_eq, inverse_at_edge]
    positivity
  unfold gaussianK131RecoveryVariation
  rw [k131_amplitude_eq]
  exact
    add_nonneg (mul_nonneg (by norm_num only) hw)
      (mul_nonneg (mul_nonneg (by positivity) (Real.exp_pos _).le) (moment_nonneg _))

/-- The bundle's actual finite square-recovery term has nonpositive
normalized curvature throughout the affine bridge. -/
theorem gaussian_k131_recovery_curvature {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let y := gaussianBridgeScale L
    let D := (81 / 100 : ℝ) * gaussianK131RecoveryVariation
    y ^ 2 * deriv (deriv (logPowerPoly (-(1 / 2 : ℝ)) (Polynomial.C (-D)))) y ≤ 0 := by
  intro y D
  have hy := gaussian_bridge_scale_mem hL
  exact
    k131_recovery_curvature_le (mul_nonneg (by norm_num only) gaussian_k131_recovery_nonneg)
      ((by norm_num only : (0 : ℝ) < 465644807 / 400000).trans_le hy.1)

private def gammaIntegralZero : ℚ :=
  ∑ j : Fin 9, inverseCoeffs j * ((2 * j.val + 3).factorial : ℚ) / (19 / 16 : ℚ) ^ (2 * j.val + 4)

private def kernelNumerator (x : ℚ) : ℚ :=
  x ^ 8 + 29 / 2 * x ^ 6 + 12 * x ^ 2 + 54

private def negativePole : ℚ :=
  gaussianK131Amplitude * kernelNumerator (19 / 16) ^ 2 / (19 / 16 : ℚ) ^ 20

private noncomputable def reciprocalLogLower : ℝ :=
  459469055436280922658411175473583991 / 250000000000000000000000000000000000

/-- The coefficient of the reciprocal-radius term in the expanded K131
comparison combines the shifted pole, Gamma integral and cutoff boundary. -/
noncomputable def gaussianK131Reciprocal : ℝ :=
  -3 * (negativePole : ℝ) *
      (1831 / 10000 - 973 / 5000 * Real.exp (1 / 20) + 1 / 80 * Real.exp (21 / 20) -
        13 / 1250 * Real.exp (9 / 4)) +
    3 * (gaussianK131Amplitude : ℝ) * Real.exp (-(9 / 8 : ℝ)) * (gammaIntegralZero : ℝ) +
    4 * gaussianK131UnitWeight * reciprocalLogLower

private theorem pole_cap :
    -3 * (negativePole : ℝ) *
        (1831 / 10000 - 973 / 5000 * Real.exp (1 / 20) + 1 / 80 * Real.exp (21 / 20) -
          13 / 1250 * Real.exp (9 / 4)) ≤
      16 := by
  have h₁ :=
    Analysis.exp_le_taylor_ratio (x := 1 / 20) (q := 1 / 4) (n := 13) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)
  have h₂ := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 21 / 20) 13
  have h₃ :=
    Analysis.exp_le_taylor_ratio (x := 9 / 4) (q := 1 / 4) (n := 13) (by norm_num only)
      (by norm_num only) (by norm_num only) (by norm_num only)
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at h₁ h₂ h₃
  norm_num only [negativePole, k131_amplitude_eq, kernelNumerator, Rat.cast_div, Rat.cast_mul,
    Rat.cast_add, Rat.cast_pow, Rat.cast_ofNat]
  linarith only [h₁, h₂, h₃]

private theorem gamma_cap :
    3 * (gaussianK131Amplitude : ℝ) * Real.exp (-(9 / 8 : ℝ)) * (gammaIntegralZero : ℝ) ≤ 61 := by
  have hG : gammaIntegralZero = 16137535984833796448326844416 / 37589973457545958193355601 := by
    decide +kernel
  have ht := Real.sum_le_exp_of_nonneg (by norm_num only : (0 : ℝ) ≤ 9 / 8) 12
  norm_num only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial, Nat.cast_ofNat,
    Nat.cast_zero, Nat.cast_one] at ht
  have he : Real.exp (-(9 / 8 : ℝ)) ≤ 13 / 40 := by
    rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
    linarith only [ht]
  norm_num only [k131_amplitude_eq, hG, Rat.cast_div, Rat.cast_ofNat]
  linarith only [he]

/-- The actual reciprocal-radius coefficient satisfies the rational bound
used by the K131 normalized curvature comparison. -/
theorem gaussian_k131_reciprocal_le : gaussianK131Reciprocal ≤ 81 := by
  have hw := gaussian_k131_rh_coeff_mem
  unfold gaussianK131RhCoeff at hw
  have hp : (0 : ℝ) < 2 * (314159 / 100000) := by norm_num only
  have hw₀ := (le_div_iff₀ hp).mp hw.1
  rw [zero_mul] at hw₀
  have hw₁ := (div_le_iff₀ hp).mp hw.2
  have hlog : reciprocalLogLower ≤ 2 := by norm_num only [reciprocalLogLower]
  unfold gaussianK131Reciprocal
  linarith only [pole_cap, gamma_cap, hw₁, mul_le_mul_of_nonneg_left hlog hw₀]

/-- The reciprocal term of the K131 comparison contributes at most 7/50
to the normalized curvature on the whole bridge. -/
theorem gaussian_k131_reciprocal_curvature {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    logPowerPoly (-1 : ℝ) (logPowerCurvature 1 (Polynomial.C gaussianK131Reciprocal))
        (gaussianBridgeScale L) ≤
      7 / 50 := by
  exact k131_reciprocal_curvature_le gaussian_k131_reciprocal_le (gaussian_bridge_scale_mem hL).1

/-- With the analytic K131 coefficients fixed, the remaining scalar inputs
are the polynomial curvature budget and the two endpoint comparisons. -/
theorem gaussian_k131_gap_of_polynomials {ι : Type*} (s : Finset ι) (p : ι → ℝ)
    (P : ι → Polynomial ℝ) {L : ℝ} (hL : L ∈ Set.Icc (9055 / 4 : ℝ) 8000) :
    let a : ℝ := 465644807 / 400000
    let b : ℝ := 1036273 / 250
    let D := (81 / 100 : ℝ) * gaussianK131RecoveryVariation
    let G := fun y ↦
      (∑ i ∈ s, logPowerPoly (-p i) (P i) y) +
        (k131PrincipalError gaussianK131RhCoeff y +
          logPowerPoly (-(1 / 2 : ℝ)) (Polynomial.C (-D)) y)
    (∀ y ∈ Set.Ioo a b,
        (∑ i ∈ s, logPowerPoly (-p i) (logPowerCurvature (p i) (P i)) y) ≤ -43 / 50) →
      1 / 200 < G a → 1 / 200 < G b → 1 / 200 < G (gaussianBridgeScale L) := by
  exact
    k131_gap_of_poly_bounds s p P gaussian_k131_rh_coeff_mem
      (mul_nonneg (by norm_num only) gaussian_k131_recovery_nonneg) hL

end PseudoPrime.PrimeTestBounds.MillerRabin
