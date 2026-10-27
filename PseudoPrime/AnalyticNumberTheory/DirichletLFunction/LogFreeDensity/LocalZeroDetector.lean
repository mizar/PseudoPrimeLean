/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroPowerSums
public import PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity.LocalZeroCountBounds

/-! # Completed L-function local zero derivative detectors -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity

/--
Inputs: a natural local zero-count cap represented by the explicit ceiling formula and a bound on
the scale-weighted conductor-height logarithm.
Claim: the local cap is at most an absolute natural constant.
Proof: bound the ceiling argument by `1933` times the uniform local zero-count constant and use
monotonicity of `Nat.ceil`.
Role: turns the explicit local count into the uniform multiplicity input needed for an
`exp(-C₃K)` detector on bounded conductor-height ranges.
-/
theorem completedLFunction_local_zero_multiplicity_cap_le_fixed {q : ℕ} {η : ℝ} {t : ℝ} {C : ℕ}
    (hscale : η * Real.log ((q : ℝ) * (|t| + 3)) ≤ 3)
    (hC :
      C =
        Nat.ceil
          (completedZeroLocalLogBoundConstant * (1 + 644 * η * Real.log ((q : ℝ) * (|t| + 3))))) :
    C ≤ Nat.ceil (1933 * completedZeroLocalLogBoundConstant) := by
  rw [hC]
  apply Nat.ceil_le_ceil
  calc
    completedZeroLocalLogBoundConstant * (1 + 644 * η * Real.log ((q : ℝ) * (|t| + 3))) ≤
        completedZeroLocalLogBoundConstant * 1933 :=
      mul_le_mul_of_nonneg_left (by nlinarith only [hscale])
        completedZeroLocalLogBoundConstant_pos.le
    _ = 1933 * completedZeroLocalLogBoundConstant := by ring

/-- The fixed multiplicity cap valid when `η * log(q * (|t| + 3)) ≤ 3`. -/
noncomputable def completedLFunctionNearOneDetectorMultiplicityCap : ℕ :=
  Nat.ceil (1933 * completedZeroLocalLogBoundConstant)

/--
A fixed natural upper bound for the remote-tail order under a bounded scaled conductor-height
logarithm.
-/
noncomputable def completedGenusRemoteTailUniformOrderBound : ℕ :=
  Nat.ceil
      (72 *
        (((Nat.ceil (1933 * completedZeroLocalLogBoundConstant) + 1 : ℕ) : ℝ) *
          (4 * completedGenusMassShiftConstant + 11 +
            completedGenusMassCenterConstant * (Real.log 4 + 1)))) +
    3

/--
Inputs: a conductor at least two, a small positive shift, a height, a local count cutoff, and a
bound on the scale-weighted conductor-height logarithm.
Claim: the fixed-mass remote-tail cutoff is bounded by an absolute natural order and the requested
minimum order.
Proof: bound the local cutoff by its fixed multiplicity cap, then scale the inverse-square mass
expression by `η^2` and use the conductor-height logarithm bound.
Role: makes the remote-tail order uniform on the ranges used by the near-one zero detector.
-/
theorem completedGenusRemoteTailUniformCutoff_le_fixed {q : ℕ} [NeZero q] (hq : 2 ≤ q) {η : ℝ}
    (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (t : ℝ) (hscale : η * Real.log ((q : ℝ) * (|t| + 3)) ≤ 3)
    (C Kmin : ℕ)
    (hC :
      C =
        Nat.ceil
          (completedZeroLocalLogBoundConstant * (1 + 644 * η * Real.log ((q : ℝ) * (|t| + 3))))) :
    completedGenusRemoteTailUniformCutoff q η t ((C + 1 : ℕ) : ℝ) Kmin ≤
      max completedGenusRemoteTailUniformOrderBound Kmin := by
  let X : ℝ := (q : ℝ) * (|t| + 3)
  let U : ℝ := |t|
  let W : ℝ :=
    4 / η + completedGenusMassShiftConstant * (Real.log (4 + U) + 1) + Real.log q + 4 +
      completedGenusMassCenterConstant * (Real.log 4 + 1)
  let cap : ℕ := Nat.ceil (1933 * completedZeroLocalLogBoundConstant)
  let Nbound : ℝ := ((cap + 1 : ℕ) : ℝ)
  have hηle : η ≤ 1 := by nlinarith only [hηsmall]
  have hqcast : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hqpos : 0 < (q : ℝ) := lt_of_lt_of_le (by norm_num) hqcast
  have hXpos : 0 < X := by
    dsimp only [X]
    exact mul_pos hqpos (by positivity)
  have hqnonneg : 0 ≤ (q : ℝ) := le_of_lt hqpos
  have hU : 0 ≤ U := by simpa only [U] using abs_nonneg t
  have hqleX : (q : ℝ) ≤ X := by
    dsimp only [X, U]
    have hfactor : 1 ≤ |t| + 3 := by
      have hu : 0 ≤ |t| := abs_nonneg t
      linarith only [hu]
    calc
      (q : ℝ) = (q : ℝ) * 1 := by rw [mul_one]
      _ ≤ (q : ℝ) * (|t| + 3) := mul_le_mul_of_nonneg_left hfactor hqnonneg
  have h4leX : 4 + U ≤ X := by
    dsimp only [X, U]
    have hfactor : 4 + |t| ≤ 2 * (|t| + 3) := by nlinarith only [abs_nonneg t]
    calc
      4 + |t| ≤ 2 * (|t| + 3) := hfactor
      _ ≤ (q : ℝ) * (|t| + 3) := mul_le_mul_of_nonneg_right hqcast (by positivity)
  have hlogq : Real.log (q : ℝ) ≤ Real.log X :=
    Real.log_le_log (by exact_mod_cast (show 0 < q by omega)) hqleX
  have hlog4 : Real.log (4 + U) ≤ Real.log X := by
    dsimp only [U] at h4leX
    exact Real.log_le_log (by positivity) h4leX
  have hηlogq : η * Real.log (q : ℝ) ≤ 3 := by
    exact le_trans (mul_le_mul_of_nonneg_left hlogq hη.le) hscale
  have hηlog4 : η * (Real.log (4 + U) + 1) ≤ 4 := by
    have h := mul_le_mul_of_nonneg_left hlog4 hη.le
    have hlogplus : η * (Real.log (4 + U) + 1) ≤ η * Real.log X + η := by
      calc
        η * (Real.log (4 + U) + 1) = η * Real.log (4 + U) + η := by ring
        _ ≤ η * Real.log X + η := add_le_add h (le_refl η)
    nlinarith only [hlogplus, hscale, hηle]
  have hCcap : C ≤ cap := by
    dsimp only [cap]
    exact completedLFunction_local_zero_multiplicity_cap_le_fixed hscale hC
  have hN : ((C + 1 : ℕ) : ℝ) ≤ Nbound := by
    dsimp only [Nbound, cap]
    exact_mod_cast Nat.add_le_add_right hCcap 1
  have hA : 0 < completedGenusMassShiftConstant := by
    rw [show
        completedGenusMassShiftConstant =
          Classical.choose exists_uniform_norm_completed_logDeriv_small_shift_bound
        by rfl]
    exact (Classical.choose_spec exists_uniform_norm_completed_logDeriv_small_shift_bound).1
  have hB : 0 < completedGenusMassCenterConstant := by
    rw [show
        completedGenusMassCenterConstant =
          Classical.choose
            (exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only)
              (by norm_num only))
        by rfl]
    exact
      (Classical.choose_spec
          (exists_norm_completed_logDeriv_small_shift_bound (r := 1) (by norm_num only)
            (by norm_num only))).1
  have hAterm :
    completedGenusMassShiftConstant * (η * Real.log (4 + U) + η) ≤
      completedGenusMassShiftConstant * 4 :=
    mul_le_mul_of_nonneg_left (by nlinarith only [hηlog4]) hA.le
  have hlog4nonneg : 0 ≤ Real.log 4 + 1 := by
    have h := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith only [h]
  have hBfactor : η * (Real.log 4 + 1) ≤ Real.log 4 + 1 := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hηle hlog4nonneg
  have hBterm :
    completedGenusMassCenterConstant * (η * (Real.log 4 + 1)) ≤
      completedGenusMassCenterConstant * (Real.log 4 + 1) :=
    mul_le_mul_of_nonneg_left hBfactor hB.le
  have hfour : η * (4 / η) = 4 := by
    rw [div_eq_mul_inv]
    calc
      η * (4 * η⁻¹) = 4 * (η * η⁻¹) := by ring
      _ = 4 := by rw [mul_inv_cancel₀ (ne_of_gt hη), mul_one]
  have hidentity :
    η * W =
      η * (4 / η) + completedGenusMassShiftConstant * (η * Real.log (4 + U) + η) +
        η * Real.log (q : ℝ) +
        4 * η +
        completedGenusMassCenterConstant * (η * (Real.log 4 + 1)) := by
    dsimp only [W]
    ring
  have hmassη :
    η * W ≤
      4 * completedGenusMassShiftConstant + 11 +
        completedGenusMassCenterConstant * (Real.log 4 + 1) := by
    rw [hidentity, hfour]
    nlinarith only [hAterm, hBterm, hηlogq, hηle]
  have hcancel : η ^ 2 * ((1 / η) * W) = η * W := by
    rw [pow_two, one_div]
    calc
      η * η * (η⁻¹ * W) = η * (η * (η⁻¹ * W)) := by exact mul_assoc _ _ _
      _ = η * ((η * η⁻¹) * W) := by
        congr 1
        exact (mul_assoc _ _ _).symm
      _ = η * W := by rw [mul_inv_cancel₀ (ne_of_gt hη), one_mul]
  have hscaled :
    η ^ 2 * ((1 / η) * W) ≤
      4 * completedGenusMassShiftConstant + 11 +
        completedGenusMassCenterConstant * (Real.log 4 + 1) := by
    rw [hcancel]
    exact hmassη
  have hHnonneg :
    0 ≤
      4 * completedGenusMassShiftConstant + 11 +
        completedGenusMassCenterConstant * (Real.log 4 + 1) := by
    positivity
  have hbase :
    72 * ((C + 1 : ℕ) : ℝ) * ((1 / η) * W) * η ^ 2 ≤
      72 * Nbound *
        (4 * completedGenusMassShiftConstant + 11 +
          completedGenusMassCenterConstant * (Real.log 4 + 1)) := by
    calc
      72 * ((C + 1 : ℕ) : ℝ) * ((1 / η) * W) * η ^ 2 =
          72 * ((C + 1 : ℕ) : ℝ) * (η ^ 2 * ((1 / η) * W)) :=
        by ring
      _ ≤
          72 * ((C + 1 : ℕ) : ℝ) *
            (4 * completedGenusMassShiftConstant + 11 +
              completedGenusMassCenterConstant * (Real.log 4 + 1)) :=
        mul_le_mul_of_nonneg_left hscaled (by positivity)
      _ ≤
          72 * Nbound *
            (4 * completedGenusMassShiftConstant + 11 +
              completedGenusMassCenterConstant * (Real.log 4 + 1)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN (by norm_num)) hHnonneg
  have hceil :
    Nat.ceil (max (72 * ((C + 1 : ℕ) : ℝ) * ((1 / η) * W) * η ^ 2) 0) ≤
      Nat.ceil
        (72 * Nbound *
          (4 * completedGenusMassShiftConstant + 11 +
            completedGenusMassCenterConstant * (Real.log 4 + 1))) := by
    apply Nat.ceil_le_ceil
    exact max_le hbase (by positivity)
  have hfinal :
    Nat.ceil (max (72 * ((C + 1 : ℕ) : ℝ) * ((1 / η) * W) * η ^ 2) 0) + 3 ≤
      Nat.ceil
          (72 *
            (((cap + 1 : ℕ) : ℝ) *
              (4 * completedGenusMassShiftConstant + 11 +
                completedGenusMassCenterConstant * (Real.log 4 + 1)))) +
        3 := by
    calc
      _ ≤
          Nat.ceil
              (72 * Nbound *
                (4 * completedGenusMassShiftConstant + 11 +
                  completedGenusMassCenterConstant * (Real.log 4 + 1))) +
            3 :=
        Nat.add_le_add_right hceil 3
      _ = _ := by
        dsimp only [Nbound]; congr 1; congr 1; ring
  change
    max (Nat.ceil (max (72 * ((C + 1 : ℕ) : ℝ) * ((1 / η) * W) * η ^ 2) 0) + 3) Kmin ≤
      max
        (Nat.ceil
            (72 *
              (((Nat.ceil (1933 * completedZeroLocalLogBoundConstant) + 1 : ℕ) : ℝ) *
                (4 * completedGenusMassShiftConstant + 11 +
                  completedGenusMassCenterConstant * (Real.log 4 + 1)))) +
          3)
        Kmin
  exact max_le_max hfinal le_rfl

/-- The fixed exponential loss associated with the completed near-one detector cap. -/
noncomputable def completedLFunctionNearOneDetectorExponent : ℝ :=
  (completedLFunctionNearOneDetectorMultiplicityCap : ℝ) * Real.log 3 +
    Real.log (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1))

/-- The fixed exponential loss after transferring the detector to the ordinary `L` function. -/
noncomputable def ordinaryLFunctionNearOneDetectorExponent : ℝ :=
  completedLFunctionNearOneDetectorExponent + Real.log 2 / 2

/--
Inputs: a nonnegative order-independent constant in the gamma-factor derivative estimate.
Claim: beyond some natural order, the normalized gamma correction is less than half the fixed
local zero signal, using the uniform multiplicity cap.
Proof: the ratio is bounded by a fixed multiple of `(3 / 322)^n`, which tends to zero.
Role: supplies the order threshold needed to absorb the gamma factor in the ordinary `L`-function
detector.
-/
theorem exists_order_threshold_for_uniform_gamma_absorption (G : ℝ) :
    ∃ n₀ : ℕ,
      ∀ n : ℕ,
        n₀ ≤ n →
          192 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G *
              ((3 : ℝ) / 322) ^ n <
            1 := by
  let A : ℝ := 192 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G
  have hpow : Filter.Tendsto (fun n : ℕ => ((3 : ℝ) / 322) ^ n) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  have hlim : Filter.Tendsto (fun n : ℕ => A * ((3 : ℝ) / 322) ^ n) Filter.atTop (nhds 0) := by
    simpa only [mul_zero] using hpow.const_mul A
  have hev := hlim.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rcases Filter.eventually_atTop.mp hev with ⟨n₀, hn₀⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  have h := hn₀ n hn
  simpa only [A] using h

/-- The explicit order cutoff that absorbs the uniform gamma-factor correction. -/
noncomputable def uniformGammaAbsorptionOrderCutoff (G : ℝ) : ℕ :=
  Nat.ceil
      (max (3 * (192 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G) / 319) 0) +
    1

/--
Inputs: the nonnegative-order-independent gamma-factor constant and an order above the cutoff.
Claim: the normalized gamma correction is strictly smaller than the fixed local zero signal.
Proof: Bernoulli's inequality bounds `(3/322)^n` by the reciprocal of a linear function of `n`;
the ceiling cutoff makes its denominator larger than the correction coefficient.
Role: makes the gamma-absorption order in the ordinary derivative detector explicit.
-/
theorem explicit_uniform_gamma_absorption_order_bound (G : ℝ) :
    ∀ n : ℕ,
      uniformGammaAbsorptionOrderCutoff G ≤ n →
        192 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G *
            ((3 : ℝ) / 322) ^ n <
          1 := by
  let A : ℝ := 192 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G
  let B : ℝ := 3 * A / 319
  let Bpos : ℝ := max B 0
  intro n hn
  have hceil : Bpos ≤ (Nat.ceil Bpos : ℝ) := Nat.le_ceil Bpos
  have hnceil : (Nat.ceil Bpos : ℝ) < n := by
    have hn' : Nat.ceil Bpos + 1 ≤ n := by
      simpa only [uniformGammaAbsorptionOrderCutoff, A, B, Bpos] using hn
    exact_mod_cast (show Nat.ceil Bpos < n by omega)
  have hBposn : Bpos < (n : ℝ) := lt_of_le_of_lt hceil hnceil
  have hB : B ≤ Bpos := le_max_left _ _
  have hA : A = (319 / 3 : ℝ) * B := by
    dsimp only [B]
    ring
  have hAupper : A ≤ (319 / 3 : ℝ) * Bpos := hA ▸ mul_le_mul_of_nonneg_left hB (by norm_num)
  have hgeo : 1 + (319 : ℝ) / 3 * n ≤ (322 / 3 : ℝ) ^ n := by
    have h := Real.mul_add_one_le_add_one_pow (a := (319 : ℝ) / 3) (by positivity) n
    have hbase : (319 : ℝ) / 3 + 1 = 322 / 3 := by norm_num
    rw [hbase] at h
    simpa only [add_comm] using h
  have hden : 0 < 1 + (319 : ℝ) / 3 * n := by positivity
  have hpow : ((3 : ℝ) / 322) ^ n ≤ 1 / (1 + (319 : ℝ) / 3 * n) := by
    apply (le_div_iff₀ hden).2
    calc
      ((3 : ℝ) / 322) ^ n * (1 + (319 : ℝ) / 3 * n) ≤ ((3 : ℝ) / 322) ^ n * (322 / 3 : ℝ) ^ n :=
        mul_le_mul_of_nonneg_left hgeo (by positivity)
      _ = 1 := by
        rw [← mul_pow]; norm_num
  have hratio : 0 ≤ ((3 : ℝ) / 322) ^ n := by positivity
  have hcoef : 0 ≤ (319 / 3 : ℝ) * Bpos := by positivity
  have hmajor : A * ((3 : ℝ) / 322) ^ n ≤ ((319 / 3 : ℝ) * Bpos) / (1 + (319 : ℝ) / 3 * n) := by
    calc
      A * ((3 : ℝ) / 322) ^ n ≤ ((319 / 3 : ℝ) * Bpos) * ((3 : ℝ) / 322) ^ n :=
        mul_le_mul_of_nonneg_right hAupper hratio
      _ ≤ ((319 / 3 : ℝ) * Bpos) * (1 / (1 + (319 : ℝ) / 3 * n)) :=
        mul_le_mul_of_nonneg_left hpow hcoef
      _ = _ := by ring
  have hnum : (319 / 3 : ℝ) * Bpos < 1 + (319 : ℝ) / 3 * n := by
    have h := mul_lt_mul_of_pos_left hBposn (by norm_num : (0 : ℝ) < 319 / 3)
    nlinarith only [h]
  have hfrac : ((319 / 3 : ℝ) * Bpos) / (1 + (319 : ℝ) / 3 * n) < 1 := (div_lt_one hden).2 hnum
  simpa only [A] using lt_of_le_of_lt hmajor hfrac

/--
Inputs: a small positive scale, a conductor-height logarithm bound, and an order satisfying the
uniform gamma-absorption threshold.
Claim: the normalized gamma-factor derivative correction is at most half the fixed local detector
signal at that order.
Proof: compare `log (4 * |t| + 4)` with the conductor-height logarithm, then use
`12 * η ≤ 3 / 322` and the threshold inequality.
Role: converts the order threshold into a positive ordinary `L`-function derivative bound.
-/
theorem normalized_gamma_correction_le_half_detector {η t G : ℝ} {q : ℕ} (hq : 2 ≤ q) (hη : 0 < η)
    (hηsmall : η ≤ 1 / 1288) (hscale : η * Real.log ((q : ℝ) * (|t| + 3)) ≤ 3) (hG : 0 ≤ G) (n : ℕ)
    (hthreshold :
      192 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G * ((3 : ℝ) / 322) ^ n <
        1) :
    G * η ^ (n + 1) * (Real.log (4 * |t| + 4) + 1) * 4 ^ n ≤
      (1 / (16 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1))) *
        (1 / (3 : ℝ)) ^ (n + 1) := by
  let cap : ℝ := completedLFunctionNearOneDetectorMultiplicityCap
  let u : ℝ := |t|
  have hu : 0 ≤ u := by
    dsimp only [u]; positivity
  have hqcast : (2 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hQpos : 0 < (q : ℝ) * (u + 3) := by positivity
  have hargpos : 0 < 4 * u + 4 := by positivity
  have hargle : 4 * u + 4 ≤ 2 * ((q : ℝ) * (u + 3)) := by nlinarith only [hu, hqcast]
  have hlog := Real.log_le_log hargpos hargle
  rw [Real.log_mul (by norm_num only : (2 : ℝ) ≠ 0) (ne_of_gt hQpos)] at hlog
  have hlog2raw := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num only)
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    simpa only [show (2 : ℝ) - 1 = 1 by norm_num only] using hlog2raw
  have hηlog2 : η * Real.log 2 ≤ η := by
    calc
      η * Real.log 2 ≤ η * 1 := mul_le_mul_of_nonneg_left hlog2 hη.le
      _ = η := by rw [mul_one]
  have hscale' : η * Real.log ((q : ℝ) * (u + 3)) ≤ 3 := by simpa only [u] using hscale
  have hηlogarg : η * (Real.log (4 * u + 4) + 1) ≤ 4 := by
    calc
      η * (Real.log (4 * u + 4) + 1) ≤ η * (Real.log 2 + Real.log ((q : ℝ) * (u + 3)) + 1) := by
        exact mul_le_mul_of_nonneg_left (by linarith only [hlog]) hη.le
      _ = η * Real.log 2 + η * Real.log ((q : ℝ) * (u + 3)) + η := by ring
      _ ≤ η + 3 + η := by nlinarith only [hηlog2, hscale']
      _ ≤ 4 := by nlinarith only [hηsmall]
  have hbase : 12 * η ≤ (3 : ℝ) / 322 := by nlinarith only [hηsmall]
  have hpow : (12 * η) ^ n ≤ ((3 : ℝ) / 322) ^ n := pow_le_pow_left₀ (by positivity) hbase n
  have hcoef : 48 * (cap + 1) * G * (η * (Real.log (4 * u + 4) + 1)) ≤ 192 * (cap + 1) * G := by
    calc
      48 * (cap + 1) * G * (η * (Real.log (4 * u + 4) + 1)) ≤ 48 * (cap + 1) * G * 4 :=
        mul_le_mul_of_nonneg_left hηlogarg (by positivity)
      _ = 192 * (cap + 1) * G := by ring
  have hthreshold' : 192 * (cap + 1) * G * ((3 : ℝ) / 322) ^ n < 1 := by
    simpa only [cap] using hthreshold
  have hpow34 : (3 : ℝ) ^ n * 4 ^ n = (12 : ℝ) ^ n := by
    calc
      (3 : ℝ) ^ n * 4 ^ n = (3 * 4) ^ n := by rw [← mul_pow]
      _ = (12 : ℝ) ^ n := by norm_num only
  have hpoweta : (12 : ℝ) ^ n * η ^ n = (12 * η) ^ n := by rw [← mul_pow]
  have hratio :
    16 * (cap + 1) * (3 : ℝ) ^ (n + 1) * (G * η ^ (n + 1) * (Real.log (4 * u + 4) + 1) * 4 ^ n) <
      1 := by
    calc
      _ =
          16 * (cap + 1) * ((3 : ℝ) ^ n * 3) *
            (G * (η ^ n * η) * (Real.log (4 * u + 4) + 1) * 4 ^ n) :=
        by rw [pow_succ, pow_succ]
      _ = 48 * (cap + 1) * G * (η * (Real.log (4 * u + 4) + 1)) * (3 ^ n * 4 ^ n * η ^ n) := by ring
      _ = 48 * (cap + 1) * G * (η * (Real.log (4 * u + 4) + 1)) * (12 ^ n * η ^ n) := by rw [hpow34]
      _ = 48 * (cap + 1) * G * (η * (Real.log (4 * u + 4) + 1)) * (12 * η) ^ n := by rw [hpoweta]
      _ ≤ 192 * (cap + 1) * G * ((3 : ℝ) / 322) ^ n := by
        calc
          _ ≤ 192 * (cap + 1) * G * (12 * η) ^ n := mul_le_mul_of_nonneg_right hcoef (by positivity)
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ < 1 := hthreshold'
  have hdenpos : 0 < 16 * (cap + 1) * (3 : ℝ) ^ (n + 1) := by positivity
  have herr :
    G * η ^ (n + 1) * (Real.log (4 * u + 4) + 1) * 4 ^ n <
      1 / (16 * (cap + 1) * (3 : ℝ) ^ (n + 1)) := by
    apply (lt_div_iff₀ hdenpos).2
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hratio
  have hcappos : cap + 1 ≠ 0 := by positivity
  have h3ne : (3 : ℝ) ≠ 0 := by norm_num only
  have hpow3 : (1 / (3 : ℝ)) ^ (n + 1) * (3 : ℝ) ^ (n + 1) = 1 := by
    rw [← mul_pow]
    norm_num only
    simp only [one_pow]
  have hden :
    1 / (16 * (cap + 1) * (3 : ℝ) ^ (n + 1)) =
      (1 / (16 * (cap + 1))) * (1 / (3 : ℝ)) ^ (n + 1) := by
    field_simp [hcappos, h3ne]
    rw [mul_comm]
    exact hpow3.symm
  have hstrict :
    G * η ^ (n + 1) * (Real.log (4 * u + 4) + 1) * 4 ^ n <
      (1 / (16 * (cap + 1))) * (1 / (3 : ℝ)) ^ (n + 1) := by
    calc
      _ < 1 / (16 * (cap + 1) * (3 : ℝ) ^ (n + 1)) := herr
      _ = _ := hden
  exact le_of_lt (by simpa only [cap, u] using hstrict)

/--
Inputs: a local multiplicity cap and a derivative exponent bounded by a fixed multiple of the
block's lower order.
Claim: the normalized detector scale is bounded below by an explicit exponential in the block
parameter.
Proof: take logarithms of the reciprocal scale and use the cap and exponent bounds.
Role: supplies the exponential form required by the positive zero-detection contract.
-/
theorem local_detector_scale_ge_exp_neg {Cmax C K m : ℕ} (hC : C ≤ Cmax) (hK : 1 ≤ K)
    (hm : m ≤ K * C) :
    Real.exp (-((Cmax : ℝ) * Real.log 3 + Real.log (8 * ((Cmax : ℝ) + 1))) * (K : ℝ)) ≤
      (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m := by
  have htargetPos : 0 < (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m := by positivity
  have hlogTarget :
    Real.log ((1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m) =
      -Real.log (8 * ((C : ℝ) + 1)) - (m : ℝ) * Real.log 3 := by
    rw [Real.log_mul (by positivity) (by positivity), one_div, Real.log_inv, Real.log_pow, one_div,
      Real.log_inv]
    ring
  have hCcast : (C : ℝ) + 1 ≤ (Cmax : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hC 1
  have hden : 8 * ((C : ℝ) + 1) ≤ 8 * ((Cmax : ℝ) + 1) := by nlinarith only [hCcast]
  have hlogDenLe : Real.log (8 * ((C : ℝ) + 1)) ≤ Real.log (8 * ((Cmax : ℝ) + 1)) :=
    Real.log_le_log (by positivity) hden
  have hlogDenPos : 0 < Real.log (8 * ((Cmax : ℝ) + 1)) :=
    Real.log_pos
      (by
        have hnonneg : 0 ≤ (Cmax : ℝ) := by positivity
        nlinarith only [hnonneg])
  have hlog3Pos : 0 < Real.log 3 := Real.log_pos (by norm_num only)
  have hKreal : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hmC : m ≤ K * Cmax := Nat.le_trans hm (Nat.mul_le_mul_left K hC)
  have hmCReal : (m : ℝ) ≤ (K : ℝ) * (Cmax : ℝ) := by exact_mod_cast hmC
  have hnumProduct := mul_le_mul_of_nonneg_right hmCReal hlog3Pos.le
  have hdenProduct := mul_le_mul_of_nonneg_right hKreal hlogDenPos.le
  rw [← Real.exp_log htargetPos]
  apply Real.exp_le_exp.mpr
  calc
    -((Cmax : ℝ) * Real.log 3 + Real.log (8 * ((Cmax : ℝ) + 1))) * (K : ℝ) =
        -((K : ℝ) * (Cmax : ℝ)) * Real.log 3 - (K : ℝ) * Real.log (8 * ((Cmax : ℝ) + 1)) :=
      by ring
    _ ≤ -Real.log (8 * ((C : ℝ) + 1)) - (m : ℝ) * Real.log 3 := by
      have hnum : -((K : ℝ) * (Cmax : ℝ)) * Real.log 3 ≤ -(m : ℝ) * Real.log 3 := by
        nlinarith only [hnumProduct]
      have hdenPart :
        -(K : ℝ) * Real.log (8 * ((Cmax : ℝ) + 1)) ≤ -Real.log (8 * ((C : ℝ) + 1)) := by
        nlinarith only [hdenProduct, hlogDenLe]
      linarith only [hnum, hdenPart]
    _ = Real.log ((1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m) := by rw [hlogTarget]

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function with a near-one zero, a
nonzero center to its right, and a bounded scale-weighted conductor-height logarithm.
Claim: a positive order `n` exists in a fixed-multiple block, and its normalized completed
logarithmic derivative is at least `exp(-D K)` for an absolute `D`.
Proof: use the explicit local multiplicity ceiling, the local-plus-remote power-sum comparison,
and the logarithmic conversion of its reciprocal scale into an exponential.
Role: gives the completed-function exponential detector under the bounded conductor-height
condition used by the later zero-density argument.
-/
theorem exists_completedLFunction_logDeriv_exp_detector_on_log_scale {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) {c ρ : ℂ} (hcre : c.re = 1 + η)
    (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ K m n : ℕ,
      2 ≤ K ∧
        0 < n ∧
        n + 1 = m ∧
        K ≤ m ∧
        m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
        Real.exp (-(completedLFunctionNearOneDetectorExponent * (K : ℝ))) ≤
          (η ^ (n + 1) / (n.factorial : ℝ)) *
            ‖iteratedDeriv n (fun z : ℂ => logDeriv χ.completedLFunction z) c‖ := by
  obtain ⟨_, _, _, _, C, K, m, n, _, _, hK, _, hn, hnm, hmK, hmKC, hraw, hnorm, hCeq⟩ :=
    exists_completedLFunction_iteratedDeriv_logDeriv_lower_bound_near_one_zero hq hχ hp hinv hη
      hηsmall 2 (by norm_num) hcre hcim hρre hzero hc
  have hCcap := completedLFunction_local_zero_multiplicity_cap_le_fixed hscale hCeq
  have hmCap : m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap :=
    hmKC.trans (Nat.mul_le_mul_left K hCcap)
  have hscaleExp := local_detector_scale_ge_exp_neg hCcap (by omega) hmKC
  refine ⟨K, m, n, hK, hn, hnm, hmK, hmCap, ?_⟩
  calc
    Real.exp (-(completedLFunctionNearOneDetectorExponent * (K : ℝ))) ≤
        (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m :=
      by
      simpa only [completedLFunctionNearOneDetectorExponent,
        completedLFunctionNearOneDetectorMultiplicityCap, neg_mul] using hscaleExp
    _ ≤
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          ‖iteratedDeriv n (fun z : ℂ => logDeriv χ.completedLFunction z) c‖ :=
      hnorm

/--
Inputs: a near-one zero, a nonzero completed-function center, and a height bound.
Claim: the ordinary Dirichlet L-function derivative is bounded below by the completed-function
zero signal minus an explicit uniform gamma-factor error.
Proof: combine the completed logarithmic-derivative lower bound with the Cauchy estimate for
iterated derivatives of the gamma factor.
Role: expresses the detector in the ordinary derivative form used by Euler-series estimates,
while keeping the correction term visible for its later quantitative absorption.
-/
theorem exists_completedLFunction_detector_transfer_to_LFunction {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Kmin : ℕ) (hKmin : 2 ≤ Kmin) {c ρ : ℂ}
    (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) (G : ℝ)
    (hgamma :
      ∀ n : ℕ,
        ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
          χ ≠ 1 →
            ∀ {s : ℂ} {T : ℝ},
              1 < s.re →
                1 ≤ s.re →
                s.re ≤ 5 / 4 →
                0 ≤ T →
                |s.im| ≤ T →
                ∀ {A : ℝ},
                  A ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) s‖ →
                    A - (n.factorial : ℝ) * G * (Real.log (4 * T + 4) + 1) / (1 / 4 : ℝ) ^ n ≤
                      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖)
    {T : ℝ} (hT : 0 ≤ T) (hheight : |ρ.im| ≤ T) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ C K m n : ℕ,
          Kmin ≤ K ∧
            K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
            K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
            2 ≤ K ∧
            0 < n ∧
            n + 1 = m ∧
            K ≤ m ∧
            m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
            C =
              Nat.ceil
                (completedZeroLocalLogBoundConstant *
                  (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
            ((1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
                (n.factorial : ℝ) * G * (Real.log (4 * T + 4) + 1) / (1 / 4 : ℝ) ^ n) ≤
              ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, C, K, m, n, hKmin', hKupper, hK, _, hn, hnm,
      hmK, hmKC, hraw, _, hCeq⟩ :=
    exists_completedLFunction_iteratedDeriv_logDeriv_lower_bound_near_one_zero hq hχ hp hinv hη
      hηsmall Kmin hKmin hcre hcim hρre hzero hc
  have hCcap := completedLFunction_local_zero_multiplicity_cap_le_fixed hscale hCeq
  have hmCap : m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap :=
    hmKC.trans (Nat.mul_le_mul_left K hCcap)
  have hheight' : |c.im| ≤ T := by simpa only [hcim] using hheight
  have hcreLo : 1 ≤ c.re := by
    rw [hcre]; linarith only [hη]
  have hcreHi : c.re ≤ 5 / 4 := by
    rw [hcre]
    nlinarith only [hηsmall]
  let A : ℝ := (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ)
  have hA : A ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) c‖ := by
    simpa only [A] using hraw
  have hordinary :=
    hgamma n hχ
      (by
        rw [hcre]; linarith only [hη])
      hcreLo hcreHi hT hheight' (A := A) hA
  have hKupper' : K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C + 1 : ℕ) : ℝ) Kmin := by
    simpa only [Nat.cast_add, Nat.cast_one] using hKupper
  have hKupperFixed :=
    hKupper'.trans
      (completedGenusRemoteTailUniformCutoff_le_fixed hq hη hηsmall ρ.im hscale C Kmin hCeq)
  refine
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, C, K, m, n, hKmin', hKupper, hKupperFixed,
      hK, hn, hnm, hmK, hmCap, hCeq, ?_⟩
  simpa only [A] using hordinary

/--
Inputs: a primitive nonprincipal character, a completed-function zero close to one, a bounded
conductor-height logarithm, and a requested minimum block order.
Claim: a block order at least the requested minimum contains an iterate whose ordinary Dirichlet
`L` logarithmic-derivative norm is positive, with the order range controlled by the fixed local
multiplicity cap and remote-tail order bounded uniformly, and its normalized norm has an explicit
exponential lower bound.
Proof: raise the block minimum above both the requested order and the uniform gamma-absorption
threshold, then transfer the completed zero signal to the ordinary `L` function and absorb the
factor of one half into the exponential loss.
Role: supplies a scale-selectable positive ordinary-derivative detector for later density work.
-/
theorem exists_completedLFunction_positive_LFunction_logDeriv_iterate {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ) (hKrequested : 2 ≤ Krequested)
    {c ρ : ℂ} (hcre : c.re = 1 + η) (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ Kmin : ℕ,
          ∃ C K m n : ℕ,
            Krequested ≤ K ∧
              K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
              K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
              Kmin ≤ K ∧
              2 ≤ K ∧
              0 < n ∧
              n + 1 = m ∧
              K ≤ m ∧
              m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
              C =
                Nat.ceil
                  (completedZeroLocalLogBoundConstant *
                    (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
              0 < ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ ∧
              Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) ≤
                (η ^ (n + 1) / (n.factorial : ℝ)) *
                  ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
  obtain ⟨G, hG, hgamma⟩ := exists_uniform_gamma_subtraction_for_ordinary_LFunction_derivative_all
  let n₀ := uniformGammaAbsorptionOrderCutoff G
  have hn₀ := explicit_uniform_gamma_absorption_order_bound G
  let Kmin : ℕ := max (n₀ + 1) Krequested
  have hKmin : 2 ≤ Kmin := by
    dsimp only [Kmin]; omega
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, C, K, m, n, hKmin', hKupper, hKupperFixed,
      hK, hn, hnm, hmK, hmCap, hCeq, hordinary⟩ :=
    exists_completedLFunction_detector_transfer_to_LFunction hq hχ hp hinv hη hηsmall Kmin hKmin
      hcre hcim hρre hzero hc hscale G hgamma (T := |ρ.im|) (abs_nonneg ρ.im) (le_rfl)
  have hCcap := completedLFunction_local_zero_multiplicity_cap_le_fixed hscale hCeq
  have hKlarge : n₀ ≤ n := by
    have hthreshold : n₀ + 1 ≤ K := by exact le_trans (le_max_left _ _) hKmin'
    omega
  have hηlog : η * (Real.log (4 * |ρ.im| + 4) + 1) ≤ 4 := by
    let Q : ℝ := (q : ℝ) * (|ρ.im| + 3)
    have hQ : 0 < Q := by
      dsimp only [Q]; positivity
    have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    have habs : 0 ≤ |ρ.im| := abs_nonneg ρ.im
    have hQbound : |ρ.im| + 1 ≤ Q := by
      dsimp only [Q]
      calc
        |ρ.im| + 1 ≤ (q : ℝ) * (|ρ.im| + 1) := by
          have := mul_le_mul_of_nonneg_right hqreal (show 0 ≤ |ρ.im| + 1 by positivity)
          simpa only [one_mul] using this
        _ ≤ (q : ℝ) * (|ρ.im| + 3) := mul_le_mul_of_nonneg_left (by nlinarith only) (by positivity)
    have harg : 4 * |ρ.im| + 4 ≤ 4 * Q := by nlinarith only [hQbound]
    have hlog : Real.log (4 * |ρ.im| + 4) ≤ Real.log (4 * Q) := Real.log_le_log (by positivity) harg
    have hlogMul : Real.log (4 * Q) = Real.log 4 + Real.log Q := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hQ)]
    have hlog4 : Real.log 4 ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      nlinarith only [h]
    have hηlog4 : η * (Real.log 4 + 1) ≤ 1 := by
      have hfour : Real.log 4 + 1 ≤ 4 := by linarith only [hlog4]
      have hmul := mul_le_mul_of_nonneg_left hfour (le_of_lt hη)
      nlinarith only [hmul, hηsmall]
    have hlogPlus : Real.log (4 * |ρ.im| + 4) + 1 ≤ Real.log (4 * Q) + 1 := by linarith only [hlog]
    calc
      η * (Real.log (4 * |ρ.im| + 4) + 1) ≤ η * (Real.log (4 * Q) + 1) :=
        mul_le_mul_of_nonneg_left hlogPlus (le_of_lt hη)
      _ = η * Real.log Q + η * (Real.log 4 + 1) := by
        rw [hlogMul]; ring
      _ ≤ 3 + 1 := add_le_add (by simpa only [Q] using hscale) hηlog4
      _ = 4 := by norm_num
  let S : ℝ := (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m
  let E : ℝ := G * η * (Real.log (4 * |ρ.im| + 4) + 1) * (4 * η) ^ n
  let R : ℝ := 24 * ((C : ℝ) + 1) * G * (η * (Real.log (4 * |ρ.im| + 4) + 1)) * (12 * η) ^ n
  have hS : 0 < S := by
    dsimp only [S]; positivity
  have hηL : 0 ≤ η * (Real.log (4 * |ρ.im| + 4) + 1) := by
    have hlognonneg : 0 ≤ Real.log (4 * |ρ.im| + 4) :=
      Real.log_nonneg (by nlinarith only [abs_nonneg ρ.im])
    positivity
  have hη12 : 0 ≤ 12 * η := by positivity
  have hη12le : 12 * η ≤ (3 : ℝ) / 322 := by nlinarith only [hηsmall]
  have hpow : (12 * η) ^ n ≤ ((3 : ℝ) / 322) ^ n := pow_le_pow_left₀ hη12 hη12le n
  have hCcast : (C : ℝ) + 1 ≤ (completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hCcap 1
  have hcoeff :
    24 * ((C : ℝ) + 1) * G * (η * (Real.log (4 * |ρ.im| + 4) + 1)) ≤
      96 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G := by
    have hbase :
      24 * ((C : ℝ) + 1) * G ≤
        24 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G := by
      exact mul_le_mul_of_nonneg_right (by nlinarith only [hCcast]) (by positivity)
    calc
      _ = (24 * ((C : ℝ) + 1) * G) * (η * (Real.log (4 * |ρ.im| + 4) + 1)) := by ring
      _ ≤
          (24 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G) *
            (η * (Real.log (4 * |ρ.im| + 4) + 1)) :=
        mul_le_mul_of_nonneg_right hbase hηL
      _ ≤ (24 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G) * 4 :=
        mul_le_mul_of_nonneg_left hηlog (by positivity)
      _ = _ := by ring
  have hratio : R ≤ 1 / 2 := by
    have hsmall := hn₀ n hKlarge
    have hsmall' :
      96 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G * ((3 : ℝ) / 322) ^ n ≤
        1 / 2 := by
      nlinarith only [hsmall]
    calc
      R ≤
          96 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G *
            ((3 : ℝ) / 322) ^ n :=
        by
        dsimp only [R]
        calc
          _ ≤
              (96 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G) *
                (12 * η) ^ n :=
            by apply mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hη12 n)
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 1 / 2 := hsmall'
  have hpowSignal : (12 * η) ^ n * (1 / 3 : ℝ) ^ (n + 1) = (4 * η) ^ n / 3 := by
    have hmulPow : (12 * η) ^ n * (1 / 3 : ℝ) ^ n = (4 * η) ^ n := by
      calc
        _ = (12 * η * (1 / 3 : ℝ)) ^ n := by rw [← mul_pow]
        _ = _ := by
          congr 1; ring
    rw [pow_succ, ← mul_assoc, hmulPow]
    ring
  have hEeq : E = R * S := by
    calc
      E = G * η * (Real.log (4 * |ρ.im| + 4) + 1) * (4 * η) ^ n := by rfl
      _ =
          (24 * ((C : ℝ) + 1) * G * (η * (Real.log (4 * |ρ.im| + 4) + 1)) / (8 * ((C : ℝ) + 1))) *
            ((4 * η) ^ n / 3) :=
        by
        field_simp [ne_of_gt (show 0 < 8 * ((C : ℝ) + 1) by positivity)]
        ring
      _ =
          (24 * ((C : ℝ) + 1) * G * (η * (Real.log (4 * |ρ.im| + 4) + 1)) / (8 * ((C : ℝ) + 1))) *
            ((12 * η) ^ n * (1 / 3 : ℝ) ^ (n + 1)) :=
        by rw [hpowSignal]
      _ = R * S := by
        dsimp only [R, S]
        rw [← hnm, pow_succ]
        ring
  have hEleS : E ≤ S / 2 := by
    calc
      E = R * S := hEeq
      _ ≤ (1 / 2 : ℝ) * S := mul_le_mul_of_nonneg_right hratio hS.le
      _ = S / 2 := by ring
  let F : ℝ := (n.factorial : ℝ) / η ^ m
  have hF : 0 < F := by
    dsimp only [F]; positivity
  have hsignalEq : (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) = F * S := by
    dsimp only [F, S]
    have hpowEta : (1 / (3 * η) : ℝ) ^ m = (η⁻¹) ^ m * (1 / 3 : ℝ) ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp [ne_of_gt hη]
    rw [hpowEta]
    field_simp [ne_of_gt hη, ne_of_gt (show 0 < 8 * ((C : ℝ) + 1) by positivity)]
    rw [← mul_pow]
    have hcancel : (1 / η : ℝ) * η = 1 := by field_simp [ne_of_gt hη]
    rw [hcancel, one_pow]
  have herrorEq :
    (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n = F * E := by
    dsimp only [F, E]
    rw [← hnm]
    have hquarter : ((1 / 4 : ℝ) ^ n)⁻¹ = (4 : ℝ) ^ n := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
    have hpow4 : (4 * η) ^ n = (4 : ℝ) ^ n * η ^ n := by rw [mul_pow]
    rw [div_eq_mul_inv, hquarter, hpow4, pow_succ]
    field_simp [ne_of_gt hη, show (1 / 4 : ℝ) ≠ 0 by norm_num]
  have hrawEq :
    (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
        (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n =
      F * (S - E) := by
    rw [hsignalEq, herrorEq]
    ring
  have hrawPositive :
    0 <
      (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
        (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n := by
    rw [hrawEq]
    apply mul_pos hF
    have hSpos : 0 < S / 2 := by positivity
    exact lt_of_lt_of_le hSpos (by linarith only [hEleS])
  have hKrequested' : Krequested ≤ K := le_trans (le_max_right _ _) hKmin'
  let A : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  have hA : 0 < A := by
    dsimp only [A]; positivity
  have hAF : A * F = 1 := by
    dsimp only [A, F]
    rw [hnm]
    field_simp [ne_of_gt hη, show (n.factorial : ℝ) ≠ 0 by positivity]
  have hscaledRaw :
    A *
        ((1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
          (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n) =
      S - E := by
    rw [hrawEq, ← mul_assoc, hAF, one_mul]
  have hscaledLower :
    S / 2 ≤ A * ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
    calc
      S / 2 ≤ S - E := by linarith only [hEleS]
      _ =
          A *
            ((1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
              (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n) :=
        hscaledRaw.symm
      _ ≤ A * ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ :=
        mul_le_mul_of_nonneg_left hordinary hA.le
  have hcompletedExp :=
    local_detector_scale_ge_exp_neg (C := completedLFunctionNearOneDetectorMultiplicityCap) (Cmax :=
      completedLFunctionNearOneDetectorMultiplicityCap) (K := K) (m := m) (Nat.le_refl _) (by omega)
      hmCap
  let Sbase : ℝ :=
    (1 / (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1))) * (1 / 3 : ℝ) ^ m
  have hSbase : Sbase ≤ S := by
    have hden :
      8 * ((C : ℝ) + 1) ≤ 8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) := by
      nlinarith only [hCcast]
    have hinv :
      1 / (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1)) ≤
        1 / (8 * ((C : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) hden
    dsimp only [Sbase, S]
    exact mul_le_mul_of_nonneg_right hinv (by positivity)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only)
  have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hexpHalf : Real.exp (-((Real.log 2 / 2) * (K : ℝ))) ≤ 1 / 2 := by
    have harg : -((Real.log 2 / 2) * (K : ℝ)) ≤ -Real.log 2 := by nlinarith only [hlog2, hKreal]
    have h := Real.exp_le_exp.mpr harg
    have hExpLog : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hExpLog] at h
    exact h
  have hExpIdentity :
    Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) =
      Real.exp (-(completedLFunctionNearOneDetectorExponent * (K : ℝ))) *
        Real.exp (-((Real.log 2 / 2) * (K : ℝ))) := by
    change Real.exp (-((completedLFunctionNearOneDetectorExponent + Real.log 2 / 2) * (K : ℝ))) = _
    rw [add_mul, neg_add, Real.exp_add]
  have hnormalized :
    Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) ≤
      A * ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
    rw [hExpIdentity]
    calc
      _ ≤ Sbase * (1 / 2 : ℝ) := by
        have hcompletedExp' :
          Real.exp (-(completedLFunctionNearOneDetectorExponent * (K : ℝ))) ≤ Sbase := by
          have harg :
            -(completedLFunctionNearOneDetectorExponent * (K : ℝ)) =
              -((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) * Real.log 3 +
                    Real.log (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1))) *
                (K : ℝ) := by
            dsimp only [completedLFunctionNearOneDetectorExponent]
            ring
          rw [harg]
          simpa only [Sbase] using hcompletedExp
        exact mul_le_mul hcompletedExp' hexpHalf (by positivity) (by positivity)
      _ ≤ S / 2 := by linarith only [hSbase]
      _ ≤ A * ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := hscaledLower
  exact
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, hKrequested', hKupper,
      hKupperFixed, hKmin', hK, hn, hnm, hmK, hmCap, hCeq, lt_of_lt_of_le hrawPositive hordinary,
      hnormalized⟩

/--
Inputs: a primitive nonprincipal character, a near-one completed-function zero, a bounded
conductor-height scale, and a fixed uniform gamma-factor derivative bound.
Claim: a positive ordinary logarithmic-derivative iterate exists with an order bounded using only
the shared gamma constant, the requested minimum order, and the fixed local multiplicity cap.
Proof: apply the completed zero detector with the supplied gamma estimate and absorb its correction
above the corresponding uniform order cutoff.
Role: exposes a zero-independent order envelope for choosing one mesh across a family of zeros.
-/
theorem exists_completedLFunction_positive_LFunction_logDeriv_iterate_with_fixed_gamma {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) (Krequested : ℕ)
    (hKrequested : 2 ≤ Krequested) {c ρ : ℂ} (hcre : c.re = 1 + η) (hcim : c.im = ρ.im)
    (hρre : |ρ.re - 1| ≤ η) (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0)
    (hscale : η * Real.log ((q : ℝ) * (|ρ.im| + 3)) ≤ 3) (G : ℝ) (hG : 0 ≤ G)
    (hgamma :
      ∀ n : ℕ,
        ∀ {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N},
          χ ≠ 1 →
            ∀ {s : ℂ} {T : ℝ},
              1 < s.re →
                1 ≤ s.re →
                s.re ≤ 5 / 4 →
                0 ≤ T →
                |s.im| ≤ T →
                ∀ {A : ℝ},
                  A ≤ ‖iteratedDeriv n (logDeriv (DirichletCharacter.completedLFunction χ)) s‖ →
                    A - (n.factorial : ℝ) * G * (Real.log (4 * T + 4) + 1) / (1 / 4 : ℝ) ^ n ≤
                      ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) s‖) :
    ∃ massConstA massConstB : ℝ,
      0 < massConstA ∧
        0 < massConstB ∧
        ∃ Kmin : ℕ,
          ∃ C K m n : ℕ,
            Krequested ≤ K ∧
              K ≤ completedGenusRemoteTailUniformCutoff q η ρ.im ((C : ℝ) + 1) Kmin ∧
              K ≤ max completedGenusRemoteTailUniformOrderBound Kmin ∧
              K ≤
                max completedGenusRemoteTailUniformOrderBound
                  (max (uniformGammaAbsorptionOrderCutoff G + 1) Krequested) ∧
              Kmin ≤ K ∧
              2 ≤ K ∧
              0 < n ∧
              n + 1 = m ∧
              K ≤ m ∧
              m ≤ K * completedLFunctionNearOneDetectorMultiplicityCap ∧
              C =
                Nat.ceil
                  (completedZeroLocalLogBoundConstant *
                    (1 + 644 * η * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
              0 < ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ ∧
              Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) ≤
                (η ^ (n + 1) / (n.factorial : ℝ)) *
                  ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
  let n₀ := uniformGammaAbsorptionOrderCutoff G
  have hn₀ := explicit_uniform_gamma_absorption_order_bound G
  let Kmin : ℕ := max (n₀ + 1) Krequested
  have hKmin : 2 ≤ Kmin := by
    dsimp only [Kmin]; omega
  obtain
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, C, K, m, n, hKmin', hKupper, hKupperFixed,
      hK, hn, hnm, hmK, hmCap, hCeq, hordinary⟩ :=
    exists_completedLFunction_detector_transfer_to_LFunction hq hχ hp hinv hη hηsmall Kmin hKmin
      hcre hcim hρre hzero hc hscale G hgamma (T := |ρ.im|) (abs_nonneg ρ.im) (le_rfl)
  have hCcap := completedLFunction_local_zero_multiplicity_cap_le_fixed hscale hCeq
  have hKlarge : n₀ ≤ n := by
    have hthreshold : n₀ + 1 ≤ K := by exact le_trans (le_max_left _ _) hKmin'
    omega
  have hηlog : η * (Real.log (4 * |ρ.im| + 4) + 1) ≤ 4 := by
    let Q : ℝ := (q : ℝ) * (|ρ.im| + 3)
    have hQ : 0 < Q := by
      dsimp only [Q]; positivity
    have hqreal : 1 ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
    have habs : 0 ≤ |ρ.im| := abs_nonneg ρ.im
    have hQbound : |ρ.im| + 1 ≤ Q := by
      dsimp only [Q]
      calc
        |ρ.im| + 1 ≤ (q : ℝ) * (|ρ.im| + 1) := by
          have := mul_le_mul_of_nonneg_right hqreal (show 0 ≤ |ρ.im| + 1 by positivity)
          simpa only [one_mul] using this
        _ ≤ (q : ℝ) * (|ρ.im| + 3) := mul_le_mul_of_nonneg_left (by nlinarith only) (by positivity)
    have harg : 4 * |ρ.im| + 4 ≤ 4 * Q := by nlinarith only [hQbound]
    have hlog : Real.log (4 * |ρ.im| + 4) ≤ Real.log (4 * Q) := Real.log_le_log (by positivity) harg
    have hlogMul : Real.log (4 * Q) = Real.log 4 + Real.log Q := by
      rw [Real.log_mul (by norm_num) (ne_of_gt hQ)]
    have hlog4 : Real.log 4 ≤ 3 := by
      have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4)
      nlinarith only [h]
    have hηlog4 : η * (Real.log 4 + 1) ≤ 1 := by
      have hfour : Real.log 4 + 1 ≤ 4 := by linarith only [hlog4]
      have hmul := mul_le_mul_of_nonneg_left hfour (le_of_lt hη)
      nlinarith only [hmul, hηsmall]
    have hlogPlus : Real.log (4 * |ρ.im| + 4) + 1 ≤ Real.log (4 * Q) + 1 := by linarith only [hlog]
    calc
      η * (Real.log (4 * |ρ.im| + 4) + 1) ≤ η * (Real.log (4 * Q) + 1) :=
        mul_le_mul_of_nonneg_left hlogPlus (le_of_lt hη)
      _ = η * Real.log Q + η * (Real.log 4 + 1) := by
        rw [hlogMul]; ring
      _ ≤ 3 + 1 := add_le_add (by simpa only [Q] using hscale) hηlog4
      _ = 4 := by norm_num
  let S : ℝ := (1 / (8 * ((C : ℝ) + 1))) * (1 / 3 : ℝ) ^ m
  let E : ℝ := G * η * (Real.log (4 * |ρ.im| + 4) + 1) * (4 * η) ^ n
  let R : ℝ := 24 * ((C : ℝ) + 1) * G * (η * (Real.log (4 * |ρ.im| + 4) + 1)) * (12 * η) ^ n
  have hS : 0 < S := by
    dsimp only [S]; positivity
  have hηL : 0 ≤ η * (Real.log (4 * |ρ.im| + 4) + 1) := by
    have hlognonneg : 0 ≤ Real.log (4 * |ρ.im| + 4) :=
      Real.log_nonneg (by nlinarith only [abs_nonneg ρ.im])
    positivity
  have hη12 : 0 ≤ 12 * η := by positivity
  have hη12le : 12 * η ≤ (3 : ℝ) / 322 := by nlinarith only [hηsmall]
  have hpow : (12 * η) ^ n ≤ ((3 : ℝ) / 322) ^ n := pow_le_pow_left₀ hη12 hη12le n
  have hCcast : (C : ℝ) + 1 ≤ (completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1 := by
    exact_mod_cast Nat.add_le_add_right hCcap 1
  have hcoeff :
    24 * ((C : ℝ) + 1) * G * (η * (Real.log (4 * |ρ.im| + 4) + 1)) ≤
      96 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G := by
    have hbase :
      24 * ((C : ℝ) + 1) * G ≤
        24 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G := by
      exact mul_le_mul_of_nonneg_right (by nlinarith only [hCcast]) (by positivity)
    calc
      _ = (24 * ((C : ℝ) + 1) * G) * (η * (Real.log (4 * |ρ.im| + 4) + 1)) := by ring
      _ ≤
          (24 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G) *
            (η * (Real.log (4 * |ρ.im| + 4) + 1)) :=
        mul_le_mul_of_nonneg_right hbase hηL
      _ ≤ (24 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G) * 4 :=
        mul_le_mul_of_nonneg_left hηlog (by positivity)
      _ = _ := by ring
  have hratio : R ≤ 1 / 2 := by
    have hsmall := hn₀ n hKlarge
    have hsmall' :
      96 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G * ((3 : ℝ) / 322) ^ n ≤
        1 / 2 := by
      nlinarith only [hsmall]
    calc
      R ≤
          96 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G *
            ((3 : ℝ) / 322) ^ n :=
        by
        dsimp only [R]
        calc
          _ ≤
              (96 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) * G) *
                (12 * η) ^ n :=
            by apply mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hη12 n)
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
      _ ≤ 1 / 2 := hsmall'
  have hpowSignal : (12 * η) ^ n * (1 / 3 : ℝ) ^ (n + 1) = (4 * η) ^ n / 3 := by
    have hmulPow : (12 * η) ^ n * (1 / 3 : ℝ) ^ n = (4 * η) ^ n := by
      calc
        _ = (12 * η * (1 / 3 : ℝ)) ^ n := by rw [← mul_pow]
        _ = _ := by
          congr 1; ring
    rw [pow_succ, ← mul_assoc, hmulPow]
    ring
  have hEeq : E = R * S := by
    calc
      E = G * η * (Real.log (4 * |ρ.im| + 4) + 1) * (4 * η) ^ n := by rfl
      _ =
          (24 * ((C : ℝ) + 1) * G * (η * (Real.log (4 * |ρ.im| + 4) + 1)) / (8 * ((C : ℝ) + 1))) *
            ((4 * η) ^ n / 3) :=
        by
        field_simp [ne_of_gt (show 0 < 8 * ((C : ℝ) + 1) by positivity)]
        ring
      _ =
          (24 * ((C : ℝ) + 1) * G * (η * (Real.log (4 * |ρ.im| + 4) + 1)) / (8 * ((C : ℝ) + 1))) *
            ((12 * η) ^ n * (1 / 3 : ℝ) ^ (n + 1)) :=
        by rw [hpowSignal]
      _ = R * S := by
        dsimp only [R, S]
        rw [← hnm, pow_succ]
        ring
  have hEleS : E ≤ S / 2 := by
    calc
      E = R * S := hEeq
      _ ≤ (1 / 2 : ℝ) * S := mul_le_mul_of_nonneg_right hratio hS.le
      _ = S / 2 := by ring
  let F : ℝ := (n.factorial : ℝ) / η ^ m
  have hF : 0 < F := by
    dsimp only [F]; positivity
  have hsignalEq : (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) = F * S := by
    dsimp only [F, S]
    have hpowEta : (1 / (3 * η) : ℝ) ^ m = (η⁻¹) ^ m * (1 / 3 : ℝ) ^ m := by
      rw [← mul_pow]
      congr 1
      field_simp [ne_of_gt hη]
    rw [hpowEta]
    field_simp [ne_of_gt hη, ne_of_gt (show 0 < 8 * ((C : ℝ) + 1) by positivity)]
    rw [← mul_pow]
    have hcancel : (1 / η : ℝ) * η = 1 := by field_simp [ne_of_gt hη]
    rw [hcancel, one_pow]
  have herrorEq :
    (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n = F * E := by
    dsimp only [F, E]
    rw [← hnm]
    have hquarter : ((1 / 4 : ℝ) ^ n)⁻¹ = (4 : ℝ) ^ n := by
      rw [show (1 / 4 : ℝ) = (4 : ℝ)⁻¹ by norm_num, inv_pow, inv_inv]
    have hpow4 : (4 * η) ^ n = (4 : ℝ) ^ n * η ^ n := by rw [mul_pow]
    rw [div_eq_mul_inv, hquarter, hpow4, pow_succ]
    field_simp [ne_of_gt hη, show (1 / 4 : ℝ) ≠ 0 by norm_num]
  have hrawEq :
    (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
        (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n =
      F * (S - E) := by
    rw [hsignalEq, herrorEq]
    ring
  have hrawPositive :
    0 <
      (1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
        (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n := by
    rw [hrawEq]
    apply mul_pos hF
    have hSpos : 0 < S / 2 := by positivity
    exact lt_of_lt_of_le hSpos (by linarith only [hEleS])
  have hKrequested' : Krequested ≤ K := le_trans (le_max_right _ _) hKmin'
  let A : ℝ := η ^ (n + 1) / (n.factorial : ℝ)
  have hA : 0 < A := by
    dsimp only [A]; positivity
  have hAF : A * F = 1 := by
    dsimp only [A, F]
    rw [hnm]
    field_simp [ne_of_gt hη, show (n.factorial : ℝ) ≠ 0 by positivity]
  have hscaledRaw :
    A *
        ((1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
          (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n) =
      S - E := by
    rw [hrawEq, ← mul_assoc, hAF, one_mul]
  have hscaledLower :
    S / 2 ≤ A * ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
    calc
      S / 2 ≤ S - E := by linarith only [hEleS]
      _ =
          A *
            ((1 / (8 * ((C : ℝ) + 1))) * (1 / (3 * η)) ^ m * (n.factorial : ℝ) -
              (n.factorial : ℝ) * G * (Real.log (4 * |ρ.im| + 4) + 1) / (1 / 4 : ℝ) ^ n) :=
        hscaledRaw.symm
      _ ≤ A * ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ :=
        mul_le_mul_of_nonneg_left hordinary hA.le
  have hcompletedExp :=
    local_detector_scale_ge_exp_neg (C := completedLFunctionNearOneDetectorMultiplicityCap) (Cmax :=
      completedLFunctionNearOneDetectorMultiplicityCap) (K := K) (m := m) (Nat.le_refl _) (by omega)
      hmCap
  let Sbase : ℝ :=
    (1 / (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1))) * (1 / 3 : ℝ) ^ m
  have hSbase : Sbase ≤ S := by
    have hden :
      8 * ((C : ℝ) + 1) ≤ 8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1) := by
      nlinarith only [hCcast]
    have hinv :
      1 / (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1)) ≤
        1 / (8 * ((C : ℝ) + 1)) :=
      one_div_le_one_div_of_le (by positivity) hden
    dsimp only [Sbase, S]
    exact mul_le_mul_of_nonneg_right hinv (by positivity)
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num only)
  have hKreal : (2 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hexpHalf : Real.exp (-((Real.log 2 / 2) * (K : ℝ))) ≤ 1 / 2 := by
    have harg : -((Real.log 2 / 2) * (K : ℝ)) ≤ -Real.log 2 := by nlinarith only [hlog2, hKreal]
    have h := Real.exp_le_exp.mpr harg
    have hExpLog : Real.exp (-Real.log 2) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hExpLog] at h
    exact h
  have hExpIdentity :
    Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) =
      Real.exp (-(completedLFunctionNearOneDetectorExponent * (K : ℝ))) *
        Real.exp (-((Real.log 2 / 2) * (K : ℝ))) := by
    change Real.exp (-((completedLFunctionNearOneDetectorExponent + Real.log 2 / 2) * (K : ℝ))) = _
    rw [add_mul, neg_add, Real.exp_add]
  have hnormalized :
    Real.exp (-(ordinaryLFunctionNearOneDetectorExponent * (K : ℝ))) ≤
      A * ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := by
    rw [hExpIdentity]
    calc
      _ ≤ Sbase * (1 / 2 : ℝ) := by
        have hcompletedExp' :
          Real.exp (-(completedLFunctionNearOneDetectorExponent * (K : ℝ))) ≤ Sbase := by
          have harg :
            -(completedLFunctionNearOneDetectorExponent * (K : ℝ)) =
              -((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) * Real.log 3 +
                    Real.log (8 * ((completedLFunctionNearOneDetectorMultiplicityCap : ℝ) + 1))) *
                (K : ℝ) := by
            dsimp only [completedLFunctionNearOneDetectorExponent]
            ring
          rw [harg]
          simpa only [Sbase] using hcompletedExp
        exact mul_le_mul hcompletedExp' hexpHalf (by positivity) (by positivity)
      _ ≤ S / 2 := by linarith only [hSbase]
      _ ≤ A * ‖iteratedDeriv n (logDeriv (DirichletCharacter.LFunction χ)) c‖ := hscaledLower
  have hKglobal :
    K ≤
      max completedGenusRemoteTailUniformOrderBound
        (max (uniformGammaAbsorptionOrderCutoff G + 1) Krequested) := by
    simpa only [Kmin, n₀] using hKupperFixed
  exact
    ⟨massConstA, massConstB, hmassConstA, hmassConstB, Kmin, C, K, m, n, hKrequested', hKupper,
      hKupperFixed, hKglobal, hKmin', hK, hn, hnm, hmK, hmCap, hCeq,
      lt_of_lt_of_le hrawPositive hordinary, hnormalized⟩

/--
Inputs: a primitive nonprincipal completed Dirichlet `L`-function, a zero close to `1`, and a
nonzero center immediately to its right.
Claim: some positive iterated derivative of the logarithmic derivative at the center is nonzero.
Proof: apply the explicit positive lower bound and use that a norm with a positive lower bound is
nonzero.
Role: retains the qualitative nonvanishing interface for existing callers.
-/
theorem exists_completedLFunction_nonzero_iteratedDerivWithin_logDeriv_near_one_zero {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hq : 2 ≤ q) (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {η : ℝ} (hη : 0 < η) (hηsmall : η ≤ 1 / 1288) {c ρ : ℂ} (hcre : c.re = 1 + η)
    (hcim : c.im = ρ.im) (hρre : |ρ.re - 1| ≤ η)
    (hzero : DirichletCharacter.completedLFunction χ ρ = 0)
    (hc : DirichletCharacter.completedLFunction χ c ≠ 0) :
    ∃ n : ℕ,
      0 < n ∧
        iteratedDerivWithin n (fun z : ℂ => logDeriv χ.completedLFunction z) {z : ℂ | 1 < z.re} c ≠
          0 := by
  obtain ⟨_, _, _, _, C, K, m, n, _, _, _, _, hn, hnm, hmK, hmKC, hbound, _⟩ :=
    exists_completedLFunction_iteratedDerivWithin_logDeriv_lower_bound_near_one_zero hq hχ hp hinv
      hη hηsmall 2 (by norm_num) hcre hcim hρre hzero hc
  refine ⟨n, hn, ?_⟩
  exact (norm_pos_iff.mp (lt_of_lt_of_le (by positivity) hbound))

/--
Inputs: a primitive nonprincipal character, a center with real part `2 - σ`, and
`71 / 72 ≤ σ < 1`.
Claim: the divisor support in the ball of radius `4 * (1 - σ)` has cardinality at most
`C * (1 + (1 - σ) * log(q * (|c.im| + 3)) )` for some positive constant `C`.
Proof: enclose the support in a rectangle within `9 * (1 - σ)` of `1 + i * c.im`, apply the
local multiplicity estimate with scale `36 * (1 - σ)`, and absorb the factor 36 into `C`.
Role: supplies a local support-size bound at the near-one scale used by the Turán detection step.
-/
theorem exists_completedLFunction_explicit_local_divisor_support_card_le_scaled_log_bound {q : ℕ}
    [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive)
    (hinv : χ⁻¹ ≠ 1) {σ : ℝ} (hσ : (71 / 72 : ℝ) ≤ σ) (hσlt : σ < 1) {c : ℂ} (hcre : c.re = 2 - σ) :
    ∃ C : ℝ,
      0 < C ∧
        (((completedLFunction_local_zero_support_finite χ hχ c (4 * (1 - σ))).toFinset.card : ℕ) :
            ℝ) ≤
          C * (1 + (1 - σ) * Real.log ((q : ℝ) * (|c.im| + 3))) := by
  let δ : ℝ := 1 - σ
  let R : ℝ := 4 * δ
  let η : ℝ := 36 * δ
  let z : ℂ := ⟨c.re - R, c.im - R⟩
  let w : ℂ := ⟨c.re + R, c.im + R⟩
  have hδpos : 0 < δ := by
    dsimp only [δ]
    linarith only [hσlt]
  have hδle : δ ≤ 1 / 72 := by
    dsimp only [δ]
    linarith only [hσ]
  have hRpos : 0 < R := by
    dsimp only [R]
    positivity
  have hRabs : |R| = R := abs_of_pos hRpos
  have hηpos : 0 < η := by
    dsimp only [η]
    positivity
  have hηle : η ≤ 1 / 2 := by
    dsimp only [η]
    nlinarith only [hδle]
  have hcenter : c.re = 1 + δ := by
    dsimp only [δ]
    calc
      c.re = 2 - σ := hcre
      _ = 1 + (1 - σ) := by ring
  have hbox :
    ∀ u,
      u ∈
          (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
              (Metric.ball c |R|)).support →
        u ∈ dirichletCompletedLFunctionRectangleBox z w := by
    intro u hu
    have hu' :
      u ∈
        (MeromorphicOn.divisor (DirichletCharacter.completedLFunction χ)
            (Metric.ball c R)).support := by
      rw [← hRabs]
      exact hu
    have hmem := completedLFunction_local_divisor_support_mem_centered_square χ c hRpos hu'
    simpa only [z, w] using hmem
  have hboxCenter :
    ∀ u,
      u ∈ dirichletCompletedLFunctionRectangleBox z w →
        ‖u - ((1 : ℂ) + (c.im : ℂ) * Complex.I)‖ ≤ η / 4 := by
    intro u hu
    change u.re ∈ Set.uIcc (c.re - R) (c.re + R) ∧ u.im ∈ Set.uIcc (c.im - R) (c.im + R) at hu
    have hcoords := hu
    rw [Set.uIcc_of_le
        (by
          dsimp only [R]; nlinarith only [hδpos]),
      Set.uIcc_of_le
        (by
          dsimp only [R]; nlinarith only [hδpos])] at hcoords
    have hreal : |u.re - 1| ≤ 5 * δ := by
      apply abs_le.mpr
      constructor
      · dsimp only [R] at hcoords
        nlinarith only [hcoords.1.1, hcenter, hδpos]
      · dsimp only [R] at hcoords
        nlinarith only [hcoords.1.2, hcenter, hδpos]
    have himag : |u.im - c.im| ≤ 4 * δ := by
      apply abs_le.mpr
      constructor
      · dsimp only [R] at hcoords
        linarith only [hcoords.2.1]
      · dsimp only [R] at hcoords
        linarith only [hcoords.2.2]
    calc
      ‖u - ((1 : ℂ) + (c.im : ℂ) * Complex.I)‖ ≤
          |(u - ((1 : ℂ) + (c.im : ℂ) * Complex.I)).re| +
            |(u - ((1 : ℂ) + (c.im : ℂ) * Complex.I)).im| :=
        Complex.norm_le_abs_re_add_abs_im _
      _ = |u.re - 1| + |u.im - c.im| := by
        simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re,
          Complex.I_im, Complex.one_re, Complex.one_im, mul_zero, mul_one, sub_zero, add_zero,
          zero_add]
      _ ≤ 5 * δ + 4 * δ := add_le_add hreal himag
      _ = η / 4 := by
        dsimp only [η]
        ring
  obtain ⟨C, hC, hcount⟩ :=
    exists_completedZeroMultiplicityCountInRectangle_le_local_log_bound hq hχ hp hinv hηpos hηle z w
      hboxCenter
  have hcard := completedLFunction_local_divisor_support_card_le_rectangle_count χ hχ c R z w hbox
  have hqreal : 1 ≤ (q : ℝ) := by
    have hq' : 1 ≤ q := by omega
    exact_mod_cast hq'
  have hheight : 1 ≤ |c.im| + 3 := by
    have habs : 0 ≤ |c.im| := abs_nonneg c.im
    nlinarith only [habs]
  have hlog : 0 ≤ Real.log ((q : ℝ) * (|c.im| + 3)) := by
    apply Real.log_nonneg
    nlinarith only [hqreal, hheight]
  have hscale :
    1 + 36 * δ * Real.log ((q : ℝ) * (|c.im| + 3)) ≤
      36 * (1 + δ * Real.log ((q : ℝ) * (|c.im| + 3))) := by
    nlinarith only [hlog]
  refine ⟨36 * C, mul_pos (by norm_num) hC, ?_⟩
  calc
    (((completedLFunction_local_zero_support_finite χ hχ c (4 * (1 - σ))).toFinset.card : ℕ) : ℝ) ≤
        completedZeroMultiplicityCountInRectangle χ hχ z w :=
      by simpa only [R, δ] using hcard
    _ ≤ C * (1 + η * Real.log ((q : ℝ) * (|c.im| + 3))) := hcount
    _ = C * (1 + 36 * δ * Real.log ((q : ℝ) * (|c.im| + 3))) := by rw [show η = 36 * δ from rfl]
    _ ≤ C * (36 * (1 + δ * Real.log ((q : ℝ) * (|c.im| + 3)))) :=
      mul_le_mul_of_nonneg_left hscale hC.le
    _ = (36 * C) * (1 + δ * Real.log ((q : ℝ) * (|c.im| + 3))) := by ring

/-!
## Scaled local support bound with derivative data
-/

/--
Inputs: a primitive nonprincipal character, positive zero count in `σ ≤ Re ρ ≤ 1`, and a
uniform remainder bound for the local analytic factor, with `71 / 72 ≤ σ < 1`.
Claim: a counted zero yields explicit-center derivative data together with the scaled logarithmic
bound for the local divisor-support cardinality.
Proof: obtain the local derivative data from the zero count, then apply the scaled support bound
at its center and rewrite the center height using the selected zero.
Role: joins local zero detection, its finite derivative cost, and the local multiplicity estimate.
-/
theorem exists_primitive_zeroCount_local_derivative_with_scaled_card_of_pos {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {σ T : ℝ} (hσlower : (71 / 72 : ℝ) ≤ σ) (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T)
    (M : ℕ) (remainder : ℕ → ℝ)
    (hremainder :
      ∀ (c : ℂ) (R : ℝ) n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          ∃ R : ℝ,
            R = 4 * (1 - σ) ∧
              0 < R ∧
              R ≤ 1 ∧
              c.re = 2 - σ ∧
              c.im = ρ.im ∧
              DirichletCharacter.completedLFunction χ c ≠ 0 ∧
              CompletedLFunctionLocalDerivativeLowerBoundData χ c R M remainder ∧
              ∃ C : ℝ,
                0 < C ∧
                  (((completedLFunction_local_zero_support_finite χ hχ c R).toFinset.card : ℕ) :
                      ℝ) ≤
                    C * (1 + (1 - σ) * Real.log ((q : ℝ) * (|ρ.im| + 3))) := by
  obtain ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hRdef, hR, hRle, hcre, hcim, hc, hdata⟩ :=
    exists_completedZeroCount_explicit_local_derivative_lower_bound_of_pos χ hχ
      (le_trans (by norm_num only : (3 / 4 : ℝ) ≤ 71 / 72) hσlower) hσupper hT hcount M remainder
      hremainder
  have hσlt : σ < 1 := by
    have hRpos : 0 < 4 * (1 - σ) := by
      rw [← hRdef]; exact hR
    nlinarith only [hRpos]
  obtain ⟨C, hC, hscaled⟩ :=
    exists_completedLFunction_explicit_local_divisor_support_card_le_scaled_log_bound hq hχ hp hinv
      hσlower hσlt hcre
  rw [← hRdef, hcim] at hscaled
  exact
    ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hRdef, hR, hRle, hcre, hcim, hc, hdata, C, hC,
      hscaled⟩

/--
Inputs: a positive zero count in a sufficiently narrow near-one strip and a uniform local
remainder bound for the analytic factor.
Claim: the selected zero has both explicit local derivative data and a fixed-multiple
reciprocal-power-sum block with an explicit natural multiplicity cap.
Proof: combine the existing local derivative and support-count output with the near-one rectangle
specialization, retaining the same zero and center throughout.
Role: joins the completed local zero analysis to the multiplicity-aware Turán detection input.
-/
theorem exists_primitive_zeroCount_local_derivative_and_power_block_of_pos {q : ℕ} [NeZero q]
    (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hp : χ.IsPrimitive) (hinv : χ⁻¹ ≠ 1)
    {σ T : ℝ} (hσlower : (1287 / 1288 : ℝ) ≤ σ) (hσupper : σ ≤ 1) (hT : 0 ≤ T)
    (hcount : 0 < PseudoPrime.AnalyticNumberTheory.DirichletLFunction.completedZeroCount χ hχ σ T)
    (M : ℕ) (remainder : ℕ → ℝ)
    (hremainder :
      ∀ (c : ℂ) (R : ℝ) n (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g (Metric.ball c |R|) →
          (∀ u : Metric.ball c |R|, g u ≠ 0) → ‖iteratedDeriv n (logDeriv g) c‖ ≤ remainder n)
    (K : ℕ) :
    ∃ ρ : ℂ,
      σ ≤ ρ.re ∧
        ρ.re ≤ 1 ∧
        -T ≤ ρ.im ∧
        ρ.im ≤ T ∧
        DirichletCharacter.completedLFunction χ ρ = 0 ∧
        ∃ c : ℂ,
          ∃ R : ℝ,
            R = 4 * (1 - σ) ∧
              0 < R ∧
              R ≤ 1 ∧
              c.re = 2 - σ ∧
              c.im = ρ.im ∧
              DirichletCharacter.completedLFunction χ c ≠ 0 ∧
              CompletedLFunctionLocalDerivativeLowerBoundData χ c R M remainder ∧
              (∃ C : ℝ,
                0 < C ∧
                  (((completedLFunction_local_zero_support_finite χ hχ c R).toFinset.card : ℕ) :
                      ℝ) ≤
                    C * (1 + (1 - σ) * Real.log ((q : ℝ) * (|ρ.im| + 3)))) ∧
              (∃ Cblock : ℕ,
                completedZeroMultiplicityCountInRectangle χ hχ
                      ⟨c.re - 80 * (1 - σ), c.im - 80 * (1 - σ)⟩
                      ⟨c.re + 80 * (1 - σ), c.im + 80 * (1 - σ)⟩ ≤
                    (Cblock : ℝ) ∧
                  CompletedLFunctionLocalZeroPowerSumBlockData χ c (1 - σ) ρ K Cblock) := by
  have hσlowerOld : (71 / 72 : ℝ) ≤ σ := by
    have hnum : (71 / 72 : ℝ) ≤ (1287 / 1288 : ℝ) := by norm_num
    exact le_trans hnum hσlower
  obtain
    ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hRdef, hR, hRle, hcre, hcim, hc, hdata, C, hC,
      hscaled⟩ :=
    exists_primitive_zeroCount_local_derivative_with_scaled_card_of_pos hq hχ hp hinv hσlowerOld
      hσupper hT hcount M remainder hremainder
  have hηpos : 0 < 1 - σ := by
    have hRpos : 0 < 4 * (1 - σ) := by
      rw [← hRdef]; exact hR
    nlinarith only [hRpos]
  have hηsmall : 1 - σ ≤ 1 / 1288 := by linarith only [hσlower]
  have hcreNear : c.re = 1 + (1 - σ) := by
    rw [hcre]
    ring
  have hρre : |ρ.re - 1| ≤ 1 - σ := by
    apply abs_le.mpr
    constructor <;> linarith only [hσρ, hρ1]
  obtain ⟨Cblock, hblockCount, hblock, _hblockCap⟩ :=
    exists_completedLFunction_local_zero_power_sum_block_of_near_one_zero hq hχ hp hinv hηpos
      hηsmall hcreNear hcim hρre hzero hc K
  exact
    ⟨ρ, hσρ, hρ1, himLower, himUpper, hzero, c, R, hRdef, hR, hRle, hcre, hcim, hc, hdata,
      ⟨C, hC, hscaled⟩, ⟨Cblock, hblockCount, hblock⟩⟩

/-
Inputs: a nonprincipal Dirichlet character, a point in the Euler half-plane, and a derivative order.
Claim: the iterated derivative of the completed logarithmic derivative is the sum of the
ordinary and gamma-factor logarithmic-derivative terms.
Proof: establish the logarithmic-derivative identity throughout the open half-plane, then apply
the iterated-derivative sum rule and transfer derivatives from within the half-plane.
Role: exposes the exact correction term that must be quantitatively bounded before using the
ordinary finite Euler-series approximation on the completed-function detector.
-/
theorem iteratedDeriv_logDeriv_completed_eq_LFunction_add_gammaFactor_of_one_lt_re {q : ℕ}
    [NeZero q] {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {c : ℂ} (hc : 1 < c.re) (n : ℕ) :
    iteratedDeriv n (logDeriv χ.completedLFunction) c =
      iteratedDeriv n (logDeriv χ.LFunction) c + iteratedDeriv n (logDeriv χ.gammaFactor) c := by
  let U : Set ℂ := {z : ℂ | 1 < z.re}
  have hopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU : UniqueDiffOn ℂ U := hopen.uniqueDiffOn
  have hcU : c ∈ U := hc
  have hcompA : AnalyticAt ℂ (fun z : ℂ => χ.completedLFunction z) c :=
    (χ.differentiable_completedLFunction hχ).analyticAt c
  have hgammaA : AnalyticAt ℂ (fun z : ℂ => χ.gammaFactor z) c :=
    analyticAt_gammaFactor_of_re_pos χ (by linarith only [hc])
  have hcompNZ : χ.completedLFunction c ≠ 0 :=
    completedLFunction_ne_zero_of_one_le_re hχ (by linarith only [hc])
  have hgammaNZ : χ.gammaFactor c ≠ 0 := gammaFactor_ne_zero_of_re_pos χ (by linarith only [hc])
  have hlevel : q ≠ 1 := dirichletCharacter_level_ne_one_of_ne_one hχ
  have hLfun :
    (fun z : ℂ => χ.LFunction z) = fun z => χ.completedLFunction z / χ.gammaFactor z := by
    funext z
    exact dirichletLFunction_eq_completed_div_gammaFactor χ z (Or.inr hlevel)
  have hLA : AnalyticAt ℂ (fun z : ℂ => χ.LFunction z) c := by
    rw [hLfun]
    exact hcompA.div hgammaA hgammaNZ
  have hLc := congrFun hLfun c
  have hLNZ : χ.LFunction c ≠ 0 := by
    rw [hLc]
    exact div_ne_zero hcompNZ hgammaNZ
  have hfA : AnalyticAt ℂ (logDeriv χ.completedLFunction) c := hcompA.deriv.div hcompA hcompNZ
  have hLAlog : AnalyticAt ℂ (logDeriv χ.LFunction) c := hLA.deriv.div hLA hLNZ
  have hGAlog : AnalyticAt ℂ (logDeriv χ.gammaFactor) c := hgammaA.deriv.div hgammaA hgammaNZ
  have hpointwise :
    Set.EqOn (logDeriv χ.completedLFunction)
      (fun z => logDeriv χ.LFunction z + logDeriv χ.gammaFactor z) U := by
    intro z hz
    change 1 < z.re at hz
    have hzre : 1 ≤ z.re := le_of_lt hz
    have hF : χ.completedLFunction z ≠ 0 := completedLFunction_ne_zero_of_one_le_re hχ hzre
    have hG : χ.gammaFactor z ≠ 0 := gammaFactor_ne_zero_of_re_pos χ (by linarith only [hz])
    have hdG : DifferentiableAt ℂ (fun w : ℂ => χ.gammaFactor w) z :=
      (analyticAt_gammaFactor_of_re_pos χ (by linarith only [hz])).differentiableAt
    have hbridge := logDeriv_dirichletLFunction_eq_completed_sub_gammaFactor_of_regular hχ hF hG hdG
    change logDeriv χ.completedLFunction z = logDeriv χ.LFunction z + logDeriv χ.gammaFactor z
    rw [hbridge]
    ring
  have hEqOn := iteratedDerivWithin_congr (n := n) hpointwise
  have hsum :=
    iteratedDerivWithin_fun_add (n := n) hcU hU hLAlog.contDiffAt.contDiffWithinAt
      hGAlog.contDiffAt.contDiffWithinAt
  have hFwithin := iteratedDerivWithin_eq_iteratedDeriv (n := n) hU hfA.contDiffAt hcU
  have hLwithin := iteratedDerivWithin_eq_iteratedDeriv (n := n) hU hLAlog.contDiffAt hcU
  have hGwithin := iteratedDerivWithin_eq_iteratedDeriv (n := n) hU hGAlog.contDiffAt hcU
  calc
    iteratedDeriv n (logDeriv χ.completedLFunction) c =
        iteratedDerivWithin n (logDeriv χ.completedLFunction) U c :=
      hFwithin.symm
    _ = iteratedDerivWithin n (fun z => logDeriv χ.LFunction z + logDeriv χ.gammaFactor z) U c :=
      hEqOn hcU
    _ =
        iteratedDerivWithin n (logDeriv χ.LFunction) U c +
          iteratedDerivWithin n (logDeriv χ.gammaFactor) U c :=
      hsum
    _ = _ := by rw [hLwithin, hGwithin]

/--
Inputs: a positive normalization scale, a bounded-height center in a fixed right strip, and a
derivative order.
Claim: the normalized gamma-factor correction is bounded by a constant times the scale, a
logarithmic height term, and the exponentially decreasing factor `(4 * η)^n`.
Proof: apply the uniform vertical-strip Cauchy estimate for gamma-factor logarithmic derivatives
and simplify the factorial and radius factors.
Role: quantifies one error term in transferring the completed-function detector to the ordinary
logarithmic derivative.
-/
theorem exists_scaled_gammaFactor_iteratedDeriv_bound {η T : ℝ} (hη : 0 < η) (hT : 0 ≤ T) {q : ℕ}
    (χ : DirichletCharacter ℂ q) {c : ℂ} (hcLo : 1 ≤ c.re) (hcHi : c.re ≤ 5 / 4) (hcT : |c.im| ≤ T)
    (n : ℕ) :
    ∃ C : ℝ,
      0 ≤ C ∧
        (η ^ (n + 1) / (n.factorial : ℝ)) * ‖iteratedDeriv n (logDeriv χ.gammaFactor) c‖ ≤
          C * η * (Real.log (4 * T + 4) + 1) * (4 * η) ^ n := by
  obtain ⟨C, hC, hgamma⟩ := exists_uniform_norm_iteratedDeriv_gammaFactor_vertical_le n
  refine ⟨C, hC, ?_⟩
  have hbound := hgamma χ hcLo hcHi hT hcT
  have hscale : 0 ≤ η ^ (n + 1) / (n.factorial : ℝ) := by positivity
  have hfactorial : (n.factorial : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr (Nat.factorial_pos n))
  calc
    _ ≤
        (η ^ (n + 1) / (n.factorial : ℝ)) *
          ((n.factorial : ℝ) * C * (Real.log (4 * T + 4) + 1) / (1 / 4 : ℝ) ^ n) :=
      mul_le_mul_of_nonneg_left hbound hscale
    _ = C * η * (Real.log (4 * T + 4) + 1) * (4 * η) ^ n := by
      have hquarter : (1 / 4 : ℝ) = (4 : ℝ)⁻¹ := by norm_num only
      rw [hquarter, inv_pow]
      field_simp [hfactorial]
      calc
        η ^ (n + 1) * C * (Real.log (4 * (T + 1)) + 1) * 4 ^ n =
            C * (Real.log (4 * (T + 1)) + 1) * η * (4 ^ n * η ^ n) :=
          by
          rw [pow_succ]
          ring
        _ = _ := by rw [← mul_pow]

end PseudoPrime.AnalyticNumberTheory.DirichletLFunction.LogFreeDensity
