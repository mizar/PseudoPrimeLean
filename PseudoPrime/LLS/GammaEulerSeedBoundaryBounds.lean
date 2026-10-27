/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.GammaFiniteCenterScalarCertificate
public import PseudoPrime.LLS.GammaEulerSeedErrorBounds

/-! # Certified signed boundary tail at the small Euler-prefix seed -/

@[expose] public section

namespace PseudoPrime.LLS

/-- Claim: the existing ten node intervals certify the weight, slope and main-tail allowances.
Proof: exact rational kernel arithmetic. Role: retain signed cancellation at the seed cutoff. -/
theorem gamma_seed100_boundary_scalar_checks :
    Analysis.gammaFiniteEulerUpper errorSeed100Ratios ≤ (5463 / 1000000 : ℚ) ∧
      (-6139 / 1000000 : ℚ) ≤
        gammaFiniteWeightedLower gammaSlopeRationalCoefficient errorSeed100Ratios ∧
      (10329 / 1000 : ℚ) ≤
        gammaFiniteWeightedLower (gammaTailRationalCoefficient 100) errorSeed100Ratios := by
  decide +kernel

/-- Claim: psi(100)<=95, without RH. Proof: use the logarithm of lcm(1,...,100)
and the checked bound lcm<=2^137. Role: control the negative seed boundary product compactly. -/
theorem gamma_seed100_psi_upper : Chebyshev.psi 100 ≤ (95 : ℝ) := by
  have hn : Nat.lcmUpto 100 ≤ 2 ^ 137 := by decide +kernel
  have hp : (0 : ℝ) < Nat.lcmUpto 100 := Nat.cast_pos.mpr (Nat.lcmUpto_pos 100)
  have hnR : (Nat.lcmUpto 100 : ℝ) ≤ (2 : ℝ) ^ 137 := by exact_mod_cast hn
  have hm := Real.log_le_log hp hnR
  rw [Real.log_pow] at hm
  norm_num only [Nat.cast_ofNat] at hm
  have he := Chebyshev.psi_eq_log_lcmUpto 100
  norm_num only [Nat.cast_ofNat] at he
  rw [he]
  linarith only [hm, Real.log_two_lt_d9]

/-- Input: RH. Claim: the smoothed Mangoldt sum at 100 is at most 201/2.
Proof: apply the existing one-sided square-root error. Role: avoid a finite smoothed-sum payload. -/
theorem gamma_seed100_smoothed_upper (hRH : RiemannHypothesis) :
    AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum 100 ≤ (201 / 2 : ℝ) := by
  have h := logWeightedMangoldtSum_le_add_sqrt_twentieth hRH (by norm_num only : (1 : ℝ) < 100)
  have hs : Real.sqrt (100 : ℝ) = 10 := by
    rw [show (100 : ℝ) = (10 : ℝ) ^ 2 by norm_num only, Real.sqrt_sq (by norm_num only)]
  rw [hs] at h
  norm_num only at h
  exact h

/-- Claim: the actual Euler weight at 100 is at most 5463/1000000.
Proof: combine the node check and signed rational upper bound.
Role: control the seed's negative Chebyshev product. -/
theorem gamma_seed100_weight_upper :
    Analysis.gammaResolventEulerWeight 100 ≤ (5463 / 1000000 : ℝ) := by
  have h := (Analysis.gamma_finite_ratio_check_euler_bounds error_seed100_ratio_check).2
  have hr := (Rat.cast_le (K := ℝ)).mpr gamma_seed100_boundary_scalar_checks.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hr
  exact h.trans hr

/-- Claim: the actual Euler logarithmic slope at 100 is at least -6139/1000000.
Proof: apply the signed weighted-node interval. Role: retain a lower bound on the negative slope. -/
theorem gamma_seed100_slope_lower : (-6139 / 1000000 : ℝ) ≤ gammaEulerLogSlope 100 := by
  have h := (gamma_finite_weighted_bounds error_seed100_ratio_check gammaSlopeRationalCoefficient).1
  have hr := (Rat.cast_le (K := ℝ)).mpr gamma_seed100_boundary_scalar_checks.2.1
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hr
  rw [gamma_slope_eq_weighted]
  simpa only [neg_div] using hr.trans h

/-- Claim: the actual main tail at 100 is at least 10329/1000.
Proof: compare signed weighted nodes using the exact main-tail identity.
Role: certify the positive main contribution to the seed boundary tail. -/
theorem gamma_seed100_main_lower : (10329 / 1000 : ℝ) ≤ gammaEulerTailMain 100 := by
  have h :=
    (gamma_finite_weighted_bounds error_seed100_ratio_check (gammaTailRationalCoefficient 100)).1
  have hr := (Rat.cast_le (K := ℝ)).mpr gamma_seed100_boundary_scalar_checks.2.2
  norm_num only [Rat.cast_div, Rat.cast_ofNat] at h hr
  rw [show (100 : ℝ) = ((100 : ℚ) : ℝ) by norm_num only,
    gamma_tail_main_eq_weighted (by norm_num only : (0 : ℚ) < 100)]
  exact hr.trans h

/-- Input: an Euler-weight upper bound, psi upper bound, nonpositive slope lower bound,
nonnegative smoothed sum with an upper bound, and main-tail lower bound.
Claim: the signed scalar expression bounds the boundary tail below.
Proof: compare the two products with their proper signs. Role: reuse lower-tail certificates. -/
theorem gamma_euler_boundary_tail_lower {b h p g v M : ℝ}
    (hh : Analysis.gammaResolventEulerWeight b ≤ h) (hh0 : 0 ≤ h) (hp : Chebyshev.psi b ≤ p)
    (hg : g ≤ gammaEulerLogSlope b) (hg0 : g ≤ 0)
    (hv0 : 0 ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b)
    (hv : AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b ≤ v)
    (hM : M ≤ gammaEulerTailMain b) : -h * p + g * v + M ≤ gammaEulerBoundaryTail b := by
  have h1 := mul_le_mul hh hp (Chebyshev.psi_nonneg b) hh0
  have h2 := mul_le_mul_of_nonneg_right hg hv0
  have h3 := mul_le_mul_of_nonpos_left hv hg0
  dsimp only [gammaEulerBoundaryTail]
  linarith only [h1, h2, h3, hM]

/-- Input: a positive cutoff. Claim: the logarithmically weighted Mangoldt sum is nonnegative.
Proof: sum the nonnegative terms. Role: justify signed slope comparisons at arbitrary cutoffs. -/
theorem gamma_logWeightedMangoldtSum_nonneg {b : ℝ} (hb : 0 < b) :
    0 ≤ AnalyticNumberTheory.Arithmetic.logWeightedMangoldtSum b := by
  exact
    Finset.sum_nonneg
      (fun n hn ↦
        AnalyticNumberTheory.Arithmetic.logWeightedMangoldtTerm_nonneg hb (Finset.mem_Ioc.mp hn).1
          (Finset.mem_Ioc.mp hn).2)

/-- Input: RH. Claim: the actual signed boundary tail at 100 is at least 919/100.
Proof: combine certified scalar inputs and the analytic smoothed upper bound.
Role: eliminate the seed boundary field from prefix transport. -/
theorem gamma_seed100_boundary_tail_lower (hRH : RiemannHypothesis) :
    (919 / 100 : ℝ) ≤ gammaEulerBoundaryTail 100 := by
  have h :=
    gamma_euler_boundary_tail_lower gamma_seed100_weight_upper (by norm_num only)
      gamma_seed100_psi_upper gamma_seed100_slope_lower (by norm_num only)
      (gamma_logWeightedMangoldtSum_nonneg (by norm_num only : (0 : ℝ) < 100))
      (gamma_seed100_smoothed_upper hRH) gamma_seed100_main_lower
  linarith only [h]

/-- Input: RH, b>=50000 and an upper bound B on the actual boundary tail at b.
Claim: 61423/5000-B bounds the full actual prefix below.
Proof: combine the certified seed, seed tail and half-line error cap.
Role: replace a large finite prefix certificate by one analytic tail upper bound. -/
theorem gamma_euler_prefix_lower_of_tail_upper (hRH : RiemannHypothesis) {b B : ℝ} (hb : 50000 ≤ b)
    (hB : gammaEulerBoundaryTail b ≤ B) :
    (61423 / 5000 : ℝ) - B ≤ ∑ m ∈ Finset.Ioc 0 ⌊b⌋₊, Analysis.gammaResolventMangoldtWeight m := by
  have h :=
    gamma_euler_prefix_lower_from_seed100_error hRH hb (gamma_seed100_boundary_tail_lower hRH) hB
  linarith only [h]

/-- Input: RH, odd nonsquare n, log n<=L, x>=4096, b>=50000 and tail/dual upper bounds.
Claim: these two scalar inputs bound the actual Jacobi joint budget.
Proof: substitute the certified seed boundary into the actual comparison.
Role: reduce the remaining quantitative witness obligations to the target tail and dual cost. -/
theorem gamma_joint_prefix_le_of_tail_upper (hRH : RiemannHypothesis) {n : ℕ} (hn : Odd n)
    (hns : ¬IsSquare n) {b B L x D : ℝ} (hb : 50000 ≤ b) (hlog : Real.log n ≤ L) (hx : 4096 ≤ x)
    (hB : gammaEulerBoundaryTail b ≤ B) (hD : gammaScaleSignedDualBudget L x ≤ D) :
    gammaJointPrefixLocalBudget (NumberTheory.complexQuadraticCharacter n hn) b x ≤
      (11783423 / 25000000 : ℝ) * (L + 7 / 5) + 3 / 4 + D - 2 * (61423 / 5000 - B) + 7 / 60 := by
  have h :=
    gamma_joint_prefix_le_from_seed100_error hRH hn hns hb hlog hx
      (gamma_seed100_boundary_tail_lower hRH) hB hD
  linarith only [h]

end PseudoPrime.LLS
