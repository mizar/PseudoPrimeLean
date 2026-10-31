/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaPrimePowerCosts

/-! # Reciprocal bounds for the intrinsic signed Gamma Euler weight -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a nonnegative real u. Claim: the retained cubic is at most one fifth.
Proof: use the nonnegative product (u-3/5)^2 (u+3/10).
Role: absorb the large positive node using the negative node. -/
theorem gamma_signed_cubic_le_one_fifth (u : ℝ) (hu : 0 ≤ u) :
    (144548748 / 100000000 : ℝ) * u ^ 2 - (156741759 / 100000000 : ℝ) * u ^ 3 ≤ 1 / 5 := by
  have h := mul_nonneg (sq_nonneg (u - 3 / 5)) (show 0 ≤ u + 3 / 10 by linarith only [hu])
  nlinarith only [h]

/-- Input: t in [0,1]. Claim: the signed Euler polynomial is at most three halves.
Proof: retain the negative degree-36 term and apply the cubic bound to t^12.
Role: certify a reciprocal envelope without discarding all negative coefficients. -/
theorem gamma_signed_polynomial_le_three_halves (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (56157519 * t + 16846179 * t ^ 6 + 52329992 * t ^ 10 + 144548748 * t ^ 24 - 206770197 * t ^ 36 -
              10561870 * t ^ 54 +
            50028438 * t ^ 80 -
          8311425 * t ^ 130) /
        (100000000 : ℝ) ≤
      3 / 2 := by
  have h6 : t ^ 6 ≤ 1 := pow_le_one₀ ht ht1
  have h10 : t ^ 10 ≤ 1 := pow_le_one₀ ht ht1
  have h44 : t ^ 44 ≤ 1 := pow_le_one₀ ht ht1
  have h80 : t ^ 80 ≤ t ^ 36 := by
    calc
      _ = t ^ 36 * t ^ 44 := by ring
      _ ≤ t ^ 36 * 1 := mul_le_mul_of_nonneg_left h44 (pow_nonneg ht 36)
      _ = _ := mul_one _
  have hc := gamma_signed_cubic_le_one_fifth (t ^ 12) (pow_nonneg ht 12)
  have he2 : (t ^ 12) ^ 2 = t ^ 24 := by ring
  have he3 : (t ^ 12) ^ 3 = t ^ 36 := by ring
  rw [he2, he3] at hc
  nlinarith only [ht1, h6, h10, h80, hc, pow_nonneg ht 54, pow_nonneg ht 130]

/-- Input: m at least one. Claim: the actual Euler weight is at most 3/(2m).
Proof: substitute t=m^(-1/20) in the signed polynomial and factor m inverse.
Role: provide a sharper termwise envelope for convergent prime-power sums. -/
theorem gamma_euler_weight_le_signed_reciprocal {m : ℝ} (hm : 1 ≤ m) :
    gammaResolventEulerWeight m ≤ (3 / 2 : ℝ) * m⁻¹ := by
  let t := m ^ (-1 / 20 : ℝ)
  have hm0 : 0 < m := zero_lt_one.trans_le hm
  have ht : 0 ≤ t := Real.rpow_nonneg hm0.le _
  have ht1 : t ≤ 1 :=
    (Real.rpow_le_rpow_of_exponent_le hm (by norm_num only : (-1 / 20 : ℝ) ≤ 0)).trans_eq
      (Real.rpow_zero m)
  have he (k : ℕ) : m ^ (-(k : ℝ) / 20) = t ^ k := by
    dsimp only [t]
    rw [← Real.rpow_mul_natCast hm0.le]
    congr 1
    ring
  have hs := gamma_signed_polynomial_le_three_halves t ht ht1
  have h21 := he 21
  have h26 := he 26
  have h30 := he 30
  have h44 := he 44
  have h56 := he 56
  have h74 := he 74
  have h100 := he 100
  have h150 := he 150
  have h20 := he 20
  norm_num only [Nat.cast_ofNat, neg_div, Real.rpow_neg_one] at h21 h26 h30 h44
  norm_num only [Nat.cast_ofNat, neg_div, Real.rpow_neg_one] at h56 h74 h100 h150 h20
  have hfactor :
    gammaResolventEulerWeight m =
      t ^ 20 *
        ((56157519 * t + 16846179 * t ^ 6 + 52329992 * t ^ 10 + 144548748 * t ^ 24 -
                206770197 * t ^ 36 -
                10561870 * t ^ 54 +
              50028438 * t ^ 80 -
            8311425 * t ^ 130) /
          (100000000 : ℝ)) := by
    norm_num only [gammaResolventEulerWeight, AnalyticNumberTheory.Gamma.gammaResolventCoefficients,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    rw [h21, h26, h30, h44, h56, h74, h100, h150]
    ring
  rw [hfactor, h20]
  exact (mul_le_mul_of_nonneg_left hs (pow_nonneg ht 20)).trans_eq (mul_comm _ _)

/-- Input: a real base p greater than one. Claim: its signed Euler cost is at most
3/(2(p-1)). Proof: sum the new termwise envelope using absolute convergence.
Role: reduce the support of the ramified dual excess. -/
theorem gamma_prime_euler_cost_le_signed_reciprocal {p : ℝ} (hp : 1 < p) :
    gammaPrimeEulerCost p ≤ (3 / 2 : ℝ) / (p - 1) := by
  have hs :=
    (summable_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)).mul_left (3 / 2 : ℝ)
  have hle :=
    (summable_gammaResolventEulerWeight_powers hp).tsum_le_tsum
      (fun k ↦ by
        simpa only [Real.rpow_neg_one] using
          gamma_euler_weight_le_signed_reciprocal (one_le_pow₀ hp.le : (1 : ℝ) ≤ p ^ (k + 1)))
      hs
  rw [tsum_gammaResolventEulerWeight_powers_eq_cost hp, tsum_mul_left,
    tsum_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)] at hle
  have hr : p ^ (-1 : ℝ) / (1 - p ^ (-1 : ℝ)) = 1 / (p - 1) := by
    have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
    have he : 1 - p⁻¹ = p⁻¹ * (p - 1) := by rw [mul_sub, inv_mul_cancel₀ hp0, mul_one]
    rw [Real.rpow_neg_one, he, mul_comm p⁻¹ (p - 1)]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ) (p - 1) (inv_ne_zero hp0)
  rw [hr] at hle
  simpa only [mul_one_div] using hle

end PseudoPrime.Analysis
