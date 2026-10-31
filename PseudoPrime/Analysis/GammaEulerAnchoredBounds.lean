/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaEulerReciprocalBounds
public import PseudoPrime.Analysis.GammaEulerSeed100

/-! # Anchored bounds for the intrinsic Gamma Euler weight -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: 0<a<=u and sigma>=1. Claim: each signed power is bounded by its positive
coefficient times the anchored shifted power and 1/u. Proof: factor the reciprocal and
use negative-power monotonicity. Role: construct sharper envelopes at positive cutoffs. -/
theorem gamma_signed_power_le_anchored_reciprocal {u a σ c : ℝ} (ha : 0 < a) (hau : a ≤ u)
    (hσ : 1 ≤ σ) : c * u ^ (-σ) ≤ max c 0 * a ^ (1 - σ) * u⁻¹ := by
  have hu : 0 < u := ha.trans_le hau
  have he : u ^ (-σ) = u ^ (1 - σ) * u⁻¹ := by
    rw [← Real.rpow_neg_one, ← Real.rpow_add hu]
    congr 1
    ring
  by_cases hc : 0 ≤ c
  · rw [max_eq_left hc, he]
    have hp := Real.rpow_le_rpow_of_nonpos ha hau (sub_nonpos.mpr hσ)
    simpa only [mul_assoc] using
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hc) (inv_nonneg.mpr hu.le)
  · rw [max_eq_right (le_of_not_ge hc), zero_mul, zero_mul]
    exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_ge hc) (Real.rpow_nonneg hu.le _)

/-- Input: a positive anchor a. Definition: positive node coefficients times a^(1-sigma).
Output: a real reciprocal-envelope coefficient. Role: control all Euler weights above the anchor. -/
noncomputable def gammaAnchoredReciprocalCoefficient (a : ℝ) : ℝ :=
  (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map
      (fun ab ↦ max (ab.2 : ℝ) 0 * a ^ (1 - (1 / 2 + (ab.1 : ℝ))))).sum

/-- Input: any 0<a<=u. Claim: the actual Euler weight is at most its anchored coefficient/u.
Proof: sum the signed node bounds. Role: reuse one finite anchor for all larger inputs. -/
theorem gamma_euler_weight_le_anchored_reciprocal {a u : ℝ} (ha : 0 < a) (hau : a ≤ u) :
    gammaResolventEulerWeight u ≤ gammaAnchoredReciprocalCoefficient a * u⁻¹ := by
  have h :=
    List.sum_le_sum
      (fun (ab : ℚ × ℚ) hab ↦
        gamma_signed_power_le_anchored_reciprocal ha hau
          (show (1 : ℝ) ≤ 1 / 2 + (ab.1 : ℝ)
            by
            have h : ((1 / 2 : ℚ) : ℝ) < (ab.1 : ℝ) :=
              Rat.cast_lt.mpr
                (List.forall_iff_forall_mem.mp
                  AnalyticNumberTheory.Gamma.gammaResolvent_scales_gt_half ab hab)
            norm_num only at h
            linarith only [h])
          (c := (ab.2 : ℝ)))
  rw [List.sum_map_mul_right] at h
  exact h

/-- Definition: ten consecutive millionth-grid intervals at anchor 20.
Output: rational node data. Role: certify the small common envelope coefficient. -/
def gammaAnchor20Ratios : ℚ → ℚ × ℚ :=
  smallSeedRatios [43044, 31901, 20354, 11180, 4551, 1373, 227, 15, 0, 0]

/-- Claim: the ten node intervals at 20 pass the exact power check.
Proof: kernel arithmetic. Role: certify the real-power endpoints independently of their search. -/
theorem gamma_anchor20_ratio_check : gammaFiniteEulerRatioCheck 20 gammaAnchor20Ratios = true := by
  decide +kernel

/-- Claim: the positive shifted-node envelope at anchor 20 is at most 71/100.
Proof: exact rational kernel arithmetic. Role: certify a common large-input coefficient. -/
theorem gamma_anchor20_mass_check :
    (AnalyticNumberTheory.Gamma.gammaResolventCoefficients.map
          (fun ab ↦ max ab.2 0 * (20 * (gammaAnchor20Ratios ab.1).2))).sum ≤
      (71 / 100 : ℚ) := by
  decide +kernel

/-- Claim: the real anchored reciprocal coefficient at 20 is at most 71/100.
Proof: multiply the checked full node powers by 20 and sum the positive coefficients.
Role: transfer the small finite numerical certificate to the actual real Euler weight. -/
theorem gamma_anchor20_coefficient_le : gammaAnchoredReciprocalCoefficient 20 ≤ (71 / 100 : ℝ) := by
  have hn (ab : ℚ × ℚ) (hab : ab ∈ AnalyticNumberTheory.Gamma.gammaResolventCoefficients) :
    (20 : ℝ) ^ (1 - (1 / 2 + (ab.1 : ℝ))) ≤ 20 * ((gammaAnchor20Ratios ab.1).2 : ℝ) := by
    have h := (gamma_finite_ratio_check_sound gamma_anchor20_ratio_check ab hab).2
    norm_num only [Rat.cast_ofNat] at h
    rw [show (1 : ℝ) - (1 / 2 + (ab.1 : ℝ)) = -(1 / 2 + (ab.1 : ℝ)) + 1 by ring,
      Real.rpow_add_one (by norm_num only : (20 : ℝ) ≠ 0)]
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left h (by norm_num only : (0 : ℝ) ≤ 20)
  have hs :=
    List.sum_le_sum
      (fun (ab : ℚ × ℚ) hab ↦ mul_le_mul_of_nonneg_left (hn ab hab) (le_max_right (ab.2 : ℝ) 0))
  have hc := (Rat.cast_le (K := ℝ)).mpr gamma_anchor20_mass_check
  norm_num only [Rat.cast_list_sum, List.map_map, Function.comp_def, Rat.cast_mul, Rat.cast_max,
    Rat.cast_zero, Rat.cast_ofNat, Rat.cast_div] at hc
  exact hs.trans hc

/-- Input: u>=20. Claim: the actual Euler weight is at most 71/(100u).
Proof: combine the generic anchored bound with the certified coefficient.
Role: avoid per-prime node data for every sufficiently large prime power. -/
theorem gamma_euler_weight_le_reciprocal_of_twenty_le {u : ℝ} (hu : 20 ≤ u) :
    gammaResolventEulerWeight u ≤ (71 / 100 : ℝ) * u⁻¹ := by
  exact
    (gamma_euler_weight_le_anchored_reciprocal (by norm_num only : (0 : ℝ) < 20) hu).trans
      (mul_le_mul_of_nonneg_right gamma_anchor20_coefficient_le
        (inv_nonneg.mpr (by linarith only [hu] : (0 : ℝ) ≤ u)))

/-- Input: p>1 and a common c/p^k bound for all positive-power Euler weights.
Claim: the exact signed prime Euler cost is at most c/(p-1).
Proof: compare the absolutely convergent power series and normalize the geometric sum.
Role: reuse arbitrary local reciprocal envelopes without repeating infinite-sum arguments. -/
theorem gamma_prime_euler_cost_le_of_power_reciprocal {p c : ℝ} (hp : 1 < p)
    (h : ∀ k : ℕ, gammaResolventEulerWeight (p ^ (k + 1)) ≤ c * (p ^ (k + 1))⁻¹) :
    gammaPrimeEulerCost p ≤ c / (p - 1) := by
  have hs := (summable_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)).mul_left c
  have hle :=
    (summable_gammaResolventEulerWeight_powers hp).tsum_le_tsum
      (fun k ↦ by simpa only [Real.rpow_neg_one] using h k) hs
  rw [tsum_gammaResolventEulerWeight_powers_eq_cost hp, tsum_mul_left,
    tsum_gamma_euler_positive_powers hp (zero_lt_one : (0 : ℝ) < 1)] at hle
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hr : p ^ (-1 : ℝ) / (1 - p ^ (-1 : ℝ)) = 1 / (p - 1) := by
    have he : 1 - p⁻¹ = p⁻¹ * (p - 1) := by rw [mul_sub, inv_mul_cancel₀ hp0, mul_one]
    rw [Real.rpow_neg_one, he, mul_comm p⁻¹ (p - 1)]
    simpa only [one_mul] using mul_div_mul_right (1 : ℝ) (p - 1) (inv_ne_zero hp0)
  rw [hr] at hle
  simpa only [mul_one_div] using hle

/-- Input: p>=20. Claim: the exact signed prime Euler cost is at most 71/(100(p-1)).
Proof: every positive power is above the certified anchor; apply the generic series comparison.
Role: provide a cheap analytic allowance for large-prime dual excess. -/
theorem gamma_prime_euler_cost_le_of_twenty_le {p : ℝ} (hp : 20 ≤ p) :
    gammaPrimeEulerCost p ≤ (71 / 100 : ℝ) / (p - 1) := by
  have hp1 : 1 < p := by linarith only [hp]
  exact
    gamma_prime_euler_cost_le_of_power_reciprocal hp1
      (fun k ↦
        gamma_euler_weight_le_reciprocal_of_twenty_le
          (hp.trans (le_self_pow₀ hp1.le (Nat.succ_ne_zero k))))

end PseudoPrime.Analysis
