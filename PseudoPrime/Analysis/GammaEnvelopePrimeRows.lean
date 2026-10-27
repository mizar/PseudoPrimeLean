/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaAnchoredReciprocalBounds
public import PseudoPrime.Analysis.GammaLocalPrimeRows

/-! # Local dual rows with independently proved Euler upper bounds -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a local row and common cell. Definition: logarithm, finite ramp, cost
and excess checks, leaving the Euler upper bound as a separate analytic input.
Output: an executable Bool. Role: allow either exact-node or common reciprocal Euler bounds. -/
def GammaLocalPrimeRow.envelopeCheck (r : GammaLocalPrimeRow) (c : GammaLocalCellData) : Bool :=
  rationalLogIntervalCheck r.prime r.logScale r.logTerms r.logLower r.logUpper &&
    decide
      ((99 / 40 : ℚ) * c.hi ≤ (r.prime : ℚ) ^ (r.powers + 1) ∧
        (∀ k ∈ Finset.range r.powers,
          ((r.prime : ℚ) ^ (k + 1) / c.lo) / (r.expTerms + 1 : ℕ) ≤ 1 / 2) ∧
        gammaSignedRampPrefixUpper r.prime r.powers c.lo c.hi r.expTerms ≤ r.rampUpper ∧
        r.eulerUpper + max r.rampUpper 0 / c.rootLo ≤ r.costUpper ∧
        max (r.costUpper - c.theta / c.rootHi) 0 ≤ r.excessUpper)

/-- Input: a checked cell, a prime row passing envelopeCheck, and a proved Euler upper bound.
Claim: the row cost allowance holds for every scale in the cell.
Proof: combine the analytic Euler input with the certified signed ramp prefix.
Role: avoid per-prime real-power data for large primes with a common analytic envelope. -/
theorem GammaLocalPrimeRow.cost_le_of_euler_bound (r : GammaLocalPrimeRow) (c : GammaLocalCellData)
    (hcell : c.check = true) (hp : r.prime.Prime) (hc : r.envelopeCheck c = true)
    (hE : gammaPrimeEulerCost r.prime ≤ (r.eulerUpper : ℝ)) {x : ℝ} (hlox : (c.lo : ℝ) ≤ x)
    (hxhi : x ≤ (c.hi : ℝ)) : gammaRamifiedSignedCombinedCost r.prime x ≤ (r.costUpper : ℝ) := by
  obtain ⟨hlo, hlohi, hslo, hrootlo, hshi, hroothi, htheta⟩ := c.check_sound hcell
  obtain ⟨hlog, hnum⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hcut, hsize, hr, hcost, hex⟩ := of_decide_eq_true hnum
  have hcutR := (Rat.cast_le (K := ℝ)).mpr hcut
  norm_num only [Rat.cast_mul, Rat.cast_div, Rat.cast_ofNat, Rat.cast_pow,
    Rat.cast_natCast] at hcutR
  have hS := gamma_ramified_series_le_natural_cell_prefix hp.one_lt hlo hlox hxhi hcutR
  have hP :=
    gamma_signed_ramp_prefix_upper_valid r.prime r.powers ((Rat.cast_pos (K := ℝ)).mp hlo)
      ((Rat.cast_pos (K := ℝ)).mp (hlo.trans_le hlohi)) r.expTerms hsize
  have hmax := max_le_max (hP.trans ((Rat.cast_le (K := ℝ)).mpr hr)) (le_refl (0 : ℝ))
  have hden :=
    (div_le_div_of_nonneg_right hmax (Real.sqrt_nonneg (c.lo : ℝ))).trans
      (div_le_div₀ (le_max_right _ _) le_rfl hslo hrootlo)
  have hR := hS.trans hden
  have hcostR := (Rat.cast_le (K := ℝ)).mpr hcost
  norm_num only [Rat.cast_add, Rat.cast_div, Rat.cast_max, Rat.cast_zero] at hcostR
  exact (add_le_add hE hR).trans hcostR

/-- Input: the same checked row, analytic Euler input and actual scale in the cell.
Claim: its rational allowance bounds the logarithm-weighted positive dual excess.
Proof: retain the lower price and use the certified logarithm upper endpoint.
Role: supply uniform prime contributions for mixed analytic and finite certificates. -/
theorem GammaLocalPrimeRow.weighted_excess_le_of_euler_bound (r : GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : r.prime.Prime)
    (hc : r.envelopeCheck c = true) (hE : gammaPrimeEulerCost r.prime ≤ (r.eulerUpper : ℝ)) {x : ℝ}
    (hlox : (c.lo : ℝ) ≤ x) (hxhi : x ≤ (c.hi : ℝ)) :
    Real.log r.prime *
        max (gammaRamifiedSignedCombinedCost r.prime x - gammaRamifiedThetaParameter c.theta x) 0 ≤
      (r.allowance : ℝ) := by
  obtain ⟨hlo, hlohi, hslo, hrootlo, hshi, hroothi, htheta⟩ := c.check_sound hcell
  obtain ⟨hlog, hnum⟩ := Bool.and_eq_true_iff.mp hc
  obtain ⟨hcut, hsize, hr, hcost, hex⟩ := of_decide_eq_true hnum
  have hcostReal := r.cost_le_of_euler_bound c hcell hp hc hE hlox hxhi
  have hmu : (c.theta : ℝ) / c.rootHi ≤ gammaRamifiedThetaParameter c.theta x :=
    div_le_div₀ htheta le_rfl (Real.sqrt_pos.mpr (hlo.trans_le hlox))
      ((Real.sqrt_le_sqrt hxhi).trans hroothi)
  have hd :
    gammaRamifiedSignedCombinedCost r.prime x - gammaRamifiedThetaParameter c.theta x ≤
      (r.costUpper : ℝ) - c.theta / c.rootHi := by
    linarith only [hcostReal, hmu]
  have hEx := (Rat.cast_le (K := ℝ)).mpr hex
  norm_num only [Rat.cast_max, Rat.cast_sub, Rat.cast_div, Rat.cast_zero] at hEx
  have hbound := (max_le_max hd (le_refl (0 : ℝ))).trans hEx
  have hLog := (rationalLogIntervalCheck_sound hlog).2
  norm_num only [Rat.cast_natCast] at hLog
  have hLog0 := Real.log_nonneg (by exact_mod_cast hp.one_le : (1 : ℝ) ≤ r.prime)
  rw [GammaLocalPrimeRow.allowance, Rat.cast_mul]
  exact mul_le_mul hLog hbound (le_max_right _ _) (hLog0.trans hLog)

/-- Input: a finite prime set, checked rows with matching indices, and actual Euler bounds.
Claim: the actual finite signed excess sum is at most the rational row allowance sum.
Proof: sum the uniform row inequalities and commute the rational cast.
Role: connect compact mixed certificates to the factor-independent dual budget. -/
theorem gamma_envelope_prime_sum_upper (R : Finset ℕ) (r : ℕ → GammaLocalPrimeRow)
    (c : GammaLocalCellData) (hcell : c.check = true) (hp : ∀ p ∈ R, p.Prime)
    (hi : ∀ p ∈ R, (r p).prime = p) (hc : ∀ p ∈ R, (r p).envelopeCheck c = true)
    (hE : ∀ p ∈ R, gammaPrimeEulerCost p ≤ ((r p).eulerUpper : ℝ)) {x : ℝ} (hlox : (c.lo : ℝ) ≤ x)
    (hxhi : x ≤ (c.hi : ℝ)) :
    (∑ p ∈ R,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter c.theta x) 0) ≤
      ((∑ p ∈ R, (r p).allowance : ℚ) : ℝ) := by
  rw [Rat.cast_sum]
  apply Finset.sum_le_sum
  intro p hpr
  have hp' : (r p).prime.Prime := (hi p hpr).symm ▸ hp p hpr
  have he' : gammaPrimeEulerCost (r p).prime ≤ ((r p).eulerUpper : ℝ) := (hi p hpr).symm ▸ hE p hpr
  have h := (r p).weighted_excess_le_of_euler_bound c hcell hp' (hc p hpr) he' hlox hxhi
  simpa only [hi p hpr] using h

end PseudoPrime.Analysis
