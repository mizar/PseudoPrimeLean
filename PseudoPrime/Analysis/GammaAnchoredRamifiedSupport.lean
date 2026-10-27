/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaRamifiedDualParameterBounds
public import PseudoPrime.Analysis.GammaDyadicAnchorBounds

/-! # Anchored reciprocal envelopes shrink the signed ramified support -/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: anchor a, reciprocal coefficient B, dual parameter theta and scale x.
Definition: maximum of the anchor, second-power cutoff and anchored Euler threshold.
Role: bound the support of signed dual excess without new prime tables. -/
noncomputable def gammaAnchoredThetaCutoff (a B θ x : ℝ) : ℝ :=
  max a (max (Real.sqrt ((99 / 40 : ℝ) * x)) (1 + B * Real.sqrt x / (θ - 1)))

/-- Input: theta > 1, x >= 1 and a reciprocal Euler envelope beyond a.
Claim: every prime above the anchored cutoff has cost below theta/sqrt(x).
Use the envelope and the one-power count bound. Role: shrink finite support. -/
theorem gamma_ramified_cost_lt_anchored_theta {p : ℕ} (hp : 1 < p) {a B θ x : ℝ} (hθ : 1 < θ)
    (hx : 1 ≤ x) (hEuler : ∀ p : ℝ, 1 < p → a ≤ p → gammaPrimeEulerCost p ≤ B / (p - 1))
    (hpbig : gammaAnchoredThetaCutoff a B θ x < p) :
    gammaRamifiedCombinedCost p x < gammaRamifiedThetaParameter θ x := by
  have hx0 := zero_lt_one.trans_le hx
  have hs := Real.sqrt_pos.mpr hx0
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  have hθ0 := sub_pos.mpr hθ
  have ha : a < p := (le_max_left _ _).trans_lt hpbig
  have htail := (le_max_right _ _).trans_lt hpbig
  have hsqrt : Real.sqrt ((99 / 40 : ℝ) * x) < p := (le_max_left _ _).trans_lt htail
  have hbig : 1 + B * Real.sqrt x / (θ - 1) < p := (le_max_right _ _).trans_lt htail
  have hcut : (99 / 40 : ℝ) * x < (p : ℝ) ^ 2 := by
    have ht :=
      (sq_lt_sq₀ (Real.sqrt_nonneg ((99 / 40 : ℝ) * x)) (zero_lt_one.trans hpR).le).mpr hsqrt
    rw [Real.sq_sqrt (mul_nonneg (by norm_num only) hx0.le)] at ht
    exact ht
  have hprod :=
    (div_lt_iff₀ hθ0).mp (show B * Real.sqrt x / (θ - 1) < (p : ℝ) - 1 by linarith only [hbig])
  have hd : B / ((p : ℝ) - 1) < (θ - 1) / Real.sqrt x := by
    apply (div_lt_div_iff₀ (sub_pos.mpr hpR) hs).mpr
    nlinarith only [hprod]
  have he := hEuler p hpR ha.le
  have hr := gamma_ramp_count_le_one_of_square_above hp hx hcut
  have hb := add_lt_add_of_lt_of_le (he.trans_lt hd) (div_le_div_of_nonneg_right hr hs.le)
  have heq : (θ - 1) / Real.sqrt x + 1 / Real.sqrt x = θ / Real.sqrt x := by ring
  simpa only [gammaRamifiedCombinedCost, gammaRamifiedThetaParameter, heq] using hb

end PseudoPrime.Analysis

namespace PseudoPrime.Analysis

/-- Input: the anchored tail hypotheses. Claim: the signed positive excess is
zero beyond the cutoff. Compare signed and count-based costs.
Role: remove every unsupported prime from the actual dual sum. -/
theorem gamma_anchored_signed_excess_eq_zero {p : ℕ} (hp : 1 < p) {a B θ x : ℝ} (hθ : 1 < θ)
    (hx : 1 ≤ x) (hEuler : ∀ p : ℝ, 1 < p → a ≤ p → gammaPrimeEulerCost p ≤ B / (p - 1))
    (hpbig : gammaAnchoredThetaCutoff a B θ x < p) :
    max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0 = 0 := by
  apply max_eq_right
  exact
    sub_nonpos.mpr
      ((gamma_ramified_signed_cost_le_combined hp (zero_lt_one.trans_le hx)).trans
        (gamma_ramified_cost_lt_anchored_theta hp hθ hx hEuler hpbig).le)

/-- Input: an odd-prime set and a common upper bound K on the anchored cutoff.
Claim: its signed excess is bounded by the sum over odd primes through K.
Use exact tail vanishing and nonnegative summands. Role: reuse compact supports. -/
theorem gamma_anchored_signed_excess_le_certificate (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime ∧ 3 ≤ p)
    {a B θ x K : ℝ} (hθ : 1 < θ) (hx : 1 ≤ x)
    (hEuler : ∀ p : ℝ, 1 < p → a ≤ p → gammaPrimeEulerCost p ≤ B / (p - 1))
    (hcap : gammaAnchoredThetaCutoff a B θ x ≤ K) :
    (∑ p ∈ S,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0) ≤
      ∑ p ∈ gammaRamifiedCertificatePrimeSet K,
        Real.log p *
          max (gammaRamifiedSignedCombinedCost p x - gammaRamifiedThetaParameter θ x) 0 := by
  have hK : 0 ≤ K :=
    (Real.sqrt_nonneg _).trans ((le_max_left _ _).trans ((le_max_right _ _).trans hcap))
  apply gamma_supported_sum_le_finite
  · intro p hp hn
    have hfloor : ⌊K⌋₊ < p := by
      apply lt_of_not_ge
      intro hle
      exact hn (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨(hS p hp).2, hle⟩, (hS p hp).1⟩)
    rw [gamma_anchored_signed_excess_eq_zero (hS p hp).1.one_lt hθ hx hEuler
        (hcap.trans_lt ((Nat.floor_lt hK).mp hfloor)),
      mul_zero]
  · intro p hp
    exact
      mul_nonneg (Real.log_nonneg (by exact_mod_cast (Finset.mem_filter.mp hp).2.one_le))
        (le_max_right _ _)

/-- Input: real p >= 160 and p > 1. Claim: its full Euler cost is at most
(13/25)/(p-1). Reuse the existing dyadic anchor. Role: improve the old positive
coefficient bound without adding numerical data. -/
theorem gamma_euler_anchor160_reciprocal {p : ℝ} (hp : 1 < p) (ha : 160 ≤ p) :
    gammaPrimeEulerCost p ≤ (13 / 25 : ℝ) / (p - 1) := by
  have h :=
    gamma_prime_euler_cost_le_dyadic_anchor (a := 160) (by decide +kernel) hp
      (by
        norm_num only; exact ha)
  norm_num only [gammaDyadicAnchorCap, Rat.cast_div, Rat.cast_ofNat] at h
  exact h

/-- Input: x >= 1. Claim: the anchor-160, theta-5/4 cutoff is at most
max(160,1+(52/25)sqrt(x)). Bound the square-root branch algebraically.
Role: reduce the certificate support uniformly over arbitrary scales. -/
theorem gamma_anchor160_cutoff_le {x : ℝ} (hx : 1 ≤ x) :
    gammaAnchoredThetaCutoff 160 (13 / 25) (5 / 4) x ≤
      max 160 (1 + (52 / 25 : ℝ) * Real.sqrt x) := by
  have hx0 := (zero_lt_one.trans_le hx).le
  have hr : Real.sqrt ((99 / 40 : ℝ) * x) ≤ (52 / 25 : ℝ) * Real.sqrt x := by
    apply (Real.sqrt_le_iff).mpr
    exact
      ⟨mul_nonneg (by norm_num only) (Real.sqrt_nonneg x), by
        nlinarith only [Real.sq_sqrt hx0, hx0]⟩
  dsimp only [gammaAnchoredThetaCutoff]
  norm_num only
  apply max_le_max (le_refl (160 : ℝ))
  apply max_le
  · linarith only [hr]
  · ring_nf
    exact le_rfl

end PseudoPrime.Analysis
