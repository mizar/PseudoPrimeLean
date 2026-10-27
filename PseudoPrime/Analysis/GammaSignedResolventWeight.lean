/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.Analysis.GammaResolventCertificate
public import PseudoPrime.Analysis.GammaLocalBudget
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Signed Euler weight for the Gamma resolvent

Keep the resolvent coefficients signed before bounding the local prime costs.
-/

@[expose] public section

namespace PseudoPrime.Analysis

/-- Input: a nonnegative antitone weight on the rational nodes.
Claim: the signed resolvent combination is nonnegative.
Proof: combine adjacent differences with the positive cumulative coefficients.
Role: supply positivity without replacing the signed coefficients by absolute values. -/
theorem gammaResolvent_weighted_nonneg (w : ℚ → ℝ) (hw : Antitone w) (hzero : 0 ≤ w 7) :
    0 ≤ (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * w ab.1)).sum := by
  have h1 := hw (by norm_num only : (11 / 20 : ℚ) ≤ 16 / 20)
  have h2 := hw (by norm_num only : (16 / 20 : ℚ) ≤ 20 / 20)
  have h3 := hw (by norm_num only : (20 / 20 : ℚ) ≤ 34 / 20)
  have h4 := hw (by norm_num only : (34 / 20 : ℚ) ≤ 46 / 20)
  have h5 := hw (by norm_num only : (46 / 20 : ℚ) ≤ 64 / 20)
  have h6 := hw (by norm_num only : (64 / 20 : ℚ) ≤ 90 / 20)
  have h7 := hw (by norm_num only : (90 / 20 : ℚ) ≤ 140 / 20)
  norm_num only [gammaResolventCoefficients, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at ⊢ h1 h2 h3 h4 h5 h6 h7
  linarith only [h1, h2, h3, h4, h5, h6, h7, hzero]

/-- The finite signed Euler weight at a real input m.
Definition: sum b times m to the power -(1/2+a) over the certified resolvent nodes.
Input: a real m; positivity will be proved for m at least one.
Output: the combined Euler weight H(m) used in prefix and local corrections. -/
noncomputable def gammaResolventEulerWeight (m : ℝ) : ℝ :=
  (gammaResolventCoefficients.map (fun ab ↦ (ab.2 : ℝ) * m ^ (-(1 / 2 + (ab.1 : ℝ))))).sum

/-- Input: a real m at least one.
Claim: the signed Euler weight is nonnegative for every such m.
Proof: the real powers decrease with the rational node; apply the finite certificate.
Role: justify the signed prefix and local losses for all prime powers. -/
theorem gamma_resolvent_euler_weight_nonneg {m : ℝ} (hm : 1 ≤ m) :
    0 ≤ gammaResolventEulerWeight m := by
  have hanti : Antitone (fun a : ℚ ↦ m ^ (-(1 / 2 + (a : ℝ)))) := by
    intro a b hab
    exact Real.rpow_le_rpow_of_exponent_le hm (neg_le_neg (add_le_add le_rfl (Rat.cast_le.mpr hab)))
  exact gammaResolvent_weighted_nonneg _ hanti (Real.rpow_nonneg (zero_le_one.trans hm) _)

/-- Input: finite inputs at least one and real character values at least minus one.
Claim: the signed Euler sum retains the prefix gain and its local correction.
Proof: keep the prefix contribution exact and bound the complement using positivity.
Role: finite-sum interface for the signed Poisson prefix estimate. -/
theorem gamma_signed_euler_prefix_le {ι : Type*} [DecidableEq ι] (S B : Finset ι) (m c : ι → ℝ)
    (hm : ∀ i ∈ S, 1 ≤ m i) (hc : ∀ i ∈ S, -1 ≤ c i) :
    ∑ i ∈ S, -c i * gammaResolventEulerWeight (m i) ≤
      (∑ i ∈ S, gammaResolventEulerWeight (m i)) -
          2 * (∑ i ∈ S, if i ∈ B then gammaResolventEulerWeight (m i) else 0) +
        ∑ i ∈ S, if i ∈ B then (1 - c i) * gammaResolventEulerWeight (m i) else 0 := by
  have hp :=
    Finset.sum_le_sum (s := S)
      (fun i hi ↦
        show
          -c i * gammaResolventEulerWeight (m i) ≤
            gammaResolventEulerWeight (m i) -
                2 * (if i ∈ B then gammaResolventEulerWeight (m i) else 0) +
              (if i ∈ B then (1 - c i) * gammaResolventEulerWeight (m i) else 0)
          from by
          split_ifs with h
          · ring_nf; exact le_rfl
          · nlinarith only [hc i hi, gamma_resolvent_euler_weight_nonneg (hm i hi)])
  simpa only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum] using hp

end PseudoPrime.Analysis
